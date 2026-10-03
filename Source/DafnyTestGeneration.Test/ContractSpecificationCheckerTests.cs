#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractSpecificationCheckerTests {
  // Logical well-formedness never supplies the separate native correctness obligation of a by-method.
  [Theory]
  [InlineData(true, true)]
  [InlineData(true, false)]
  [InlineData(false, true)]
  [InlineData(false, false)]
  public async Task SeparatesLogicalAndExecutionCertificates(bool validDefinition, bool matchingImplementation) {
    var definition = validDefinition ? "x" : "x + 1";
    var implementation = matchingImplementation ? definition : validDefinition ? "x + 1" : "x";
    var (program, checker) = await Parse("module Model { function Root(x:int):(r:int) ensures r == x { " +
      definition + " } by method { return " + implementation + "; } }");
    var root = Functions(program).Single();
    var logical = checker.LogicalScope([root]);
    var execution = checker.Scope([root]);
    Assert.NotEqual(logical.CacheIdentity, execution.CacheIdentity);
    Assert.DoesNotContain("Model.Root (correctness)", logical.RequiredNativeChecks);
    Assert.Contains("Model.Root (correctness)", execution.RequiredNativeChecks);
    Assert.Equal(validDefinition, await Complete(checker, logical));
    Assert.False(checker.IsValidated(root));
    Assert.False(checker.IsValidated(root.ByMethodDecl!));
    Assert.Equal(validDefinition && matchingImplementation, await Complete(checker, execution));
    Assert.Equal(validDefinition && matchingImplementation, checker.IsValidated(root));
  }

  // A dependency used only in a compiled by-method remains in execution reachability, never in logical reachability.
  [Fact]
  public async Task LogicalReachabilityExcludesOnlyCompiledBodyDependencies() {
    var (program, checker) = await Parse("""
      module Model {
        function Bad():int requires false { 0 }
        function Root(x:int):int { x } by method { return Bad(); }
      }
      """);
    var root = Functions(program).Single(function => function.Name == "Root");
    var logical = checker.LogicalScope([root]);
    var execution = checker.Scope([root]);
    Assert.DoesNotContain("Function:Model.Bad", logical.Symbols);
    Assert.Contains("Function:Model.Bad", execution.Symbols);
    Assert.True(await Complete(checker, logical));
    Assert.False(await Complete(checker, execution));
    Assert.False(checker.IsValidated(root));
  }

  // Logical traversal preserves defaults, reads, direct call preconditions and result refinement checks.
  [Theory]
  [InlineData("function Root(x:int := Bad()):int { x }")]
  [InlineData("function Root():int { Bad() }")]
  [InlineData("function Root():nat { -1 }")]
  [InlineData("function Root():(x:int) ensures x == 1 { 0 }")]
  public async Task LogicalScopeRetainsOriginalWellFormedness(string declaration) {
    var (program, checker) = await Parse("module Model { function Bad():int requires false { 0 } " + declaration + " }");
    var scope = checker.LogicalScope([Functions(program).Single(function => function.Name == "Root")]);
    Assert.False(await Complete(checker, scope));
    Assert.False(checker.Accept(scope));
  }

  // Proof methods in original function bodies retain full native correctness, even without function-call edges.
  [Theory]
  [InlineData("true", true)]
  [InlineData("false", false)]
  public async Task LogicalScopeChecksInvokedProofMethods(string condition, bool expected) {
    var (program, checker) = await Parse("module Model { lemma Proof() ensures " + condition +
      " {} function Root():int { Proof(); 0 } }");
    var scope = checker.LogicalScope([Functions(program).Single()]);
    Assert.Contains("Model.Proof (well-formedness)", scope.RequiredNativeChecks);
    Assert.Contains("Model.Proof (correctness)", scope.RequiredNativeChecks);
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // Direct entry-contract proof statements and constants cannot disappear when there are no function roots.
  [Theory]
  [InlineData("lemma Bad() ensures false {}", "(Bad(); true)", "Lemma:Model.Bad")]
  [InlineData("const Bad:nat := -1", "Bad >= 0", "ConstantField:Model.Bad")]
  public async Task LogicalExpressionIncludesDirectProofAndConstantDependencies(string dependency, string expression, string symbol) {
    var (program, checker) = await Parse("module Model { " + dependency + " method Goal() ensures " + expression + " {} }");
    var goal = ContractRuntimeObligationTransformer.Members(program).OfType<Method>().Single(method => method.Name == "Goal");
    var scope = checker.LogicalScope(goal.Ens.Single().E);
    Assert.Contains(symbol, scope.Symbols);
    Assert.False(await Complete(checker, scope));
  }

  // A proof assumption directly in an entry contract is rejected even if its expression has no dependencies.
  [Fact]
  public async Task LogicalExpressionRejectsDirectAssumption() {
    var (program, checker) = await Parse("module Model { method Goal() ensures (assume false; true) {} }");
    var goal = ContractRuntimeObligationTransformer.Members(program).OfType<Method>().Single();
    var scope = checker.LogicalScope(goal.Ens.Single().E);
    Assert.Contains("assume", scope.Failure!);
    Assert.False(checker.Accept(scope));
  }

  // Logical proofs preserve original trust rejection in definitions, contracts and invoked proof bodies.
  [Theory]
  [InlineData("function Root():int { assume false; 0 }")]
  [InlineData("function {:axiom} Root():int")]
  [InlineData("function {:extern} Root():int")]
  [InlineData("lemma Bad() ensures false { assume false; } function Root():int { Bad(); 0 }")]
  [InlineData("lemma Bad() { assert {:only} true; } function Root():int { Bad(); 0 }")]
  public async Task LogicalScopeRejectsTrustEscapes(string source) {
    var (program, checker) = await Parse("module Model { " + source + " }");
    var scope = checker.LogicalScope([Functions(program).Single()]);
    Assert.NotNull(scope.Failure);
    Assert.False(await Complete(checker, scope));
  }

  // Proof statements in a declared type witness remain dependencies of a logical result type.
  [Theory]
  [InlineData("true", true)]
  [InlineData("false", false)]
  public async Task LogicalTypeWitnessIncludesProofStatements(string condition, bool expected) {
    var (program, checker) = await Parse("module Model { lemma Proof() ensures " + condition +
      " {} type Count = n:int | n >= 0 ghost witness (Proof(); 0) function Root():Count { 0 } }");
    var scope = checker.LogicalScope([Functions(program).Single()]);
    Assert.Contains("Lemma:Model.Proof", scope.Symbols);
    Assert.Contains("SubsetTypeDecl:Model.Count", scope.Symbols);
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // Scope ownership and exact declaration identity reject another parsed program even at the same path and name.
  [Fact]
  public async Task RoleScopesCannotMoveAcrossCheckersOrSourcePrograms() {
    const string source = "module Model { function Root(x:int):int { x } by method { return x; } }";
    var (program, checker) = await Parse(source);
    var (otherProgram, otherChecker) = await Parse(source.Replace("return x;", "return x + 1;"));
    var logical = checker.LogicalScope([Functions(program).Single()]);
    Assert.True(await Complete(checker, logical));
    Assert.False(otherChecker.Accept(logical));
    Assert.False((await otherChecker.CheckModuleAsync(logical, "Model", CancellationToken.None)).Verified);
    Assert.NotNull(checker.LogicalScope([Functions(otherProgram).Single()]).Failure);
    Assert.NotEqual(logical.CacheIdentity, otherChecker.LogicalScope([Functions(otherProgram).Single()]).CacheIdentity);
  }

  // Original imported definition visibility remains necessary even after that definition earns its own certificate.
  [Theory]
  [InlineData("provides", false)]
  [InlineData("reveals", true)]
  public async Task LogicalCertificatesKeepOriginalImportVisibility(string visibility, bool expected) {
    var (program, checker) = await Parse("module Library { export " + visibility +
      " Value function Value():int { 0 } } module Model { import L=Library function Root():nat { L.Value() } }");
    var scope = checker.LogicalScope([Functions(program).Single(function => function.Name == "Root")]);
    Assert.Contains("Function:Library.Value", scope.Symbols);
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // Equal member names in different imported modules cannot exchange proof obligations or source identity.
  [Theory]
  [InlineData("Good", true)]
  [InlineData("Bad", false)]
  public async Task LogicalCertificatesKeepImportedNamesDistinct(string dependency, bool expected) {
    var (program, checker) = await Parse("module Good { function Value():int { 0 } } " +
      "module Bad { function Value():int { -1 } } module Model { import Good import Bad " +
      "function Root():nat { " + dependency + ".Value() } }");
    var scope = checker.LogicalScope([Functions(program).Single(function => function.Name == "Root")]);
    Assert.Contains("Function:" + dependency + ".Value", scope.Symbols);
    Assert.DoesNotContain("Function:" + (dependency == "Good" ? "Bad" : "Good") + ".Value", scope.Symbols);
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // Invoked proof overrides retain their native override check in addition to both bodies' correctness.
  [Theory]
  [InlineData("n >= 0", true)]
  [InlineData("n > 0", false)]
  public async Task LogicalProofMethodsRetainOverrideObligations(string requirement, bool expected) {
    var (program, checker) = await Parse("module Model { " +
      "trait Parent extends object { lemma Proof(n:int) requires n >= 0 ensures n >= 0 {} } " +
      "class Child extends Parent { lemma Proof(n:int) requires " + requirement + " ensures n >= 0 {} } " +
      "function Root(child:Child):int { child.Proof(1); 0 } }");
    var scope = checker.LogicalScope([Functions(program).Single()]);
    Assert.Contains("Model.Child.Proof (override check)", scope.RequiredNativeChecks);
    Assert.Contains("Model.Parent.Proof (correctness)", scope.RequiredNativeChecks);
    Assert.Contains("Model.Child.Proof (correctness)", scope.RequiredNativeChecks);
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // An unused contradictory function contract cannot prove a false original result refinement.
  [Fact]
  public async Task LogicalCertificateDoesNotUseUnrelatedFalseEnsures() {
    var (program, checker) = await Parse("module Model { function Poison():bool ensures false { true } function Root():nat { -1 } }");
    var scope = checker.LogicalScope([Functions(program).Single(function => function.Name == "Root")]);
    Assert.DoesNotContain("Function:Model.Poison", scope.Symbols);
    Assert.False(await Complete(checker, scope));
  }

  // Native certification checks transitive implementation postconditions before exposing a usable certificate.
  [Theory]
  [InlineData("x", true)]
  [InlineData("x + 1", false)]
  public async Task ChecksTransitivePostcondition(string body, bool expected) {
    var (program, checker) = await Parse("""
      module Model {
        function Leaf(x: int): (r: int) ensures r == x { BODY }
        ghost predicate Root(x: int) { Leaf(x) == x }
      }
      """.Replace("BODY", body));
    var root = Functions(program).Single(function => function.Name == "Root");
    var scope = checker.Scope([root]);
    Assert.Equal(expected, await Complete(checker, scope));
    Assert.Equal(expected, checker.IsValidated(root));
  }

  // A requires-only dependency does not hide an ill-defined call in a contract-free caller.
  [Theory]
  [InlineData("x >= 0 && Leaf(x) == x", true)]
  [InlineData("Leaf(x) == x", false)]
  public async Task ChecksTransitivePreconditions(string body, bool expected) {
    var (program, checker) = await Parse("""
      module Model {
        function Leaf(x: int): int requires x >= 0 { x }
        ghost predicate Root(x: int) { BODY }
      }
      """.Replace("BODY", body));
    Assert.Equal(expected, await Complete(checker, checker.Scope([Functions(program).Single(function => function.Name == "Root")])));
  }

  // A declared subset witness is proved with its actual constraint and is not accepted by its declared type.
  [Theory]
  [InlineData("0", true)]
  [InlineData("-1", false)]
  public async Task ChecksOriginalSubsetWitness(string witness, bool expected) {
    var (program, checker) = await Parse("""
      module Model {
        function Leaf(x: int): int requires x >= 0 { x }
        ghost predicate Valid(x: int) { x >= 0 && Leaf(x) == x }
        type Positive = x: int | Valid(x) witness WITNESS
        class Cell { ghost var unused: Positive }
      }
      """.Replace("WITNESS", witness));
    var initial = new[] { new ContractHeapObject("cell", "Model.Cell", new Dictionary<string, ContractValue>()) };
    var scope = checker.Scope([], ContractRuntimeHeapChecking.InitialTypes(program, initial));
    Assert.Contains(scope.Symbols, symbol => symbol.EndsWith(":Model.Positive", StringComparison.Ordinal));
    Assert.Equal(expected, await Complete(checker, scope));
    if (expected) { Assert.True(ContractRuntimeHeapChecking.CheckInitialTypes(program, initial, checker)); }
  }

  // Alias chains have no native WF procedure, while their underlying refinement and witness still require proof.
  [Theory]
  [InlineData("0", true)]
  [InlineData("-1", false)]
  public async Task AliasChainsRetainUnderlyingRefinement(string witness, bool expected) {
    var (program, checker) = await Parse("""
      module Model {
        type Count = value:int | value >= 0 witness WITNESS
        type Alias = Count
        type Rows<T> = seq<T>
        type Values = Rows<Alias>
        ghost predicate Root(values:Values) { forall i :: 0 <= i < |values| ==> values[i] >= 0 }
      }
      """.Replace("WITNESS", witness));
    var root = Functions(program).Single(function => function.Name == "Root");
    var dependencies = new HashSet<Declaration>();
    ContractRuntimeObligationTransformer.ExecutionReachable(program, [root], declarationDependencies: dependencies);
    Assert.Contains(dependencies, declaration => declaration is TypeSynonymDecl and not SubsetTypeDecl);
    var scope = checker.Scope([root]);
    Assert.Contains(scope.Symbols, symbol => symbol.EndsWith(":Model.Count", StringComparison.Ordinal));
    Assert.DoesNotContain(scope.Symbols, symbol => symbol.StartsWith("ConcreteTypeSynonymDecl:", StringComparison.Ordinal));
    Assert.Equal(expected, await Complete(checker, scope));
  }

  // A function-by-method must prove that its implementation returns the logical function result.
  [Theory]
  [InlineData("x", true, false)]
  [InlineData("x + 1", false, false)]
  [InlineData("x", true, true)]
  [InlineData("x + 1", false, true)]
  public async Task ChecksByMethodEquality(string result, bool expected, bool sourceSkipped) {
    var (program, checker) = await Parse("module " + (sourceSkipped ? "{:verify false}" : "") +
      " Model { function Root(x: int): int { x } by method { return " + result + "; } }");
    Assert.Equal(expected, await Complete(checker, checker.Scope([Functions(program).Single(function => function.Name == "Root")])));
  }

  // Source assumptions and absent implementations cannot produce specification certificates, even under a source skip.
  [Theory]
  [InlineData("function {:axiom} Root(x: int): int")]
  [InlineData("function Root(x: int): int")]
  [InlineData("function Root(x: int): int { x } by method { assume false; return x; }")]
  [InlineData("function {:verify false} Root(x: int): int { x } by method { assume false; return x; }")]
  public async Task RejectsTrustDependencies(string declaration) {
    var (program, checker) = await Parse("module Model { " + declaration + " }");
    var scope = checker.Scope([Functions(program).Single(function => function.Name == "Root")]);
    Assert.NotNull(scope.Failure);
    Assert.False(checker.Accept(scope));
  }

  // A skipped source body earns a certificate only by passing actual native checks in a private copy.
  [Theory]
  [InlineData("module", "x", true)]
  [InlineData("module", "x + 1", false)]
  [InlineData("class", "x", true)]
  [InlineData("class", "x + 1", false)]
  [InlineData("member", "x", true)]
  [InlineData("member", "x + 1", false)]
  public async Task RechecksSourceSkippedBodies(string owner, string body, bool expected) {
    string Skip(string kind) => owner == kind ? "{:verify false}" : "";
    var (program, checker) = await Parse("module " + Skip("module") + " Model { class " + Skip("class") +
      " Box { function " + Skip("member") + " Root(x:int): (r:int) ensures r == x { " + body + " } } }");
    var root = Functions(program).Single();
    var module = root.EnclosingClass.EnclosingModuleDefinition;
    var before = new[] { module.Attributes?.ToString(), root.EnclosingClass.Attributes?.ToString(), root.Attributes?.ToString() };
    var scope = checker.Scope([root]);
    Assert.Null(scope.Failure);
    var result = await checker.CheckModuleAsync(scope, "Model", CancellationToken.None);
    Assert.NotEmpty(result.Implementations);
    Assert.Equal(expected, result.Verified);
    Assert.Equal(expected, checker.Accept(scope));
    Assert.Equal(expected, checker.IsValidated(root));
    Assert.Equal(before, new[] { module.Attributes?.ToString(), root.EnclosingClass.Attributes?.ToString(), root.Attributes?.ToString() });
  }

  // Re-enabling a skipped type owner still checks the actual subset witness before exposing inhabitance.
  [Theory]
  [InlineData(0, true)]
  [InlineData(-1, false)]
  public async Task RechecksSourceSkippedWitness(int witness, bool expected) {
    var (program, checker) = await Parse("module {:verify false} Model { type Count = value:int | value >= 0 witness " +
      witness + " class Cell { ghost var unused:Count } }");
    var heap = new[] { new ContractHeapObject("cell", "Model.Cell", new Dictionary<string, ContractValue>()) };
    var scope = checker.Scope([], ContractRuntimeHeapChecking.InitialTypes(program, heap));
    Assert.Null(scope.Failure);
    var result = await checker.CheckModuleAsync(scope, "Model", CancellationToken.None);
    Assert.NotEmpty(result.Implementations);
    Assert.Equal(expected, result.Verified);
    Assert.Equal(expected, checker.Accept(scope));
  }

  // Constructor-initialized immutable instance slots retain their refined types without inventing a missing native body proof.
  [Fact]
  public async Task InstanceConstantRetainsTypeDependencies() {
    var (program, checker) = await Parse("""
      module Model {
        type Positive = value:int | value >= 0 witness 0
        class Cell {
          const slot:Positive
          constructor(value:Positive) { slot := value; }
          function Root(): (r:int) reads this ensures r >= 0 { slot }
        }
      }
      """);
    var root = Functions(program).Single();
    var scope = checker.Scope([root]);
    Assert.Contains(scope.Symbols, symbol => symbol.EndsWith(":Model.Positive", StringComparison.Ordinal));
    Assert.DoesNotContain(scope.Symbols, symbol => symbol.Contains("ConstantField", StringComparison.Ordinal));
    Assert.True(await Complete(checker, scope));
  }

  // A bodyless static constant is not a captured immutable heap slot and remains an unsupported source assumption.
  [Fact]
  public async Task RejectsBodylessStaticConstant() {
    var (program, checker) = await Parse("module Model { static const value:int function Root():int { value } }");
    var scope = checker.Scope([Functions(program).Single()]);
    Assert.Contains("bodyless constant", scope.Failure);
    Assert.False(checker.Accept(scope));
  }

  // Exact declaration ownership excludes an unrelated same-named function with a false contract.
  [Fact]
  public async Task DoesNotConfuseSameNamedDeclarations() {
    var (program, checker) = await Parse("""
      module Good { function Root(x: int): (r: int) ensures r == x { x } }
      module Bad { function Root(x: int): (r: int) ensures false { x } }
      """);
    var root = Functions(program).Single(function => function.FullDafnyName == "Good.Root");
    var scope = checker.Scope([root]);
    Assert.Equal(new[] { "Good" }, checker.PendingModules(scope));
    var result = await checker.CheckModuleAsync(scope, "Good", CancellationToken.None);
    Assert.True(result.Verified, result.Diagnostics);
    Assert.Equal(result.Implementations.Count, result.VerifiedCount);
    Assert.True(checker.Accept(scope));
    Assert.False(checker.IsValidated(Functions(program).Single(function => function.FullDafnyName == "Bad.Root")));
  }

  // Native procedures with no assertions are covered explicitly rather than requiring a fake verified count.
  [Fact]
  public async Task RecordsAssertionFreeDeclaration() {
    var (program, checker) = await Parse("module Model { function Root(x: int): int { x } }");
    var scope = checker.Scope([Functions(program).Single()]);
    var result = await checker.CheckModuleAsync(scope, "Model", CancellationToken.None);
    Assert.True(result.Verified, result.Diagnostics);
    Assert.Contains("Model.Root", result.AssertionFreeDeclarations);
    Assert.Empty(result.Implementations);
    Assert.True(checker.Accept(scope));
  }

  // A proved module prefix cannot authorize a caller until every dependency module also succeeds.
  [Fact]
  public async Task PartialModuleSuccessDoesNotReleaseCertificate() {
    var (program, checker) = await Parse("""
      module A { function Leaf(x: int): (r: int) ensures r == x { x } }
      module B { function Leaf(x: int): (r: int) ensures r == x { x + 1 } }
      module C { import A import B ghost predicate Root(x: int) { A.Leaf(x) == B.Leaf(x) } }
      """);
    var root = Functions(program).Single(function => function.Name == "Root");
    var scope = checker.Scope([root]);
    Assert.True((await checker.CheckModuleAsync(scope, "A", CancellationToken.None)).Verified);
    Assert.False(checker.Accept(scope));
    Assert.False(checker.IsValidated(root));
    Assert.False(await Complete(checker, scope));
    Assert.False(checker.IsValidated(root));
  }

  // A deadline observed after native verification prevents the finished proof from entering the certificate cache.
  [Fact]
  public async Task CancellationAfterSolverDoesNotAcceptModule() {
    var (program, checker) = await Parse("module Model { function Root(x: int): (r: int) ensures r == x { x } }");
    var scope = checker.Scope([Functions(program).Single()]);
    using var cancellation = new CancellationTokenSource();
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => checker.CheckModuleAsync(scope, "Model", cancellation.Token,
      (phase, state) => { if (phase == "boogie:Model" && state == "completed") { cancellation.Cancel(); } }));
    Assert.False(checker.Accept(scope));
    Assert.Equal(new[] { "Model" }, checker.PendingModules(scope));
  }

  // A late native proof cannot enter the certificate cache even when its cancellation token remains uncancelled.
  [Fact]
  public async Task MonotonicDeadlinePreventsLateCertificate() {
    var (program, checker) = await Parse("module Model { function Root(x: int): (r: int) ensures r == x { x } }");
    var scope = checker.Scope([Functions(program).Single()]);
    var deadline = ContractQueryDeadline.AfterMilliseconds(3000);
    var sawSolver = false;
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => checker.CheckModuleAsync(scope, "Model", CancellationToken.None,
      (phase, state) => {
        if (phase == "boogie:Model" && state == "completed") {
          sawSolver = true;
          while (System.Diagnostics.Stopwatch.GetTimestamp() < deadline) { Thread.Sleep(5); }
        }
      }, deadline));
    Assert.True(sawSolver);
    Assert.False(checker.Accept(scope));
    Assert.Equal(new[] { "Model" }, checker.PendingModules(scope));
  }

  private static async Task<bool> Complete(ContractSpecificationChecker checker, ContractSpecificationScope scope) {
    if (scope.Failure != null) { return false; }
    foreach (var module in checker.PendingModules(scope)) {
      var result = await checker.CheckModuleAsync(scope, module, CancellationToken.None);
      if (!result.Verified) { return false; }
    }
    return checker.Accept(scope);
  }

  private static IEnumerable<Function> Functions(Program program) => program.RawModules()
    .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
    .SelectMany(declaration => declaration.Members).OfType<Function>();

  private static async Task<(Program, ContractSpecificationChecker)> Parse(string text) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var source = new ContractSource("specification.dfy", text, ContractHarnessBuilder.Hash(text));
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, [source], CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    return (program, new(program, [source], options));
  }
}
