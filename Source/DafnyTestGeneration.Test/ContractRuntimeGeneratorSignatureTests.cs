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

// Test boundary trace: every helper parses or transforms bounded source strings in memory. No helper creates a
// directory, starts a process, invokes a native compiler or solver, synchronizes storage, or schedules cleanup.
public class ContractRuntimeGeneratorSignatureTests {
  // A legacy static goal keeps the established random-source name and output order.
  [Fact]
  public async Task FormatsLegacyStaticSignature() {
    var (program, _, _) = await Parse("module M { method Goal(x: int, flag: bool) {} }");
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);

    Assert.Equal("method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int, flag: bool)",
      ContractRuntimeGeneratorSignature.Format(goal));
  }

  // Existing module-level names reserve each earlier generator name in the deterministic zero chain.
  [Theory]
  [InlineData("method Generate() {}", "Generate0")]
  [InlineData("method Generate() {} method Generate0() {}", "Generate00")]
  public async Task PreparesFreshGeneratorMemberName(string laterDeclarations, string expectedName) {
    var source = "module M { method Goal(x: int) {} " + laterDeclarations + " }";
    var generator = "method {:pbt_generator \"M.Goal\"} " + expectedName +
      "(r: PbtRandom.Source) returns (x: int) { x := 1; }";
    var (program, options, sources) = await Parse(source);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);

    Assert.Contains("} " + expectedName + "(r: PbtRandom.Source)",
      ContractRuntimeGeneratorSignature.Format(goal), StringComparison.Ordinal);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(program, sources, goal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    Assert.Equal(expectedName, prepared.GeneratorMethodName);
    var preparedSources = WithRuntime(prepared.Sources);
    var resolved = await Resolve(preparedSources, options);
    var preparedGoal = ContractCallableSelector.SelectMethod(resolved, new("M.Goal"), requireConcreteReceiver: false);
    var selected = ContractRuntimeGeneratorSignature.Select(resolved, preparedGoal, prepared.GeneratorMethodName);

    Assert.Equal(expectedName, selected.Name);
    var reachable = ContractRuntimeObligationTransformer.DiagnosticReachable(resolved, preparedGoal, selected).ToList();
    Assert.Contains(selected, reachable);
    Assert.DoesNotContain(reachable, method => method.Name == "Generate" && !ReferenceEquals(method, selected));
    var transformed = new ContractRuntimeObligationTransformer(resolved, preparedSources, preparedGoal,
      selectedGenerator: selected).Transform();
    Assert.Contains(expectedName + "(pbtRandom)",
      transformed.Sources.Single(source => source.Path == "M.dfy").Content, StringComparison.Ordinal);
    await Resolve(transformed.Sources, options);
  }

  // A goal that itself owns a reserved runtime name retains its identity through exact selection and wrapper emission.
  [Theory]
  [InlineData("Generate", "Generate0", "PbtMain")]
  [InlineData("PbtMain", "Generate", "PbtMain0")]
  public async Task TransformsSelectedTargetNamedForRuntimeMember(string goalName, string generatorName,
    string mainName) {
    var source = "module M { method " + goalName +
      "(x: int) returns (y: int) requires x >= 0 { y := x; } }";
    var generator = "method {:pbt_generator \"M." + goalName + "\"} " + generatorName +
      "(r: PbtRandom.Source) returns (x: int) { x := 1; }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M." + goalName),
      requireConcreteReceiver: false);

    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M." + goalName), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);
    var transformed = new ContractRuntimeObligationTransformer(program, preparedSources, goal, prepared.SourceMap,
      selectedGenerator: selectedGenerator).Transform();

    Assert.Equal(generatorName, prepared.GeneratorMethodName);
    Assert.Equal(generatorName, selectedGenerator.Name);
    Assert.Equal("M." + mainName, transformed.MainName);
    Assert.Contains(generatorName + "(pbtRandom)",
      ContractSourceSnapshot.Find(transformed.Sources, goal.Origin.Uri).Content, StringComparison.Ordinal);
    Assert.Contains(transformed.Clauses, clause => clause.Owner.FullDafnyName == "M." + goalName &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition);
    await Resolve(transformed.Sources, options);
  }

  // A draft helper cannot consume the generator name already reported from the original module.
  [Fact]
  public async Task RejectsDraftHelperTakingReportedGeneratorName() {
    const string source = "module M { method Helper(x: int) returns (y: int) { assert false; } " +
      "method Goal(x: int) returns (y: int) { y := Helper(x); } }";
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := Make(x); } " +
      "method Generate(x: int) returns (y: int) { y := x; } method Make(x: int) returns (y: int) { y := x; }";
    const string generator =
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }";
    var (program, options, sources) = await Parse(source);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var drafts = new[] { new ContractRuntimeDraft("M.Helper", "Helper.dfy", draft, ContractHarnessBuilder.Hash(draft)) };

    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      ContractRuntimeSourcePreparation.PrepareAsync(program, sources, goal, drafts, Source("Generator.dfy", generator),
        options, CancellationToken.None));

    Assert.Contains("Generate", error.Message, StringComparison.Ordinal);
    Assert.Contains("collides", error.Message, StringComparison.Ordinal);
  }

  // A static input named r reserves that identity for the output and deterministically freshens the RNG formal.
  [Fact]
  public async Task PreparesStaticGeneratorWithCollidingRandomName() {
    const string source = "module M { method Goal(r: int) requires r >= 0 {} }";
    const string generator =
      "method {:pbt_generator \"M.Goal\"} Generate(r0: PbtRandom.Source) returns (r: int) { r := 1; }";
    var (original, options, sources) = await Parse(source);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);

    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, goal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);

    Assert.Contains("Generate(r0: PbtRandom.Source) returns (r: int)", prepared.Sources.Single().Content,
      StringComparison.Ordinal);
    var resolved = await ResolveWithRuntime(prepared.Sources, options);
    var resolvedGoal = ContractCallableSelector.SelectMethod(resolved, new("M.Goal"), requireConcreteReceiver: false);
    _ = new ContractRuntimeObligationTransformer(resolved, WithRuntime(prepared.Sources), resolvedGoal, null);
  }

  // Valid runtime-looking inputs cannot capture the fresh alias or its canonical runtime calls and shape helper.
  [Theory]
  [InlineData("PbtChecks", "PbtRuntimeAlias", "PbtRuntimeBridge")]
  [InlineData("PbtRandom", "PbtRuntimeAlias", "PbtRuntimeBridge")]
  [InlineData("PbtRuntime", "PbtRuntimeAlias", "PbtRuntimeBridge")]
  [InlineData("PbtRuntimeAlias", "PbtRuntimeAlias0", "PbtRuntimeBridge")]
  [InlineData("PbtRuntimeBridge", "PbtRuntimeAlias", "PbtRuntimeBridge0")]
  public async Task TransformsRuntimeLookingInputWithoutRuntimeCapture(string inputName, string expectedAlias,
    string expectedBridge) {
    var source = "module M { class PbtChecks { static function InstantiateShape(shape: string, " +
      "arguments: seq<string>): string { shape } } " +
      "module PbtRuntime { class PbtChecks { static function InstantiateShape(shape: string, " +
      "arguments: seq<string>): string { shape } } } " +
      "method Helper<T(==)>(x: T) returns (y: T) requires true ensures y == x { y := x; } method Goal(" + inputName +
      ": int) returns (result: int) requires " + inputName + " >= 0 { result := Helper(" + inputName + "); } }";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (" +
      inputName + ": int) { " + inputName + " := 1; }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);

    var transformed = new ContractRuntimeObligationTransformer(program, preparedSources, goal, prepared.SourceMap,
      selectedGenerator: selectedGenerator).Transform();
    var content = ContractSourceSnapshot.Find(transformed.Sources, goal.Origin.Uri).Content;
    var runtimeContent = transformed.Sources.Single(source => source.Path == "PbtRuntime.dfy").Content;

    Assert.Contains("import " + expectedAlias + " = " + expectedBridge + "\n", content,
      StringComparison.Ordinal);
    Assert.Contains("module " + expectedBridge + " {\nimport Runtime = PbtRuntime\nexport provides Runtime",
      runtimeContent, StringComparison.Ordinal);
    Assert.Contains(expectedAlias + ".Runtime.PbtChecks.InstantiateShape", content, StringComparison.Ordinal);
    var resolved = await Resolve(transformed.Sources, options);
    var canonicalModule = resolved.RawModules().Single(module => module.FullDafnyName == "PbtRuntime");
    var canonicalClass = canonicalModule.TopLevelDecls.OfType<TopLevelDeclWithMembers>()
      .Single(declaration => declaration.Name == "PbtChecks");
    var canonicalInstantiateShape = canonicalClass.Members.OfType<Function>()
      .Single(function => function.Name == "InstantiateShape");
    var runtimeFunctions = resolved.Descendants().OfType<FunctionCallExpr>()
      .Where(call => call.Function.EnclosingClass.Name == "PbtChecks").ToList();
    var runtimeMethods = resolved.Descendants().OfType<CallStmt>()
      .Where(call => call.Method.EnclosingClass.Name == "PbtChecks").ToList();
    Assert.Contains(runtimeFunctions, call => ReferenceEquals(call.Function, canonicalInstantiateShape));
    Assert.NotEmpty(runtimeMethods);
    Assert.All(runtimeFunctions, call => Assert.Same(canonicalClass, call.Function.EnclosingClass));
    Assert.All(runtimeMethods, call => Assert.Same(canonicalClass, call.Method.EnclosingClass));
  }

  // An include-first named source retains its preamble while aliases use the parsed attributed-module body boundary.
  [Fact]
  public async Task TransformsIncludeFirstNamedModuleAtParsedBodyBoundary() {
    const string main = "include \"Helper.dfy\"\n" +
      "module {:pbt_probe {0}} M { import PbtRandom method Goal(x: int) {} " +
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    IReadOnlyList<ContractSource> supplied = [
      Source("Main.dfy", main),
      Source("Helper.dfy", "module Helper {}")
    ];
    var sources = WithRuntime(supplied);
    var (program, options, _) = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var generator = ContractRuntimeGeneratorSignature.Select(program, goal, "Generate");

    var transformed = new ContractRuntimeObligationTransformer(program, sources, goal,
      selectedGenerator: generator).Transform();

    var transformedMain = transformed.Sources.Single(source => source.Path == "Main.dfy").Content;
    Assert.StartsWith("include \"Helper.dfy\"\n", transformedMain);
    Assert.Contains("module {:pbt_probe {0}} M {\nimport PbtRuntimeAlias = PbtRuntimeBridge\n",
      transformedMain, StringComparison.Ordinal);
    Assert.DoesNotContain("module PbtRuntimeBridge", transformedMain, StringComparison.Ordinal);
    Assert.Same(sources, transformed.Prepared.Sources);
    var resolved = await Resolve(transformed.Sources, options);
    AssertCanonicalRuntimeBindings(resolved, "M");
  }

  // An include-first default-module source resolves the global runtime facade without changing its preamble.
  [Fact]
  public async Task TransformsIncludeFirstDefaultModuleAfterPreamble() {
    const string main = "include \"Helper.dfy\"\n" +
      "method Goal(x: int) {} " +
      "method {:pbt_generator \"Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }";
    IReadOnlyList<ContractSource> supplied = [
      Source("Main.dfy", main),
      Source("Helper.dfy", "module Helper {}")
    ];
    var sources = WithRuntime(supplied);
    var (program, options, _) = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("Goal"), requireConcreteReceiver: false);
    var generator = ContractRuntimeGeneratorSignature.Select(program, goal, "Generate");

    var transformed = new ContractRuntimeObligationTransformer(program, sources, goal,
      selectedGenerator: generator).Transform();

    var transformedMain = transformed.Sources.Single(source => source.Path == "Main.dfy").Content;
    var transformedRuntime = transformed.Sources.Single(source => source.Path == "PbtRuntime.dfy").Content;
    Assert.StartsWith("include \"Helper.dfy\"\n", transformedMain);
    Assert.DoesNotContain("import PbtRuntimeAlias", transformedMain, StringComparison.Ordinal);
    Assert.DoesNotContain("module PbtRuntimeBridge", transformedMain, StringComparison.Ordinal);
    Assert.Contains("module PbtRuntimeBridge {\nimport Runtime = PbtRuntime", transformedRuntime,
      StringComparison.Ordinal);
    Assert.Contains("module PbtRuntimeAlias {\nimport Runtime = PbtRuntimeBridge.Runtime\n" +
      "export provides Runtime", transformedRuntime, StringComparison.Ordinal);
    Assert.Contains("PbtRuntimeAlias.Runtime.PbtChecks", transformedMain, StringComparison.Ordinal);
    Assert.Same(sources, transformed.Prepared.Sources);
    var resolved = await Resolve(transformed.Sources, options);
    AssertCanonicalRuntimeBindings(resolved, null);
  }

  // Include-linked default-module files share the global facade when both emit runtime calls.
  [Fact]
  public async Task TransformsRuntimeCallsAcrossDefaultModuleFiles() {
    const string main = "include \"Helper.dfy\"\n" +
      "method Goal(x: int) returns (y: int) { y := Assist(x); } " +
      "method {:pbt_generator \"Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }";
    const string helper = "method Assist(x: int) returns (y: int) { y := x; }";
    IReadOnlyList<ContractSource> supplied = [
      Source("Main.dfy", main),
      Source("Helper.dfy", helper)
    ];
    var sources = WithRuntime(supplied);
    var (program, options, _) = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("Goal"), requireConcreteReceiver: false);
    var generator = ContractRuntimeGeneratorSignature.Select(program, goal, "Generate");

    var transformed = new ContractRuntimeObligationTransformer(program, sources, goal,
      selectedGenerator: generator).Transform();

    var transformedMain = transformed.Sources.Single(source => source.Path == "Main.dfy").Content;
    var transformedHelper = transformed.Sources.Single(source => source.Path == "Helper.dfy").Content;
    Assert.StartsWith("include \"Helper.dfy\"\n", transformedMain);
    Assert.DoesNotContain("import PbtRuntimeAlias", transformedMain, StringComparison.Ordinal);
    Assert.DoesNotContain("import PbtRuntimeAlias", transformedHelper, StringComparison.Ordinal);
    Assert.Contains("PbtRuntimeAlias.Runtime.PbtChecks.Location", transformedMain, StringComparison.Ordinal);
    Assert.Contains("PbtRuntimeAlias.Runtime.PbtChecks.Location", transformedHelper, StringComparison.Ordinal);
    Assert.Same(sources, transformed.Prepared.Sources);
    var resolved = await Resolve(transformed.Sources, options);
    AssertCanonicalRuntimeBindings(resolved, null);
  }

  // An unrelated include-first root does not make runtime bridge placement depend on supplied source order.
  [Fact]
  public async Task TransformsLaterNamedGoalIndependentlyOfSourceOrder() {
    const string goalSource = "module M { import PbtRandom method Goal(x: int) {} " +
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    IReadOnlyList<ContractSource> supplied = [
      Source("Dependency.dfy", "include \"Helper.dfy\"\nmodule Dependency {}"),
      Source("Helper.dfy", "module Helper {}"),
      Source("Goal.dfy", goalSource)
    ];
    var sources = WithRuntime(supplied);
    var (program, options, _) = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var generator = ContractRuntimeGeneratorSignature.Select(program, goal, "Generate");

    var transformed = new ContractRuntimeObligationTransformer(program, sources, goal,
      selectedGenerator: generator).Transform();
    var resolved = await Resolve(transformed.Sources, options);

    var dependency = transformed.Sources[0];
    Assert.Equal("Dependency.dfy", dependency.Path);
    Assert.StartsWith("include \"Helper.dfy\"\n", dependency.Content);
    Assert.DoesNotContain("module PbtRuntimeBridge", dependency.Content, StringComparison.Ordinal);
    Assert.Same(sources, transformed.Prepared.Sources);
    AssertCanonicalRuntimeBindings(resolved, "M");
  }

  // A different fresh-looking RNG formal is rejected instead of weakening exact generator validation.
  [Fact]
  public async Task RejectsNoncanonicalRandomNameAfterCollision() {
    const string source = "module M { method Goal(r: int) {} }";
    const string generator =
      "method {:pbt_generator \"M.Goal\"} Generate(r1: PbtRandom.Source) returns (r: int) { r := 1; }";
    var (program, options, sources) = await Parse(source);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);

    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      ContractRuntimeSourcePreparation.PrepareAsync(program, sources, goal, [], Source("Generator.dfy", generator),
        options, CancellationToken.None));

    Assert.Contains("signature", error.Message, StringComparison.Ordinal);
  }

  // An instance generator cannot choose an arbitrary alias for the fresh implicit receiver.
  [Fact]
  public async Task RejectsNoncanonicalImplicitReceiverName() {
    const string source = "module M { class C { method Goal(receiver: int) {} } }";
    const string generator = "method {:pbt_generator \"M.C.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (self: C, receiver: int) { self := new C; receiver := 1; }";
    var (program, options, sources) = await Parse(source);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.C.Goal"), requireConcreteReceiver: false);

    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      ContractRuntimeSourcePreparation.PrepareAsync(program, sources, goal, [], Source("Generator.dfy", generator),
        options, CancellationToken.None));

    Assert.Contains("receiver", error.Message, StringComparison.Ordinal);
  }

  // Instance capture distinguishes its receiver from a tuple input and avoids user wrapper-local names.
  [Fact]
  public async Task TransformsInstanceGeneratorWithoutCapturingCollidingNames() {
    const string source = "module M { method Reserve(pbtRandom: int) returns (pbtOutput0: int) { pbtOutput0 := pbtRandom; } " +
      "class C { method Goal(receiver: (int, bool)) returns (result: int) { result := receiver.0; } } }";
    const string generator = "method {:pbt_generator \"M.C.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (receiver0: C, receiver: (int, bool)) { receiver0 := new C; receiver := (1, true); }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M.C.Goal"), requireConcreteReceiver: false);
    Assert.Equal("method {:pbt_generator \"M.C.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (receiver0: C, receiver: (int, bool))", ContractRuntimeGeneratorSignature.Format(originalGoal));
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.C.Goal"), requireConcreteReceiver: false);

    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);
    var transformed = new ContractRuntimeObligationTransformer(program, preparedSources, goal, prepared.SourceMap,
      diagnosticConstructors: prepared.DiagnosticConstructors, selectedGenerator: selectedGenerator).Transform();
    var content = ContractSourceSnapshot.Find(transformed.Sources, goal.Origin.Uri).Content;

    Assert.Contains("var pbtRandom0 := PbtRandom.New();", content, StringComparison.Ordinal);
    Assert.Contains("var receiver0, receiver := Generate(pbtRandom0);", content, StringComparison.Ordinal);
    Assert.Contains("var pbtOutput00 := receiver0.Goal__pbt_goal(receiver);", content, StringComparison.Ordinal);
    Assert.Contains("\"receiver0\"", content, StringComparison.Ordinal);
    Assert.Contains("\"receiver\"", content, StringComparison.Ordinal);
    await Resolve(transformed.Sources, options);
  }

  // A module-level PbtMain freshens the emitted entry point while named-class methods occupy separate scopes.
  [Theory]
  [InlineData("method PbtMain() {}", "PbtMain0")]
  [InlineData("method PbtMain() {} method PbtMain0() {}", "PbtMain00")]
  [InlineData("class Names { static method Generate() {} static method PbtMain() {} }", "PbtMain")]
  public async Task FreshensOnlyModuleLevelRuntimeMembers(string declarations, string expectedMainName) {
    var source = "module M { " + declarations + " method Goal(x: int) returns (y: int) { y := x; } }";
    const string generator =
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    Assert.Equal("Generate", prepared.GeneratorMethodName);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);

    var transformed = new ContractRuntimeObligationTransformer(program, preparedSources, goal, prepared.SourceMap,
      diagnosticConstructors: prepared.DiagnosticConstructors, selectedGenerator: selectedGenerator).Transform();

    Assert.Equal("M." + expectedMainName, transformed.MainName);
    Assert.Contains("method " + expectedMainName + "()", transformed.Sources.Single(source => source.Path == "M.dfy").Content,
      StringComparison.Ordinal);
    await Resolve(transformed.Sources, options);
  }

  // A user PbtMain remains an ordinary reachable method whose assertion and call contract are instrumented.
  [Fact]
  public async Task InstrumentsUserRuntimeMainFamilyMember() {
    const string source = "module M { method PbtMain(x: int) returns (y: int) requires x >= 0 " +
      "{ assert x >= 0; y := x; } method Goal(x: int) returns (y: int) { y := PbtMain(x); } }";
    const string generator =
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);

    var transformed = new ContractRuntimeObligationTransformer(program, preparedSources, goal,
      selectedGenerator: selectedGenerator).Transform();

    Assert.Equal("M.PbtMain0", transformed.MainName);
    Assert.Contains(transformed.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.CallPrecondition &&
      clause.Obligation.Callee == "M.PbtMain");
    await Resolve(transformed.Sources, options);
  }

  // Runtime-main freshening does not exempt any other reserved diagnostic member family.
  [Theory]
  [InlineData("PbtChecks")]
  [InlineData("PbtRandom")]
  [InlineData("PbtHelper")]
  [InlineData("user__pbt_helper")]
  [InlineData("pbtTypeShape")]
  public async Task RejectsOtherReservedDiagnosticMemberNames(string reservedName) {
    var source = "module M { method " + reservedName + "() {} method Goal() {} " +
      "method {:pbt_generator \"M.Goal\"} Generate() {} }";
    var (_, options, sources) = await Parse(source);
    var preparedSources = WithRuntime(sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, "Generate");

    var error = Assert.Throws<NotSupportedException>(() =>
      new ContractRuntimeObligationTransformer(program, preparedSources, goal,
        selectedGenerator: selectedGenerator).Transform());

    Assert.Contains("Reserved Pbt diagnostic name collision", error.Message, StringComparison.Ordinal);
  }

  // Omitted-field auditing follows the selected fresh generator instead of an unrelated legacy Generate member.
  [Fact]
  public async Task AuditsOmittedGhostFieldsThroughFreshGenerator() {
    const string source = "module M { class Box { ghost var value: int } method Generate() {} " +
      "method Goal(box: Box) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Box\"} " +
      "Generate0(r: PbtRandom.Source) returns (box: Box) ensures box.value == 7 " +
      "{ box := new Box.ContractDiagnosticCreate(); }";
    var (original, options, sources) = await Parse(source);
    var originalGoal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [],
      Source("Generator.dfy", generator), options, CancellationToken.None);
    var preparedSources = WithRuntime(prepared.Sources);
    var program = await Resolve(preparedSources, options);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var selectedGenerator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);

    var error = Assert.Throws<NotSupportedException>(() => ContractDiagnosticConstruction.AuditResolved(
      program, goal, selectedGenerator, prepared.DiagnosticConstructors!));

    Assert.Contains("M.Box.value", error.Message, StringComparison.Ordinal);
    Assert.Contains("Generate0", error.Message, StringComparison.Ordinal);
  }

  // The strict selector rejects a method whose canonical name and target marker do not identify the same declaration.
  [Theory]
  [InlineData("method {:pbt_generator \"M.Goal\"} Other() {}")]
  [InlineData("method Generate() {}")]
  public async Task SelectorRejectsWrongNameOrMarker(string declaration) {
    var (program, _, _) = await Parse("module M { method Goal() {} " + declaration + " }");
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);

    Assert.Throws<NotSupportedException>(() => ContractRuntimeGeneratorSignature.Select(program, goal, "Generate"));
  }

  // The strict selector does not accept a marked generator from another source snapshot in the default module.
  [Fact]
  public async Task SelectorRejectsGeneratorFromDifferentSource() {
    IReadOnlyList<ContractSource> sources = [
      Source("Goal.dfy", "method Goal() {}"),
      Source("Generator.dfy", "method {:pbt_generator \"Goal\"} Generate() {}")
    ];
    var (program, _, _) = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("Goal"), requireConcreteReceiver: false);

    Assert.Throws<NotSupportedException>(() => ContractRuntimeGeneratorSignature.Select(program, goal, "Generate"));
  }

  // Heap preparation reads the fresh implicit receiver key while retaining the explicit receiver formal.
  [Fact]
  public async Task HeapPreparationSeparatesImplicitAndExplicitReceiver() {
    const string source = "module M { class C { method Goal(receiver: int) {} } }";
    var (program, _, sources) = await Parse(source);
    var campaign = new ContractRuntimeCampaignRequest(2, sources, new("M.C.Goal"), "receiver-collision");
    var receiver = new ContractValue(ContractValueKind.Reference, "object");
    var explicitInput = new ContractValue(ContractValueKind.Integer, "7");
    var inputs = new Dictionary<string, ContractValue>(StringComparer.Ordinal) {
      ["receiver0"] = receiver,
      ["receiver"] = explicitInput
    };
    var heap = new[] {
      new ContractHeapObject("object", "M.C", new Dictionary<string, ContractValue>(StringComparer.Ordinal))
    };

    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, inputs, heap);

    Assert.Equal(receiver, check.Request.Entry.Receiver);
    Assert.Equal(explicitInput, check.Request.Inputs["receiver"]);
    Assert.DoesNotContain("receiver0", check.Request.Inputs.Keys);
  }

  private static ContractSource Source(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static async Task<(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources)> Parse(
    string source) => await Parse([Source("M.dfy", source)]);

  private static async Task<(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources)> Parse(
    IReadOnlyList<ContractSource> sources) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    return (await Resolve(sources, options), options, sources);
  }

  private static IReadOnlyList<ContractSource> WithRuntime(IReadOnlyList<ContractSource> sources) {
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    return sources.Append(Source("PbtRuntime.dfy", runtime)).ToList();
  }

  private static Task<Program> ResolveWithRuntime(IReadOnlyList<ContractSource> sources, DafnyOptions options) =>
    Resolve(WithRuntime(sources), options);

  private static void AssertCanonicalRuntimeBindings(Program program, string? goalModuleName) {
    var canonicalModule = program.RawModules().Single(module => module.FullDafnyName == "PbtRuntime");
    var bridge = program.RawModules().Single(module => module.FullDafnyName == "PbtRuntimeBridge");
    var bridgeImport = bridge.TopLevelDecls.OfType<AliasModuleDecl>()
      .Single(import => import.Name == "Runtime");
    var alias = program.RawModules().Single(module => module.FullDafnyName == "PbtRuntimeAlias");
    var aliasImport = alias.TopLevelDecls.OfType<AliasModuleDecl>()
      .Single(import => import.Name == "Runtime");
    var canonicalClass = canonicalModule.TopLevelDecls.OfType<TopLevelDeclWithMembers>()
      .Single(declaration => declaration.Name == "PbtChecks");
    var runtimeFunctions = program.Descendants().OfType<FunctionCallExpr>()
      .Where(call => call.Function.EnclosingClass.Name == "PbtChecks").ToList();
    var runtimeMethods = program.Descendants().OfType<CallStmt>()
      .Where(call => call.Method.EnclosingClass.Name == "PbtChecks").ToList();

    Assert.Same(canonicalModule, bridgeImport.Signature.ModuleDef);
    Assert.Same(canonicalModule, aliasImport.Signature.ModuleDef);
    if (goalModuleName != null) {
      var goalModule = program.RawModules().Single(module => module.FullDafnyName == goalModuleName);
      var goalImport = goalModule.TopLevelDecls.OfType<AliasModuleDecl>()
        .Single(import => import.Name == "PbtRuntimeAlias");
      Assert.Same(bridge, goalImport.Signature.ModuleDef);
    }
    Assert.NotEmpty(runtimeFunctions);
    Assert.NotEmpty(runtimeMethods);
    Assert.All(runtimeFunctions, call => Assert.Same(canonicalClass, call.Function.EnclosingClass));
    Assert.All(runtimeMethods, call => Assert.Same(canonicalClass, call.Method.EnclosingClass));
  }

  private static async Task<Program> Resolve(IReadOnlyList<ContractSource> sources, DafnyOptions options) {
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Take(16).Select(message => message.ErrorId + ": " + message.Message)));
    return program;
  }
}
