#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractRuntimeCheckTests {
  // Existing compiled recursive membership can admit exact captured carriers without an empty native proof query.
  [Theory]
  [InlineData(1, false, true)]
  [InlineData(0, false, false)]
  [InlineData(1, true, false)]
  public async Task ReusesCompiledRecursiveTypeCheckForCapturedHeap(int childId, bool invalidCalleeContract, bool valid) {
    var source = """
      module M {
        function contractResult():int { 0 }
        datatype Tree = Node(id:int, children:map<int,Tree>)
        function Ids(tree:Tree):set<int> decreases tree {
          {tree.id} + set name:int, id:int | name in tree.children && id in Ids(tree.children[name]) :: id
        }
        function Paths(tree:Tree, id:int):set<seq<int>> decreases tree {
          (if tree.id == id then {[]} else {}) +
          set name:int, suffix:seq<int> | name in tree.children && suffix in Paths(tree.children[name], id) :: [name] + suffix
        }
        predicate Unique(tree:Tree) { forall id :: id in Ids(tree) ==> |Paths(tree,id)| == 1 }
        type UniqueTree = tree:Tree | Unique(tree) witness Node(0,map[])
        class Cell { var value:UniqueTree constructor(value:Tree) { this.value := value; } }
        function Read(cell:Cell):UniqueTree reads cell { cell.value }
        method Goal(cell:Cell) ensures false { var value := Read(cell); }
      }
      """;
    if (invalidCalleeContract) { source = source.Replace("reads cell { cell.value }", "reads cell ensures false { cell.value }"); }
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ cell := new Cell(Node(0,map[1 := Node(" + childId + ",map[])])); }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-membership-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxClosedQueries: 1, sampleCount: 1, artifactDirectory: directory);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive),
      System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
    if (valid) {
      var certificate = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(
        Assert.Single(Directory.GetFiles(directory, "initial-type-certificate-*.json")))).RootElement;
      Assert.True(certificate.GetProperty("passed").GetBoolean());
      Assert.False(certificate.GetProperty("requiresNativeProof").GetBoolean());
      var reused = certificate.GetProperty("runtimeChecks").EnumerateArray().Select(item => item.GetString()).ToList();
      Assert.NotEmpty(reused);
      Assert.Contains(result.Obligations, obligation => reused.Contains(obligation.Id) &&
        obligation.Callee == "M.Read" && obligation.Clause.Contains("contractResult"));
      Assert.Empty(Directory.GetFiles(directory, "initial-type-query-*.dfy"));
    }
  }

  // Cross-module specification wrappers keep their imported qualification and validate the callee at runtime.
  [Fact]
  public async Task ImportedSpecificationWrapperKeepsCompiledCheck() {
    const string source = """
      module Numbers {
        function Width(x: int): nat { if x < 0 then 0 else 1 }
      }
      module Encoding {
        import N = Numbers
        function Encode(x: int): seq<int>
          ensures |Encode(x)| == N.Width(x)
        { if x < 0 then [] else [x] }
      }
      module M {
        import E = Encoding
        method Goal(x: int) returns (result: int)
          ensures result == 2
        { result := |E.Encode(x)|; }
      }
      """;
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound,
      System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractUnchecked);
    Assert.Equal(0, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Obligations.Sum(obligation => obligation.Evaluations.ClosedSmt));
  }

  private const string ImportedDefinitionSource = """
    module Data { datatype Item = Item(value: int) }
    module Operations {
      import D = Data
      function Encode(values: seq<int>): seq<D.Item>
        decreases |values|
      { if values == [] then [] else [D.Item(values[0])] + Encode(values[1..]) }
      by method {
        return if values == [] then [] else [D.Item(values[0])] + Encode(values[1..]);
      }
    }
    module M {
      import O = Operations
      method Goal(values: seq<int>) returns (result: int)
        ensures result == |values| + 1
      { result := |O.Encode(values)|; }
    }
    """;
  private const string ImportedDefinitionGenerator = """
    method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (values: seq<int>) {
      values := [1, 2];
    }
    """;

  // Recursive by-method definition equality evaluates imported constructors in the declaring module.
  [Fact]
  public async Task ImportedRecursiveDefinitionKeepsCompiledCheck() {
    var result = await Run(ImportedDefinitionSource, ImportedDefinitionGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound,
      System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractUnchecked);
    Assert.Equal(0, result.Obligations.Sum(obligation => obligation.Evaluations.ClosedSmt));
  }

  // Fixing recursive definition rendering must still exclude an implementation whose returned datatype sequence is wrong.
  [Fact]
  public async Task ImportedRecursiveDefinitionRejectsInvalidImplementation() {
    var source = ImportedDefinitionSource.Replace(
      "return if values == [] then [] else [D.Item(values[0])] + Encode(values[1..]);", "return [];");
    var result = await Run(source, ImportedDefinitionGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(0, result.Population.Valid);
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.CalleeContractUnchecked);
    Assert.Empty(result.Violations);
  }

  // A concrete postcondition defect is reported from a compiled diagnostic execution.
  [Fact]
  public async Task ReportsPostconditionViolation() {
    const string source = "module M { method Goal(x: int) returns (y: int) ensures y == x + 1 { y := x; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := r.Int(1, 5); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(ContractRuntimeObligationKind.Postcondition, Assert.Single(result.Obligations).Kind);
    Assert.Equal(2, result.Violations.Count);
  }

  // A generator syntax error is reported at its model-relative path with line and column.
  [Fact]
  public async Task LocatesGeneratorSyntaxError() {
    const string source = "module M { method Goal(x: int) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) {\n  x := ;\n}";
    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      Run(source, generator, generatorPath: ".top-down-pbt/generators/Goal.dfy"));
    Assert.Contains(".top-down-pbt/generators/Goal.dfy:2:8: invalid Rhs", error.Message);
  }

  // A missing generator is surfaced before compilation or sample execution.
  [Fact]
  public async Task RequiresGenerator() {
    var result = await Run("module M { method Goal(x: int) {} }", null);
    Assert.Equal(ContractRuntimeStatus.GeneratorRequired, result.Status);
    Assert.NotNull(result.MissingGenerator);
    Assert.Equal(0, result.Population.Generated);
  }

  // A bad invariant at the initial loop head is reported with iteration zero.
  [Fact]
  public async Task ReportsInvariantEntry() {
    var result = await Run("module M { method Goal(x: int) { var i := x; while i < 3 invariant i == 0 { i := i + 1; } } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Violations, v => v.Kind == ContractRuntimeObligationKind.LoopInvariantEntry && v.Iteration == 0);
  }

  // A later loop head records the exact iteration where the invariant becomes false.
  [Fact]
  public async Task ReportsInvariantMaintenance() {
    var result = await Run("module M { method Goal(x: int) { var i := 0; while i < 3 invariant i <= 1 { i := i + 1; } } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Violations, v => v.Kind == ContractRuntimeObligationKind.LoopInvariantMaintenance && v.Iteration == 2);
  }

  // A break skips the final invariant check for precisely the loop it exits.
  [Fact]
  public async Task BreakDoesNotCheckExitInvariant() {
    var result = await Run("module M { method Goal(x: int) { var i := 0; while i < 3 invariant i <= 1 { i := 9; break; } } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Empty(result.Violations);
  }

  // Runtime diagnostics do not turn a weak but true invariant into a proof-level counterexample.
  [Fact]
  public async Task WeakInvariantIsNotViolation() {
    var result = await Run("module M { method Goal(x: int) { var i := 0; while i < 3 invariant i >= 0 { i := i + 1; } } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // A caller's concrete argument is checked against the callee precondition at its call site.
  [Fact]
  public async Task ReportsCallPrecondition() {
    var result = await Run("module M { method Helper(x: int) requires x > 5 {} method Goal(x: int) { Helper(x); } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Violations, v => v.Kind == ContractRuntimeObligationKind.CallPrecondition);
  }

  // Rejected entry inputs are excluded from the valid and violating sample denominators.
  [Fact]
  public async Task RejectsEntryPrecondition() {
    var result = await Run("module M { method Goal(x: int) requires x < 0 ensures false {} }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.PreconditionRejected);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Ghost output values and recursive ghost functions are preserved by the diagnostic compile.
  [Fact]
  public async Task ExecutesGhostPostcondition() {
    var result = await Run("module M { ghost function Sum(s: seq<int>): int { if |s| == 0 then 0 else s[0] + Sum(s[1..]) } method Goal(x: int) returns (ghost y: int) ensures y == Sum([x]) { ghost var a := x; y := a + 1; } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.All(result.Obligations, o => Assert.Equal(ContractRuntimeDecisionMethod.Runtime, o.DecisionMethod));
  }

  // A function-by-method goal executes its implementation and checks the original function contract.
  [Fact]
  public async Task ExecutesFunctionByMethod() {
    var result = await Run("module M { function Goal(x: int): (y: int) ensures y == x + 1 { x } by method { return x; } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // An unbounded quantified clause remains unchecked when the closed-query budget is zero.
  [Fact]
  public async Task ReportsClosedQueryBudget() {
    var result = await Run("module M { method Goal(x: int) ensures forall n: int :: n <= x {} }", ConstantGenerator);
    Assert.Equal("closed_query_budget_exhausted", Assert.Single(result.Obligations).UncheckedReason);
    Assert.Equal(2, Assert.Single(result.Obligations).Evaluations.Unchecked);
  }

  // Closed SMT decides a quantified clause only after fixing the observed concrete inputs.
  [Fact]
  public async Task ChecksClosedQuantifier() {
    var result = await Run("module M { method Goal(x: int) ensures forall n: int :: n <= x {} }", ConstantGenerator, maxClosedQueries: 1);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, Assert.Single(result.Obligations).DecisionMethod);
    Assert.Equal(2, result.Violations.Count);
  }

  // A failing draft postcondition invalidates its sample instead of indicting the goal.
  [Fact]
  public async Task SeparatesDraftContractViolation() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; }";
    var result = await Run("module M { method {:extern} {:axiom} Helper(x: int) returns (y: int) ensures y > x method Goal(x: int) returns (y: int) ensures y > x { y := Helper(x); } }", ConstantGenerator,
      draft: new("M.Helper", "Helper.dfy", draft, ContractHarnessBuilder.Hash(draft)));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.All(result.CalleeViolations, v => Assert.True(v.Draft));
    Assert.Empty(result.Violations);
  }

  // A false call precondition terminates the sample before out-of-domain callee behavior.
  [Fact]
  public async Task InvalidCallDoesNotExecuteCallee() {
    var result = await Run("module M { method Helper(x: int) requires x < 0 ensures false { while true {} } method Goal(x: int) { Helper(x); } }", ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.ViolationFound, result.Status);
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.Timeouts);
  }

  // Each timed-out sample is killed before the next ordinal starts.
  [Fact]
  public async Task ContinuesAfterSampleTimeout() {
    var result = await Run("module M { method Goal(x: int) { while true {} } }", ConstantGenerator, sampleTimeout: 300);
    Assert.Equal(2, result.Population.Generated);
    Assert.Equal(2, result.Population.Timeouts);
    Assert.Equal(0, result.Population.Valid);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
  }

  // The same seed and ordinal reproduce the input and concrete violation exactly.
  [Fact]
  public async Task ReplaysOrdinal() {
    const string source = "module M { method Goal(x: int) ensures x < 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := r.Int(1, 100); }";
    var first = await Run(source, generator);
    var selected = first.Violations.Single(v => v.SampleOrdinal == 1);
    var second = await Run(source, generator, replay: 1);
    Assert.Equal(System.Text.Json.JsonSerializer.Serialize(selected, ContractJson.Options), System.Text.Json.JsonSerializer.Serialize(Assert.Single(second.Violations), ContractJson.Options));
  }

  // For-loop checks retain the index in scope at both entry and the final loop head.
  [Fact]
  public async Task ChecksForLoop() {
    var result = await Run("module M { method Goal(x: int) { for i := 0 to 3 invariant i < 3 {} } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Violations, v => v.Kind == ContractRuntimeObligationKind.LoopInvariantMaintenance && v.Iteration == 3);
  }

  // Old field values are captured before mutation and compared at return.
  [Fact]
  public async Task ChecksOldState() {
    const string source = "module M { class Box { var f: int constructor() { f := 1; } } method Goal(x: Box) modifies x ensures x.f == old(x.f) + 1 { x.f := x.f + 2; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: Box) { x := new Box(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, Assert.Single(result.Obligations, o => o.Kind == ContractRuntimeObligationKind.Postcondition).DecisionMethod);
  }

  // Unchanged compares the captured fields rather than object identity alone.
  [Fact]
  public async Task ChecksUnchangedFields() {
    const string source = "module M { class Box { var f: int constructor() { f := 1; } } method Goal(x: Box) modifies x ensures unchanged(x) { x.f := 2; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: Box) { x := new Box(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // Function expressions check their callee requirements through an expression wrapper.
  [Fact]
  public async Task ChecksFunctionCallPrecondition() {
    var result = await Run("module M { function Helper(x: int): int requires x < 0 { x } method Goal(x: int) returns (y: int) { y := Helper(x); } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Violations, v => v.Kind == ContractRuntimeObligationKind.CallPrecondition);
  }

  // A diagnostic generator may construct a region through an otherwise hidden ghost constructor.
  [Fact]
  public async Task ConstructsHiddenGhostRegion() {
    const string source = "module Store { export reveals Box provides Read class Box { ghost var f: int ghost constructor Init() { f := 1; } } ghost function Read(x: Box): int reads x { x.f } } module M { import S = Store method Goal(x: S.Box) ensures S.Read(x) == 2 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: S.Box) { x := new S.Box.Init(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // Non-compilable ghost inputs fail before requesting an impossible concrete generator.
  [Fact]
  public async Task RejectsOrdinalInput() {
    var result = await Run("module M { method Goal(ghost x: ORDINAL) {} }", "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: ORDINAL) { x := 0; }");
    Assert.Equal(ContractRuntimeStatus.Unsupported, result.Status);
    Assert.Contains("non_compilable_input_type", result.Reason);
  }

  // A nested helper contract violation invalidates the sample even when the direct callee contract is true.
  [Fact]
  public async Task SeparatesNestedCalleeViolation() {
    var result = await Run("module M { method Inner(x: int) returns (y: int) ensures y == x + 1 { y := x; } method Outer(x: int) returns (y: int) ensures y == x { y := Inner(x); } method Goal(x: int) returns (y: int) ensures y != x { y := Outer(x); } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Empty(result.Violations);
  }

  // Proof-only statements are removed while preserving the surrounding executable assignments.
  [Fact]
  public async Task RemovesProofStatements() {
    var result = await Run("module M { lemma Same(x: int) ensures x == x {} method Goal(x: int) returns (y: int) ensures y == x + 1 { Same(x); calc { x; == x; } assert x == x; y := x; } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // A resolver-rejected ghost compiled copy leaves its exclusion visible in the result.
  [Fact]
  public async Task ReportsResolverExclusion() {
    var result = await Run("module M { datatype D = ghost Hidden | Visible ghost function Choose(): D { Hidden } method Goal(x: int) ensures Choose() == Hidden {} }", ConstantGenerator);
    Assert.Contains(result.DeghostExclusions, e => e.Symbol == "M.Choose");
  }

  // Missing and scaffold callees return their original contract and signature before execution.
  [Theory]
  [InlineData("")]
  [InlineData("{ assert false; }")]
  public async Task RequiresMissingCalleeDraft(string body) {
    var result = await Run("module M { method Helper(x: int) returns (y: int) ensures y == x " + body + " method Goal(x: int) returns (y: int) { y := Helper(x); } }", null);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, result.Status);
    var missing = Assert.Single(result.MissingDrafts);
    Assert.Equal("M.Helper", missing.Symbol);
    Assert.Contains("returns", missing.Signature);
    Assert.Contains("ensures", missing.Contract);
    Assert.NotNull(result.MissingGenerator);
  }

  // An unimplemented native extern is requested as a draft rather than called natively.
  [Fact]
  public async Task RequiresExternDraft() {
    var result = await Run("module M { method {:extern} {:axiom} Helper(x: int) method Goal(x: int) { Helper(x); } }", ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, result.Status);
    Assert.Equal(ContractRuntimeDraftKind.ExternMethod, Assert.Single(result.MissingDrafts).Kind);
  }

  // An opaque finite predicate executes as ordinary diagnostic code after deghosting.
  [Fact]
  public async Task ExecutesOpaqueFinitePredicate() {
    var result = await Run("module M { opaque ghost predicate Good(s: seq<int>) { |set x | x in s| == 0 } method Goal(x: int) ensures Good([x]) {} }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, Assert.Single(result.Obligations).DecisionMethod);
  }

  // A ghost-method-produced local stays unavailable; the executed samples are valid but decide no goal obligation.
  [Fact]
  public async Task ExecutesWithUnavailableGhostLocal() {
    var result = await Run("module M { ghost method Hidden() returns (y: int) { y := 1; } method Goal(x: int) { ghost var y := Hidden(); while false invariant y == x {} } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.All(result.Obligations, o => Assert.Equal("value_unavailable", o.UncheckedReason));
  }

  // A nested ordinary function must satisfy its own callee domain before goal evidence is valid.
  [Fact]
  public async Task RejectsNestedFunctionDomainViolation() {
    var result = await Run("module M { function Inner(x:int):int requires x < 0 { x } function Outer(x:int):int { Inner(x) } method Goal(x:int) returns(y:int) ensures y != x { y := Outer(x); } }", ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Old heap fields through an immutable local alias are captured using the original input identity.
  [Fact]
  public async Task CapturesOldThroughLocalAlias() {
    var result = await Run("module M { class Box { var f:int constructor() { f:=1; } } method Goal(x:Box) modifies x { var b := x; while false invariant b.f == old(b.f) {} } }", "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(x:Box) { x:=new Box(); }");
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.All(result.Obligations, o => Assert.Equal(ContractRuntimeDecisionMethod.Runtime, o.DecisionMethod));
  }

  // An unavailable ghost output records an unchecked checkpoint, which cannot support a no-violation status.
  [Fact]
  public async Task ReportsUnavailableGhostOutput() {
    var result = await Run("module M { ghost method Unknown() returns(v:int) { v :| true; } method Goal(x:int) returns(ghost y:int) ensures y == x { y := Unknown(); } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal("No goal obligation was decided in a valid sample.", result.Reason);
    var obligation = Assert.Single(result.Obligations);
    Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, obligation.DecisionMethod);
    Assert.Equal("value_unavailable", obligation.UncheckedReason);
    Assert.Equal(2, obligation.Evaluations.Unchecked);
  }

  // CLI validation failures keep the caller seed so the strict transport can decode the receipt.
  [Fact]
  public async Task CliPreservesSeedOnGeneratorFailure() {
    const string source = "module M { method Goal(x:int) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(x:bool) { x:=false; }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-cli-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var request = new ContractRuntimeCampaignRequest(1, [new("M.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("M.Goal"), "17", Generator: new("G.dfy", generator, ContractHarnessBuilder.Hash(generator)));
    var path = Path.Combine(directory, "request.json");
    await File.WriteAllTextAsync(path, System.Text.Json.JsonSerializer.Serialize(request, ContractJson.Options));
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(30));
    var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      path,
      "--runtime-check"], directory, timeout.Token);
    var result = System.Text.Json.JsonSerializer.Deserialize<ContractRuntimeCampaignResult>(process.StandardOutput, ContractJson.Options)!;
    Assert.Equal("17", result.Seed);
    Assert.Equal(ContractRuntimeStatus.Unsupported, result.Status);
  }

  // A pure goal runs although unrelated modules keep logical ghost initialization and native-only dependencies.
  [Fact]
  public async Task IsolatesUnrelatedNativeHostState() {
    const string source = """
      module Host {
        class Region {
          ghost var value: int
          ghost constructor Init(initial: int) ensures value == initial { value := initial; }
        }
        class Handle {
          ghost const region: Region
          constructor Init() requires false {
            ghost var initial: int :| true;
            region := new Region.Init(initial);
          }
          method {:extern "NativeHost", "Write"} Write(x: int)
        }
        const {:extern "NativeHost", "Current"} Current: Handle
        function Open(): Handle { Current }
        method {:extern "NativeHost", "Stop"} Stop(code: int)
        method Run() { var handle := Open(); handle.Write(1); Stop(0); }
      }
      module M {
        import Host
        ghost function Id<T>(x: T): T { x }
        opaque function Double(x: int): int { 2 * x }
        method Goal(x: int) returns (y: int) ensures y == Double(x) + 1 {
          reveal Double();
          assert Id(x) == x;
          y := 2 * x;
        }
      }
      """;
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.RuntimeErrors);
  }

  // A function-by-method result that differs from the original definition is reported at that definition.
  [Fact]
  public async Task ChecksFunctionByMethodDefinition() {
    const string source = "module M { function Goal(x: int): int { x + 1 } by method { return x; } }";
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    var obligation = Assert.Single(result.Obligations);
    Assert.Equal(ContractRuntimeObligationKind.Postcondition, obligation.Kind);
    Assert.Equal("x + 1", obligation.Clause);
    Assert.Equal(source.IndexOf("x + 1", StringComparison.Ordinal) + 1, obligation.Column);
    var violation = result.Violations.First();
    Assert.Equal("1", violation.Values["contractResult"].Value);
    Assert.Equal("2", violation.Values["Goal(x)"].Value);
  }

  // Obligations of a correct recursive function-by-method evaluate its definition instead of re-entering the implementation.
  [Fact]
  public async Task EvaluatesRecursiveDefinitionInObligations() {
    const string source = """
      module M {
        function Goal(n: nat): nat { if n == 0 then 0 else Goal(n - 1) + 1 } by method {
          var i, c := 0, 0;
          while i < n invariant 0 <= i <= n invariant c == Goal(i) { i, c := i + 1, c + 1; }
          return c;
        }
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (n: nat) { n := r.Nat(5); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.All(result.Obligations, o => Assert.Equal(ContractRuntimeDecisionMethod.Runtime, o.DecisionMethod));
  }

  // A contract-violating function evaluated only by the goal postcondition invalidates the sample for ordinary and ghost functions.
  [Theory]
  [InlineData("")]
  [InlineData("ghost ")]
  public async Task SeparatesSpecFunctionContractViolation(string ghost) {
    var result = await Run("module M { " + ghost + "function Bad(x: int): (b: bool) ensures b { false } method Goal(x: int) ensures Bad(x) {} }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.All(result.CalleeViolations, v => Assert.Equal("M.Bad", v.Callee));
    var callee = Assert.Single(result.Obligations, o => o.Kind == ContractRuntimeObligationKind.CalleePostcondition);
    Assert.Equal("b", callee.Clause);
  }

  // Mutually referring contracts check all evaluated callees without repeating an identical pending obligation.
  [Fact]
  public async Task ChecksSpecFunctionContractsWithoutRecursiveWrapping() {
    const string source = "module M { function Pos(x: int): (b: bool) ensures b == !Neg(x) { x > 0 } function Neg(x: int): (b: bool) ensures b == !Pos(x) { x <= 0 } method Goal(x: int) returns (y: bool) ensures y == Pos(x) && !Neg(x) { y := Pos(x); } }";
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    var callees = result.Obligations.Where(o => o.Kind == ContractRuntimeObligationKind.CalleePostcondition).ToList();
    Assert.Equal(3, callees.Count);
    Assert.All(callees, o => Assert.True(o.Evaluations.Runtime >= 2));
  }

  // A callee's by-method body must agree with its defining expression even without explicit ensures.
  [Fact]
  public async Task RejectsFunctionByMethodCalleeDefinitionMismatch() {
    var result = await Run("module M { function Helper(x: int): int { 0 } by method { return 1; } method Goal(x: int) returns (y: int) ensures y == 0 { y := Helper(x); } }", ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.All(result.Obligations.Where(o => o.Kind == ContractRuntimeObligationKind.Postcondition), o => Assert.Equal(0, o.Violations));
  }

  // Recursive callee definitions evaluate the definition while validating the actual by-method results.
  [Fact]
  public async Task AcceptsRecursiveFunctionByMethodCallee() {
    const string source = "module M { function Helper(x: int): int { if x <= 0 then 0 else Helper(x - 1) + 1 } by method { var y := 0; if x > 0 { y := Helper(x - 1) + 1; } return y; } method Goal(x: int) returns (y: int) ensures y == x { y := Helper(x); } }";
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractUnchecked);
  }

  // An unbounded spec-function domain stays unchecked when no closed-query budget is available.
  [Fact]
  public async Task ExcludesUncheckedSpecFunctionDomain() {
    const string source = "module M { function Helper(x: int): bool requires forall k: int :: k*k >= 0 && x < 0 { false } method Goal(x: int) ensures Helper(x) {} }";
    var result = await Run(source, ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(2, result.Population.CalleeContractUnchecked);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // A false non-runtime domain decided from concrete inputs invalidates the callee instead of the goal.
  [Fact]
  public async Task RejectsClosedSpecFunctionDomain() {
    const string source = "module M { function Helper(x: int): bool requires forall k: int :: k*k >= 0 && x < 0 { false } method Goal(x: int) ensures Helper(x) {} }";
    var result = await Run(source, ConstantGenerator, maxClosedQueries: 4);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // A closed decision of an unbounded valid spec-function domain can admit the sample.
  [Fact]
  public async Task AcceptsClosedSpecFunctionDomain() {
    const string source = "module M { function Helper(x: int): bool requires forall k: int :: k == k && x > 0 { true } method Goal(x: int) ensures Helper(x) {} }";
    var result = await Run(source, ConstantGenerator, maxClosedQueries: 4);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
  }

  // A function called only from a callee's postcondition must satisfy its own contract.
  [Fact]
  public async Task RejectsNestedSpecFunctionContractViolation() {
    const string source = "module M { function Bad(): (b: bool) ensures b { false } method Helper(x: int) returns (y: int) ensures !Bad() { y := 1; } method Goal(x: int) returns (y: int) ensures y == 0 { y := Helper(x); } }";
    var result = await Run(source, ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.Contains(result.CalleeViolations, v => v.Callee == "M.Bad");
  }

  // Distinct decreasing arguments inside contracts retain their own validity checks.
  [Fact]
  public async Task AcceptsDescendingSpecFunctionContracts() {
    const string source = "module M { function Count(x: int): (n: int) ensures x <= 0 || n == Count(x - 1) + 1 { if x <= 0 then 0 else Count(x - 1) + 1 } method Goal(x: int) ensures Count(x) == x {} }";
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
  }

  // Entry-state function captures validate the function before its result can indict the goal.
  [Fact]
  public async Task RejectsOldStateSpecFunctionContractViolation() {
    const string source = "module M { class Box { var f: int constructor() { f := 0; } } function Bad(o: Box): (n: int) reads o ensures n == 0 { o.f + 1 } method Goal(o: Box) modifies o ensures old(Bad(o)) == 0 { o.f := 2; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (o: Box) { o := new Box(); }";
    var result = await Run(source, generator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Valid transitive contracts inside old use the entry heap even when the goal later mutates it.
  [Fact]
  public async Task AcceptsOldStateTransitiveSpecContracts() {
    const string source = "module M { class Box { var f: int constructor() { f := 0; } } function Read(o: Box): (n: int) reads o ensures n == o.f { o.f } function Outer(o: Box): (n: int) reads o ensures n == Read(o) { Read(o) } method Goal(o: Box) modifies o ensures old(Outer(o)) == 0 { o.f := 2; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (o: Box) { o := new Box(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
  }

  // An unverified by-method may change the heap while a mutual contract is pending, so reference cycles stay unchecked.
  [Fact]
  public async Task ExcludesReentrantMutableSpecContracts() {
    const string source = "module M { class Box { var f: int constructor() { f := 0; } } function Pos(o: Box): (b: bool) reads o ensures o.f == 0 && Neg(o) { true } function Neg(o: Box): (b: bool) reads o ensures Pos(o) { true } by method { o.f := 1; return true; } method Goal(o: Box) ensures !Pos(o) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (o: Box) { o := new Box(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractUnchecked);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, o => o.UncheckedReason == "recursive_heap_contract" && o.Evaluations.Unchecked > 0);
  }

  // A bodyless method reached only through a function-by-method body is requested before any compilation.
  [Fact]
  public async Task RequiresDraftInsideFunctionByMethod() {
    var result = await Run(FunctionByMethodHelper, ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, result.Status);
    var missing = Assert.Single(result.MissingDrafts);
    Assert.Equal("M.Helper", missing.Symbol);
    Assert.Contains("ensures", missing.Contract);
  }

  // A drafted method call inside a function-by-method body executes and satisfies the original definition.
  [Fact]
  public async Task ExecutesDraftInsideFunctionByMethod() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; }";
    var result = await Run(FunctionByMethodHelper, ConstantGenerator, draft: new("M.Helper", "Helper.dfy", draft, ContractHarnessBuilder.Hash(draft)));
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
  }

  private const string FunctionByMethodHelper = "module M { method Helper(x: int) returns (y: int) ensures y == x function Goal(x: int): int { x } by method { var y := Helper(x); return y; } }";

  // A conjunctive quantified postcondition is checked in its written, compilable form instead of being erased.
  [Fact]
  public async Task ChecksConjunctiveQuantifiedPostcondition() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: set<int>) { s := {1, 2}; }";
    var result = await Run("module M { method Goal(s: set<int>) returns (r: set<int>) ensures forall e :: e in r ==> e in s && e % 2 == 0 { r := s; } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    var obligation = Assert.Single(result.Obligations);
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
    Assert.Equal(2, obligation.Evaluations.Runtime);
  }

  // A callee postcondition in the same quantified shape still invalidates the sample instead of indicting the goal.
  [Fact]
  public async Task ChecksConjunctiveQuantifiedCalleePostcondition() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: set<int>) { s := {1, 2}; }";
    var result = await Run("module M { method Evens(s: set<int>) returns (r: set<int>) ensures forall e :: e in r ==> e in s && e % 2 == 0 { r := s; } method Goal(s: set<int>) returns (b: bool) ensures b { var r := Evens(s); b := 1 !in r; } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Empty(result.Violations);
  }

  // A runtime check erased by ghost inference is decided by a closed query instead of passing unevaluated.
  [Fact]
  public async Task LowersErasedRuntimeCheckToClosedQuery() {
    var result = await Run("module M { datatype D = A | B | ghost C method Goal(x: int) returns (d: D) ensures d != C && d != A { d := A; } }", ConstantGenerator, maxClosedQueries: 1);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    var obligation = Assert.Single(result.Obligations);
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, obligation.DecisionMethod);
    Assert.Equal(0, obligation.Evaluations.Runtime);
    Assert.Equal(2, obligation.Evaluations.ClosedSmt);
  }

  // Without a closed-query budget an erased check leaves valid samples inconclusive rather than violation-free.
  [Fact]
  public async Task ErasedCheckWithoutBudgetIsInconclusive() {
    var result = await Run("module M { datatype D = A | B | ghost C method Goal(x: int) returns (d: D) ensures d != C && d != A { d := A; } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, Assert.Single(result.Obligations).Evaluations.Runtime);
  }

  // An erased entry precondition is never treated as satisfied, so its samples are discarded as unchecked.
  [Fact]
  public async Task ErasedEntryPreconditionDiscardsSamples() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (d: D) { d := A; }";
    var result = await Run("module M { datatype D = A | B | ghost C method Goal(d: D) requires d != C && d != A ensures false {} }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.PreconditionUnchecked);
    Assert.Equal(0, result.Population.Valid);
  }

  // A true clause that the solver cannot prove is left unchecked instead of being reported as violated.
  [Fact]
  public async Task ClosedQueryDoesNotReportUnprovenClause() {
    var result = await Run("module M { function Sum(k: nat): int { if k == 0 then 0 else k + Sum(k - 1) } method Goal(x: int) ensures forall k: nat :: Sum(k) >= 0 {} }", ConstantGenerator, maxClosedQueries: 1);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Empty(result.Violations);
    Assert.StartsWith("closed_query_", Assert.Single(result.Obligations, o => o.Kind == ContractRuntimeObligationKind.Postcondition).UncheckedReason);
  }

  // A generic function used by the goal postcondition must satisfy its own contract before goal evidence is valid.
  [Fact]
  public async Task SeparatesGenericSpecFunctionViolation() {
    var result = await Run("module M { function Pick<T(==)>(a: T, b: T): (c: T) ensures c == a { b } method Goal(x: int) returns (r: int) ensures r == Pick(x, 0) { r := x; } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Empty(result.Violations);
  }

  // A closed-query clause that calls a contract-bearing function cannot indict the goal through that function.
  [Fact]
  public async Task ClosedClauseWithUnvalidatedCalleeIsUnchecked() {
    var result = await Run("module M { ghost function Bad(x: int): (b: bool) ensures b { forall k: int :: k != k } method Goal(x: int) ensures Bad(x) {} }", ConstantGenerator, maxClosedQueries: 1);
    Assert.NotEqual(ContractRuntimeStatus.ViolationFound, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal("callee_contract_unvalidated", Assert.Single(result.Obligations).UncheckedReason);
  }

  // A generated input outside the goal's declared subset type is rejected like a failed precondition.
  [Fact]
  public async Task RejectsGeneratedSubsetViolation() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (n: nat) { n := -1; }";
    var result = await Run("module M { method Goal(n: nat) returns (r: int) ensures r >= 0 { r := n; } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.PreconditionRejected);
    Assert.Empty(result.Violations);
  }

  // A generated newtype value outside its constraint, nested in a sequence, is rejected before the goal runs.
  [Fact]
  public async Task RejectsGeneratedNewtypeViolation() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: seq<Small>) { s := [3 as Small, 12 as Small]; }";
    var result = await Run("module M { newtype Small = x: int | 0 <= x < 10 method Goal(s: seq<Small>) ensures false {} }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.PreconditionRejected);
  }

  // A predicate evaluated by a subset constraint cannot run outside its declared domain and admit the goal input.
  [Fact]
  public async Task RejectsTypeConstraintFunctionDomainViolation() {
    const string source = "module M { function Accept(n: int): bool requires n < 0 { true } type T = n: int | Accept(n) witness -1 method Goal(x: T) ensures false {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: T) { x := 3; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.RuntimeErrors);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // A non-runtime predicate domain in a type constraint stays excluded when closed-query evidence is unavailable.
  [Fact]
  public async Task ExcludesUncheckedTypeConstraintFunctionDomain() {
    const string source = "module M { function Accept(n: int): bool requires forall k: int :: k*k >= 0 && n < 0 { true } type T = n: int | Accept(n) witness -1 method Goal(x: T) ensures false {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: T) { x := 3; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractUnchecked);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Membership predicates admit a goal counterexample only when their own postcondition holds, across supported type shapes.
  [Theory]
  [InlineData("type T = n: int | Accept(n) witness 0", "T", "3", false)]
  [InlineData("type T = n: int | Accept(n) witness 0", "T", "3", true)]
  [InlineData("type T = n: int | Accept(n) witness 0", "seq<seq<T>>", "[[3]]", false)]
  [InlineData("type T = n: int | Accept(n) witness 0", "seq<seq<T>>", "[[3]]", true)]
  [InlineData("newtype T = n: int | Accept(n) witness 0", "T", "3 as T", false)]
  [InlineData("newtype T = n: int | Accept(n) witness 0", "T", "3 as T", true)]
  [InlineData("newtype T = n: int | Accept(n) witness 0", "seq<seq<T>>", "[[3 as T]]", false)]
  [InlineData("newtype T = n: int | Accept(n) witness 0", "seq<seq<T>>", "[[3 as T]]", true)]
  [InlineData("datatype D = D(n: int) type T = d: D | Accept(d.n) witness D(0)", "T", "D(3)", false)]
  [InlineData("datatype D = D(n: int) type T = d: D | Accept(d.n) witness D(0)", "T", "D(3)", true)]
  public async Task ChecksTypeConstraintFunctionPostconditions(string declaration, string type, string value, bool validCallee) {
    var source = "module M { function Accept(n: int): (v: bool) ensures " + (validCallee ? "v" : "!v") + " { true } " + declaration + " method Goal(x: " + type + ") ensures false {} }";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: " + type + ") { x := " + value + "; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (validCallee ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(validCallee ? 2 : 0, result.Population.Valid);
    Assert.Equal(validCallee ? 0 : 2, result.Population.CalleeContractViolations);
    Assert.Equal(validCallee ? 2 : 0, result.Population.ViolatingSamples);
    Assert.All(result.Obligations.Where(o => o.Kind == ContractRuntimeObligationKind.Postcondition), o => Assert.Equal(validCallee ? 2 : 0, o.Violations));
  }

  // Declared constraints inside supported datatype fields, map ranges and deeply nested collections decide input validity.
  [Theory]
  [InlineData("datatype Box = Box(n: nat)", "Box", "Box(-1)", false)]
  [InlineData("datatype Box = Box(n: nat)", "Box", "Box(1)", true)]
  [InlineData("datatype Box = Box(n: seq<nat>)", "Box", "Box([-1])", false)]
  [InlineData("datatype Box = Box(n: seq<nat>)", "Box", "Box([1])", true)]
  [InlineData("", "map<int, seq<nat>>", "map[0 := [-1]]", false)]
  [InlineData("", "map<int, seq<nat>>", "map[0 := [1]]", true)]
  [InlineData("", "seq<seq<seq<seq<seq<nat>>>>>", "[[[[[-1]]]]]", false)]
  [InlineData("", "seq<seq<seq<seq<seq<nat>>>>>", "[[[[[1]]]]]", true)]
  public async Task ChecksStructuralTypeConstraint(string declaration, string type, string value, bool validInput) {
    var source = "module M { " + declaration + " method Goal(x: " + type + ") ensures false {} }";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: " + type + ") { x := " + value + "; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (validInput ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(validInput ? 2 : 0, result.Population.Valid);
    Assert.Equal(validInput ? 0 : 2, result.Population.PreconditionRejected);
    Assert.Equal(validInput ? 2 : 0, result.Population.ViolatingSamples);
  }

  // Multiple method outputs retain executable structural constraints without capturing C# out parameters in lambdas.
  [Theory]
  [InlineData("Box", "Box(1)", true)]
  [InlineData("Box", "Box(-1)", false)]
  [InlineData("seq<Box>", "[Box(1)]", true)]
  [InlineData("seq<Box>", "[Box(-1)]", false)]
  [InlineData("map<int, seq<Box>>", "map[0 := [Box(1)]]", true)]
  [InlineData("map<int, seq<Box>>", "map[0 := [Box(-1)]]", false)]
  public async Task ChecksMultipleStructuralOutputs(string type, string value, bool validOutput) {
    var source = "module M { datatype Box = Box(n:nat) method Goal(x:int) returns (b:" + type + ", marker:int) ensures true { b := " + value + "; marker := 0; } }";
    var result = await Run(source, ConstantGenerator, sampleCount: 1);
    Assert.True(result.Status == (validOutput ? ContractRuntimeStatus.NoViolationFound : ContractRuntimeStatus.ViolationFound), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(validOutput ? 0 : 1, result.Population.ViolatingSamples);
    if (!validOutput) {
      var violation = Assert.Single(result.Violations);
      Assert.Equal(ContractRuntimeObligationKind.Postcondition, violation.Kind);
      Assert.True(violation.Values.ContainsKey("b"));
    }
  }

  // Invalid structured callee outputs stay outside valid goal evidence, while their normal counterparts remain usable.
  [Theory]
  [InlineData("Box", "Box(1)", true)]
  [InlineData("Box", "Box(-1)", false)]
  [InlineData("seq<Box>", "[Box(1)]", true)]
  [InlineData("seq<Box>", "[Box(-1)]", false)]
  public async Task ChecksMultipleCalleeStructuralOutputs(string type, string value, bool validOutput) {
    var source = "module M { datatype Box = Box(n:nat) method Helper() returns (b:" + type + ", marker:int) { b := " + value + "; marker := 0; } method Goal(x:int) returns (b:" + type + ", marker:int) ensures false { b, marker := Helper(); } }";
    var result = await Run(source, ConstantGenerator, sampleCount: 1);
    Assert.True(result.Status == (validOutput ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(validOutput ? 1 : 0, result.Population.Valid);
    Assert.Equal(validOutput ? 0 : 1, result.Population.CalleeContractViolations);
    Assert.Equal(validOutput ? 1 : 0, result.Population.ViolatingSamples);
  }

  // A genuine backend error reaches the public structured result with its compiler code and offending symbol.
  [Fact]
  public async Task CliReportsBackendCompilationError() {
    const string source = "module M { method Goal(x:int) ensures true {} }";
    const string dependency = "class BrokenDependency { static int Value() => MissingContractDiagnosticSymbol; }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-compiler-error-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var dependencyPath = Path.Combine(directory, "BrokenDependency.cs");
    await File.WriteAllTextAsync(dependencyPath, dependency);
    var request = new ContractRuntimeCampaignRequest(1, [new("M.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("M.Goal"), "17", Dependencies: [new(dependencyPath, ContractHarnessBuilder.Hash(dependency))],
      Generator: new("G.dfy", ConstantGenerator, ContractHarnessBuilder.Hash(ConstantGenerator)), SampleCount: 1);
    var path = Path.Combine(directory, "request.json");
    await File.WriteAllTextAsync(path, System.Text.Json.JsonSerializer.Serialize(request, ContractJson.Options));
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
    var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      path,
      "--runtime-check"], directory, timeout.Token);
    Assert.Equal(0, process.ExitCode);
    var result = System.Text.Json.JsonSerializer.Deserialize<ContractRuntimeCampaignResult>(process.StandardOutput, ContractJson.Options)!;
    Assert.Equal(ContractRuntimeStatus.Unsupported, result.Status);
    Assert.Equal(0, result.Population.Generated);
    Assert.Contains("CS0103", result.Reason);
    Assert.Contains("MissingContractDiagnosticSymbol", result.Reason);
  }

  // Null values are rejected at declared non-null formals and datatype fields while allocated controls remain valid.
  [Theory]
  [InlineData(false, false)]
  [InlineData(false, true)]
  [InlineData(true, false)]
  [InlineData(true, true)]
  public async Task ChecksNonnullStructuralTypeConstraint(bool boxed, bool validInput) {
    var source = "module M { class C { constructor() {} } datatype Box = Box(c: C) method Goal(x: " + (boxed ? "Box" : "C") + ") ensures false {} }";
    var value = validInput ? "c" : "null";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: " + (boxed ? "Box" : "C") + ") { var c := new C(); x := " + (boxed ? "Box(" + value + ")" : value) + "; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (validInput ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(validInput ? 2 : 0, result.Population.Valid);
    Assert.Equal(validInput ? 0 : 2, result.Population.PreconditionRejected);
    Assert.Equal(validInput ? 2 : 0, result.Population.ViolatingSamples);
  }

  // A spec function's declared non-null input is a validity condition even without explicit requires or ensures.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task ChecksSpecNonnullStructuralTypeConstraint(bool validCallee) {
    const string source = "module M { class C { constructor() {} } function Accept(x: C): bool { true } method Goal(x: C?) ensures !Accept(x) {} }";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: C?) { var c := new C(); x := " + (validCallee ? "c" : "null") + "; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (validCallee ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(validCallee ? 2 : 0, result.Population.Valid);
    Assert.Equal(validCallee ? 0 : 2, result.Population.CalleeContractViolations);
    Assert.Equal(validCallee ? 2 : 0, result.Population.ViolatingSamples);
  }

  // A nested helper's declared input type is checked before its result can count as valid goal evidence.
  [Fact]
  public async Task ChecksNestedStructuralTypeConstraint() {
    const string source = "module M { class C {} function Accept(x: C): bool { true } method Helper(x: C?) { var b := Accept(x); } method Goal(x: C?) ensures false { Helper(x); } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: C?) { x := null; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Finite recursive datatype membership validates nested constraints without a depth cutoff.
  [Theory]
  [InlineData(-1)]
  [InlineData(1)]
  public async Task ChecksRecursiveStructuralTypeConstraint(int value) {
    const string source = "module M { datatype List = Nil | Cons(n: nat, tail: List) method Goal(x: List) ensures false {} }";
    var generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: List) { x := Cons(0, Cons(" + value + ", Nil)); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (value >= 0 ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(value >= 0 ? 0 : 2, result.Population.PreconditionRejected);
    Assert.Equal(value >= 0 ? 2 : 0, result.Population.Valid);
    Assert.Equal(value >= 0 ? 2 : 0, result.Violations.Count);
  }

  // A draft result outside its declared subset type is a callee contract violation, not goal evidence.
  [Fact]
  public async Task SeparatesDraftResultSubsetViolation() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: nat) { y := x - 5; }";
    var result = await Run("module M { method Helper(x: int) returns (y: nat) method Goal(x: int) returns (r: int) ensures r >= 0 { r := Helper(x); } }", ConstantGenerator,
      draft: new("M.Helper", "Helper.dfy", draft, ContractHarnessBuilder.Hash(draft)));
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Empty(result.Violations);
  }

  // Obligation violation counts include only failures from samples classified by that obligation.
  [Fact]
  public async Task CountsObligationViolationsByClassification() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { var b := r.Bool(); x := if b then 1 else 0; }";
    var result = await Run("module M { method Helper(x: int) returns (y: int) ensures y >= 0 { y := if x < 1 then -1 else x; } method Goal(x: int) returns (r: int) ensures r > 100 { r := Helper(x); } }", generator, sampleCount: 8);
    Assert.True(result.Population.Valid > 0 && result.Population.CalleeContractViolations > 0, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    var goal = result.Obligations.Single(o => o.Kind == ContractRuntimeObligationKind.Postcondition);
    var callee = result.Obligations.Single(o => o.Kind == ContractRuntimeObligationKind.CalleePostcondition);
    Assert.Equal(8, goal.Evaluations.Runtime);
    Assert.Equal(result.Population.Valid, goal.Violations);
    Assert.Equal(result.Population.CalleeContractViolations, callee.Violations);
  }

  // A subset-type test on a type from another module keeps its constraint function executable.
  [Fact]
  public async Task ExecutesCrossModuleSubsetTypeTest() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: set<int>) { s := {1, 2, 4}; }";
    var result = await Run("module A { predicate IsEven(x: int) { x % 2 == 0 } type Even = x: int | IsEven(x) witness 0 } module M { import A method Goal(s: set<int>) returns (r: set<A.Even>) ensures forall e :: e in r ==> e in s && e % 2 == 0 { r := set x: A.Even | x in s; } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(0, result.Population.RuntimeErrors);
  }

  // A cross-module subset witness used as an array default value remains executable.
  [Fact]
  public async Task ExecutesCrossModuleSubsetWitness() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (n: nat) { n := 2; }";
    var result = await Run("module A { function Lo(): int { 3 } type Big = x: int | x >= Lo() witness Lo() } module M { import A method Goal(n: nat) returns (r: int) requires n > 0 ensures r >= 3 { var a := new A.Big[n]; r := a[0]; } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(0, result.Population.RuntimeErrors);
  }

  // Capturing keeps the original initializer executable; accepting its readonly equation needs native validation.
  [Theory]
  [InlineData(0, false)]
  [InlineData(6, true)]
  public async Task CapturesObjectWithConstantInitializer(int queries, bool valid) {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (b: Box) { b := new Box(1); }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-initializer-" + Guid.NewGuid().ToString("N"));
    var result = await Run("module M { function Seed(): int { 7 } class Box { var v: int const tag: int := Seed() constructor(a: int) ensures v == a { v := a; } } method Goal(b: Box) returns (r: int) ensures r == b.v + 1 { r := b.v; } }",
      generator, maxClosedQueries: queries, artifactDirectory: directory);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive),
      System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Executed);
    Assert.Equal(valid ? 2 : 0, result.Population.Valid);
    Assert.Equal(valid ? 0 : 2, result.Population.PreconditionUnchecked);
    Assert.Equal(0, result.Population.RuntimeErrors);
    var captured = false;
    foreach (var line in File.ReadLines(Path.Combine(directory, "sample-0.jsonl"))) {
      using var record = System.Text.Json.JsonDocument.Parse(line);
      if (record.RootElement.GetProperty("kind").GetString() != "heap_capture" ||
          record.RootElement.GetProperty("phase").GetString() != "entry") { continue; }
      var box = record.RootElement.GetProperty("heap").EnumerateArray().Single(item => item.GetProperty("type").GetString() == "M.Box");
      Assert.Equal("7", box.GetProperty("fields").GetProperty("tag").GetProperty("value").GetString());
      captured = true;
    }
    Assert.True(captured);
    if (valid) { Assert.Equal("7", result.Violations.First().Values["b.tag"].Value); } else { Assert.Empty(result.Violations); }
  }

  private const string TraitSource = "module M { trait Shape extends object { function Area(): int reads this method Scale(k: int) returns (a: int) ensures a == k * Area() } class Square extends Shape { var side: int constructor(s: int) ensures side == s { side := s; } function Area(): int reads this { side * side } method Scale(k: int) returns (a: int) ensures a == k * Area() { a := k * side * side; } } method Goal(s: Shape, k: int) returns (r: int) ensures r == k * s.Area() { r := s.Scale(k); if k > 2 { r := r + 1; } } }";
  private const string TraitGenerator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: Shape, k: int) { s := new Square(2); k := 3; }";

  // A call through a trait dispatches to the concrete override instead of requesting drafts for abstract members.
  [Fact]
  public async Task DispatchesTraitCallToOverride() {
    var result = await Run(TraitSource, TraitGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Empty(result.MissingDrafts);
    Assert.Equal(2, result.Population.Valid);
  }

  // Drafts supplied for abstract trait members are ignored because the overrides implement them.
  [Fact]
  public async Task IgnoresDraftsForAbstractTraitMembers() {
    const string scale = "method {:pbt_draft \"M.Shape.Scale\"} Scale(k: int) returns (a: int) { a := k * Area(); }";
    const string area = "function {:pbt_draft \"M.Shape.Area\"} Area(): int reads this { 0 }";
    var result = await Run(TraitSource, TraitGenerator, drafts: [
      new("M.Shape.Scale", "Scale.dfy", scale, ContractHarnessBuilder.Hash(scale)),
      new("M.Shape.Area", "Area.dfy", area, ContractHarnessBuilder.Hash(area))
    ]);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // A generic function call in the goal body gets a generic call-site wrapper.
  [Fact]
  public async Task WrapsGenericCallSite() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: seq<int>) { s := [4, 5]; }";
    var result = await Run("module M { function Head<T>(s: seq<T>): T requires |s| > 0 { s[0] } method Goal(s: seq<int>) returns (r: int) requires |s| > 0 ensures r == s[0] { r := Head(s); } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, result.Obligations.Single(o => o.Kind == ContractRuntimeObligationKind.CallPrecondition).DecisionMethod);
  }

  // Generic functions and methods forward exact nested Dafny shapes even when CLR bitvector types coincide.
  [Fact]
  public async Task CapturesNestedGenericCallSiteBitvectorShapes() {
    const string source = """
      module M {
        function Pick<T(==)>(a: T, b: T): (c: T) ensures c == a { a }
        function Nested<U(==)>(s: seq<U>): seq<U> { Pick(s, s) }
        method Relay<V(==)>(s: seq<V>) returns (t: seq<V>) ensures t == s { t := Nested(s); }
        method Goal(left: bv7, right: bv8) returns (a: seq<bv7>, b: seq<bv8>) ensures false {
          a := Relay([left]); b := Relay([right]);
        }
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (left: bv7, right: bv8) { left := 7; right := 7; }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-generic-shapes-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, sampleCount: 1, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(1, result.Population.Valid);
    var widths = new HashSet<int>();
    foreach (var line in File.ReadLines(Path.Combine(directory, "sample-0.jsonl"))) {
      using var record = System.Text.Json.JsonDocument.Parse(line);
      var observation = record.RootElement;
      if (observation.GetProperty("kind").GetString() != "check" ||
          !observation.GetProperty("id").GetString()!.StartsWith("callee_postcondition:", StringComparison.Ordinal)) { continue; }
      foreach (var value in observation.GetProperty("values").EnumerateObject()) {
        var captured = System.Text.Json.JsonSerializer.Deserialize<ContractValue>(value.Value.GetRawText(), ContractJson.Options)!;
        foreach (var item in captured.Items ?? []) {
          if (item.Kind == ContractValueKind.Bitvector) { widths.Add(item.Width!.Value); }
        }
      }
    }
    Assert.Equal(new[] { 7, 8 }, widths.Order().ToArray());
  }

  // Nested generic specification wrappers preserve shape bindings while excluding the invalid inner callee.
  [Fact]
  public async Task SeparatesNestedGenericSpecFunctionViolation() {
    const string source = """
      module M {
        function Inner<U(==)>(a: U, b: U): (c: U) ensures c == a { b }
        function Outer<T(==)>(a: seq<T>, b: seq<T>): (c: seq<T>) ensures c == Inner(a, b) { a }
        method Goal(x: int) ensures Outer([x], [0]) == [x] {}
      }
      """;
    var result = await Run(source, ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.CalleeContractViolations);
    Assert.Equal(0, result.Population.RuntimeErrors);
    Assert.Empty(result.Violations);
  }

  // First-class generic references remain explicit exclusions until they can carry shape arguments.
  [Fact]
  public async Task RejectsGenericHigherOrderShapeErasure() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      Run("module M { function Id<T>(x: T): T { x } method Goal(x: int) ensures false { var f := Id<int>; var y := f(x); } }", ConstantGenerator));
    Assert.Contains("Generic higher-order function references", error.Message);
  }

  // User formals cannot shadow the generated type-shape parameters.
  [Fact]
  public async Task RejectsGenericShapeFormalCollision() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      Run("module M { function Id<T>(pbtTypeShape0: T): T { pbtTypeShape0 } method Goal(x: int) ensures false { var y := Id(x); } }", ConstantGenerator));
    Assert.Contains("Reserved Pbt diagnostic name collision", error.Message);
  }

  // A compiled forall statement keeps its assignment-only body free of diagnostic markers.
  [Fact]
  public async Task ExecutesCompiledForallStatement() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (n: nat) { n := 3; }";
    var result = await Run("module M { method Goal(n: nat) returns (a: array<int>) ensures a.Length == n ensures forall i :: 0 <= i < n ==> a[i] == 1 { a := new int[n]; forall i | 0 <= i < n { a[i] := 2; } } }", generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // A missing implementation reached only through the generator is reported at its original source line.
  [Fact]
  public async Task ReportsGeneratorMissingDraftAtOriginalLine() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := MakeInput(); }";
    var result = await Run("module M {\n  method MakeInput() returns (x: int) ensures x >= 0\n  method Goal(x: int) returns (r: int) ensures r == x { r := x; }\n}", generator);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, result.Status);
    var missing = Assert.Single(result.MissingDrafts);
    Assert.Equal("M.dfy", missing.Path);
    Assert.Equal(2, missing.Line);
  }

  // A bodyless extern function is requested with the function draft kind.
  [Fact]
  public async Task ReportsExternFunctionDraftKind() {
    var result = await Run("module M { function {:extern} Native(x: int): int method Goal(x: int) returns (r: int) ensures r == x { r := Native(x); } }", ConstantGenerator);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, result.Status);
    Assert.Equal(ContractRuntimeDraftKind.Function, Assert.Single(result.MissingDrafts).Kind);
  }

  // An export too short to rewrite in place no longer prevents the diagnostic from revealing its declarations.
  [Fact]
  public async Task ToleratesShortExportDeclaration() {
    var result = await Run("module Lib { export A reveals F export B function F(): int { 1 } } module M { import Lib`A method Goal(x: int) returns (r: int) ensures r == Lib.F() + 1 { r := Lib.F(); } }", ConstantGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
  }

  private const string ExternMemberSource = "module Lib { class Store { ghost var state: int constructor() ensures state == 0 { state := 0; } method {:extern} {:axiom} Read() returns (r: int) ensures r == state } } module M { import Lib method Goal(s: Lib.Store) returns (r: int) ensures r == s.state + 1 { r := s.Read(); } }";
  private const string ExternMemberGenerator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (s: Lib.Store) { s := new Lib.Store(); }";

  // A class-member draft can use ghost state after diagnostic preparation while retaining the original contract.
  [Fact]
  public async Task ExecutesGhostStateDraftForExternMember() {
    const string draft = "method {:pbt_draft \"Lib.Store.Read\"} Read() returns (r: int) { r := state; }";
    var result = await Run(ExternMemberSource, ExternMemberGenerator, draft: new("Lib.Store.Read", "Read.dfy", draft, ContractHarnessBuilder.Hash(draft)));
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(2, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractViolations);
  }

  // A compilable class-member draft for an extern method executes and is checked against the original contract.
  [Fact]
  public async Task ExecutesCompilableDraftForExternMember() {
    const string draft = "method {:pbt_draft \"Lib.Store.Read\"} Read() returns (r: int) { r := 0; }";
    var result = await Run(ExternMemberSource, ExternMemberGenerator, draft: new("Lib.Store.Read", "Read.dfy", draft, ContractHarnessBuilder.Hash(draft)));
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(0, result.Population.CalleeContractViolations);
  }

  private const string ConstantGenerator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }";

  private static async Task<ContractRuntimeCampaignResult> Run(string source, string? generator, int maxClosedQueries = 0, ContractRuntimeDraft? draft = null, int sampleTimeout = 5000, int? replay = null,
    int sampleCount = 2, IReadOnlyList<ContractRuntimeDraft>? drafts = null, string? artifactDirectory = null, string generatorPath = "G.dfy") {
    var directory = artifactDirectory ?? Path.Combine("/workspace/tmp", "contract-runtime-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var request = new ContractRuntimeCampaignRequest(1, [new("M.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("M.Goal"), "17", Generator: generator == null ? null : new(generatorPath, generator, ContractHarnessBuilder.Hash(generator)),
      SampleCount: sampleCount, TimeoutMilliseconds: 60000, MaxClosedQueries: maxClosedQueries, Drafts: drafts ?? (draft == null ? null : [draft]),
      SampleTimeoutMilliseconds: sampleTimeout, ReplayOrdinal: replay);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
    return await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token);
  }
}
