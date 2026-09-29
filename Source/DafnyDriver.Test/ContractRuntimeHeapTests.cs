#nullable enable
using System;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractRuntimeHeapTests {
  // A single source-bound global certificate admits many distinct pure inputs despite an unused ghost output.
  [Fact]
  public async Task IndependentGlobalProofIsReusedAcrossPureSamples() {
    const string source = "module Client { type Positive=n:int | n > 0 witness 1 " +
      "class Region { ghost var value:Positive ghost var callback:int -> Positive } " +
      "ghost const {:extern} unused:Region const count:nat:=1 " +
      "datatype Input=Input(value:int, flag:bool) " +
      "method Goal(input:Input) returns(result:int, ghost evidence:int) ensures result==input.value+1 " +
      "{ result:=input.value; evidence:=0; } }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(input:Input) " +
      "{ var n:=r.Int(0,1000000000); input:=Input(n,true); }";
    var directory = Path.Combine("/workspace/tmp", "contract-global-reuse-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, sampleCount: 20, maxQueries: 3, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(20, result.Population.Valid);
    Assert.Equal(0, result.Population.PreconditionUnchecked);
    var inputs = Directory.GetFiles(directory, "sample-*.jsonl").SelectMany(File.ReadAllLines)
      .Select(line => System.Text.Json.JsonDocument.Parse(line).RootElement.Clone())
      .Where(record => record.GetProperty("kind").GetString() == "input")
      .Select(record => record.GetProperty("value").GetRawText()).Distinct().Count();
    Assert.Equal(20, inputs);
    Assert.Single(Directory.GetFiles(directory, "specification-query-*.result.json"));
    Assert.Empty(Directory.GetFiles(directory, "heap-query-*.result.json"));
    Assert.Empty(Directory.GetFiles(directory, "initial-type-query-*.result.json"));
    var certificates = Directory.GetFiles(directory, "initial-type-certificate-*.json");
    Assert.Equal(20, certificates.Length);
    foreach (var path in certificates) {
      using var certificate = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(path));
      Assert.True(certificate.RootElement.GetProperty("passed").GetBoolean());
      Assert.True(certificate.RootElement.GetProperty("hostMembershipChecks").GetInt32() > 0);
      Assert.NotEqual(System.Text.Json.JsonValueKind.Null, certificate.RootElement.GetProperty("independentGlobals").ValueKind);
    }
  }

  private const string Store = """
    module Store {
      class Cell {
        ghost var value: int
        ghost var unused: int -> int
        constructor Init() requires false {
          ghost var initial: int :| true;
          value := initial;
          ghost var callback: int -> int :| true;
          unused := callback;
        }
        ghost function Read(): int reads this { value }
        method {:extern} {:axiom} ReadValue() returns (result: int)
          ensures result == Read()
      }
    }
    module Client {
      import Store
      method Goal(cell: Store.Cell) returns (result: int)
        ensures result == cell.Read() + 1
      { result := cell.ReadValue(); }
    }
    """;
  private const string Generator = """
    method {:pbt_generator "Client.Goal"}
      {:pbt_heap_constructor "Store.Cell", "Store.Cell.value"}
      Generate(r: PbtRandom.Source) returns (cell: Store.Cell) {
      cell := new Store.Cell.ContractDiagnosticCreate(7);
    }
    """;
  private const string Draft = """
    method {:pbt_draft "Store.Cell.ReadValue"} ReadValue() returns (result: int) {
      result := Read();
    }
    """;

  // A cross-module ghost-backed draft runs over an explicitly supplied partial logical heap.
  [Fact]
  public async Task ConstructsPartialHeapAndExecutesGhostDraft() {
    var result = await Run(Store, Generator, Draft);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractViolations);
    Assert.Contains(result.Violations, violation => violation.Kind == ContractRuntimeObligationKind.Postcondition);
  }

  // A wrong draft return is excluded instead of being blamed on the entry implementation.
  [Fact]
  public async Task InvalidGhostDraftExcludesSample() {
    var result = await Run(Store, Generator, Draft.Replace("result := Read();", "result := Read() + 2;"));
    Assert.Equal(0, result.Population.Valid);
    Assert.True(result.Population.CalleeContractViolations > 0, Detail(result));
    Assert.Empty(result.Violations);
  }

  // A draft cannot make a ghost field relevant after the initial omission audit accepted it.
  [Fact]
  public async Task RejectsOmittedStateReadOnlyByDraft() {
    var source = Store.Replace("ghost var unused: int -> int", "ghost var unused: int")
      .Replace("ghost var callback: int -> int :| true;", "ghost var callback: int :| true;");
    var error = await Assert.ThrowsAsync<NotSupportedException>(() =>
      Run(source, Generator, Draft.Replace("result := Read();", "result := Read() + unused;")));
    Assert.Contains("Store.Cell.unused", error.Message);
  }

  // The original false-precondition constructor is never redirected to diagnostic construction.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task OriginalConstructorRemainsUncallable(bool ghost) {
    var source = "module M { class Box { " + (ghost ? "ghost " : "") + "var value: int " + (ghost ? "ghost " : "") +
      "constructor Init() requires false { value := 7; } } method Goal(box: Box) ensures box.value == 8 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns(box: Box) { box := new Box.Init(); }";
    var result = await Run(source, generator, entry: "M.Goal");
    Assert.Equal(0, result.Population.Executed);
    Assert.Equal(1, result.Population.RuntimeErrors);
    Assert.Empty(result.Violations);
  }

  private const string TwoStateSource = """
    module Client {
      class Cell { var value: int constructor(value: int) { this.value := value; } }
      twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
      method Goal(cell: Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; }
    }
    """;
  private const string TwoStateGenerator = """
    method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns(cell: Cell) {
      cell := new Cell(7);
    }
    """;

  private const string CapturedGhostHeapSource = """
    module Client {
      class Cell { var value: int constructor(value: int) { this.value := value; } }
      twostate predicate Changed(cell: Cell, amount: int) reads cell {
        cell.value == old(cell.value) + amount
      }
      method Goal(cell: Cell, ghost amount: int) modifies cell
        ensures Changed(cell, amount) {
        cell.value := cell.value + INCREMENT;
      }
    }
    """;
  private const string CapturedGhostHeapGenerator = """
    method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns(cell: Cell, amount: int) {
      cell := new Cell(7); amount := 2;
    }
    """;

  // A fully captured ghost input decides both original old/current heap polarities without replacing either heap.
  [Theory]
  [InlineData(1, false)]
  [InlineData(2, true)]
  public async Task CapturedGhostHeapDecidesOriginalTransition(int increment, bool holds) {
    var source = CapturedGhostHeapSource.Replace("INCREMENT", increment.ToString());
    var result = await Run(source, CapturedGhostHeapGenerator, maxQueries: 10);
    Assert.True(result.Status == (holds ? ContractRuntimeStatus.NoViolationFound : ContractRuntimeStatus.ViolationFound),
      Detail(result));
    Assert.Equal(1, result.Population.Valid);
    var obligation = Assert.Single(result.Obligations.Where(item =>
      item.Kind == ContractRuntimeObligationKind.Postcondition));
    Assert.Equal(1, obligation.Evaluations.ClosedSmt);
    if (holds) {
      Assert.Empty(result.Violations);
      return;
    }
    var violation = Assert.Single(result.Violations);
    Assert.Equal("2", violation.Inputs["amount"].Value);
    Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$initial/") && pair.Value.Value == "7");
    Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$final/") && pair.Value.Value == "8");
  }

  // A contract on a specification function still blocks a ghost-dependent heap verdict in both polarities.
  [Fact]
  public async Task CapturedGhostHeapKeepsUnvalidatedSpecificationUnchecked() {
    var source = CapturedGhostHeapSource
      .Replace("class Cell", "function Offset(n:int):int ensures false { n } class Cell")
      .Replace("+ amount", "+ Offset(amount)")
      .Replace("INCREMENT", "2");
    var result = await Run(source, CapturedGhostHeapGenerator, maxQueries: 10);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.Evaluations.ClosedSmt == 0 && obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // An inconsistent unused global cannot turn a real captured transition into a valid sample or entry violation.
  [Theory]
  [InlineData("type Empty = value:int | false witness 0 ghost const unused:Empty")]
  [InlineData("type Empty = value:int | false witness * ghost const unused:Empty := 0")]
  public async Task GlobalInconsistencyCannotAuthorizeCapturedSample(string declaration) {
    var source = TwoStateSource.Replace("module Client {", "module Client { " + declaration);
    var result = await Run(source, TwoStateGenerator, maxQueries: 10);
    Assert.Equal(1, result.Population.Executed);
    Assert.True(result.Population.Valid == 0, Detail(result));
    Assert.Empty(result.Violations);
  }

  // Unused datatype constants cannot make an empty-heap scalar execution count as valid; ordinary datatypes remain usable.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task ScalarAdmissionChecksUnusedDatatypeConstants(bool constant) {
    var source = "module Client { type Empty = value:int | false witness * datatype Item = Item " +
      (constant ? "{ const bad:Empty := 0 } " : " ") +
      "method Goal(x:int) returns(result:int) ensures result == x+1 { result:=x; } }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(x:int) { x:=1; }";
    var result = await Run(source, generator, maxQueries: 0);
    Assert.Equal(1, result.Population.Executed);
    Assert.True(result.Population.Valid == (constant ? 0 : 1), Detail(result));
    Assert.Equal(constant ? 0 : 1, result.Violations.Count);
  }

  // Initialized ghost slots need original WD and unpruned consistency independently of their ordinary field types.
  [Theory]
  [InlineData("nat", "-1", "", false)]
  [InlineData("int", "Seed()", "function Seed():int requires false { 7 }", false)]
  [InlineData("nat", "1", "", true)]
  public async Task InitialConstantEquationsRequireValidation(string type, string initializer, string function, bool valid) {
    var source = "module Client { " + function + " class Cell { var value:int ghost const tag:" + type +
      " := " + initializer + " constructor(value:int) { this.value:=value; } } " +
      "method Goal(cell:Cell) ensures false {} }";
    var result = await Run(source, TwoStateGenerator, maxQueries: 6);
    Assert.Equal(1, result.Population.Executed);
    Assert.True(result.Population.Valid == (valid ? 1 : 0), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Violations.Count);
  }

  // Explicit initial construction and exact final memberships preserve both original two-state polarities.
  [Theory]
  [InlineData(1, false)]
  [InlineData(2, true)]
  public async Task ObservedConstructionDecidesBothOriginalPolarities(int increment, bool holds) {
    var source = """
      module Client {
        type Positive = value:int | value > 0 witness 1
        class Cell { var value:Positive constructor(value:int) { this.value := value; } }
        twostate predicate Changed(cell:Cell, result:Positive) reads cell {
          result == cell.value && cell.value == old(cell.value) + 2
        }
        method Goal(cell:Cell) returns(result:Positive) modifies cell ensures Changed(cell,result) {
          cell.value := cell.value + INCREMENT; result := cell.value;
        }
      }
      """.Replace("INCREMENT", increment.ToString());
    var directory = Path.Combine("/workspace/tmp", "contract-observed-construction-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, TwoStateGenerator, maxQueries: 10, artifactDirectory: directory);
    Assert.True(result.Status == (holds ? ContractRuntimeStatus.NoViolationFound : ContractRuntimeStatus.ViolationFound), Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.Evaluations.ClosedSmt == 1);
    var certificate = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(
      Assert.Single(Directory.GetFiles(directory, "observed-type-certificate-*.json")))).RootElement;
    Assert.True(certificate.GetProperty("constructive").GetBoolean());
    Assert.True(certificate.GetProperty("passed").GetBoolean());
    Assert.False(certificate.GetProperty("requiresNativeProof").GetBoolean());
    Assert.NotEmpty(certificate.GetProperty("runtimeChecks").EnumerateArray());
  }

  // A rejected original P cannot be bypassed by valid captured type memberships in either heap.
  [Fact]
  public async Task ObservedConstructionKeepsInvalidEntryRejected() {
    var source = TwoStateSource.Replace("class Cell { var value: int", "type Positive = value:int | value > 0 witness 1 class Cell { var value: Positive")
      .Replace("modifies cell ensures Changed", "requires cell.value == 99 modifies cell ensures Changed");
    var directory = Path.Combine("/workspace/tmp", "contract-observed-invalid-entry-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, TwoStateGenerator, maxQueries: 10, artifactDirectory: directory);
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.Empty(Directory.GetFiles(directory, "observed-type-certificate-*.json"));
  }

  // A native two-state predicate rejects the observed mutation using the original old heap.
  [Fact]
  public async Task DecidesOriginalTwoStateHeapPostcondition() {
    var result = await Run(TwoStateSource, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    var violation = Assert.Single(result.Violations);
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, violation.DecisionMethod);
    Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$initial/") && pair.Value.Value == "7");
    Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$final/") && pair.Value.Value == "8");
  }

  // A valid observed transition satisfies the unchanged two-state predicate.
  [Fact]
  public async Task AcceptsOriginalTwoStateHeapPostcondition() {
    var result = await Run(TwoStateSource.Replace("cell.value := cell.value + 1", "cell.value := cell.value + 2"), TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.NoViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition && obligation.Evaluations.ClosedSmt == 1);
  }

  // Synthetic entry and call wrappers retain the original declarations' nontermination permission.
  [Fact]
  public async Task PreservesNonterminationPermission() {
    var source = TwoStateSource.Replace("method Goal(cell: Cell)",
      "method Step(cell: Cell) modifies cell decreases * { cell.value := cell.value + 1; } method Goal(cell: Cell)")
      .Replace("ensures Changed(cell) { cell.value := cell.value + 1; }",
        "ensures Changed(cell) decreases * { Step(cell); }");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
  }

  // Consistency queries consume the same finite budget and cannot be counted as a decided postcondition.
  [Fact]
  public async Task HeapQueryBudgetExhaustionRemainsUnchecked() {
    var result = await Run(TwoStateSource, TwoStateGenerator, maxQueries: 1);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.UncheckedReason == "closed_query_budget_exhausted");
  }

  // A violated executed callee contract excludes the sample before final heap evidence is considered.
  [Fact]
  public async Task InvalidCalleeExcludesHeapDecision() {
    var source = TwoStateSource.Replace("method Goal(cell: Cell)",
      "method Bad() returns (x: int) ensures x == 1 { x := 0; } method Goal(cell: Cell)")
      .Replace("{ cell.value := cell.value + 1; }", "{ var x := Bad(); cell.value := cell.value + 1; }");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Population.CalleeContractViolations == 1, Detail(result));
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // An unexecuted spec function's explicit contract cannot become evidence against the entry body.
  [Fact]
  public async Task UnvalidatedSpecificationCalleeRemainsUnchecked() {
    var result = await Run(TwoStateSource.Replace("reads cell {", "reads cell ensures false {"), TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // Unvalidated specification contracts block a matching transition as well as a mismatching one.
  [Theory]
  [InlineData(1)]
  [InlineData(2)]
  public async Task DirectSpecificationContractBlocksBothPolarities(int increment) {
    var source = TwoStateSource.Replace("reads cell {", "reads cell ensures false {")
      .Replace("cell.value := cell.value + 1", "cell.value := cell.value + " + increment);
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.Evaluations.ClosedSmt == 0 && obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // The specification dependency closure includes contracts hidden behind a two-state predicate.
  [Fact]
  public async Task TransitiveSpecificationContractRemainsUnchecked() {
    var source = TwoStateSource.Replace("twostate predicate Changed", "function Bad(): int ensures Bad() == 1 { 0 } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "old(cell.value) + Bad()");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // Logical use needs the original definition; an unexecuted compiled by-method is not a proof of that definition.
  [Fact]
  public async Task LogicalHeapCertificateDoesNotRequireUnexecutedByMethod() {
    var source = TwoStateSource.Replace("twostate predicate Changed",
        "function Hidden(n:int):int { 0 } by method { return 1; } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "old(cell.value) + Hidden(1)");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractViolations);
    Assert.Contains(result.Violations, violation => violation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt);
  }

  // A logical certificate cannot rescue a sample whose actual by-method result disagrees with its definition.
  [Theory]
  [InlineData(2, true)]
  [InlineData(3, false)]
  public async Task LogicalHeapCertificateRetainsExecutedByMethodChecks(int actualIncrement, bool valid) {
    var source = TwoStateSource.Replace("twostate predicate Changed",
        "function Offset(n:int):int { n + 2 } by method { return n + (if n == 7 then " + actualIncrement + " else 3); } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "Offset(old(cell.value))")
      .Replace("{ cell.value := cell.value + 1; }", "{ var actual := Offset(cell.value); cell.value := cell.value + 1; }");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
    Assert.Equal(valid ? 0 : 1, result.Population.CalleeContractViolations);
    if (valid) {
      Assert.Contains(result.Violations, violation => violation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt);
    } else { Assert.Empty(result.Violations); }
  }

  // A false original logical contract blocks Q even when the unexecuted by-method returns its contract's expected value.
  [Fact]
  public async Task LogicalHeapCertificateRejectsBadDefinitionWithContractMatchingMethod() {
    var source = TwoStateSource.Replace("twostate predicate Changed",
        "function Offset(n:int):(result:int) ensures result == n + 2 { n + 3 } by method { return n + 2; } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "Offset(old(cell.value))");
    var result = await Run(source, TwoStateGenerator);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition &&
      obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // Logical dependency traversal retains invalid type predicates and recursive contracts with cycle guards.
  [Theory]
  [InlineData("predicate Good(n: int) ensures false { true } type Positive = n: int | Good(n) witness 1 function Hidden(n: Positive): int { 0 }")]
  [InlineData("function Hidden(n: int): int ensures Hidden(n) == 1 { if n <= 0 then 0 else Hidden(n - 1) }")]
  public async Task AuditsSpecificationTypeByMethodAndRecursiveDependencies(string dependency) {
    var source = TwoStateSource.Replace("twostate predicate Changed", dependency + " twostate predicate Changed")
      .Replace("old(cell.value) + 2", "old(cell.value) + Hidden(1)");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // Runtime-only postconditions cannot indict a goal reached with an invalid typed initial field.
  [Theory]
  [InlineData(-1, false)]
  [InlineData(2, false)]
  [InlineData(-1, true)]
  public async Task ValidatesInitialFieldsBeforeRuntimeGoalEvidence(int value, bool mutateAfterConstruction) {
    const string source = "module Client { class Cell { ghost var value: nat constructor() { value := 0; } } method Goal(cell: Cell) ensures false {} }";
    var generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\", \"Client.Cell.value\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(" +
      (mutateAfterConstruction ? 0 : value) + "); " + (mutateAfterConstruction ? "cell.value := " + value + ";" : "") + " }";
    var result = await Run(source, generator, maxQueries: 0);
    Assert.True(result.Status == (value < 0 ? ContractRuntimeStatus.Inconclusive : ContractRuntimeStatus.ViolationFound), Detail(result));
    Assert.Equal(value < 0 ? 0 : 1, result.Population.Valid);
    Assert.Equal(value < 0 ? 1 : 0, result.Population.PreconditionRejected);
  }

  // A nullable reference cycle does not hide invalid nested datatype fields or consume solver budget.
  [Theory]
  [InlineData(-1)]
  [InlineData(2)]
  public async Task ValidatesNestedFieldsInCyclicInitialHeap(int value) {
    const string source = "module Client { datatype Tree = Node(n: nat, children: seq<Tree>) class Cell { var tree: Tree var next: Cell? constructor(tree: Tree) { this.tree := tree; next := null; } } method Goal(cell: Cell) ensures false {} }";
    var generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(Node(0, [Node(" + value + ", [])])); cell.next := cell; }";
    var result = await Run(source, generator, maxQueries: 0);
    Assert.True(result.Status == (value < 0 ? ContractRuntimeStatus.Inconclusive : ContractRuntimeStatus.ViolationFound), Detail(result));
    Assert.Equal(value < 0 ? 0 : 1, result.Population.Valid);
  }

  // An exact successful membership proof admits a second distinct heap without consuming a closed-query slot.
  [Fact]
  public async Task MembershipReuseAdmitsDistinctHeapsAfterQueryCap() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive var unrelated:int constructor(value:Positive, unrelated:int) " +
      "{ this.value := value; this.unrelated := unrelated; } } method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ var unrelated := r.Int(1,1000000000); cell := new Cell(2, unrelated); }";
    var directory = Path.Combine("/workspace/tmp", "contract-membership-reuse-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxQueries: 2, sampleCount: 2, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(2, result.Population.Valid);
    var heaps = Directory.GetFiles(directory, "sample-*.jsonl").SelectMany(File.ReadAllLines)
      .Select(line => System.Text.Json.JsonDocument.Parse(line).RootElement.Clone())
      .Where(record => record.GetProperty("kind").GetString() == "heap_capture" &&
        record.GetProperty("phase").GetString() == "entry")
      .Select(record => record.GetProperty("heap").GetRawText()).Distinct().ToList();
    Assert.Equal(2, heaps.Count);
    Assert.Single(Directory.GetFiles(directory, "initial-type-query-*.result.json"));
    Assert.Equal(2, Directory.GetFiles(directory, "initial-type-certificate-*.json").Length);
    var receiptPath = Assert.Single(Directory.GetFiles(directory, "membership-proof-reuse-initial-*.json"));
    using var receipt = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(receiptPath));
    var original = receipt.RootElement.GetProperty("originalProof");
    Assert.Equal("unsat", original.GetProperty("outcome").GetString());
    Assert.Equal(receipt.RootElement.GetProperty("identitySha256").GetString(),
      original.GetProperty("identitySha256").GetString());
    foreach (var artifactProperty in new[] { "queryArtifact", "resultArtifact" }) {
      var artifact = Path.Combine(directory, original.GetProperty(artifactProperty).GetString()!);
      Assert.True(File.Exists(artifact));
      var hashProperty = artifactProperty == "queryArtifact" ? "querySha256" : "resultSha256";
      Assert.Equal(original.GetProperty(hashProperty).GetString(),
        ContractHarnessBuilder.Hash(await File.ReadAllTextAsync(artifact)));
    }
  }

  // Different refined values produce distinct membership identities and native proofs.
  [Fact]
  public async Task MembershipReuseRejectsChangedValue() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ var value := r.Int(1,1000000000); cell := new Cell(value); }";
    var directory = Path.Combine("/workspace/tmp", "contract-membership-changed-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxQueries: 3, sampleCount: 2, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(2, result.Population.Valid);
    var queries = Directory.GetFiles(directory, "initial-type-query-*.dfy");
    Assert.Equal(2, queries.Length);
    Assert.Equal(2, queries.Select(File.ReadAllText).Distinct().Count());
    Assert.Empty(Directory.GetFiles(directory, "membership-proof-reuse-*.json"));
  }

  // An identical unsuccessful membership query is retried and never authorizes either invalid heap.
  [Fact]
  public async Task MembershipReuseRejectsUnsuccessfulProof() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive var unrelated:int constructor(value:Positive, unrelated:int) " +
      "{ this.value := value; this.unrelated := unrelated; } } method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ var unrelated := r.Int(1,1000000000); cell := new Cell(-1, unrelated); }";
    var directory = Path.Combine("/workspace/tmp", "contract-membership-failed-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxQueries: 3, sampleCount: 2, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Equal(0, result.Population.Valid);
    var queries = Directory.GetFiles(directory, "initial-type-query-*.dfy");
    Assert.Equal(2, queries.Length);
    Assert.Single(queries.Select(File.ReadAllText).Distinct());
    foreach (var path in Directory.GetFiles(directory, "initial-type-query-*.result.json")) {
      using var queryResult = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(path));
      Assert.NotEqual("unsat", queryResult.RootElement.GetProperty("outcome").GetString());
    }
    Assert.Empty(Directory.GetFiles(directory, "membership-proof-reuse-*.json"));
  }

  // An exact observed-state membership can cite the initial proof while the original transition is checked separately.
  [Fact]
  public async Task MembershipReuseSharesExactInitialProofWithObservedState() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive var counter:int constructor(value:Positive, counter:int) " +
      "{ this.value := value; this.counter := counter; } } " +
      "twostate predicate Changed(cell:Cell) reads cell { cell.counter == old(cell.counter) + 2 } " +
      "method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.counter := cell.counter + 1; } }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ cell := new Cell(2, 0); }";
    var directory = Path.Combine("/workspace/tmp", "contract-membership-observed-reuse-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxQueries: 4, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Single(Directory.GetFiles(directory, "initial-type-query-*.result.json"));
    Assert.Empty(Directory.GetFiles(directory, "observed-type-query-*.result.json"));
    var receiptPath = Assert.Single(Directory.GetFiles(directory, "membership-proof-reuse-observed-*.json"));
    using var receipt = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(receiptPath));
    Assert.Equal("observed", receipt.RootElement.GetProperty("role").GetString());
    Assert.Equal("initial", receipt.RootElement.GetProperty("originalProof").GetProperty("role").GetString());
    Assert.Equal(receipt.RootElement.GetProperty("identitySha256").GetString(),
      receipt.RootElement.GetProperty("originalProof").GetProperty("identitySha256").GetString());
  }

  // A valid initial proof cannot admit a changed invalid observed carrier.
  [Fact]
  public async Task MembershipReuseKeepsInvalidLaterStateUnchecked() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value) - 3 } " +
      "method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.value := -1; } }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ cell := new Cell(2); }";
    var directory = Path.Combine("/workspace/tmp", "contract-membership-invalid-later-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, generator, maxQueries: 3, artifactDirectory: directory);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Single(Directory.GetFiles(directory, "initial-type-query-*.result.json"));
    var observedResultPath = Assert.Single(Directory.GetFiles(directory, "observed-type-query-*.result.json"));
    using var observedResult = System.Text.Json.JsonDocument.Parse(await File.ReadAllTextAsync(observedResultPath));
    Assert.NotEqual("unsat", observedResult.RootElement.GetProperty("outcome").GetString());
    Assert.Empty(Directory.GetFiles(directory, "membership-proof-reuse-*.json"));
  }

  // Exact proof state remains campaign-local when the supplied source view changes.
  [Fact]
  public async Task MembershipReuseDoesNotCrossCampaignOrSourceView() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) " +
      "{ cell := new Cell(2); }";
    var firstDirectory = Path.Combine("/workspace/tmp", "contract-membership-campaign-first-" + Guid.NewGuid().ToString("N"));
    var secondDirectory = Path.Combine("/workspace/tmp", "contract-membership-campaign-second-" + Guid.NewGuid().ToString("N"));
    var first = await Run(source, generator, maxQueries: 2, artifactDirectory: firstDirectory);
    var second = await Run(source + "\n// distinct supplied source view", generator, maxQueries: 2,
      artifactDirectory: secondDirectory);
    Assert.True(first.Status == ContractRuntimeStatus.ViolationFound, Detail(first));
    Assert.True(second.Status == ContractRuntimeStatus.ViolationFound, Detail(second));
    var firstQuery = Assert.Single(Directory.GetFiles(firstDirectory, "initial-type-query-*.dfy"));
    var secondQuery = Assert.Single(Directory.GetFiles(secondDirectory, "initial-type-query-*.dfy"));
    Assert.NotEqual(File.ReadAllText(firstQuery), File.ReadAllText(secondQuery));
    Assert.Empty(Directory.GetFiles(firstDirectory, "membership-proof-reuse-*.json"));
    Assert.Empty(Directory.GetFiles(secondDirectory, "membership-proof-reuse-*.json"));
  }

  // Residual refinement constraints require a satisfiable typed initial state before runtime evidence.
  [Theory]
  [InlineData(-1, 2)]
  [InlineData(2, 2)]
  [InlineData(2, 0)]
  public async Task ValidatesResidualInitialFieldConstraint(int value, int queries) {
    const string source = "module Client { type Positive = n: int | n > 0 witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }";
    var generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(" + value + "); }";
    var result = await Run(source, generator, maxQueries: queries);
    var valid = value > 0 && queries > 0;
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
  }

  // Exact initial construction includes refined root arguments even when the captured heap is valid.
  [Theory]
  [InlineData(2, true)]
  [InlineData(-1, false)]
  public async Task NativeConstructionIncludesRefinedRootInput(int argument, bool valid) {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "method Goal(cell:Cell, argument:Positive) ensures false {} }";
    var generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell, argument:Positive) " +
      "{ cell := new Cell(2); argument := " + argument + "; }";
    var result = await Run(source, generator, maxQueries: 2);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
  }

  // A plain ill-defined function cannot supply a type certificate merely because it has no explicit contracts.
  [Fact]
  public async Task NativeConstructionRequiresPlainFunctionWellDefinedness() {
    const string source = "module Client { function Divide(n:int):int { 1 / n } " +
      "type Positive = n:int | Divide(n) > 0 witness * " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(1); }";
    var result = await Run(source, generator, maxQueries: 2);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Equal(0, result.Population.Valid);
  }

  // Reusing the exact initial construction certificate leaves enough budget for the original observed-state decision.
  [Fact]
  public async Task ReusesExactNativeInitialCertificateForHeapDecision() {
    const string source = "module Client { type Positive = n:int | n > 0 witness 1 " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } " +
      "twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value) + 2 } " +
      "method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; } }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }";
    var result = await Run(source, generator, maxQueries: 5);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Contains(result.Violations, violation => violation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt);
  }

  // Type-constraint dependencies cannot admit a heap using an unvalidated function contract.
  [Fact]
  public async Task InitialFieldConstraintCalleeRemainsUnchecked() {
    const string source = "module Client { predicate Good(n: int) ensures false { n > 0 } type Positive = n: int | Good(n) witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Omitted refined ghost fields still require a satisfiable original typed heap.
  [Theory]
  [InlineData("false", 2, false)]
  [InlineData("n > 0", 2, true)]
  [InlineData("n > 0", 0, false)]
  public async Task ValidatesOmittedRefinedGhostField(string constraint, int queries, bool valid) {
    var source = "module Client { type Hidden = n: int | " + constraint + " witness * class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value: Hidden :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }";
    var result = await Run(source, generator, maxQueries: queries);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
  }

  // Unconstrained ordinary function fields can remain omitted without a solver query.
  [Fact]
  public async Task KeepsSafeOrdinaryArrowOmission() {
    const string source = "module Client { class Cell { ghost var unused: int -> int constructor Init() requires false { ghost var value: int -> int :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }";
    var result = await Run(source, generator, maxQueries: 0);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
  }

  // An omitted ghost function returning an empty refined sequence has a valid constant-function inhabitant.
  [Fact]
  public async Task RunsWithConstructibleRefinedArrowOmission() {
    const string source = "module Client { type Empty = n: int | false witness * class Cell { ghost var unused: int -> seq<Empty> constructor Init() requires false { ghost var value: int -> seq<Empty> :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }";
    var result = await Run(source, generator, maxQueries: 0);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.PreconditionUnchecked);
  }

  // An original declared witness can admit omitted state only after its native dependency and witness proofs succeed.
  [Theory]
  [InlineData(1, true)]
  [InlineData(0, false)]
  public async Task CertifiesOriginalOmittedWitness(int witness, bool valid) {
    var source = "module Client { ghost predicate Good(n:int) ensures Good(n) == (n > 0) { n > 0 } " +
      "type Hidden = n:int | Good(n) witness " + witness +
      " class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value:Hidden :| true; unused := value; } } " +
      "method Goal(cell:Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }";
    var result = await Run(source, generator, maxQueries: 1);
    Assert.True(result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), Detail(result));
    Assert.Equal(valid ? 1 : 0, result.Population.Valid);
  }

  // A certified requires-only specification supports either polarity of the unchanged captured-heap property.
  [Theory]
  [InlineData(1, true)]
  [InlineData(2, false)]
  public async Task CertifiedSpecificationDecidesBothHeapPolarities(int increment, bool violation) {
    var source = TwoStateSource.Replace("twostate predicate Changed", "function Offset(n:int):int requires n >= 0 { n + 2 } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "if old(cell.value) >= 0 then Offset(old(cell.value)) else 0")
      .Replace("cell.value := cell.value + 1", "cell.value := cell.value + " + increment);
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == (violation ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.NoViolationFound), Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition && obligation.Evaluations.ClosedSmt == 1);
  }

  // Actual captured transitions retain native original Q after a checked heap-projection equivalence.
  [Theory]
  [InlineData(1, true)]
  [InlineData(2, false)]
  public async Task HeapProjectionKeepsOriginalRuntimeTransition(int increment, bool violation) {
    var source = TwoStateSource.Replace("cell.value := cell.value + 1", "cell.value := cell.value + " + increment);
    var directory = Path.Combine("/workspace/tmp", "contract-heap-projection-" + Guid.NewGuid().ToString("N"));
    var result = await Run(source, TwoStateGenerator, artifactDirectory: directory);
    Assert.True(result.Status == (violation ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.NoViolationFound), Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.RuntimeErrors);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.Postcondition && obligation.Evaluations.ClosedSmt == 1);
    Assert.Contains(Directory.GetFiles(directory, "heap-query-*.result.json"), path =>
      File.ReadAllText(path).Contains("addedCheckedEquivalences=1", StringComparison.Ordinal));
  }

  // An empty refinement nested in an omitted datatype must not be hidden by partial capture.
  [Fact]
  public async Task RejectsOmittedNestedEmptyRefinement() {
    const string source = "module Client { type Empty = n: int | false witness * datatype Box<T> = Box(value: T) class Cell { ghost var unused: Box<Empty> constructor Init() requires false { ghost var value: Box<Empty> :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} {:pbt_heap_constructor \"Client.Cell\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // A higher-order reference to an invalid predicate remains a constraint dependency.
  [Fact]
  public async Task HigherOrderInitialFieldConstraintRemainsUnchecked() {
    const string source = "module Client { predicate Good(n: int) ensures false { n > 0 } type Positive = n: int | (var f := Good; f(n)) witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }";
    const string generator = "method {:pbt_generator \"Client.Goal\"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Equal(0, result.Population.Valid);
    Assert.Empty(result.Violations);
  }

  // Higher-order specification calls cannot hide an unvalidated function behind a local binding.
  [Fact]
  public async Task HigherOrderSpecificationDependencyRemainsUnchecked() {
    var source = TwoStateSource.Replace("twostate predicate Changed", "function Bad(): int ensures false { 0 } twostate predicate Changed")
      .Replace("old(cell.value) + 2", "old(cell.value) + (var f := Bad; f())");
    var result = await Run(source, TwoStateGenerator);
    Assert.True(result.Status == ContractRuntimeStatus.Inconclusive, Detail(result));
    Assert.Empty(result.Violations);
    Assert.Contains(result.Obligations, obligation => obligation.UncheckedReason == "callee_contract_unvalidated");
  }

  // Scalar callee checks use original sources even when another module contains a ghost-backed draft.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task ScalarClosedCalleeUsesOriginalSources(int offset, bool invalidCallee) {
    var source = Store.Replace("ensures result == Read()", "ensures exists k: int :: result == 2 * k")
      .Replace("ensures result == cell.Read() + 1", "ensures false");
    var generator = Generator.Replace("Create(7)", "Create(4)");
    var draft = Draft.Replace("result := Read();", "result := Read() + " + offset + ";");
    var result = await Run(source, generator, draft);
    Assert.True(result.Status == (invalidCallee ? ContractRuntimeStatus.Inconclusive : ContractRuntimeStatus.ViolationFound), Detail(result));
    Assert.Equal(invalidCallee ? 1 : 0, result.Population.CalleeContractViolations);
    Assert.Equal(invalidCallee ? 0 : 1, result.Population.Valid);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition &&
      obligation.Evaluations.ClosedSmt > 0);
  }

  // Finite recursive map children retain their nested natural-number constraints at runtime.
  [Theory]
  [InlineData(-1)]
  [InlineData(2)]
  public async Task ChecksRecursiveMapDatatype(int value) {
    const string source = "module Client { datatype Tree = Node(n: nat, children: map<int, Tree>) method Goal(tree: Tree) ensures false {} }";
    var generator = "method {:pbt_generator \"Client.Goal\"} Generate(r: PbtRandom.Source) returns(tree: Tree) { tree := Node(0, map[1 := Node(" + value + ", map[])]); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == (value < 0 ? ContractRuntimeStatus.Inconclusive : ContractRuntimeStatus.ViolationFound), Detail(result));
    Assert.Equal(value < 0 ? 1 : 0, result.Population.PreconditionRejected);
    Assert.Equal(value < 0 ? 0 : 1, result.Population.Valid);
  }

  internal static string Detail(ContractRuntimeCampaignResult result) =>
    System.Text.Json.JsonSerializer.Serialize(result, ContractJson.Options);

  internal static async Task<ContractRuntimeCampaignResult> Run(string source, string generator,
    string? draft = null, string entry = "Client.Goal", int maxQueries = 6, int sampleCount = 1, string? artifactDirectory = null) {
    var directory = artifactDirectory ?? Path.Combine("/workspace/tmp", "contract-runtime-heap-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var snapshots = new[] { new ContractSource("Main.dfy", source, ContractHarnessBuilder.Hash(source)) };
    var request = new ContractRuntimeCampaignRequest(1, snapshots, new(entry), "17",
      Drafts: draft == null ? [] : [new("Store.Cell.ReadValue", "Read.dfy", draft, ContractHarnessBuilder.Hash(draft))],
      Generator: new("Generator.dfy", generator, ContractHarnessBuilder.Hash(generator)),
      SampleCount: sampleCount, TimeoutMilliseconds: 60000, MaxClosedQueries: maxQueries,
      ClosedQueryTimeoutMilliseconds: 3000);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(65));
    return await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token);
  }
}
