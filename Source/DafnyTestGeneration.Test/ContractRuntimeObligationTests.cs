using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using System.Linq;
using Microsoft.Dafny;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeObligationTests {
  // Runtime requests preserve generator content and replay identity over the public wire format.
  [Fact]
  public void RequestRoundTrips() {
    var request = new ContractRuntimeCampaignRequest(2, [new("M.dfy", "method M() {}", "hash")],
      new("M"), "18446744073709551615", Generator: new("G.dfy", "generator", "hash"), ReplayOrdinal: 9);
    var json = JsonSerializer.Serialize(request, ContractJson.Options);
    var copy = JsonSerializer.Deserialize<ContractRuntimeCampaignRequest>(json, ContractJson.Options)!;
    Assert.Equal(request.Seed, copy.Seed);
    Assert.Equal(request.Generator, copy.Generator);
    Assert.Equal(9, copy.ReplayOrdinal);
  }

  // Unknown request properties cannot silently change the intended diagnostic campaign.
  [Fact]
  public void RequestRejectsUnknownField() {
    Assert.Throws<JsonException>(() => JsonSerializer.Deserialize<ContractRuntimeCampaignRequest>(
      "{\"schemaVersion\":2,\"sources\":[],\"entry\":{\"symbol\":\"M\"},\"seed\":\"1\",\"unexpected\":true}", ContractJson.Options));
  }

  // Runtime result enums and all population denominators retain their canonical serialized names.
  [Fact]
  public void ResultRoundTrips() {
    var result = new ContractRuntimeCampaignResult(1, ContractRuntimeStatus.ViolationFound, "", "1",
      new(Generated: 1, Executed: 1, Valid: 1, ViolatingSamples: 1),
      [new("postcondition:M.dfy:2:3:0", ContractRuntimeObligationKind.Postcondition, "M.dfy", 2, 3,
        "r > 0", null, ContractRuntimeDecisionMethod.Runtime, null, new(Runtime: 1), 1)],
      [], [], [], null, [], []);
    var json = JsonSerializer.Serialize(result, ContractJson.Options);
    var copy = JsonSerializer.Deserialize<ContractRuntimeCampaignResult>(json, ContractJson.Options)!;
    Assert.Equal(result.Population, copy.Population);
    Assert.Equal(result.Obligations[0], copy.Obligations[0]);
    Assert.Equal("violation_found", JsonDocument.Parse(json).RootElement.GetProperty("status").GetString());
  }
  // An opaque ghost predicate with finite set comprehension remains a runtime obligation.
  [Fact]
  public async Task ClassifiesOpaqueFiniteComprehension() {
    var result = await Transform("opaque ghost predicate Good(s: seq<int>) { |set x | x in s| <= |s| } method Goal(x: int) ensures Good([x]) {}");
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, Assert.Single(result.Clauses).Obligation.DecisionMethod);
  }

  // Infinite set values cannot be fabricated for a closed clause query.
  [Fact]
  public async Task InfiniteSetValueIsUnchecked() {
    var result = await Transform("method Goal(x: int) { ghost var s: iset<int> := iset i: int | i >= x; while false invariant x in s {} }");
    Assert.All(result.Clauses, c => Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, c.Obligation.DecisionMethod));
  }

  // A ghost method output unavailable to compiled code remains explicitly unchecked.
  [Fact]
  public async Task GhostMethodValueIsUnavailable() {
    var result = await Transform("ghost method Hidden() returns (y: int) { y := 1; } method Goal(x: int) { ghost var y := Hidden(); while false invariant y == x {} }");
    Assert.All(result.Clauses, c => Assert.Equal("value_unavailable", c.Obligation.UncheckedReason));
    Assert.Contains(result.Exclusions, e => e.Symbol.EndsWith(".y"));
  }

  // Allocation-state predicates remain unchecked rather than being compiled as ordinary booleans.
  [Fact]
  public async Task FreshRemainsUnchecked() {
    var result = await Transform("class Box {} method Goal(x: int) returns (o: Box) ensures fresh(o) { o := new Box; }");
    Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, Assert.Single(result.Clauses, c => c.Expression is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Fresh }).Obligation.DecisionMethod);
  }

  // Nested proof statements in a ghost function preserve both surviving expression branches during deghosting.
  [Fact]
  public async Task NestedStatementExpressionsKeepSiblingExpressions() {
    var result = await Transform("ghost function Plus(x:int):int { assert true; " +
      "if x>=0 then (assert true; x+1) else (assert true; x-1) } " +
      "method Goal(x:int) ensures Plus(x)==(if x>=0 then x+1 else x-1) {}");
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ContractSourceSnapshot.ParseAsync(reporter, result.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var plus = ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>().Single(function => function.Name == "Plus");
    Assert.False(plus.IsGhost);
    var branch = Assert.IsType<ITEExpr>(plus.Body!.Resolved);
    Assert.IsType<BinaryExpr>(branch.Thn.Resolved);
    Assert.IsType<BinaryExpr>(branch.Els.Resolved);
  }

  // Split verification quantifiers share source tokens and must not create competing runtime call wrappers.
  [Fact]
  public async Task ColumnTraceQuantifierInstrumentsOriginalCallOnce() {
    var result = await Transform("function StepColumn(byteMode:bool,ch:char,column:nat):nat { if byteMode then column+1 else column } " +
      "ghost predicate ColumnTraceRelation(byteMode:bool,data:seq<char>,initialColumn:nat,columns:seq<nat>) { " +
      "|columns|==|data|+1 && columns[0]==initialColumn && " +
      "forall i :: 0<=i<|data| ==> columns[i+1]==StepColumn(byteMode,data[i],columns[i]) } " +
      "method Goal(x:int) ensures ColumnTraceRelation(true,[],0,[0]) {}");
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ContractSourceSnapshot.ParseAsync(reporter, result.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    var wrapper = Assert.Single(members.OfType<Function>().Where(function => function.Name.StartsWith("StepColumn__pbt_site_")));
    var relation = members.OfType<Function>().Single(function => function.Name == "ColumnTraceRelation");
    Assert.False(relation.IsGhost);
    var quantifier = Assert.IsType<ForallExpr>(Assert.IsType<BinaryExpr>(relation.Body!.Resolved).E1.Resolved);
    Assert.Contains(quantifier.Term.Descendants().OfType<FunctionCallExpr>(), call => call.Function == wrapper);
  }

  // Logical method callee postconditions retain their original index and owner for per-invocation heap queries.
  [Fact]
  public async Task ClassifiesInternalMethodHeapPostcondition() {
    var result = await Transform("class Cell { var value:int } " +
      "twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value)+1 } " +
      "method Step(cell:Cell) modifies cell ensures Changed(cell) { cell.value:=cell.value+1; } " +
      "method Goal(x:int) { var cell:=new Cell; cell.value:=x; Step(cell); }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition));
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, clause.Obligation.DecisionMethod);
    Assert.Equal(0, clause.EntryHeapPostcondition);
    Assert.Equal("M.Step", clause.CallHeapScope);
  }

  private static async Task<ContractRuntimeTransformation> Transform(string text) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    // The transformer builds the harness main around the generator that the runner always inserts.
    var source = "module M { import PbtRandom " + text + " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] sources = [new("M.dfy", source, ContractHarnessBuilder.Hash(source)), new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))];
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(m => m.Message)));
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
  }

}
