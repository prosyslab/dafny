using System;
using System.Collections.Generic;
using System.IO;
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

  // A finite enumerable ghost choice is deghosted and remains available to its target assertion.
  [Fact]
  public async Task KeepsEnumerableGhostChoiceAvailable() {
    var result = await Transform("method Goal(x: int) { ghost var y: int :| y in {x}; assert y == x; }");
    var assertion = Assert.Single(result.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.Assertion);
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, assertion.Obligation.DecisionMethod);
    Assert.DoesNotContain(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".y"));
  }

  // Every ghost LHS of an unbounded choice is unavailable to assertion instrumentation.
  [Fact]
  public async Task ExcludesEveryUnboundedGhostChoiceValue() {
    var result = await Transform("method Goal(x: int) { ghost var y: seq<int>, z: seq<int> :| |y| > x && |z| > |y|; assert |z| > |y|; }");
    var assertion = Assert.Single(result.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.Assertion);
    Assert.Equal("value_unavailable", assertion.Obligation.UncheckedReason);
    Assert.Contains(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".y"));
    Assert.Contains(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".z"));
  }

  // Availability loss propagates through later ghost assignments instead of inventing a witness.
  [Fact]
  public async Task PropagatesUnavailableGhostChoiceValue() {
    var result = await Transform("method Goal(x: int) { ghost var y: seq<int> :| |y| > x; ghost var z := y; assert |z| > x; }");
    var assertion = Assert.Single(result.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.Assertion);
    Assert.Equal("value_unavailable", assertion.Obligation.UncheckedReason);
    Assert.Contains(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".y"));
    Assert.Contains(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".z"));
  }

  // A shared ghost declaration remains erased, so one unavailable initializer excludes every declared local.
  [Fact]
  public async Task ExcludesWholeSharedGhostDeclaration() {
    var result = await Transform("method Goal(x: int) { ghost var y: seq<int> :| |y| > x; ghost var z, w := y, 0; assert w == 0; }");
    var assertion = Assert.Single(result.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.Assertion);
    Assert.Equal("value_unavailable", assertion.Obligation.UncheckedReason);
    Assert.Contains(result.Exclusions, exclusion => exclusion.Symbol.EndsWith(".w"));
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
    var options = MemoryOptions();
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
    var options = MemoryOptions();
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

  // Match checks use post-call output snapshots while evidence remains bound to the original formals.
  [Fact]
  public async Task MatchPostconditionCapturesOutputsAndPreservesEvidence() {
    var result = await Transform("datatype Choice = Left | Right " +
      "method Goal(c:Choice) returns (x:int,y:int) " +
      "ensures (match c case Left => x == 0 case Right => y == 1) { x:=0; y:=1; }", ChoiceGenerator);
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition));
    var original = result.Prepared.Method;
    Assert.Same(original, clause.Owner);
    Assert.Equal(new IVariable[] { original.Ins[0], original.Outs[0], original.Outs[1] }, clause.Variables);
    Assert.Equal(result.Prepared.Source.Sha256, clause.OriginalSourceHash);
    Assert.Equal(result.Prepared.Source.Path, clause.Obligation.Path);
    Assert.Equal(original.Ens[0].E.Origin.line, clause.Obligation.Line);
    Assert.Equal(original.Ens[0].E.Origin.col, clause.Obligation.Column);
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, clause.Obligation.DecisionMethod);
    Assert.All(Identifiers(clause.Expression).Where(identifier => identifier.Var is Formal),
      identifier => Assert.Contains(identifier.Var, original.Ins.Concat(original.Outs)));
    Assert.All(original.Outs, output => Assert.Contains(Identifiers(clause.Expression), identifier => identifier.Var == output));

    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    var captures = OutputCaptures(wrapper);
    Assert.Equal(2, captures.Count);
    var check = RuntimeCheck(wrapper, clause);
    var property = RuntimeProperty(check);
    var invocation = Assert.Single(wrapper.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "Goal"));
    foreach (var capture in captures) {
      Assert.Contains(Identifiers(property), identifier => identifier.Var == capture.Local);
      Assert.DoesNotContain(Identifiers(property), identifier => identifier.Var == capture.Output);
      Assert.True(invocation.Origin.pos < capture.Assignment.Origin.pos);
      Assert.True(capture.Assignment.Origin.pos < check.Origin.pos);
    }
  }

  // Method-call postconditions capture their own outputs and retain the original callee identity.
  [Fact]
  public async Task CalleeMatchCapturesCalleeOutputs() {
    var result = await Transform("datatype Choice = Left | Right " +
      "method Step(c:Choice) returns (x:int,y:int) " +
      "ensures (match c case Left => x == 0 case Right => y == 1) { x:=0; y:=1; } " +
      "method Goal(c:Choice) { var x,y := Step(c); }", ChoiceGenerator);
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition));
    Assert.Equal("M.Step", clause.Obligation.Callee);
    Assert.Equal("Step", clause.Owner.Name);
    var parsed = await ParseMemory(result.Sources);
    var wrapper = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Method>()
      .Where(method => method.Name.StartsWith("Step__pbt_site_", StringComparison.Ordinal)));
    var captures = OutputCaptures(wrapper);
    Assert.Equal(2, captures.Count);
    var property = RuntimeProperty(RuntimeCheck(wrapper, clause));
    Assert.All(captures, capture => Assert.Contains(Identifiers(property), identifier => identifier.Var == capture.Local));
    Assert.DoesNotContain(Identifiers(property), identifier => identifier.Var is Formal formal && wrapper.Outs.Contains(formal));
  }

  // A match binder with an output's name remains its own variable and never becomes an output capture.
  [Fact]
  public async Task MatchBinderRetainsItsIdentity() {
    var result = await Transform("datatype Choice = Left(value:int) | Right " +
      "method Goal(c:Choice) returns (x:int,y:int) " +
      "ensures (match c case Left(x) => x == x + y case Right => y == 0) { x:=0; y:=0; }",
      "method Generate(r:PbtRandom.Source) returns (c:Choice) { c:=Left(0); }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition));
    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    var capture = Assert.Single(OutputCaptures(wrapper));
    Assert.Same(wrapper.Outs[1], capture.Output);
    var property = RuntimeProperty(RuntimeCheck(wrapper, clause));
    var binder = Assert.Single(Identifiers(property).Where(identifier => identifier.Var.Name == "x")
      .Select(identifier => identifier.Var).Distinct());
    Assert.IsType<BoundVar>(binder);
    Assert.NotSame(wrapper.Outs[0], binder);
    Assert.Contains(Identifiers(property), identifier => identifier.Var == capture.Local);
  }

  // Generated capture declarations cannot shadow an authored input in the preferred name family.
  [Fact]
  public async Task OutputCaptureAvoidsAuthoredNameCollision() {
    var result = await Transform("method Goal(pbtOutput0:int) returns (x:int) " +
      "ensures x == pbtOutput0 { x:=pbtOutput0; }",
      "method Generate(r:PbtRandom.Source) returns (pbtOutput0:int) { pbtOutput0:=0; }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition));
    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    var capture = Assert.Single(OutputCaptures(wrapper));
    Assert.DoesNotContain(wrapper.Ins.Concat(wrapper.Outs), formal => formal.Name == capture.Local.Name);
    var property = RuntimeProperty(RuntimeCheck(wrapper, clause));
    Assert.Contains(Identifiers(property), identifier => identifier.Var == wrapper.Ins[0]);
    Assert.Contains(Identifiers(property), identifier => identifier.Var == capture.Local);
  }

  // Old heap values are captured before invocation while returned outputs are captured afterward.
  [Fact]
  public async Task OldStateCapturePrecedesCallAndOutputCaptureFollowsIt() {
    var result = await Transform("class Cell { var value:int } " +
      "method Goal(cell:Cell) returns (x:int) modifies cell ensures x == old(cell.value) " +
      "{ x:=cell.value; cell.value:=cell.value+1; }",
      "method Generate(r:PbtRandom.Source) returns (cell:Cell) { cell:=new Cell; cell.value:=0; }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition && !item.TypeConstraint));
    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    var oldCapture = Assert.Single(wrapper.Body!.Descendants().OfType<SingleAssignStmt>().Distinct().Where(assignment =>
      assignment.Lhs.Resolved is IdentifierExpr { Var: LocalVariable } &&
      assignment.Rhs is ExprRhs { Expr.Resolved: MemberSelectExpr { Member.Name: "value" } }));
    var oldLocal = Assert.IsType<LocalVariable>(Assert.IsAssignableFrom<IdentifierExpr>(oldCapture.Lhs.Resolved).Var);
    var outputCapture = Assert.Single(OutputCaptures(wrapper));
    var invocation = Assert.Single(wrapper.Body.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "Goal"));
    var check = RuntimeCheck(wrapper, clause);
    Assert.True(oldCapture.Origin.pos < invocation.Origin.pos);
    Assert.True(invocation.Origin.pos < outputCapture.Assignment.Origin.pos);
    Assert.True(outputCapture.Assignment.Origin.pos < check.Origin.pos);
    var property = RuntimeProperty(check);
    Assert.Contains(Identifiers(property), identifier => identifier.Var == oldLocal);
    Assert.Contains(Identifiers(property), identifier => identifier.Var == outputCapture.Local);
    Assert.Contains(result.Prepared.Method.Outs[0], clause.Variables);
  }

  // An unavailable infinite-set output stays unchecked and never gains a compiled capture.
  [Fact]
  public async Task UnavailableOutputRemainsUncheckedWithoutCapture() {
    var result = await Transform("method Goal(x:int) returns (ghost hidden:iset<int>) " +
      "ensures x in hidden { hidden := iset n:int | n >= x; }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition));
    Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, clause.Obligation.DecisionMethod);
    Assert.Equal("value_unavailable", clause.Obligation.UncheckedReason);
    Assert.Contains(result.Prepared.Method.Outs[0], clause.Variables);
    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    Assert.Empty(OutputCaptures(wrapper));
    var checkpoint = Assert.Single(wrapper.Body!.Descendants().OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name == "Checkpoint" && call.Args[0].Resolved is StringLiteralExpr literal &&
      Equals(literal.Value, clause.Obligation.Id)));
    Assert.DoesNotContain(checkpoint.Args.SelectMany(Identifiers), identifier => identifier.Var is Formal formal && wrapper.Outs.Contains(formal));
  }

  // A check before an unused output is assigned reads only its already assigned output.
  [Fact]
  public async Task AssertionDoesNotCaptureUnassignedUnusedOutput() {
    var result = await Transform("method Goal(x:int) returns (used:int,unused:int) " +
      "{ used:=x; assert used == x; unused:=0; }");
    var clause = Assert.Single(result.Clauses.Where(item => item.Obligation.Kind == ContractRuntimeObligationKind.Assertion));
    var parsed = await ParseMemory(result.Sources);
    var goal = MethodNamed(parsed, "Goal");
    var capture = Assert.Single(OutputCaptures(goal));
    Assert.Same(goal.Outs[0], capture.Output);
    var unusedAssignment = Assert.Single(goal.Body!.Descendants().OfType<SingleAssignStmt>().Distinct().Where(assignment =>
      assignment.Lhs.Resolved is IdentifierExpr identifier && identifier.Var == goal.Outs[1]));
    var check = RuntimeCheck(goal, clause);
    Assert.True(capture.Assignment.Origin.pos < check.Origin.pos);
    Assert.True(check.Origin.pos < unusedAssignment.Origin.pos);
    Assert.Contains(Identifiers(RuntimeProperty(check)), identifier => identifier.Var == capture.Local);
  }

  private const string ChoiceGenerator = "method Generate(r:PbtRandom.Source) returns (c:Choice) { c:=Left; }";

  private static DafnyOptions MemoryOptions() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null) {
      TheProverFactory = new NoProverFactory()
    };
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    Assert.False(options.Trace);
    Assert.Null(options.XmlSink);
    Assert.Null(options.DafnyPrintFile);
    Assert.Null(options.DafnyPrintResolvedFile);
    Assert.Null(options.AutoReqPrintFile);
    options.XmlSink = null;
    options.DafnyPrintFile = null;
    options.DafnyPrintResolvedFile = null;
    options.AutoReqPrintFile = null;
    options.DafnyPrintExportedViews = [];
    options.AdditionalPlugins = [];
    options.AdditionalPluginArguments = [];
    options.PrintIncludesMode = DafnyOptions.IncludesModes.None;
    options.PrintStats = false;
    options.PrintFunctionCallGraph = false;
    return options;
  }

  private sealed class NoProverFactory : Microsoft.Boogie.ProverFactory {
    public override Microsoft.Boogie.ProverInterface SpawnProver(Microsoft.Boogie.SMTLibOptions libOptions,
      Microsoft.Boogie.ProverOptions options, object ctxt) => throw new InvalidOperationException("Memory tests must not spawn a prover.");

    public override Microsoft.Boogie.ProverContext NewProverContext(Microsoft.Boogie.ProverOptions options) =>
      throw new InvalidOperationException("Memory tests must not create a prover context.");
  }

  private static async Task<Program> ParseMemory(IReadOnlyList<ContractSource> sources) {
    var reporter = new BatchErrorReporter(MemoryOptions());
    var parsed = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return parsed;
  }

  private static Method MethodNamed(Program program, string name) =>
    Assert.Single(ContractRuntimeObligationTransformer.Members(program).OfType<Method>().Where(method => method.Name == name));

  private static List<(Formal Output, LocalVariable Local, SingleAssignStmt Assignment)> OutputCaptures(Method method) {
    List<(Formal Output, LocalVariable Local, SingleAssignStmt Assignment)> captures = [];
    foreach (var assignment in method.Body!.Descendants().OfType<SingleAssignStmt>().Distinct()) {
      if (assignment.Lhs.Resolved is IdentifierExpr { Var: LocalVariable local } &&
          assignment.Rhs is ExprRhs { Expr.Resolved: IdentifierExpr { Var: Formal formal } } && method.Outs.Contains(formal)) {
        captures.Add((formal, local, assignment));
      }
    }
    return captures;
  }

  private static IEnumerable<IdentifierExpr> Identifiers(Expression expression) {
    expression = expression.Resolved;
    if (expression is IdentifierExpr identifier) { yield return identifier; }
    foreach (var child in expression.SubExpressions) {
      foreach (var descendant in Identifiers(child)) { yield return descendant; }
    }
  }

  private static FunctionCallExpr RuntimeCheck(Method method, ContractRuntimeClause clause) =>
    Assert.Single(method.Body!.Descendants().OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name == "Check" && call.Args[0].Resolved is StringLiteralExpr literal &&
      Equals(literal.Value, clause.Obligation.Id)));

  private static Expression RuntimeProperty(FunctionCallExpr check) {
    var evaluated = Assert.IsType<FunctionCallExpr>(check.Args[2].Resolved);
    Assert.Equal("Evaluated", evaluated.Function.Name);
    var guarded = Assert.IsType<BinaryExpr>(Assert.Single(evaluated.Args).Resolved);
    Assert.Equal(BinaryExpr.Opcode.And, guarded.Op);
    return guarded.E1.Resolved;
  }

  private static async Task<ContractRuntimeTransformation> Transform(string text,
    string generator = "method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }") {
    var options = MemoryOptions();
    // The transformer builds the harness main around the generator that the runner always inserts.
    var source = "module M { import PbtRandom " + text + " " + generator + " }";
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] sources = [new("M.dfy", source, ContractHarnessBuilder.Hash(source)), new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))];
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(m => m.Message)));
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
  }

}
