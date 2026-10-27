using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
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

  // Removing a proof call from a reachable ghost function also removes its statement-expression separator.
  [Fact]
  public async Task ProofCallStatementExpressionConsumesSeparator() {
    const string declarations = "lemma Proof(x:int) {} ghost function Id(x:int):int { Proof(x); x } " +
      "method Goal(x:int) ensures Id(x)==x {}";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var id = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>()
      .Where(function => function.Name == "Id"));
    Assert.False(id.IsGhost);
    Assert.Equal("x", Assert.IsType<IdentifierExpr>(id.Body!.Resolved).Name);
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
  }

  // A proof-call separator inside one conditional branch disappears without changing its sibling branch.
  [Fact]
  public async Task NestedProofCallStatementExpressionPreservesBranch() {
    const string declarations = "lemma Proof(x:int) {} ghost function Select(x:int):int { " +
      "if x>=0 then (Proof(x); x) else x } method Goal(x:int) ensures Select(x)==x {}";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var select = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>()
      .Where(function => function.Name == "Select"));
    Assert.False(select.IsGhost);
    var branch = Assert.IsType<ITEExpr>(select.Body!.Resolved);
    Assert.IsType<IdentifierExpr>(branch.Thn.Resolved);
    Assert.IsType<IdentifierExpr>(branch.Els.Resolved);
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
  }

  // Adjacent proof calls lose both separators while preserving the final expression.
  [Fact]
  public async Task AdjacentProofCallStatementExpressionsConsumeSeparators() {
    const string declarations = "lemma First(x:int) {} lemma Second(x:int) {} " +
      "ghost function Id(x:int):int { First(x); Second(x); x } method Goal(x:int) ensures Id(x)==x {}";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var id = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>()
      .Where(function => function.Name == "Id"));
    Assert.False(id.IsGhost);
    Assert.Equal("x", Assert.IsType<IdentifierExpr>(id.Body!.Resolved).Name);
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
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

  // A fixed-heap postcondition uses entry and return heaps without executing its speculative old-value read.
  [Fact]
  public async Task HeapPostconditionDiscardsOldCapture() {
    var result = await Transform("class Cell { var value:int } " +
      "twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value) } " +
      "method Goal(cell:Cell) modifies cell " +
      "ensures Changed(cell) && cell.value == old(cell.value) { cell.value:=cell.value; }",
      "method Generate(r:PbtRandom.Source) returns (cell:Cell) { cell:=new Cell; cell.value:=0; }");
    var clause = Assert.Single(result.Clauses.Where(item =>
      item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition && !item.TypeConstraint));
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, clause.Obligation.DecisionMethod);
    Assert.Equal(0, clause.EntryHeapPostcondition);
    Assert.Contains(clause.Expression.DescendantsAndSelf, node => node is OldExpr);
    Assert.DoesNotContain(clause.Variables, variable => variable.Name.StartsWith("pbtOld", StringComparison.Ordinal));

    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    Assert.DoesNotContain(wrapper.Body!.Descendants().OfType<SingleAssignStmt>(), assignment =>
      assignment.Lhs.Resolved is IdentifierExpr { Var: LocalVariable local } &&
      local.Name.StartsWith("pbtOld", StringComparison.Ordinal));
    var heapCaptures = wrapper.Body.Descendants().OfType<CallStmt>().Distinct()
      .Where(call => call.Method.Name == "CaptureHeap").OrderBy(call => call.Origin.pos);
    Assert.Equal(new[] { "entry", "return" }, heapCaptures.Select(call =>
      Assert.IsType<StringLiteralExpr>(call.Args[0].Resolved).Value?.ToString()));
  }

  // An unchecked old expression neither reads its value nor renders the checked function nested inside it.
  [Fact]
  public async Task UncheckedPostconditionDiscardsOldCaptureSideEffects() {
    var result = await Transform("class Cell { var value:int } " +
      "function Read(cell:Cell):int reads cell ensures Read(cell)==cell.value { cell.value } " +
      "method Goal(cell:Cell) ensures fresh(cell) && old(Read(cell)) == 0 {}",
      "method Generate(r:PbtRandom.Source) returns (cell:Cell) { cell:=new Cell; cell.value:=0; }");
    var clause = Assert.Single(result.Clauses.Where(item =>
      item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition && !item.TypeConstraint));
    Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, clause.Obligation.DecisionMethod);
    Assert.Contains(clause.Expression.DescendantsAndSelf, node => node is OldExpr);
    Assert.DoesNotContain(clause.Variables, variable => variable.Name.StartsWith("pbtOld", StringComparison.Ordinal));

    var parsed = await ParseMemory(result.Sources);
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    Assert.DoesNotContain(members.OfType<Function>(), function =>
      function.Name.StartsWith("Read__pbt_spec_", StringComparison.Ordinal));
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    Assert.DoesNotContain(wrapper.Body!.Descendants().OfType<SingleAssignStmt>(), assignment =>
      assignment.Lhs.Resolved is IdentifierExpr { Var: LocalVariable local } &&
      local.Name.StartsWith("pbtOld", StringComparison.Ordinal));
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

  // A scalar closed-query downgrade retains old evidence after validating the non-null input.
  [Fact]
  public async Task ScalarClosedDowngradeRetainsOrderedOldCapture() {
    const string declarations = "class Cell { var value:int } " +
      "method Goal(cell:Cell) returns (x:int) modifies cell ensures x == old(cell.value) " +
      "{ x:=cell.value; cell.value:=cell.value+1; }";
    const string generator =
      "method Generate(r:PbtRandom.Source) returns (cell:Cell) { cell:=new Cell; cell.value:=0; }";
    var initial = await Transform(declarations, generator);
    var initialClause = Assert.Single(initial.Clauses.Where(item =>
      item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition && !item.TypeConstraint));
    var caps = new Dictionary<string, ContractRuntimeDecisionMethod> {
      [ContractRuntimeObligationTransformer.IdPrefix(initialClause.Obligation.Id)] =
        ContractRuntimeDecisionMethod.ClosedSmt
    };

    var result = await Transform(declarations, generator, caps);
    var clause = Assert.Single(result.Clauses.Where(item =>
      item.Obligation.Kind == ContractRuntimeObligationKind.Postcondition && !item.TypeConstraint));
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, clause.Obligation.DecisionMethod);
    Assert.Null(clause.EntryHeapPostcondition);

    var parsed = await ParseMemory(result.Sources);
    var wrapper = MethodNamed(parsed, "Goal__pbt_goal");
    var inputClause = Assert.Single(result.Clauses.Where(item => item.TypeConstraint &&
      item.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition));
    var inputCheck = RuntimeCheck(wrapper, inputClause);
    var oldCapture = Assert.Single(wrapper.Body!.Descendants().OfType<SingleAssignStmt>().Distinct().Where(assignment =>
      assignment.Lhs.Resolved is IdentifierExpr { Var: LocalVariable local } &&
      local.Name.StartsWith("pbtOld", StringComparison.Ordinal)));
    var oldLocal = Assert.IsType<LocalVariable>(Assert.IsAssignableFrom<IdentifierExpr>(oldCapture.Lhs.Resolved).Var);
    var oldExpression = Assert.Single(result.Prepared.Method.Ens.Single().E.DescendantsAndSelf.OfType<OldExpr>());
    var captureLocation = wrapper.Body.Descendants().OfType<FunctionCallExpr>().Distinct()
      .Where(call => call.Function.Name == "Location" && call.Origin.pos < oldCapture.Origin.pos)
      .MaxBy(call => call.Origin.pos)!;
    var locationText = Assert.IsType<StringLiteralExpr>(captureLocation.Args.Single().Resolved).Value?.ToString();
    var invocation = Assert.Single(wrapper.Body.Descendants().OfType<CallStmt>().Distinct().Where(call =>
      call.Method.Name == "Goal"));
    var checkpoint = Assert.Single(wrapper.Body.Descendants().OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name == "Checkpoint" && call.Args[0].Resolved is StringLiteralExpr literal &&
      Equals(literal.Value, clause.Obligation.Id)));
    Assert.True(inputCheck.Origin.pos < oldCapture.Origin.pos);
    Assert.True(inputCheck.Origin.pos < captureLocation.Origin.pos);
    Assert.NotNull(locationText);
    Assert.EndsWith(":" + oldExpression.Origin.line + ":" + oldExpression.Origin.col, locationText);
    Assert.True(oldCapture.Origin.pos < invocation.Origin.pos);
    Assert.Contains(checkpoint.Args.SelectMany(Identifiers), identifier => identifier.Var == oldLocal);
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

  // Erasing an unreachable method body discards shape insertions for generic calls that disappear with it.
  [Fact]
  public async Task ErasedMethodBodyDropsNestedGenericShapeInsertion() {
    const string declarations = "method Relay<T>(x:T) returns (y:T) { y:=x; } " +
      "method Unused() { var y:=Relay<int>(0); } " +
      "method Goal(x:int) returns (y:int) { y:=Relay<int>(x); }";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var unused = MethodNamed(parsed, "Unused");
    Assert.Contains(unused.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.DoesNotContain(unused.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "Relay");
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
  }

  // Erasing an unreachable function body discards shape insertions for generic calls that disappear with it.
  [Fact]
  public async Task ErasedFunctionBodyDropsNestedGenericShapeInsertion() {
    const string declarations = "function Id<T>(x:T):T { x } " +
      "function Unused():int { Id<int>(0) } " +
      "method Goal(x:int) returns (y:int) { y:=Id<int>(x); }";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var unused = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>()
      .Where(function => function.Name == "Unused"));
    var trap = Assert.IsType<FunctionCallExpr>(unused.Body!.Resolved);
    Assert.Equal("UnreachableValue", trap.Function.Name);
    Assert.DoesNotContain(unused.Body.DescendantsAndSelf.OfType<FunctionCallExpr>(), call => call.Function.Name == "Id");
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
  }

  // Erasing an unreachable body preserves the shape argument required by its retained generic contract call.
  [Fact]
  public async Task ErasedBodyRetainsGenericShapeInsertionInContract() {
    const string declarations = "function Id<T>(x:T):T { x } " +
      "method Unused(x:int) requires Id<int>(x)==x { var y:=Id<int>(x); } " +
      "method Goal(x:int) returns (y:int) { y:=Id<int>(x); }";
    var result = await Transform(declarations);

    var parsed = await ParseMemory(result.Sources);
    var unused = MethodNamed(parsed, "Unused");
    var contractCall = Assert.Single(unused.Req.Single().E.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .Where(call => call.Function.Name == "Id"));
    Assert.Equal(2, contractCall.Args.Count);
    Assert.IsType<StringLiteralExpr>(contractCall.Args[0].Resolved);
    Assert.Contains(unused.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.DoesNotContain(unused.Body.Descendants().OfType<FunctionCallExpr>(), call => call.Function.Name == "Id");
    var original = Assert.Single(result.Prepared.Sources!, source => source.Path == "M.dfy");
    var expected = "module M { import PbtRandom " + declarations +
      " method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; } }";
    Assert.Equal(expected, original.Content);
    Assert.Equal(ContractHarnessBuilder.Hash(expected), original.Sha256);
  }

  // An instance method wrapper retains its lexical default and forwards each evaluated input once by name.
  [Fact]
  public async Task MethodWrapperPreservesDefaultBindings() {
    var result = await Transform("module Lib { function Seed(x:int):int ensures Seed(x)==x { x } } " +
      "import L = Lib function Input(x:int):int { x } class Box { " +
      "function Local(x:int):int ensures Local(x)==x { x } " +
      "method Step<T>(a:int, nameonly b:int := this.Local(a)+L.Seed(a)) requires b>=a {} } " +
      "method Goal(box:Box,x:int) { box.Step<bool>(a := Input(x)); }",
      "method Generate(r:PbtRandom.Source) returns (box:Box,x:int) { box:=new Box; x:=0; }");
    Assert.Contains(result.Clauses, clause => clause.Owner.Name == "Local" &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);
    Assert.Contains(result.Clauses, clause => clause.Owner.Name == "Seed" &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);

    var parsed = await ParseMemory(result.Sources);
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    var wrapper = Assert.Single(members.OfType<Method>().Where(method =>
      method.Name.StartsWith("Step__pbt_site_", StringComparison.Ordinal)));
    var earlier = Assert.Single(wrapper.Ins.Where(formal => formal.Name == "a"));
    var defaultValue = Assert.Single(wrapper.Ins.Where(formal => formal.Name == "b")).DefaultValue;
    Assert.NotNull(defaultValue);
    Assert.True(wrapper.Ins.Single(formal => formal.Name == "b").IsNameOnly);
    Assert.Contains(Identifiers(defaultValue!), identifier => identifier.Var == earlier);
    var defaultCalls = defaultValue!.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct().ToList();
    var local = Assert.Single(defaultCalls.Where(call => call.Function.Name.StartsWith("Local__pbt_spec_", StringComparison.Ordinal)));
    Assert.IsType<ThisExpr>(local.Receiver.Resolved);
    var seed = Assert.Single(defaultCalls.Where(call => call.Function.Name.StartsWith("Seed__pbt_spec_", StringComparison.Ordinal)));
    Assert.Equal("Lib", seed.Function.EnclosingClass.EnclosingModuleDefinition.Name);

    var goal = MethodNamed(parsed, "Goal");
    var sourceCall = Assert.Single(goal.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method == wrapper));
    Assert.Equal(2, sourceCall.Bindings.ArgumentBindings.Count);
    Assert.Null(sourceCall.Bindings.ArgumentBindings[0].FormalParameterName);
    Assert.Equal("a", sourceCall.Bindings.ArgumentBindings[1].FormalParameterName!.val);
    Assert.Single(sourceCall.Bindings.ArgumentBindings[1].Actual.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .Where(call => call.Function.Name == "Input"));

    var forwarded = Assert.Single(wrapper.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "Step"));
    Assert.Equal(new[] { null, "a", "b" }, forwarded.Bindings.ArgumentBindings
      .Select(binding => binding.FormalParameterName?.val).ToArray());
    Assert.All(forwarded.Bindings.ArgumentBindings.Skip(1), binding =>
      Assert.Equal(binding.FormalParameterName!.val, Assert.IsType<IdentifierExpr>(binding.Actual.Resolved).Name));
    Assert.Single(forwarded.MethodSelect.TypeApplicationJustMember);
  }

  // A function wrapper keeps a nested omission so its checked callee evaluates dependent defaults without duplicating actuals.
  [Fact]
  public async Task FunctionWrapperPreservesNestedDefaultBindings() {
    var result = await Transform("function Input(x:int):int { x } " +
      "function Inner(x:int,y:int:=x):int requires x>=0 ensures Inner(x,y)==x+y { x+y } " +
      "function Pick<T>(a:int,nameonly b:int:=Inner(Input(a))):int requires a>=0 { b } " +
      "method Goal(x:int) { var y:=Pick<bool>(a:=x); }");
    Assert.Contains(result.Clauses, clause => clause.Owner.Name == "Inner" &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);

    var parsed = await ParseMemory(result.Sources);
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    var wrapper = Assert.Single(members.OfType<Function>().Where(function =>
      function.Name.StartsWith("Pick__pbt_site_", StringComparison.Ordinal)));
    var defaultValue = Assert.Single(wrapper.Ins.Where(formal => formal.Name == "b")).DefaultValue;
    Assert.NotNull(defaultValue);
    Assert.True(wrapper.Ins.Single(formal => formal.Name == "b").IsNameOnly);
    var inner = Assert.Single(defaultValue!.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name.StartsWith("Inner__pbt_spec_", StringComparison.Ordinal)));
    Assert.Single(inner.Bindings.ArgumentBindings);
    Assert.Equal(2, inner.Args.Count);
    Assert.NotNull(inner.Function.Ins.Single(formal => formal.Name == "y").DefaultValue);
    Assert.Single(inner.Bindings.ArgumentBindings[0].Actual.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .Where(call => call.Function.Name == "Input"));

    var forwarded = Assert.Single(wrapper.Body!.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name == "Pick"));
    Assert.Equal(new[] { null, "a", "b" }, forwarded.Bindings.ArgumentBindings
      .Select(binding => binding.FormalParameterName?.val).ToArray());
    Assert.All(forwarded.Bindings.ArgumentBindings.Skip(1), binding =>
      Assert.Equal(binding.FormalParameterName!.val, Assert.IsType<IdentifierExpr>(binding.Actual.Resolved).Name));
    Assert.Single(forwarded.TypeApplication_JustFunction);
  }

  // Repeated omissions share the declaration default's checked callee without competing source replacements.
  [Fact]
  public async Task RepeatedOmittedDefaultsInstrumentAuthoredExpressionOnce() {
    var result = await Transform("function Inner(x:int):int requires x>=0 ensures Inner(x)==x { x } " +
      "function Pick(x:int:=Inner(0)):int { x } " +
      "method Goal() { var first:=Pick(); var second:=Pick(); }",
      "method Generate(r:PbtRandom.Source) {}");
    Assert.Contains(result.Clauses, clause => clause.Owner.Name == "Inner" &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);

    var parsed = await ParseMemory(result.Sources);
    var functions = ContractRuntimeObligationTransformer.Members(parsed).OfType<Function>().ToList();
    var innerWrapper = Assert.Single(functions.Where(function =>
      function.Name.StartsWith("Inner__pbt_spec_", StringComparison.Ordinal)));
    Assert.DoesNotContain(functions, function =>
      function.Name.StartsWith("Pick__pbt_site_", StringComparison.Ordinal));
    Assert.DoesNotContain(functions, function =>
      function.Name.StartsWith("Inner__pbt_site_", StringComparison.Ordinal));
    var pick = Assert.Single(functions.Where(function => function.Name == "Pick"));
    var defaultValue = Assert.Single(pick.Ins.Where(formal => formal.Name == "x")).DefaultValue;
    var innerCall = Assert.Single(defaultValue!.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct());
    Assert.Same(innerWrapper, innerCall.Function);
    Assert.Single(innerCall.Bindings.ArgumentBindings);
    var goal = MethodNamed(parsed, "Goal");
    var calls = goal.Body!.Descendants().OfType<FunctionCallExpr>().Distinct().Where(call => call.Function == pick).ToList();
    Assert.Equal(2, calls.Count);
    Assert.All(calls, call => Assert.Empty(call.Bindings.ArgumentBindings));
  }

  // A datatype constructor in a wrapper default keeps its named actual and dependent nameonly omission.
  [Fact]
  public async Task WrapperDefaultPreservesDatatypeBindings() {
    var result = await Transform("datatype Pair = Pair(x:int,nameonly y:int:=x) " +
      "function Input(x:int):int { x } " +
      "method Step(a:int,p:Pair:=Pair(x:=Input(a))) requires p.x>=a {} " +
      "method Goal(x:int) { Step(x); }");

    var parsed = await ParseMemory(result.Sources);
    var wrapper = Assert.Single(ContractRuntimeObligationTransformer.Members(parsed).OfType<Method>().Where(method =>
      method.Name.StartsWith("Step__pbt_site_", StringComparison.Ordinal)));
    var defaultValue = Assert.Single(wrapper.Ins.Where(formal => formal.Name == "p")).DefaultValue;
    var pair = Assert.IsType<DatatypeValue>(defaultValue!.Resolved);
    var written = Assert.Single(pair.Bindings.ArgumentBindings);
    Assert.Equal("x", written.FormalParameterName!.val);
    Assert.Equal(2, pair.Arguments.Count);
    Assert.True(pair.Ctor!.Formals.Single(formal => formal.Name == "y").IsNameOnly);
    Assert.Single(written.Actual.DescendantsAndSelf.OfType<FunctionCallExpr>().Where(call => call.Function.Name == "Input"));
  }

  // A reached constructor default keeps its dependent argument and instruments one concrete generic checked call.
  [Fact]
  public async Task DatatypeDefaultInstrumentsCheckedGenericCall() {
    var result = await Transform("function Checked<T>(x:int):int requires x>=0 ensures Checked<T>(x)==x { x } " +
      "datatype Pair = Pair(x:int,nameonly y:int:=Checked<int>(x)) " +
      "function Other(x:int):int requires x>=0 ensures Other(x)==x { x } " +
      "datatype Spare = Spare(x:int,nameonly y:int:=Other(x)) " +
      "function Input(x:int):int { x } " +
      "method Step(a:int,p:Pair:=Pair(x:=Input(a))) requires p.x>=a {} " +
      "method Goal(x:int) { Step(x); }");
    Assert.Contains(result.Clauses, clause => clause.Owner.Name == "Checked" &&
      clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);

    var parsed = await ParseMemory(result.Sources);
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    var checkedWrapper = Assert.Single(members.OfType<Function>().Where(function =>
      function.Name.StartsWith("Checked__pbt_spec_", StringComparison.Ordinal)));
    Assert.DoesNotContain(members.OfType<Function>(), function =>
      function.Name.StartsWith("Other__pbt_spec_", StringComparison.Ordinal));
    var pair = Assert.Single(parsed.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<DatatypeDecl>().Where(datatype => datatype.Name == "Pair"));
    var constructor = Assert.Single(pair.Ctors);
    var defaultValue = Assert.Single(constructor.Formals.Where(formal => formal.Name == "y")).DefaultValue;
    var checkedCall = Assert.Single(defaultValue!.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct());
    Assert.Same(checkedWrapper, checkedCall.Function);
    Assert.Equal(2, checkedCall.Bindings.ArgumentBindings.Count);
    Assert.IsType<StringLiteralExpr>(checkedCall.Bindings.ArgumentBindings[0].Actual.Resolved);
    Assert.Equal("x", Assert.IsType<IdentifierExpr>(checkedCall.Bindings.ArgumentBindings[1].Actual.Resolved).Name);

    var stepWrapper = Assert.Single(members.OfType<Method>().Where(method =>
      method.Name.StartsWith("Step__pbt_site_", StringComparison.Ordinal)));
    var wrapperDefault = Assert.Single(stepWrapper.Ins.Where(formal => formal.Name == "p")).DefaultValue;
    var constructed = Assert.IsType<DatatypeValue>(wrapperDefault!.Resolved);
    var written = Assert.Single(constructed.Bindings.ArgumentBindings);
    Assert.Equal("x", written.FormalParameterName!.val);
    Assert.Single(written.Actual.DescendantsAndSelf.OfType<FunctionCallExpr>().Distinct().Where(call =>
      call.Function.Name == "Input"));
  }

  // Generic method and function calls with no written actuals receive a shape without a dangling comma.
  [Fact]
  public async Task GenericDefaultCallsInsertOnlyShapeArguments() {
    var result = await Transform("method UseM<T>(x:int:=1) requires x>=0 {} " +
      "function UseF<T>(x:int:=1):int requires x>=0 { x } " +
      "method Goal() { UseM<bool>(); var y:=UseF<bool>(); }",
      "method Generate(r:PbtRandom.Source) {}");

    var parsed = await ParseMemory(result.Sources);
    var members = ContractRuntimeObligationTransformer.Members(parsed).ToList();
    var goal = MethodNamed(parsed, "Goal");
    var methodWrapper = Assert.Single(members.OfType<Method>().Where(method =>
      method.Name.StartsWith("UseM__pbt_site_", StringComparison.Ordinal)));
    var functionWrapper = Assert.Single(members.OfType<Function>().Where(function =>
      function.Name.StartsWith("UseF__pbt_site_", StringComparison.Ordinal)));
    var methodCall = Assert.Single(goal.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method == methodWrapper));
    var functionCall = Assert.Single(goal.Body.Descendants().OfType<FunctionCallExpr>().Distinct().Where(call => call.Function == functionWrapper));
    Assert.Single(methodCall.Bindings.ArgumentBindings);
    Assert.Single(functionCall.Bindings.ArgumentBindings);
    Assert.Null(methodCall.Bindings.ArgumentBindings[0].FormalParameterName);
    Assert.Null(functionCall.Bindings.ArgumentBindings[0].FormalParameterName);
    Assert.NotNull(methodWrapper.Ins.Single(formal => formal.Name == "x").DefaultValue);
    Assert.NotNull(functionWrapper.Ins.Single(formal => formal.Name == "x").DefaultValue);
  }

  // Equal-offset insertions retain the reverse application order around both replacement boundaries.
  [Fact]
  public void SourceEditsPreserveEqualOffsetAndBoundaryOrder() {
    var result = ApplySourceEdits("abcdef",
      (2, 0, "first"),
      (2, 0, "second"),
      (2, 2, "replacement"),
      (4, 0, "after"));

    Assert.Equal("absecondfirstreplacementafteref", result.Content);
  }

  // UTF-8 byte offsets select complete multibyte characters without shifting a following boundary insertion.
  [Fact]
  public void SourceEditsUseUtf8ByteOffsets() {
    var alphaBytes = Encoding.UTF8.GetByteCount("α");
    var betaBytes = Encoding.UTF8.GetByteCount("β");
    var result = ApplySourceEdits("αβγ",
      (alphaBytes, betaBytes, "中"),
      (alphaBytes + betaBytes, 0, "!"));

    Assert.Equal("α中!γ", result.Content);
  }

  // A source with no edits retains every original UTF-16 code unit, including an unpaired surrogate.
  [Fact]
  public void SourceEditsPreserveUnpairedSurrogateWithoutEdits() {
    const string content = "\uD800abc";

    var result = ApplySourceEdits(content);

    Assert.Equal(content, result.Content);
  }

  // A partial UTF-8 byte offset maps through the legacy prefix character count before insertion.
  [Fact]
  public void SourceEditsPreservePartialByteOffsetMapping() {
    var result = ApplySourceEdits("éZ", (1, 0, "!"));

    Assert.Equal("é!Z", result.Content);
  }

  // An empty outer removal absorbs its nested removal and strict-interior insertion while retaining boundary insertions.
  [Fact]
  public void SourceEditsPreserveNestedRemovalContainment() {
    var result = ApplySourceEdits("0123456789",
      (2, 6, ""),
      (3, 2, ""),
      (4, 0, "discarded"),
      (2, 0, "before"),
      (8, 0, "after"));

    Assert.Equal("01beforeafter89", result.Content);
  }

  // A nonempty replacement absorbs an insertion in its strict interior.
  [Fact]
  public void SourceEditsDiscardInsertionInsideReplacement() {
    var result = ApplySourceEdits("abcdef", (1, 3, "replacement"), (2, 0, "discarded"));

    Assert.Equal("areplacementef", result.Content);
  }

  // Overlapping nonempty replacements remain an explicit transformation error.
  [Fact]
  public void SourceEditsRejectOverlappingReplacements() {
    var error = Assert.Throws<NotSupportedException>(() =>
      ApplySourceEdits("abcdef", (1, 3, "left"), (3, 2, "right")));

    Assert.StartsWith("Overlapping diagnostic source replacements are not supported.", error.Message);
  }

  // Clause text and transformed syntax retain exact locations after multibyte source content.
  [Fact]
  public async Task TransformationSlicesTextAfterUtf8Content() {
    var result = await Transform("/* 한글 */ method Goal(x:int) ensures x == x {}");

    Assert.Equal("x == x", Assert.Single(result.Clauses).Obligation.Clause);
    await ParseMemory(result.Sources);
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

  private static ContractSource ApplySourceEdits(string content, params (int Start, int Length, string Text)[] changes) {
    var source = new ContractSource("Edit.dfy", content, ContractHarnessBuilder.Hash(content));
    var uri = ContractSourceSnapshot.UriFor(source.Path);
    var edits = changes.Select(change =>
      new ContractRuntimeObligationTransformer.Edit(uri, change.Start, change.Length, change.Text)).ToList();
    var result = Assert.Single(ContractRuntimeObligationTransformer.Apply([source], edits));
    Assert.Equal(ContractHarnessBuilder.Hash(result.Content), result.Sha256);
    return result;
  }

  private static async Task<ContractRuntimeTransformation> Transform(string text,
    string generator = "method Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }",
    IReadOnlyDictionary<string, ContractRuntimeDecisionMethod>? decisionCaps = null) {
    var options = MemoryOptions();
    // The transformer builds the harness main around the generator that the runner always inserts.
    var source = "module M { import PbtRandom " + text + " " + generator + " }";
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] sources = [new("M.dfy", source, ContractHarnessBuilder.Hash(source)), new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))];
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(m => m.Message)));
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal, decisionCaps: decisionCaps).Transform();
  }

}
