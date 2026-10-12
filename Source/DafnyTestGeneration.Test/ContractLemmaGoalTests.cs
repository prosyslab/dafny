using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractLemmaGoalTests {
  // Ordinary lemmas require explicit contract-only selection and remain unavailable as executable targets.
  [Fact]
  public async Task RequiresContractSelection() {
    var (program, _) = await Parse("module M { lemma Goal(x: int) ensures x == 0 {} }");
    Assert.Throws<NotSupportedException>(() => ContractCallableSelector.SelectMethod(program, new("M.Goal")));
    Assert.IsType<Lemma>(ContractCallableSelector.SelectMethod(program, new("M.Goal"), allowLemmaContract: true));
  }

  // Recursive value datatypes and their concrete sequence inputs can be sampled for lemma contracts.
  [Fact]
  public async Task AcceptsRecursiveValueInputs() {
    var (program, _) = await Parse("module M { datatype Tree = Leaf | Branch(value: int, children: seq<Tree>) " +
      "lemma Goal(trees: seq<Tree>) ensures |trees| == 0 {} }");
    Assert.IsType<Lemma>(ContractCallableSelector.SelectMethod(program, new("M.Goal"), allowLemmaContract: true));
  }

  // Ghost execution, output witnesses, state, type parameters and target trust directives remain outside this slice.
  [Theory]
  [InlineData("ghost method Goal(x: int) ensures x == 0 {}", "M.Goal")]
  [InlineData("lemma Goal(x: int) returns (y: int) ensures y == x {}", "M.Goal")]
  [InlineData("lemma Goal<T>(x: T) {}", "M.Goal")]
  [InlineData("twostate lemma Goal(x: int) {}", "M.Goal")]
  [InlineData("least lemma Goal(x: int) {}", "M.Goal")]
  [InlineData("class C { lemma Goal(x: int) {} }", "M.C.Goal")]
  [InlineData("class C {} lemma Goal(x: C) {}", "M.Goal")]
  [InlineData("class C {} datatype Box = Box(value: C) lemma Goal(x: seq<Box>) {}", "M.Goal")]
  [InlineData("lemma {:axiom} Goal(x: int) ensures false", "M.Goal")]
  [InlineData("lemma {:extern} Goal(x: int) ensures false", "M.Goal")]
  [InlineData("lemma {:only} Goal(x: int) {}", "M.Goal")]
  [InlineData("lemma Goal(x: int) ensures old(x) == x {}", "M.Goal")]
  public async Task RejectsUnsupportedTargets(string declaration, string symbol) {
    var (program, _) = await Parse("module M { " + declaration + " }");
    Assert.Throws<NotSupportedException>(() => ContractCallableSelector.SelectMethod(program, new(symbol), allowLemmaContract: true));
  }

  // Verification skips on the target or either containing owner cannot enter contract-only lemma checking.
  [Theory]
  [InlineData("module M { lemma {:verify false} Goal(x: int) ensures x == 0 {} }", "M.Goal")]
  [InlineData("module M { class {:verify false} C { static lemma Goal(x: int) ensures x == 0 {} } }", "M.C.Goal")]
  [InlineData("module {:verify false} M { lemma Goal(x: int) ensures x == 0 {} }", "M.Goal")]
  [InlineData("module {:verify false} Outer { module M { lemma Goal(x: int) ensures x == 0 {} } }", "Outer.M.Goal")]
  public async Task RejectsSkippedVerificationOwners(string source, string symbol) {
    var (program, _) = await Parse(source);
    Assert.Throws<NotSupportedException>(() => ContractCallableSelector.SelectMethod(program, new(symbol), allowLemmaContract: true));
  }

  // Initial-state preparation preserves lemma input typing while observed execution still rejects erased proofs.
  [Fact]
  public async Task OnlyInitialPreparationAcceptsLemma() {
    var (program, sources) = await Parse("module M { lemma Goal(x: nat) requires x > 0 ensures x == 0 {} }");
    var request = new ContractTestRequest(1, sources, new("M.Goal"),
      new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "1") });
    Assert.IsType<Lemma>(ContractHarnessBuilder.PrepareInitial(program, request).Method);
    Assert.Throws<NotSupportedException>(() => ContractHarnessBuilder.PrepareObservedHeap(program, request));
  }

  // Execution type scopes retain erased proof calls in subset/newtype constraints and witnesses.
  [Theory]
  [InlineData("lemma Proof() ensures false", "type Admitted = value: int | (Proof(); value >= 0) witness 0")]
  [InlineData("lemma Proof() ensures false { assume false; }", "type Admitted = value: int | (Proof(); value >= 0) witness 0")]
  [InlineData("lemma Proof() ensures false", "newtype Admitted = value: int | (Proof(); value >= 0) witness 0")]
  [InlineData("lemma Proof() ensures false { assume false; }", "newtype Admitted = value: int | (Proof(); value >= 0) witness 0")]
  [InlineData("lemma Proof() ensures false", "type Admitted = value: int | value >= 0 ghost witness (Proof(); 0)")]
  [InlineData("lemma Proof() ensures false { assume false; }", "newtype Admitted = value: int | value >= 0 ghost witness (Proof(); 0)")]
  public async Task TracksRefinementProofDependencies(string proofDeclaration, string typeDeclaration) {
    var (program, sources) = await Parse("module M { " + proofDeclaration + " " + typeDeclaration +
      " lemma Goal(x: Admitted) ensures false {} }");
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), allowLemmaContract: true);
    var proof = ContractRuntimeObligationTransformer.Members(program).OfType<Method>().Single(method => method.Name == "Proof");
    var checker = new ContractSpecificationChecker(program, sources, program.Options);
    var scope = checker.Scope([], goal.Ins.Select(formal => formal.Type));
    Assert.True(scope.ContainsDeclaration(proof));
    Assert.NotNull(scope.Failure);
    Assert.False(checker.Accept(scope));
  }

  // A global refinement proof invoking the target cannot certify the lemma's initial state.
  [Fact]
  public async Task RejectsTargetDependentGlobalTypeScope() {
    var (program, sources) = await Parse("module M { lemma Goal() ensures true {} " +
      "type Admitted = value: int | (Goal(); value >= 0) witness 0 const Initial: Admitted := 0 }");
    var checker = new ContractSpecificationChecker(program, sources, program.Options);
    var request = new ContractRuntimeCampaignRequest(2, sources, new("M.Goal"), "17");
    var scope = ContractInitialTypeProof.RequiredScope(program, request, [], checker);
    Assert.Equal("target_lemma_dependency", scope.Failure);
    Assert.False(checker.Accept(scope));
  }

  // Scope exclusion compares original declaration identity rather than accepting detached declarations with the same name.
  [Fact]
  public async Task ScopeMembershipUsesDeclarationIdentity() {
    const string text = "module M { lemma Goal() ensures true {} }";
    var (program, sources) = await Parse(text);
    var (detached, _) = await Parse(text);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), allowLemmaContract: true);
    var copy = ContractCallableSelector.SelectMethod(detached, new("M.Goal"), allowLemmaContract: true);
    var checker = new ContractSpecificationChecker(program, sources, program.Options);
    var scope = checker.LogicalScope([goal]);
    Assert.True(scope.ContainsDeclaration(goal));
    Assert.False(scope.ContainsDeclaration(copy));
  }

  // Contract checkpoints compile without a call to the lemma or obligations from its proof body.
  [Fact]
  public async Task CompilesOnlyContractCheckpoints() {
    const string source = "module M { import PbtRandom lemma Missing() " +
      "lemma Goal(x: int) requires x > 0 ensures x == 0 { Missing(); assert false; } " +
      "method Generate(r: PbtRandom.Source) returns (x: int) { x := r.Size(); } }";
    var (program, sources) = await Parse(source, runtime: true);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), allowLemmaContract: true);
    Assert.DoesNotContain(ContractRuntimeObligationTransformer.DiagnosticReachable(program, goal),
      callable => callable.FullDafnyName is "M.Goal" or "M.Missing");
    var transformation = new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
    Assert.Equal(2, transformation.Clauses.Count);
    Assert.All(transformation.Clauses, clause => Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, clause.Obligation.DecisionMethod));
    var reporter = new BatchErrorReporter(program.Options);
    var transformed = await ContractSourceSnapshot.ParseAsync(reporter, transformation.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var wrapper = ContractRuntimeObligationTransformer.Members(transformed).OfType<Method>().Single(method => method.Name == "Goal__pbt_goal");
    Assert.DoesNotContain(wrapper.Body!.Descendants().OfType<CallStmt>(), call => call.Method is Lemma);
    var compiled = ContractRuntimeObligationTransformer.CompiledCheckLiterals(transformed);
    Assert.All(transformation.Clauses, clause => Assert.True(ContractRuntimeObligationTransformer.IsCompiled(compiled, clause.Obligation.Id)));
  }

  // Both closed-query polarities preserve the original proof statement and its bound input as one expression.
  [Theory]
  [InlineData(false, ContractQueryOutcome.Sat)]
  [InlineData(true, ContractQueryOutcome.Unsat)]
  public async Task PreservesStatementExpressionGrouping(bool negate, ContractQueryOutcome expected) {
    var (program, sources) = await Parse("module M { lemma GoodProof(x: nat) ensures x >= 0 {} " +
      "lemma Goal(x: nat) ensures (GoodProof(x); false) { assert false; } }");
    program.Options.TimeLimit = 10;
    var values = new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "7") };
    var request = new ContractTestRequest(1, sources, new("M.Goal"), values);
    var prepared = ContractHarnessBuilder.PrepareInitial(program, request);
    var clause = new ContractRuntimeClause(new ContractRuntimeObligation("lemma-post", ContractRuntimeObligationKind.Postcondition,
      "M.dfy", 1, 1, "original", null, ContractRuntimeDecisionMethod.ClosedSmt, null, new()),
      prepared.Method.Ens[0].E, prepared.Method.Ins.Cast<IVariable>().ToList(), prepared.Method);
    var query = ContractQueryBuilder.BuildClosedClause(prepared, clause, values, negate);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ClosedClause, program.Options, CancellationToken.None,
      queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
    Assert.True(result.Outcome == expected, result.Diagnostics + "\n" + query);
  }

  // Negated quantified predicates retain native proof requirements through direct and transitive logical calls.
  [Theory]
  [InlineData(false, false)]
  [InlineData(true, false)]
  [InlineData(false, true)]
  [InlineData(true, true)]
  public async Task ProvesOnlyFalseQuantifiedPredicates(bool transitive, bool trueConclusion) {
    var predicate = transitive ? "Wrapper" : "Nonzero";
    var source = "module M { datatype Item = Item(value: nat) " +
      "ghost predicate Nonzero(items: seq<Item>) { forall i :: 0 <= i < |items| ==> items[i].value > 0 } " +
      "ghost predicate Wrapper(items: seq<Item>) { Nonzero(items) } " +
      "method ContractDiagnosticQuery(items: seq<Item>) requires items == [Item(" + (trueConclusion ? "1" : "0") +
      ")] { assert {:error \"contract_query_target\"} !(" + predicate + "(items)); } }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None);
    if (trueConclusion) {
      Assert.True(result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Unknown or ContractQueryOutcome.Timeout,
        result.Diagnostics);
    } else {
      Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
    }
  }

  private static async Task<(Program Program, IReadOnlyList<ContractSource> Sources)> Parse(string text, bool runtime = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var sources = new List<ContractSource> { new("M.dfy", text, ContractHarnessBuilder.Hash(text)) };
    if (runtime) {
      var library = ContractRuntimeInstrumentation.DafnySource;
      sources.Add(new("PbtRuntime.dfy", library, ContractHarnessBuilder.Hash(library)));
    }
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (program, sources);
  }
}
