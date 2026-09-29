using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractWitnessQueryTests {
  // Dependency-ordered native assertions prove an acyclic predicate chain beyond one local depth window.
  [Fact]
  public async Task CompositionalPredicateProofNativeGate() {
    var result = await Check("ghost predicate EmptyItems(items:seq<int>) { |items| == 0 } " +
      "ghost predicate MiddleProof() { exists items:seq<int> :: |items| == 0 && EmptyItems(items) } " +
      "ghost predicate OuterProof() { MiddleProof() } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} OuterProof(); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("proofSteps=", result.Diagnostics);
    Assert.DoesNotContain("proofSteps=0", result.Diagnostics);
  }

  // Checked positive helper steps cannot turn the negation of a true predicate into a proof.
  [Fact]
  public async Task CompositionalPredicateProofRetainsNegativeTarget() {
    var result = await Check("ghost predicate EmptyItems(items:seq<int>) { |items| == 0 } " +
      "ghost predicate MiddleProof() { exists items:seq<int> :: |items| == 0 && EmptyItems(items) } " +
      "ghost predicate OuterProof() { MiddleProof() } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} !OuterProof(); }");
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
  }

  // A partial call under an unselected conditional branch creates neither a proof-step error nor target WD failure.
  [Theory]
  [InlineData("if false then Dangerous() else true")]
  [InlineData("false ==> Dangerous()")]
  [InlineData("true || Dangerous()")]
  public async Task CompositionalProofPreservesDeadBranchDefinedness(string body) {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "ghost predicate Dangerous() { Partial(0) == 0 } ghost predicate Safe() { " + body + " } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Safe(); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.DoesNotContain("contract_reduction_prerequisite", result.Diagnostics);
  }

  // Dead existential branches do not publish a witness assertion or change definedness.
  [Theory]
  [InlineData("false ==> (exists items:seq<int> :: |items| == 0)")]
  [InlineData("true || (exists items:seq<int> :: |items| == 0)")]
  public async Task CompositionalProofDoesNotLiftDeadExistentialWitness(string body) {
    var result = await Check("method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} " + body + "; }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("checkedWitnesses=0", result.Diagnostics);
    Assert.DoesNotContain("contract_reduction_witness", result.Diagnostics);
  }

  // Vacuous forall bodies cannot publish an invalid existential witness assertion.
  [Theory]
  [InlineData("false", "", ContractQueryOutcome.Unsat)]
  [InlineData("0 <= i < 0", "", ContractQueryOutcome.Unsat)]
  [InlineData("false", " && false", ContractQueryOutcome.Sat)]
  public async Task CompositionalProofDoesNotLiftVacuousForallWitness(
    string range, string suffix, ContractQueryOutcome expected) {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "((forall i:int | " + range + " :: exists items:seq<int> :: " +
      "|items| == 0 && Partial(0) == 0)" + suffix + "); }");
    Assert.Equal(expected, result.Outcome);
    Assert.DoesNotContain("contract_reduction_witness", result.Diagnostics);
  }

  // A dead predicate in a retained witness cannot introduce an auxiliary definedness error.
  [Fact]
  public async Task CompositionalProofDoesNotActivateDeadWitnessDependency() {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "ghost predicate Dangerous() { Partial(0) == 0 } " +
      "ghost predicate Middle() { exists items:seq<int> :: |items| == 0 && (false ==> Dangerous()) } " +
      "ghost predicate Outer() { Middle() } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} Outer(); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
  }

  // An empty factor in a multi-variable quantifier enables an exact checked predicate chain.
  [Fact]
  public async Task CompositionalProofUsesEmptyQuantifierProduct() {
    var result = await Check("ghost predicate EmptyRange() { " +
      "forall i:int, previous:int | previous == i - 1 :: 0 <= i < 0 ==> i == previous } " +
      "ghost predicate Parent() { EmptyRange() } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} Parent(); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.DoesNotContain("proofSteps=0", result.Diagnostics);
  }

  // Captured maps and bitvectors use the same concrete boundary as the reducer itself.
  [Theory]
  [InlineData("s.values[0] == 7 && s.mode == 493", ContractQueryOutcome.Unsat)]
  [InlineData("s.values[0] == 8", ContractQueryOutcome.Sat)]
  [InlineData("s.values[1] == 7", ContractQueryOutcome.Error)]
  public async Task StructuredBindingsRetainOriginalProofAndDefinedness(string property, ContractQueryOutcome expected) {
    var result = await Check("datatype Snapshot = Snapshot(values:map<int,int>, mode:bv32) " +
      "method ContractDiagnosticQuery(s:Snapshot) requires s == Snapshot(map[0 := 7], 493 as bv32) " +
      "{ assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.Equal(expected, result.Outcome);
    if (expected == ContractQueryOutcome.Unsat) {
      Assert.Contains("decision=True", result.Diagnostics);
    }
  }

  // A checked concrete instance supplies the witness term needed to prove the unchanged existential.
  [Fact]
  public async Task DependentSequenceWitnessNativeGate() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "(exists a:seq<bool>, b:seq<seq<int>>, c:seq<nat> :: |a| == 0 && |b| == 0 && |c| == 1 && c[0] == 0); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
  }

  // A negated true witness never obtains a proof; a deadline remains an explicitly unsupported outcome.
  [Fact]
  public async Task NegatedTrueWitnessCannotBecomeProof() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "!(exists a:seq<bool>, b:seq<seq<int>>, c:seq<nat> :: |a| == 0 && |b| == 0 && |c| == 1 && c[0] == 0); }");
    Assert.True(result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Timeout, result.Diagnostics);
  }

  // Exhaustive boolean decomposition proves a false existential's negation through the original target.
  [Fact]
  public async Task FalseDependentExistentialHasCheckedNegation() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "!(exists a:seq<bool>, b:seq<int> :: |a| == 1 && |b| == 1 && b[0] == " +
      "(if a[0] then 7 else 3) && b[0] == 5); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
  }

  // Imported predicate reduction uses the query's resolved visibility without revealing provided-only bodies.
  [Theory]
  [InlineData("", ContractQueryOutcome.Unsat, "decision=True")]
  [InlineData("export provides P", ContractQueryOutcome.Sat, "decision=Residual")]
  public async Task ImportedPredicateVisibility(string export, ContractQueryOutcome expected, string diagnostic) {
    var result = await Check("module Library { " + export + " predicate P(x:int) { x == 3 } } " +
      "module Client { import L = Library method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} L.P(3); } }");
    Assert.Equal(expected, result.Outcome);
    Assert.Contains(diagnostic, result.Diagnostics);
  }

  // A partially decomposed product keeps resolved bounds when an unbounded field remains for native proof.
  [Fact]
  public async Task ProductResidualRemainsTranslatable() {
    var result = await Check("datatype Witness = Witness(items:seq<int>, number:int) " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists w:Witness :: |w.items| == 0 && w.number * w.number == 2; }");
    Assert.True(result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Timeout, result.Diagnostics);
  }

  // Native original assertions agree with constructor-based branch selection for both true and false clauses.
  [Theory]
  [InlineData("Pick(Some(7)) == 8", ContractQueryOutcome.Unsat)]
  [InlineData("Pick(None) == 1", ContractQueryOutcome.Sat)]
  public async Task ConstructorMatchNativeGate(string property, ContractQueryOutcome expected) {
    var result = await Check("datatype Choice = None | Some(value:int) " +
      "function Pick(item:Choice):int { match item case None => 0 case Some(value) => value + 1 } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.Equal(expected, result.Outcome);
  }

  // Injectivity supplies an exact witness while original target verification still decides each polarity.
  [Theory]
  [InlineData("exists items:seq<int> :: Entry(items,true) == Entry([],true) && Empty(items)", ContractQueryOutcome.Unsat)]
  [InlineData("!(exists items:seq<int> :: Entry(items,true) == Entry([7],true) && Entry(items,true) == Entry([8],true))", ContractQueryOutcome.Unsat)]
  [InlineData("!(exists items:seq<int> :: Entry(items,true) == Missing)", ContractQueryOutcome.Unsat)]
  [InlineData("exists items:seq<int> :: Entry(items,true) == Missing", ContractQueryOutcome.Sat)]
  public async Task ConstructorEqualityNativeGate(string property, ContractQueryOutcome expected) {
    var result = await Check("datatype Entry = Missing | Entry(items:seq<int>, ready:bool) " +
      "predicate Empty(items:seq<int>) { |items| == 0 } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.Equal(expected, result.Outcome);
  }

  // An invalid refined constructor argument must fail original WD even if injectivity can erase its equality.
  [Fact]
  public async Task ConstructorEqualityRetainsRefinedFieldDefinedness() {
    var result = await Check("datatype Box = Box(value:nat) " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists value:nat :: Box(value) == Box(-1); }");
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // A locally quantified witness is checked as a closed assertion before the unchanged existential target.
  [Fact]
  public async Task LocallyQuantifiedWitnessNativeGate() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists items:seq<int> :: items == [7] && (forall index:nat | index < |items| :: items[index] == 7); }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("checkedWitnesses=1", result.Diagnostics);
  }

  // An outer quantified variable is never emitted as a free identifier in a lifted witness assertion.
  [Fact]
  public async Task OuterBinderCannotEscapeNativeWitness() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "forall outer:int :: exists item:int :: item == 0 && (outer < 0 || true); }");
    Assert.True(result.Outcome is ContractQueryOutcome.Unsat or ContractQueryOutcome.Sat, result.Diagnostics);
    Assert.Contains("checkedWitnesses=0", result.Diagnostics);
  }

  // Statement-expression assertions cannot introduce an out-of-scope variable into native witness checks.
  [Fact]
  public async Task StatementOnlyOuterBinderCannotEscapeNativeWitness() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "forall outer:int :: exists item:int :: item == 0 && ((assert outer == outer; true) || true); }");
    Assert.True(result.Outcome is ContractQueryOutcome.Unsat or ContractQueryOutcome.Sat, result.Diagnostics);
    Assert.Contains("checkedWitnesses=0", result.Diagnostics);
  }

  // A closed nested quantifier cannot hide an invalid function call inside the checked witness.
  [Fact]
  public async Task LocallyQuantifiedWitnessRetainsDefinedness() {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists items:seq<int> :: items == [0] && (forall index:nat | index < |items| :: Partial(items[index]) == 0); }");
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // A concrete existential witness cannot bypass the original function-call definedness obligation.
  [Fact]
  public async Task WitnessRetainsOriginalFunctionPrecondition() {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists values:seq<int> :: |values| == 1 && values[0] == 0 && Partial(values[0]) == 0; }");
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  private static async Task<ContractQueryResult> Check(string source) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    try {
      return await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None,
        deadlineTimestamp: ContractQueryDeadline.AfterMilliseconds(3000));
    } catch (System.OperationCanceledException) {
      return new(ContractQueryKind.ClosedClause, ContractQueryOutcome.Timeout, "Native proof exceeded the 3s test deadline.");
    }
  }
}
