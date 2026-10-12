using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractWitnessQueryTests {
  // Complete sequence splits support native proofs while contradictory residual conjuncts remain false.
  [Theory]
  [InlineData("exists a:string, b:string :: \"\\U{1F600}x\" == a + b && |a| == 1 && b == \"x\"", ContractQueryOutcome.Unsat)]
  [InlineData("exists a:seq<int>, b:seq<int> :: [1,2] == a + b && |a| == 1 && b == [9]", ContractQueryOutcome.Sat)]
  [InlineData("!(exists a:seq<int> :: [1,2] == a + a)", ContractQueryOutcome.Unsat)]
  [InlineData("exists a:seq<int> :: [1,1] == a + a", ContractQueryOutcome.Unsat)]
  [InlineData("!(exists a:seq<int> :: [1] == a + a)", ContractQueryOutcome.Unsat)]
  [InlineData("exists a:seq<nat>, b:seq<int> :: [-1] == a + b && |a| == 1", ContractQueryOutcome.Sat)]
  public async Task ConcreteConcatenationRetainsNativeTarget(string property, ContractQueryOutcome expected) {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " + property + "; }",
      unicodeCharacters: true);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Native certification uses the successful split without an unrelated failed-branch prerequisite.
  [Theory]
  [InlineData("[1,1]")]
  [InlineData("a + [1,1]")]
  public async Task SuccessfulConcatenationDoesNotCertifyAbandonedPrerequisites(string repeatedSequence) {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "exists a:seq<int>, b:seq<int> :: [1] == a + b && " +
      "(if |a| == 0 then (exists s:seq<int> :: " + repeatedSequence +
      " == s + s && s != [1]) else b == []); }");
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // An infeasible guard keeps a refuted branch's prerequisites out of the native proof.
  [Theory]
  [InlineData("guard ==> (exists s:seq<int> :: [1,1] == s + s && s != [1])")]
  [InlineData("if guard then (exists s:seq<int> :: [1,1] == s + s && s != [1]) else true")]
  [InlineData("forall i:int | guard :: exists s:seq<int> :: [1,1] == s + s && s != [1]")]
  public async Task ContextualConcatenationDoesNotCertifyPrerequisites(string property) {
    var result = await Check("method ContractDiagnosticQuery(guard:bool) requires !guard { " +
      "assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
    Assert.Contains("proofSteps=0", result.Diagnostics);
  }

  // A partially defined term in an unreachable split expression creates no unconditional witness assertion.
  [Theory]
  [InlineData("false ==> (exists a:string, b:string :: \"ab\" == a + b && Partial(0) == 0)")]
  [InlineData("forall i:int | false :: exists a:string, b:string :: \"ab\" == a + b && Partial(0) == 0")]
  public async Task ConcreteConcatenationDoesNotLiftUnreachableWitness(string property) {
    var result = await Check("function Partial(value:int):int requires value > 0 { value } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("checkedWitnesses=0", result.Diagnostics);
  }

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

  // Native checking retains the original exact-let target for both correct and incorrect constructor comparisons.
  [Theory]
  [InlineData("var rest:Chain := End; rest == End", ContractQueryOutcome.Unsat)]
  [InlineData("var rest:Chain := End; rest == Link(0, End)", ContractQueryOutcome.Sat)]
  [InlineData("match Link(1, End) case End => false case Link(value, rest) => rest == End && value == 1", ContractQueryOutcome.Unsat)]
  [InlineData("match Link(1, End) case End => true case Link(value, rest) => rest == Link(0, End)", ContractQueryOutcome.Sat)]
  public async Task ExactConcreteDatatypeLetRetainsNativeTarget(string property, ContractQueryOutcome expected) {
    var result = await Check("datatype Chain = End | Link(value:nat, rest:Chain) " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} (" + property + "); }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Native well-definedness checks retain the exact binder predicate and every nested constructor field type.
  [Theory]
  [InlineData("Box<nat>", "Box(1)", ContractQueryOutcome.Unsat)]
  [InlineData("Box<nat>", "Box(-1)", ContractQueryOutcome.Error)]
  [InlineData("Box<Box<seq<nat>>>", "Box(Box([1,2]))", ContractQueryOutcome.Unsat)]
  [InlineData("Box<Box<seq<nat>>>", "Box(Box([1,-1]))", ContractQueryOutcome.Error)]
  [InlineData("PositiveBox", "Box(1)", ContractQueryOutcome.Unsat)]
  [InlineData("PositiveBox", "Box(0)", ContractQueryOutcome.Error)]
  public async Task ExactConcreteDatatypeLetRetainsNativeMembership(string binderType, string value,
    ContractQueryOutcome expected) {
    var result = await Check("datatype Box<T> = Box(value:T) " +
      "type PositiveBox = box:Box<int> | box.value > 0 witness Box(1) " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "(var box:" + binderType + " := " + value + "; true); }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // A recursive call with a named recursive rest binder keeps its original correct and wrong-result native targets.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(3, ContractQueryOutcome.Sat)]
  public async Task RecursiveExactDatatypeLetRetainsNativeTarget(int expected, ContractQueryOutcome outcome) {
    var result = await Check("datatype Chain = End | Link(value:nat, rest:Chain) " +
      "function Size(chain:Chain):nat { match chain case End => 0 case Link(value, rest) => 1 + Size(rest) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "Size(Link(7, Link(8, End))) == " + expected + "; }");
    Assert.True(result.Outcome == outcome, result.Diagnostics);
  }

  // Recursive value equalities are checked before the unchanged native target, including a wrong-result control.
  [Theory]
  [InlineData(5, ContractQueryOutcome.Unsat)]
  [InlineData(6, ContractQueryOutcome.Sat)]
  public async Task RecursiveConcreteValueNativeGate(int expected, ContractQueryOutcome outcome) {
    var result = await Check("function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Size([4,5,6,7,8]) == " + expected + "; }");
    Assert.True(result.Outcome == outcome, result.Diagnostics);
  }

  // A negative target retains only checked call==false facts and cannot negate a true source predicate.
  [Theory]
  [InlineData(1, ContractQueryOutcome.Unsat)]
  [InlineData(0, ContractQueryOutcome.Sat)]
  public async Task NegativeConcreteCallNativeGate(int value, ContractQueryOutcome expected) {
    var result = await Check("predicate Leaf(n:int) { n == 0 } predicate Middle(n:int) { Leaf(n) } " +
      "predicate Outer(n:int) { Middle(n) } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} !Outer(" + value + "); }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Concrete recursive predicates obtain checked constructor witnesses from source-derived numeric results.
  [Theory]
  [InlineData(1, ContractQueryOutcome.Unsat)]
  [InlineData(7, ContractQueryOutcome.Sat)]
  public async Task RecursivePredicateAndValueWitnessNativeGate(int expected, ContractQueryOutcome outcome) {
    var result = await Check("datatype Parsed = Bad | Good(value:nat) " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "ghost predicate Parse(items:seq<int>, parsed:Parsed) { " +
      "if |items| == 0 then parsed == Bad else parsed == Good(Size(items)) } " +
      "ghost predicate Walk(groups:seq<seq<int>>, state:nat, result:nat) decreases |groups| { " +
      "if |groups| == 0 then result == state else exists parsed:Parsed :: Parse(groups[0], parsed) && " +
      "(match parsed case Bad => result == state case Good(value) => Walk(groups[1..], value, result)) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Walk([[3,4],[9]], 7, " + expected + "); }");
    Assert.True(result.Outcome == outcome, result.Diagnostics);
  }

  // Native verification sees the actual source definition of a value helper with a familiar name.
  [Fact]
  public async Task NamedValueHelperUsesSourceNativeGate() {
    var result = await Check("function Abs(n:int):int { n + 17 } function Middle(n:int):int { Abs(n) } " +
      "function Outer(n:int):int { Middle(n) } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} Outer(-2) == 15; }");
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // A partial concrete dependency must still fail the original call's definedness check.
  [Fact]
  public async Task ConcreteValueGraphRetainsPreconditions() {
    var result = await Check("function Partial(n:int):int requires n > 0 { n } " +
      "function Middle(n:int):int requires n > 0 { Partial(n) } " +
      "function Outer(n:int):int requires n > 0 { Middle(n) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Outer(0) == 0; }");
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // Finite constructor alternatives keep nested field typing and the original existential target.
  [Theory]
  [InlineData("exists choice:Choice :: choice.Found? && |choice.items| == 1 && choice.items[0] == 0", ContractQueryOutcome.Unsat)]
  [InlineData("exists choice:Choice :: choice.Found? && |choice.items| == 1 && choice.items[0] == -1", ContractQueryOutcome.Sat)]
  public async Task ConstructorAlternativeNativeGate(string property, ContractQueryOutcome expected) {
    var result = await Check("datatype Choice = Missing | Found(items:seq<nat>) " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " + property + "; }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // A provided-only imported recursive value function cannot supply hidden definitions to the proof graph.
  [Fact]
  public async Task RecursiveValueGraphRetainsImportVisibility() {
    var result = await Check("module Library { export provides Size " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } } " +
      "module Client { import L = Library method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} L.Size([1,2,3,4]) == 4; } }");
    Assert.True(result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Timeout, result.Diagnostics);
  }

  // Native definedness independently checks nested collection refinements at the original call boundary.
  [Theory]
  [InlineData("set<map<nat,int>>", "{map[0 := 1]}", ContractQueryOutcome.Unsat)]
  [InlineData("set<map<nat,int>>", "{map[-1 := 1]}", ContractQueryOutcome.Error)]
  [InlineData("multiset<seq<nat>>", "multiset{[0]}", ContractQueryOutcome.Unsat)]
  [InlineData("multiset<seq<nat>>", "multiset{[-1]}", ContractQueryOutcome.Error)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{0}]", ContractQueryOutcome.Unsat)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{-1} := multiset{0}]", ContractQueryOutcome.Error)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{-1}]", ContractQueryOutcome.Error)]
  public async Task ConcreteCollectionArgumentNativeGate(string type, string value, ContractQueryOutcome expected) {
    var result = await Check("function Leaf(items:" + type + "):int { 7 } " +
      "function Middle(items:" + type + "):int { Leaf(items) } function Outer(items:" + type + "):int { Middle(items) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Outer(" + value + ") == 7; }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Original logical-scope verification rejects invalid nested collection results before any query can use the definition.
  [Theory]
  [InlineData("set<map<nat,int>>", "{map[0 := 1]}", true)]
  [InlineData("set<map<nat,int>>", "{map[-1 := 1]}", false)]
  [InlineData("multiset<seq<nat>>", "multiset{[0]}", true)]
  [InlineData("multiset<seq<nat>>", "multiset{[-1]}", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{0}]", true)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{-1} := multiset{0}]", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{-1}]", false)]
  public async Task ConcreteCollectionResultLogicalScope(string type, string value, bool valid) {
    var source = "module Model { function Leaf():" + type + " { " + value + " } " +
      "function Middle():" + type + " { Leaf() } function Outer():" + type + " { Middle() } " +
      "method Entry() ensures Outer() == " + value + " {} }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    var sources = new[] { new ContractSource("membership.dfy", source, ContractHarnessBuilder.Hash(source)) };
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var method = ContractCallableSelector.SelectMethod(program, new("Model.Entry"));
    var checker = new ContractSpecificationChecker(program, sources, options);
    var scope = checker.LogicalScope(method.Ens.Single().E);
    var result = await checker.CheckModuleAsync(scope, "Model", CancellationToken.None);
    Assert.True(result.Verified == valid, result.Diagnostics);
  }

  // Native call definedness checks every refined string character in legacy and Unicode modes.
  [Theory]
  [InlineData("'\\u03A9'", "\"\\u03A9\\u03A9\"", false, ContractQueryOutcome.Unsat)]
  [InlineData("'\\u03A9'", "\"\\u03A9x\"", false, ContractQueryOutcome.Error)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}\\U{03A9}\"", true, ContractQueryOutcome.Unsat)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}x\"", true, ContractQueryOutcome.Error)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F600}\"", true, ContractQueryOutcome.Unsat)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F601}\"", true, ContractQueryOutcome.Error)]
  public async Task ConcreteStringArgumentNativeGate(string character, string value,
    bool unicodeCharacters, ContractQueryOutcome expected) {
    var result = await Check("type RefinedChar = ch:char | ch == " + character + " witness " + character + " " +
      "function Leaf(items:seq<RefinedChar>):int { 7 } " +
      "function Middle(items:seq<RefinedChar>):int { Leaf(items) } " +
      "function Outer(items:seq<RefinedChar>):int { Middle(items) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} Outer(" + value + ") == 7; }",
      unicodeCharacters: unicodeCharacters);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Original dependency verification rejects a string definition whose later character violates its return refinement.
  [Theory]
  [InlineData("'\\u03A9'", "\"\\u03A9\\u03A9\"", false, true)]
  [InlineData("'\\u03A9'", "\"\\u03A9x\"", false, false)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}\\U{03A9}\"", true, true)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}x\"", true, false)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F600}\"", true, true)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F601}\"", true, false)]
  public async Task ConcreteStringResultLogicalScope(string character, string value,
    bool unicodeCharacters, bool valid) {
    var source = "module Model { type RefinedChar = ch:char | ch == " + character + " witness " + character + " " +
      "function Leaf():seq<RefinedChar> { " + value + " } " +
      "function Middle():seq<RefinedChar> { Leaf() } function Outer():seq<RefinedChar> { Middle() } " +
      "method Entry() ensures Outer() == " + value + " {} }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.UnicodeCharacters, unicodeCharacters);
    options.TimeLimit = 3;
    var sources = new[] { new ContractSource("string-membership.dfy", source, ContractHarnessBuilder.Hash(source)) };
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var method = ContractCallableSelector.SelectMethod(program, new("Model.Entry"));
    var checker = new ContractSpecificationChecker(program, sources, options);
    var scope = checker.LogicalScope(method.Ens.Single().E);
    var result = await checker.CheckModuleAsync(scope, "Model", CancellationToken.None);
    Assert.True(result.Verified == valid, result.Diagnostics);
  }

  // An opaque residual parent cannot become proved by publishing a completed support call or earlier witness.
  [Fact]
  public async Task IncompleteInlineParentRetainsNativeTarget() {
    var result = await Check("ghost predicate Support() { true } ghost predicate {:opaque} Unknown() { false } " +
      "ghost predicate Middle() { Support() && (exists first:seq<int> :: |first| == 0) && Unknown() } " +
      "ghost predicate Outer() { Middle() } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} Outer(); }");
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
  }

  // A complete false body retains its checked call certificate under negation, while the true control stays unproved.
  [Theory]
  [InlineData(1, ContractQueryOutcome.Unsat)]
  [InlineData(0, ContractQueryOutcome.Sat)]
  public async Task CompleteInlineFalseBodyRetainsNativeCertificate(int value, ContractQueryOutcome expected) {
    var result = await Check("predicate Zero(n:int) { n == 0 } " +
      "ghost predicate Middle(n:int) { (exists items:seq<int> :: |items| == 0) && Zero(n) } " +
      "ghost predicate Outer(n:int) { Middle(n) } method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} !Outer(" + value + "); }");
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Native verification preserves both polarities of the original closed value-chain target.
  [Theory]
  [InlineData(7, ContractQueryOutcome.Unsat)]
  [InlineData(8, ContractQueryOutcome.Sat)]
  public async Task ValueParentOriginalTargetRetainsNativePolarities(int expected, ContractQueryOutcome outcome) {
    var result = await Check("ghost function Leaf():int { if exists items:seq<int> :: |items| == 0 then 7 else 8 } " +
      "ghost function Middle(n:int, marker:int):int { if marker == 0 && Leaf() == 7 then n else 0 } " +
      "ghost function Outer(n:int, marker:int):int { Middle(n, marker) } " +
      "ghost function Bridge():int { Leaf() } ghost function Live():int { Bridge() } " +
      "method ContractDiagnosticQuery(n:int) { assert {:error \"contract_query_target\"} " +
      "(Outer(n, 0), Live()) == (n, " + expected + "); }");
    Assert.True(result.Outcome == outcome, result.Diagnostics);
  }

  // Native verification retains both polarities of the exact source-derived digit-width target.
  [Theory]
  [InlineData(5, ContractQueryOutcome.Unsat)]
  [InlineData(6, ContractQueryOutcome.Sat)]
  public async Task SourceDerivedDigitWidthRelationNativeGate(int expectedWidth, ContractQueryOutcome expected) {
    var result = await Check(SourceDerivedDigitWidthDeclarations() +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "WidthArgsRelation([WidthArg(\"5\", 17)], 2, WidthParse(false, \"\", -1, " + expectedWidth + ")); }");

    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.DoesNotContain("proofSteps=0", result.Diagnostics);
  }

  // Revealed custom and chained integer subsets keep the unchanged original target as the native oracle.
  [Theory]
  [InlineData("type Positive = value:int | value > 0 witness 1 ", "Positive", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive = value:int | value > 0 witness 1 ", "Positive", 4, ContractQueryOutcome.Sat)]
  [InlineData("type Positive = value:int | value > 0 witness 1 " +
    "type Small = value:Positive | value < 10 witness 1 ", "Small", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive = value:int | value > 0 witness 1 " +
    "type Small = value:Positive | value < 10 witness 1 ", "Small", 4, ContractQueryOutcome.Sat)]
  public async Task CheckedIntegerSubsetConversionNativeGate(string declarations, string targetType,
    int expected, ContractQueryOutcome outcome) {
    var result = await Check(declarations + "method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} ((3 as " + targetType + ") as int) == " + expected + "; }");

    Assert.True(result.Outcome == outcome, result.Diagnostics);
    Assert.DoesNotContain("proofSteps=0", result.Diagnostics);
  }

  // Open generic subset and synonym targets retain both original native polarities without generated proof steps.
  [Theory]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<T>", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<T>", 4, ContractQueryOutcome.Sat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<T>", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<T>", 4, ContractQueryOutcome.Sat)]
  public async Task OpenGenericSubsetConversionUsesOriginalNativeTarget(string declarations, string targetType,
    int expected, ContractQueryOutcome outcome) {
    var result = await Check(declarations + "method ContractDiagnosticQuery<T>() { " +
      "assert {:error \"contract_query_target\"} ((3 as " + targetType + ") as int) == " + expected + "; }");

    Assert.True(result.Outcome == outcome, result.Diagnostics);
    Assert.Contains("proofSteps=0", result.Diagnostics);
  }

  // Closed generic subset and synonym instances keep both native polarities with checked conversion steps.
  [Theory]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<bool>", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<bool>", 4, ContractQueryOutcome.Sat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<bool>", 3, ContractQueryOutcome.Unsat)]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<bool>", 4, ContractQueryOutcome.Sat)]
  public async Task ClosedGenericSubsetConversionRetainsNativeTarget(string declarations, string targetType,
    int expected, ContractQueryOutcome outcome) {
    var result = await Check(declarations + "method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} ((3 as " + targetType + ") as int) == " + expected + "; }");

    Assert.True(result.Outcome == outcome, result.Diagnostics);
    Assert.DoesNotContain("proofSteps=0", result.Diagnostics);
  }

  // Repeated equal carriers retain both certificate pairs without changing the original target or its definedness.
  [Theory]
  [InlineData("((3 as Alias<bool>) as int) + (((1 + 2) as Alias<bool>) as int) == 6",
    ContractQueryOutcome.Unsat, "proofSteps=4")]
  [InlineData("((3 as Alias<bool>) as int) + (((1 + 2) as Alias<bool>) as int) == 7",
    ContractQueryOutcome.Sat, "proofSteps=4")]
  [InlineData("((0 as Alias<bool>) as int) + (((1 - 1) as Alias<bool>) as int) == 0",
    ContractQueryOutcome.Error, "proofSteps=0")]
  public async Task SameCarrierSubsetConversionsRetainNativeTargetAndDefinedness(string property,
    ContractQueryOutcome outcome, string proofSteps) {
    var result = await Check("type Positive<T> = value:int | value > 0 witness 1 " +
      "type Alias<T> = Positive<int> method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} " + property + "; }");

    Assert.True(result.Outcome == outcome, result.Diagnostics);
    Assert.Contains(proofSteps, result.Diagnostics);
  }

  // Invalid and unproved integer subset conversions retain their original native WD failures.
  [Theory]
  [InlineData("", "((-1 as nat) as int) == -1")]
  [InlineData("type Positive = value:int | value > 0 witness 1 ", "((0 as Positive) as int) == 0")]
  [InlineData("ghost predicate {:opaque} Allowed(value:int) { value > 0 } " +
    "type Positive = value:int | Allowed(value) witness 1 ", "((3 as Positive) as int) == 3")]
  public async Task CheckedIntegerSubsetConversionRetainsNativeDefinedness(string declarations, string property) {
    var result = await Check(declarations + "method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} " + property + "; }");

    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // An open integer conversion cannot acquire a closed generated certificate or bypass native WD.
  [Fact]
  public async Task CheckedIntegerSubsetConversionOpenCarrierNativeGate() {
    var result = await Check("method ContractDiagnosticQuery(value:int) { " +
      "assert {:error \"contract_query_target\"} ((value as nat) as int) == value; }");

    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
    Assert.Contains("proofSteps=0", result.Diagnostics);
  }

  // Newtype, bitvector, real, and character constraints stay on their original native paths.
  [Theory]
  [InlineData("newtype Positive = value:int | value > 0 witness 1 ",
    "((3 as Positive) as int) == 3", ContractQueryOutcome.Unsat)]
  [InlineData("type Small = value:bv8 | value < 10 witness 0 ",
    "((((3 as bv8) as Small) as bv8) == (3 as bv8))", ContractQueryOutcome.Unsat)]
  [InlineData("type Unit = value:real | 0.0 <= value <= 1.0 witness 0.0 ",
    "((1.0 as Unit) as real) == 1.0", ContractQueryOutcome.Unsat)]
  [InlineData("type OnlyA = value:char | value == 'a' witness 'a' ",
    "(('b' as OnlyA) as char) == 'b'", ContractQueryOutcome.Error)]
  public async Task UnsupportedConstrainedConversionUsesOriginalNativeTarget(string declarations, string property,
    ContractQueryOutcome expected) {
    var result = await Check(declarations + "method ContractDiagnosticQuery() { " +
      "assert {:error \"contract_query_target\"} " + property + "; }");

    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("proofSteps=0", result.Diagnostics);
  }

  // Recursive operand conversion retains correct, wrong-target and invalid-membership native outcomes.
  [Theory]
  [InlineData("[1,2,3,4]", 4, ContractQueryOutcome.Unsat)]
  [InlineData("[1,2,3,4]", 3, ContractQueryOutcome.Sat)]
  [InlineData("[1,2,3,4,5]", 5, ContractQueryOutcome.Error)]
  public async Task RecursiveOperandSubsetCastRetainsNativeDefinedness(string items, int expected,
    ContractQueryOutcome outcome) {
    var result = await Check("type Small = value:int | 0 <= value < 5 witness 0 " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} " +
      "((Size(" + items + ") as Small) as int) == " + expected + "; }");
    Assert.True(result.Outcome == outcome, result.Diagnostics);
  }

  private static string SourceDerivedDigitWidthDeclarations() =>
    "datatype NatParse = NatOk(value:nat) | NatErr " +
    "datatype WidthArg = WidthArg(text:string, tokenIndex:int) " +
    "datatype WidthParse = WidthParse(hasInvalid:bool, invalidText:string, invalidTokenIndex:int, width:nat) " +
    "function IsDigit(ch:char):bool { '0' <= ch <= '9' } " +
    "function DigitValue(ch:char):nat requires IsDigit(ch) { ((ch as int) - ('0' as int)) as nat } " +
    "ghost predicate EveryDigit(text:string) { forall k :: 0 <= k < |text| ==> IsDigit(text[k]) } " +
    "ghost function DecimalValue(digits:string):nat requires EveryDigit(digits) decreases |digits| { " +
    "if |digits| == 0 then 0 else DecimalValue(digits[..|digits|-1]) * 10 + DigitValue(digits[|digits|-1]) } " +
    "ghost predicate PositiveNatRelation(text:string, result:NatParse) { " +
    "if EveryDigit(text) && |text| > 0 && DecimalValue(text) != 0 then " +
    "result == NatOk(DecimalValue(text)) else result == NatErr } " +
    "ghost predicate WidthArgsRelation(args:seq<WidthArg>, width:nat, result:WidthParse) " +
    "requires width > 0 decreases |args| { if |args| == 0 then result == WidthParse(false, \"\", -1, width) " +
    "else exists parsed:NatParse :: PositiveNatRelation(args[0].text, parsed) && " +
    "(match parsed case NatErr => result == WidthParse(true, args[0].text, args[0].tokenIndex, width) " +
    "case NatOk(nextWidth) => if nextWidth == 0 then " +
    "result == WidthParse(true, args[0].text, args[0].tokenIndex, width) " +
    "else WidthArgsRelation(args[1..], nextWidth, result)) } ";

  private static async Task<ContractQueryResult> Check(string source, bool unicodeCharacters = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.UnicodeCharacters, unicodeCharacters);
    options.TimeLimit = 3;
    try {
      return await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None,
        deadlineTimestamp: ContractQueryDeadline.AfterMilliseconds(3000));
    } catch (System.OperationCanceledException) {
      return new(ContractQueryKind.ClosedClause, ContractQueryOutcome.Timeout, "Native proof exceeded the 3s test deadline.");
    }
  }
}
