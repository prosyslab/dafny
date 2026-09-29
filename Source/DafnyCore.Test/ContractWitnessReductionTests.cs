using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;

namespace DafnyCore.Test;

public class ContractWitnessReductionTests {
  // Native proof composition resolves an acyclic predicate chain while default reduction keeps its depth residual.
  [Fact]
  public async Task ComposesClosedPredicateProofsWithoutChangingDefaultDepth() {
    const string source = "ghost predicate EmptyItems(items:seq<int>) { |items| == 0 } " +
      "ghost predicate MiddleProof() { exists items:seq<int> :: |items| == 0 && EmptyItems(items) } " +
      "ghost predicate OuterProof() { MiddleProof() } method M() ensures OuterProof() {}";
    var baseline = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, baseline.Decision);
    Assert.Empty(baseline.ProofObligations);
    Assert.NotEmpty(composed.ProofObligations);
    Assert.Contains(composed.ProofObligations,
      obligation => obligation.Kind == ContractReductionProofKind.Predicate);
    Assert.True(composed.ExpressionExpansionNodeCount > baseline.ExpressionExpansionNodeCount);
    var predicates = composed.ProofObligations
      .Where(obligation => obligation.Kind == ContractReductionProofKind.Predicate)
      .Select(obligation => Printer.ExprToString(options: new DafnyOptions(DafnyOptions.Default), obligation.Expression))
      .ToList();
    Assert.Equal(predicates.Distinct().Count(), predicates.Count);
  }

  // Shared proof-node exhaustion discards the staged parent instead of publishing an incomplete certificate.
  [Fact]
  public async Task CompositionExhaustionDoesNotPublishParent() {
    const string source = "ghost predicate EmptyItems(items:seq<int>) { |items| == 0 } " +
      "ghost predicate MiddleProof() { exists items:seq<int> :: |items| == 0 && EmptyItems(items) } " +
      "ghost predicate OuterProof() { MiddleProof() } method M() ensures OuterProof() {}";
    var result = await Reduce(source, new ContractReductionBudget(quantifierInstanceLimit: 1),
      composeNativeProof: true);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.DoesNotContain(result.ProofObligations,
      obligation => obligation.Kind == ContractReductionProofKind.Predicate);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A partial helper in an unselected conditional branch never becomes an auxiliary proof obligation.
  [Theory]
  [InlineData("if false then Dangerous() else true")]
  [InlineData("false ==> Dangerous()")]
  [InlineData("true || Dangerous()")]
  public async Task CompositionIgnoresDeadConditionalHelper(string body) {
    const string source = "function Partial(value:int):int requires value > 0 { value } " +
      "ghost predicate Dangerous() { Partial(0) == 0 } ghost predicate Safe() { ";
    var result = await Reduce(source + body + " } method M() ensures Safe() {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.All(result.ProofObligations, obligation =>
      Assert.DoesNotContain("Dangerous", Printer.ExprToString(
        new DafnyOptions(DafnyOptions.Default), obligation.Expression)));
  }

  // Composition recognizes an empty product factor without changing ordinary quantifier reduction.
  [Theory]
  [InlineData("forall i:int, previous:int | previous == i - 1 :: 0 <= i < 0 ==> i == previous",
    ContractReductionDecision.True)]
  [InlineData("exists i:int, previous:int | previous == i - 1 :: 0 <= i < 0 && i == previous",
    ContractReductionDecision.False)]
  public async Task CompositionDetectsEmptyQuantifierProduct(string property,
    ContractReductionDecision expected) {
    var source = "method M() ensures " + property + " {}";
    var baseline = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    if (expected == ContractReductionDecision.True) {
      Assert.Equal(ContractReductionDecision.Residual, baseline.Decision);
    } else {
      Assert.Equal(expected, baseline.Decision);
    }
    Assert.Equal(expected, composed.Decision);
    if (expected == ContractReductionDecision.True) {
      Assert.Equal(0U, composed.QuantifierInstancesUsed);
    } else {
      Assert.InRange(composed.QuantifierInstancesUsed, 0U, 1U);
    }
  }

  // Existential witnesses from dead or guarded short-circuit branches are never lifted unconditionally.
  [Theory]
  [InlineData("false ==> (exists items:seq<int> :: |items| == 0)")]
  [InlineData("true || (exists items:seq<int> :: |items| == 0)")]
  [InlineData("guard ==> (exists items:seq<int> :: |items| == 0)")]
  [InlineData("!(exists items:seq<int> :: |items| == 0)")]
  public async Task CompositionDoesNotLiftGuardedExistentialWitness(string property) {
    var result = await Reduce("method M(guard:bool) ensures " + property + " {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofWitnesses);
    Assert.DoesNotContain(result.ProofObligations,
      obligation => obligation.Kind == ContractReductionProofKind.Witness);
  }

  // A witness simplified inside a forall body is not lifted beyond its quantified range.
  [Theory]
  [InlineData("false")]
  [InlineData("0 <= i < 0")]
  public async Task CompositionDoesNotLiftVacuousForallWitness(string range) {
    var result = await Reduce("function Partial(value:int):int requires value > 0 { value } " +
      "method M() ensures forall i:int | " + range + " :: " +
      "exists items:seq<int> :: |items| == 0 && Partial(0) == 0 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofWitnesses);
    Assert.DoesNotContain(result.ProofObligations,
      obligation => obligation.Kind == ContractReductionProofKind.Witness);
  }

  // Predicate dependencies are checked before the witness that uses them.
  [Fact]
  public async Task CompositionOrdersPredicateDependencyBeforeWitness() {
    var result = await Reduce("ghost predicate Support() { true } " +
      "ghost predicate Middle() { exists items:seq<int> :: |items| == 0 && Support() } " +
      "ghost predicate Outer() { Middle() } method M() ensures Outer() {}",
      new ContractReductionBudget(), composeNativeProof: true);
    var obligations = result.ProofObligations.ToList();
    var support = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Support"));
    var witness = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Witness);
    var prerequisite = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Prerequisite);
    var middle = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Middle"));
    var outer = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Outer"));
    Assert.True(0 <= support && support < witness);
    Assert.True(witness < prerequisite && prerequisite < middle && middle < outer);
  }

  // Earlier witness facts stay before a predicate discovered by a later witness.
  [Fact]
  public async Task CompositionPreservesWitnessOrderBeforeLaterPredicateDependency() {
    var result = await Reduce("ghost predicate Support() { true } " +
      "ghost predicate Middle() { " +
      "(exists first:seq<int> :: |first| == 0) && " +
      "(exists second:seq<int> :: |second| == 0 && Support()) } " +
      "ghost predicate Outer() { Middle() } method M() ensures Outer() {}",
      new ContractReductionBudget(), composeNativeProof: true);
    var obligations = result.ProofObligations.ToList();
    var firstWitness = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Witness);
    var lastWitness = obligations.FindLastIndex(obligation => obligation.Kind == ContractReductionProofKind.Witness);
    var support = obligations.FindIndex(obligation => obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Support"));
    Assert.True(0 <= firstWitness && firstWitness < support && support < lastWitness,
      string.Join(" | ", obligations.Select(obligation => obligation.Kind + ":" +
        Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression))));
  }

  // A later dependency failure discards earlier staged witnesses and every incomplete parent node.
  [Fact]
  public async Task CompositionPublishesNothingFromFailedOrderedCertificate() {
    var result = await Reduce("ghost predicate Support() { true } " +
      "ghost predicate Unsupported() { exists n:int :: n * n == 2 } " +
      "ghost predicate Middle() { Support() && " +
      "(exists first:seq<int> :: |first| == 0) && " +
      "(exists second:seq<int> :: |second| == 0 && Unsupported()) } " +
      "ghost predicate Outer() { Middle() } method M() ensures Outer() {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofObligations);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
  }

  // A predicate in a dead witness branch is not activated from deferred provenance.
  [Fact]
  public async Task CompositionDoesNotActivateDeadWitnessDependency() {
    var result = await Reduce("function Partial(value:int):int requires value > 0 { value } " +
      "ghost predicate Dangerous() { Partial(0) == 0 } " +
      "ghost predicate Middle() { exists items:seq<int> :: |items| == 0 && (false ==> Dangerous()) } " +
      "ghost predicate Outer() { Middle() } method M() ensures Outer() {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.DoesNotContain(result.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Dangerous"));
  }

  // Recursive calls may still reduce ordinarily, but never become composition graph nodes.
  [Fact]
  public async Task CompositionDoesNotAdmitRecursivePredicateNode() {
    var result = await Reduce("ghost predicate Countdown(n:nat) decreases n { " +
      "n == 0 || Countdown(n - 1) } method M() ensures Countdown(2) {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.DoesNotContain(result.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Predicate &&
      Printer.ExprToString(new DafnyOptions(DafnyOptions.Default), obligation.Expression).Contains("Countdown"));
  }

  // Exact sequence products expose deterministic dependent witnesses without selecting a guessed domain.
  [Theory]
  [InlineData("exists a:seq<bool>, b:seq<seq<int>>, c:seq<nat> :: |a| == 0 && |b| == 0 && |c| == 1 && c[0] == 0", ContractReductionDecision.True)]
  [InlineData("exists a:seq<bool>, b:seq<int> :: |a| == 1 && |b| == 1 && b[0] == (if a[0] then 7 else 3) && b[0] == 7", ContractReductionDecision.True)]
  [InlineData("exists a:seq<bool>, b:seq<int> :: |a| == 1 && |b| == 1 && b[0] == (if a[0] then 7 else 3) && b[0] == 5", ContractReductionDecision.False)]
  [InlineData("exists x:nat, y:int :: x == y && y == -1", ContractReductionDecision.False)]
  [InlineData("exists x:int, y:int :: x == y && y == 7", ContractReductionDecision.True)]
  [InlineData("exists x:int :: x * x == 2", ContractReductionDecision.Residual)]
  public async Task ExactDependentWitnesses(string property, ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures " + property + " {}", new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // A product constructor preserves field subset constraints while decomposing its exact witness shape.
  [Theory]
  [InlineData(0, ContractReductionDecision.True)]
  [InlineData(-1, ContractReductionDecision.False)]
  public async Task ProductFieldConstraints(int value, ContractReductionDecision expected) {
    var result = await Reduce("datatype Witness = Witness(items:seq<int>, cuts:seq<nat>) " +
      "method M() ensures exists w:Witness :: |w.items| == 0 && |w.cuts| == 1 && w.cuts[0] == " + value + " {}",
      new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // The shared instance cap leaves unfinished decomposition residual instead of manufacturing a verdict.
  [Fact]
  public async Task DecompositionHonorsSharedCap() {
    var result = await Reduce("method M() ensures exists a:seq<int>, b:seq<int> :: " +
      "|a| == 1 && |b| == 1 && a[0] == 7 && b[0] == 8 {}", new ContractReductionBudget(quantifierInstanceLimit: 1));
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
  }

  // Constructor selection substitutes branch variables and leaves an unknown source as a residual.
  [Theory]
  [InlineData("Pick(Some(7)) == 8", ContractReductionDecision.True)]
  [InlineData("Pick(None) == 0", ContractReductionDecision.True)]
  [InlineData("Pick(item) == 8", ContractReductionDecision.Residual)]
  public async Task KnownConstructorMatch(string property, ContractReductionDecision expected) {
    var result = await Reduce("datatype Choice = None | Some(value:int) " +
      "function Pick(item:Choice):int { match item case None => 0 case Some(value) => value + 1 } " +
      "method M(item:Choice) ensures " + property + " {}", new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // Sequence membership uses constructor identity and nested concrete fields without guessing unknown elements.
  [Theory]
  [InlineData("Input in [File([1,2])]", ContractReductionDecision.False)]
  [InlineData("File([1,2]) in [File([1,2]), Input]", ContractReductionDecision.True)]
  [InlineData("File([2,1]) !in [File([1,2])]", ContractReductionDecision.True)]
  [InlineData("Input in [item]", ContractReductionDecision.Residual)]
  public async Task ConcreteDatatypeSequenceMembership(string property, ContractReductionDecision expected) {
    var result = await Reduce("datatype Choice = Input | File(path:seq<int>) " +
      "method M(item:Choice) ensures " + property + " {}", new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // Constructor injectivity exposes exact sequence bindings, including nested generic products and conflicts.
  [Theory]
  [InlineData("exists items:seq<int> :: Entry(items,true) == Entry([],true)", ContractReductionDecision.True)]
  [InlineData("exists items:seq<int> :: Wrapper(Entry(items,true)) == Wrapper(Entry([7],true))", ContractReductionDecision.True)]
  [InlineData("exists items:seq<int> :: Entry(items,true) == Entry([7],true) && Entry(items,true) == Entry([8],true)", ContractReductionDecision.False)]
  [InlineData("exists items:seq<int> :: Entry(items,true) == Missing", ContractReductionDecision.False)]
  [InlineData("Entry(items,true) == Entry([],true)", ContractReductionDecision.Residual)]
  [InlineData("entry == Entry([],true)", ContractReductionDecision.Residual)]
  public async Task ConstructorEqualitiesExposeExactBindings(string property, ContractReductionDecision expected) {
    var result = await Reduce("datatype Entry = Missing | Entry(items:seq<int>, ready:bool) " +
      "datatype Wrapper<T> = Wrapper(value:T) " +
      "method M(items:seq<int>, entry:Entry) ensures " + property + " {}", new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // Exact field equality cannot erase the refinement on an existentially quantified field value.
  [Theory]
  [InlineData(0, ContractReductionDecision.True)]
  [InlineData(-1, ContractReductionDecision.False)]
  public async Task ConstructorEqualityPreservesRefinedBinder(int value, ContractReductionDecision expected) {
    var result = await Reduce("datatype Box = Box(value:int) " +
      "method M() ensures exists value:nat :: Box(value) == Box(" + value + ") {}", new ContractReductionBudget());
    Assert.Equal(expected, result.Decision);
  }

  // Coinductive constructor equality remains outside the ordinary inductive decomposition rule.
  [Fact]
  public async Task CoinductiveConstructorEqualityRemainsResidual() {
    var result = await Reduce("codatatype Stream = Cons(value:int, tail:Stream) " +
      "method M(tail:Stream) ensures Cons(0,tail) == Cons(1,tail) {}", new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
  }

  // Generated field equalities consume the existing node allowance and leave the original residual on exhaustion.
  [Fact]
  public async Task ConstructorEqualityHonorsNodeCap() {
    const string source = "datatype Entry = Entry(items:seq<int>, ready:bool) " +
      "method M() ensures exists items:seq<int> :: Entry(items,true) == Entry([1,2,3],true) {}";
    var full = await Reduce(source, new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, full.Decision);
    var limited = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: full.SubstitutedExpressionNodeCount + 1));
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, limited.ExhaustionReasons);
    Assert.InRange(limited.ExpressionExpansionNodeCount, 0U, 1U);
  }

  // A closed witness keeps its locally quantified fields for independent native checking.
  [Fact]
  public async Task WitnessRetainsLocallyBoundQuantifier() {
    var result = await Reduce("method M() ensures exists items:seq<int> :: items == [7] && " +
      "(forall index:nat | index < |items| :: items[index] == 7) {}", new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Contains(result.ProofWitnesses, witness => witness.DescendantsAndSelf.OfType<ForallExpr>().Any());
    Assert.All(result.ProofWitnesses, witness => Assert.DoesNotContain(
      FreeVariablesUtil.ComputeFreeVariables(new DafnyOptions(DafnyOptions.Default), witness), variable => variable is BoundVar));
  }

  // An outer binder remains free in a candidate witness even when simplification makes its occurrence irrelevant.
  [Fact]
  public async Task WitnessDoesNotEscapeOuterBinder() {
    var result = await Reduce("method M() ensures forall outer:int :: " +
      "exists item:int :: item == 0 && (outer < 0 || true) {}", new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ProofWitnesses);
  }

  // A binder referenced only by a statement-expression assertion must not escape with a lifted witness.
  [Fact]
  public async Task WitnessDoesNotEscapeStatementOnlyOuterBinder() {
    var result = await Reduce("method M() ensures forall outer:int :: exists item:int :: " +
      "item == 0 && ((assert outer == outer; true) || true) {}", new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ProofWitnesses);
  }

  // Every substituted occurrence is charged even when the same argument object can be shared.
  [Fact]
  public async Task ReservationChargesRepeatedOccurrences() {
    var result = await Reduce("function Twice(items:seq<int>):seq<int> { items + items } " +
      "method M() ensures |Twice([1,2,3,4,5])| == 10 {}", new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(15U, result.ExpressionExpansionNodeCount); // Two six-node values, their syntax wrappers, and concatenation.
  }

  // An unused large input is not multiplied into unrelated nodes of the inlined body.
  [Fact]
  public async Task ReservationDoesNotChargeUnusedArguments() {
    var values = string.Join(",", Enumerable.Range(0, 30));
    var result = await Reduce("predicate Accept(unused:seq<int>, value:int) { value == 7 } " +
      "method M() ensures Accept([" + values + "], 7) {}", new ContractReductionBudget(expressionNodeLimit: 90));
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(4U, result.ExpressionExpansionNodeCount); // Equality, the identifier's syntax wrapper, and two literals.
  }

  // A binder with the same printed name as a formal is a distinct variable during substitution accounting.
  [Fact]
  public async Task ReservationRespectsBinderIdentity() {
    var values = string.Join(",", Enumerable.Range(0, 30));
    var result = await Reduce("predicate Accept(items:seq<int>) { forall items:int | 0 <= items < 1 :: items == 0 } " +
      "method M() ensures Accept([" + values + "]) {}", new ContractReductionBudget(expressionNodeLimit: 100));
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.InRange(result.ExpressionExpansionNodeCount, 1U, 50U);
  }

  // Repeated large substitutions remain residual when their actual expansion exceeds the unchanged cap.
  [Fact]
  public async Task ReservationRejectsOversizedExpansion() {
    var values = string.Join(",", Enumerable.Range(0, 30));
    var result = await Reduce("function Twice(items:seq<int>):seq<int> { items + items } " +
      "method M() ensures |Twice([" + values + "])| == 60 {}", new ContractReductionBudget(expressionNodeLimit: 90));
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, result.ExhaustionReasons);
  }

  private static async Task<ContractReductionResult> Reduce(string source, ContractReductionBudget budget,
    bool composeNativeProof = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse(source, new Uri("untitled:contract-witness-reducer"), reporter);
    Assert.Equal(0, reporter.ErrorCount);
    var program = parsed.Program;
    await new ProgramResolver(program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single(candidate => candidate.Name == "M");
    var original = method.Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var reducer = new ContractExpressionReducer(options, program.DefaultModuleDef, program.SystemModuleManager);
    var result = composeNativeProof
      ? reducer.ReduceForNativeProofComposition(original, budget: budget)
      : reducer.Reduce(original, budget: budget);
    Assert.Equal(before, Printer.ExprToString(options, original));
    return result;
  }
}
