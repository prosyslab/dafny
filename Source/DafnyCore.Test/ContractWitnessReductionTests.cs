using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;

namespace DafnyCore.Test;

public class ContractWitnessReductionTests {
  // Bounded enumeration retains the actual full ground body before its checked native witness obligation.
  [Fact]
  public async Task BoundedExistentialPublishesActualGroundWitness() {
    const string source = "method M() ensures exists y:int :: 0 <= y && y < 1 {}";
    var result = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.False(result.BudgetExhausted);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
    var witness = Assert.Single(result.ProofWitnesses);
    var body = Assert.IsType<BinaryExpr>(witness.Resolved);
    Assert.Equal(BinaryExpr.ResolvedOpcode.And, body.ResolvedOp);
    var lower = Assert.IsType<BinaryExpr>(body.E0.Resolved);
    var upper = Assert.IsType<BinaryExpr>(body.E1.Resolved);
    Assert.Equal(BinaryExpr.ResolvedOpcode.Le, lower.ResolvedOp);
    Assert.Equal(BinaryExpr.ResolvedOpcode.Lt, upper.ResolvedOp);
    Assert.True(Expression.IsIntLiteral(lower.E0.Resolved, out var lowerBound) && lowerBound == 0);
    Assert.True(Expression.IsIntLiteral(lower.E1.Resolved, out var lowerValue) && lowerValue == 0);
    Assert.True(Expression.IsIntLiteral(upper.E0.Resolved, out var upperValue) && upperValue == 0);
    Assert.True(Expression.IsIntLiteral(upper.E1.Resolved, out var upperBound) && upperBound == 1);
    Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(new DafnyOptions(DafnyOptions.Default), witness));
    var obligation = Assert.Single(result.ProofObligations);
    Assert.Equal(ContractReductionProofKind.Witness, obligation.Kind);
    Assert.Same(witness, obligation.Expression);
  }

  // Every binder comes from the same successful assignment, including a success after earlier false instances.
  [Theory]
  [InlineData("<", 0, 1U)]
  [InlineData(">", 1, 4U)]
  public async Task BoundedExistentialCopiesCompleteSuccessfulAssignment(string comparison, int value,
    uint instances) {
    var result = await Reduce("method M() ensures exists y:int, z:int :: " +
      "0 <= y && y < 2 && 0 <= z && z < 2 && y + z " + comparison + " 1 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.False(result.BudgetExhausted);
    Assert.Equal(instances, result.QuantifierInstancesUsed);
    var witness = Assert.Single(result.ProofWitnesses);
    Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(new DafnyOptions(DafnyOptions.Default), witness));
    var sum = Assert.Single(witness.DescendantsAndSelf.OfType<BinaryExpr>()
      .Where(binary => binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Add));
    Assert.True(Expression.IsIntLiteral(sum.E0.Resolved, out var left) && left == value);
    Assert.True(Expression.IsIntLiteral(sum.E1.Resolved, out var right) && right == value);
    var obligation = Assert.Single(result.ProofObligations);
    Assert.Equal(ContractReductionProofKind.Witness, obligation.Kind);
    Assert.Same(witness, obligation.Expression);
  }

  // False, empty, unbounded and universal reductions cannot manufacture an existential witness.
  [Theory]
  [InlineData("exists y:int :: 0 <= y && y < 2 && y*y < 0", ContractReductionDecision.False)]
  [InlineData("exists y:int :: 0 <= y && y < 0", ContractReductionDecision.False)]
  [InlineData("exists y:int :: y*y == 2", ContractReductionDecision.Residual)]
  [InlineData("forall y:int | 0 <= y && y < 1 :: y < 1", ContractReductionDecision.True)]
  public async Task BoundedEnumerationRequiresActualExistentialSuccess(string property,
    ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures " + property + " {}", new ContractReductionBudget(),
      composeNativeProof: true);
    Assert.Equal(expected, result.Decision);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // A shared instance cap reached before success leaves the original quantified residual without guidance.
  [Fact]
  public async Task BoundedExistentialExhaustionDoesNotPublishWitness() {
    var result = await Reduce("method M() ensures exists y:int :: 0 <= y && y < 4 && y*y > 0 {}",
      new ContractReductionBudget(quantifierInstanceLimit: 1), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // Enumerating a concrete assignment whose remaining condition is symbolic supplies no witness.
  [Fact]
  public async Task BoundedExistentialSymbolicInstanceRemainsResidual() {
    var result = await Reduce("method M(guard:bool) ensures exists y:int :: 0 <= y && y < 1 && guard {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // One node short of recording the complete bounded witness retains charged enumeration but no proof guidance.
  [Fact]
  public async Task BoundedExistentialWitnessHonorsExpressionBudget() {
    const string source = "method M() ensures exists y:int :: 0 <= y && y < 1 {}";
    var complete = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, complete.Decision);
    Assert.Single(complete.ProofWitnesses);
    Assert.Single(complete.ProofObligations);
    var exactLimit = complete.SubstitutedExpressionNodeCount + complete.ExpressionExpansionNodeCount;
    var exact = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: exactLimit),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, exact.Decision);
    Assert.Empty(exact.ExhaustionReasons);
    Assert.Single(exact.ProofWitnesses);
    Assert.Single(exact.ProofObligations);

    var limited = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: exactLimit - 1),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, limited.ExhaustionReasons);
    Assert.Equal(1U, limited.QuantifierInstancesUsed);
    Assert.Empty(limited.ProofWitnesses);
    Assert.Empty(limited.ProofObligations);
    Assert.InRange(limited.ExpressionExpansionNodeCount, 1U, complete.ExpressionExpansionNodeCount - 1);
  }

  // The retained body includes the declared nat binder's implied nonnegative constraint.
  [Fact]
  public async Task BoundedExistentialRetainsRefinedBinderConstraint() {
    var result = await Reduce("method M() ensures exists y:nat :: y < 1 {}", new ContractReductionBudget(),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    var witness = Assert.Single(result.ProofWitnesses);
    var body = Assert.IsType<BinaryExpr>(witness.Resolved);
    Assert.Equal(BinaryExpr.ResolvedOpcode.And, body.ResolvedOp);
    var constraint = Assert.IsType<BinaryExpr>(body.E0.Resolved);
    Assert.Equal(BinaryExpr.ResolvedOpcode.Le, constraint.ResolvedOp);
    Assert.True(Expression.IsIntLiteral(constraint.E0.Resolved, out var bound) && bound == 0);
    Assert.True(Expression.IsIntLiteral(constraint.E1.Resolved, out var value) && value == 0);
    Assert.Same(witness, Assert.Single(result.ProofObligations).Expression);
  }

  // A bounded witness cannot escape an outer binder even when its occurrence simplifies away.
  [Fact]
  public async Task BoundedExistentialDoesNotEscapeOuterBinder() {
    var result = await Reduce("method M() ensures forall outer:int :: exists y:int :: " +
      "0 <= y && y < 1 && (outer < 0 || true) {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // Negation and guarded or dead branches preserve the existing rollback of bounded witness artifacts.
  [Theory]
  [InlineData("!(exists y:int :: 0 <= y && y < 1)")]
  [InlineData("guard ==> (exists y:int :: 0 <= y && y < 1)")]
  [InlineData("true || (exists y:int :: 0 <= y && y < 1)")]
  [InlineData("if guard then (exists y:int :: 0 <= y && y < 1) else true")]
  public async Task BoundedExistentialKeepsContextualRollback(string property) {
    var result = await Reduce("method M(guard:bool) ensures " + property + " {}", new ContractReductionBudget(),
      composeNativeProof: true);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // Ordinary reduction keeps its existing Boolean result without publishing new proof guidance.
  [Fact]
  public async Task BoundedExistentialKeepsOrdinaryReductionBehavior() {
    var result = await Reduce("method M() ensures exists y:int :: 0 <= y && y < 1 {}",
      new ContractReductionBudget());
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // Character displays and strings compare semantic code points in both Unicode and legacy modes.
  [Theory]
  [InlineData("['\\U{1F600}', 'x'] == \"\\U{1F600}x\"", true, ContractReductionDecision.True)]
  [InlineData("\"\\U{1F600}x\" == ['\\U{1F600}', 'x']", true, ContractReductionDecision.True)]
  [InlineData("['\\U{1F600}'] == \"\\U{1F601}\"", true, ContractReductionDecision.False)]
  [InlineData("['\\u03A9', '\\n'] == \"\\u03A9\\n\"", false, ContractReductionDecision.True)]
  public async Task CharacterDisplayUsesSemanticCodePoints(string property, bool unicodeCharacters,
    ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures " + property + " {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: unicodeCharacters);
    Assert.Equal(expected, result.Decision);
  }

  // A complete concrete witness avoids an unnecessary universally quantified proof prerequisite.
  [Fact]
  public async Task RepeatedConcatenationWitnessNeedsNoUniversalPrerequisite() {
    var result = await Reduce("method M() ensures exists a:seq<int> :: [1,1] == a + a {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofWitnesses);
    Assert.DoesNotContain(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Prerequisite);
  }

  // Exact splits retain every constraint, dependent binder, repeated operand and sequence element type.
  [Theory]
  [InlineData("exists a:seq<int>, b:seq<int> :: [] == a + b", ContractReductionDecision.True)]
  [InlineData("exists a:seq<int>, b:seq<int> :: [1,2] == a + b && |a| == 1 && b == [2]", ContractReductionDecision.True)]
  [InlineData("exists a:seq<int>, b:seq<int> :: [1,2] == a + b && |a| == 1 && b == [9]", ContractReductionDecision.False)]
  [InlineData("exists a:seq<int> :: [1,1] == a + a", ContractReductionDecision.True)]
  [InlineData("exists a:seq<int> :: [1,2] == a + a", ContractReductionDecision.False)]
  [InlineData("exists a:string, b:string :: \"a/b\" == a + \"/\" + b && a == \"a\"", ContractReductionDecision.True)]
  [InlineData("exists a:string, b:string :: \"\\U{1F600}x\" == a + b && |a| == 1 && b == \"x\"", ContractReductionDecision.True)]
  [InlineData("exists b:seq<int> :: (exists a:seq<int> :: [1,2] == a + b && |a| == 1) && b == [2]", ContractReductionDecision.True)]
  [InlineData("exists a:seq<nat>, b:seq<int> :: [-1] == a + b && |a| == 1", ContractReductionDecision.False)]
  [InlineData("exists a:seq<nat>, b:seq<int> :: [0] == a + b && |a| == 1", ContractReductionDecision.True)]
  [InlineData("exists a:seq<seq<nat>>, b:seq<seq<int>> :: [[-1]] == a + b && |a| == 1", ContractReductionDecision.False)]
  public async Task ConcreteConcatenationSplitsAreExact(string property, ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures " + property + " {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: true);
    Assert.Equal(expected, result.Decision);
  }

  // A split that would require more than the shared allowance retains an existential residual.
  [Fact]
  public async Task ConcreteConcatenationRetainsResidualOnExhaustion() {
    var result = await Reduce("method M() ensures exists a:seq<int>, b:seq<int> :: [1,2] == a + b {}",
      new ContractReductionBudget(quantifierInstanceLimit: 2), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // Failed split branches cannot leak a witness that contradicts the complete existential body.
  [Fact]
  public async Task ConcreteConcatenationDiscardsFailedBranchWitnesses() {
    var result = await Reduce("method M() ensures exists a:seq<int>, b:seq<int> :: [1] == a + b && " +
      "(exists c:seq<int> :: c == a) && |a| > 1 {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.False, result.Decision);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ProofObligations);
  }

  // A later successful split discards prerequisites from an earlier refuted branch or unknown conditional.
  [Theory]
  [InlineData("[1,1]")]
  [InlineData("a + [1,1]")]
  public async Task SuccessfulConcatenationDiscardsAbandonedPrerequisites(string repeatedSequence) {
    var result = await Reduce("method M() ensures exists a:seq<int>, b:seq<int> :: [1] == a + b && " +
      "(if |a| == 0 then (exists s:seq<int> :: " + repeatedSequence +
      " == s + s && s != [1]) else b == []) {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofWitnesses);
    Assert.DoesNotContain(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Prerequisite);
  }

  // Conditional and quantified refutations cannot publish their prerequisites outside their context.
  [Theory]
  [InlineData("guard ==> !(exists s:seq<int> :: [1,2] == s + s)")]
  [InlineData("if guard then !(exists s:seq<int> :: [1,2] == s + s) else true")]
  [InlineData("forall i:int | guard :: !(exists s:seq<int> :: [1,2] == s + s)")]
  public async Task ContextualRefutationDiscardsPrerequisites(string property) {
    var result = await Reduce("method M(guard:bool) ensures " + property + " {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.DoesNotContain(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Prerequisite);
  }

  // A negated repeated concatenation receives only a closed universally checked implication.
  [Fact]
  public async Task RepeatedConcatenationRetainsCheckedPrerequisiteUnderNegation() {
    var result = await Reduce("method M() ensures !(exists a:seq<int> :: [1,2] == a + a) {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ProofWitnesses);
    var prerequisite = Assert.Single(result.ProofObligations);
    Assert.Equal(ContractReductionProofKind.Prerequisite, prerequisite.Kind);
    Assert.IsType<ForallExpr>(prerequisite.Expression);
    Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(new DafnyOptions(DafnyOptions.Default), prerequisite.Expression));
  }

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
    Assert.Empty(result.ProofWitnesses);
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

  // Recursive predicates never become predicate-candidate nodes; checked concrete-call equalities remain separate.
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

  // Exact concrete datatype bindings propagate only in proof mode and preserve the complete selected body.
  [Theory]
  [InlineData("var rest:Chain := End; true", ContractReductionDecision.True)]
  [InlineData("var rest:Chain := End; rest == End", ContractReductionDecision.True)]
  [InlineData("var rest:Chain := End; rest == Link(0, End)", ContractReductionDecision.False)]
  [InlineData("match Link(1, End) case End => false case Link(value, rest) => rest == End && value == 1", ContractReductionDecision.True)]
  [InlineData("match Link(1, End) case End => true case Link(value, rest) => rest == Link(0, End)", ContractReductionDecision.False)]
  [InlineData("var rest:Chain := Link(1, End); (var rest:Chain := End; rest == End) && rest == Link(1, End)", ContractReductionDecision.True)]
  public async Task ExactConcreteDatatypeLetUsesProofOnlyScopedBindings(string property,
    ContractReductionDecision expected) {
    var source = "datatype Chain = End | Link(value:nat, rest:Chain) method M() ensures (" + property + ") {}";
    var ordinary = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, ordinary.Decision);
    Assert.Empty(ordinary.ProofObligations);
    Assert.Equal(expected, composed.Decision);
    Assert.Empty(composed.ExhaustionReasons);
    Assert.Equal(ContractReductionBudget.DefaultInlineDepthLimit, composed.InlineDepthLimit);
    Assert.Equal(ContractReductionBudget.DefaultQuantifierInstanceLimit, composed.QuantifierInstanceLimit);
  }

  // Original binder predicates and recursively nested field refinements must hold before an unused let is erased.
  [Theory]
  [InlineData("Box<nat>", "Box(1)", true)]
  [InlineData("Box<nat>", "Box(-1)", false)]
  [InlineData("Box<seq<nat>>", "Box([1,2])", true)]
  [InlineData("Box<seq<nat>>", "Box([1,-1])", false)]
  [InlineData("Box<Box<seq<nat>>>", "Box(Box([1,2]))", true)]
  [InlineData("Box<Box<seq<nat>>>", "Box(Box([1,-1]))", false)]
  [InlineData("PositiveBox", "Box(1)", true)]
  [InlineData("PositiveBox", "Box(0)", false)]
  public async Task ExactConcreteLetChecksOriginalRecursiveMembership(string binderType, string value, bool valid) {
    var result = await Reduce("datatype Box<T> = Box(value:T) " +
      "type PositiveBox = box:Box<int> | box.value > 0 witness Box(1) " +
      "method M() ensures (var box:" + binderType + " := " + value + "; true) {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(valid ? ContractReductionDecision.True : ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Empty(result.ExhaustionReasons);
  }

  // Symbolic fields, such-that binding, and constructor destructuring keep their original unsupported lets.
  [Theory]
  [InlineData("var box:Box := Box(input); true")]
  [InlineData("var box:Box :| box == Box(1); true")]
  [InlineData("var Box(value) := Box(1); value == 1")]
  public async Task UnsupportedDatatypeLetRetainsResidual(string property) {
    var result = await Reduce("datatype Box = Box(value:int) method M(input:int) ensures (" + property + ") {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
  }

  // An exhausted shared expression allowance cannot publish a partially admitted concrete binding.
  [Fact]
  public async Task ExactConcreteLetHonorsSharedExpressionBudget() {
    const string source = "datatype Box<T> = Box(value:T) " +
      "method M() ensures (var box:Box<seq<nat>> := Box([1,2,3]); box.value == [1,2,3]) {}";
    var complete = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, complete.Decision);
    var limited = await Reduce(source,
      new ContractReductionBudget(expressionNodeLimit: complete.SubstitutedExpressionNodeCount + 1),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, limited.ExhaustionReasons);
    Assert.Empty(limited.ProofObligations);
    Assert.Empty(limited.ProofWitnesses);
  }

  // A concrete call containing an exact datatype let discards certificates introduced under an unknown guard.
  [Fact]
  public async Task ExactConcreteLetCertificateRollsBackWithGuard() {
    const string declarations = "datatype Box = Box(value:nat) " +
      "function Read(n:nat):nat decreases n { var box:Box := Box(n); " +
      "if n == 0 then box.value else 1 + Read(n - 1) } ";
    var unguarded = await Reduce(declarations + "method M() ensures Read(1) == 1 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, unguarded.Decision);
    Assert.NotEmpty(unguarded.ProofObligations);
    Assert.Empty(unguarded.ExhaustionReasons);
    Assert.Contains(unguarded.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite &&
      obligation.Expression is BinaryExpr { E0: FunctionCallExpr call } equality &&
      call.Function.IsRecursive && call.Function.Name == "Read" && call.Args.Count == 1 &&
      Expression.IsIntLiteral(call.Args[0], out var argument) && argument == 1 &&
      Expression.IsIntLiteral(equality.E1, out var value) && value == 1);

    var result = await Reduce(declarations +
      "method M(guard:bool) ensures guard ==> Read(1) == 1 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.True(result.QuantifierInstancesUsed > 0);
    // Guard rollback retains calculation charges but never charges for publishing discarded proof nodes.
    Assert.Equal(unguarded.QuantifierInstancesUsed,
      result.QuantifierInstancesUsed + unguarded.ProofCompositionNodesAdmitted);
  }

  // Later live reuse of a concrete let call reimports the certificate discarded by a symbolic branch.
  [Fact]
  public async Task ExactConcreteLetCacheReimportsCertificate() {
    const string declarations = "datatype Box = Box(value:nat) " +
      "function Read(n:nat):nat decreases n { var box:Box := Box(n); " +
      "if n == 0 then box.value else 1 + Read(n - 1) } ";
    var unguarded = await Reduce(declarations + "method M() ensures Read(1) == 1 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, unguarded.Decision);
    Assert.NotEmpty(unguarded.ProofObligations);
    Assert.Empty(unguarded.ExhaustionReasons);
    Assert.Contains(unguarded.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite &&
      obligation.Expression is BinaryExpr { E0: FunctionCallExpr call } equality &&
      call.Function.IsRecursive && call.Function.Name == "Read" && call.Args.Count == 1 &&
      Expression.IsIntLiteral(call.Args[0], out var argument) && argument == 1 &&
      Expression.IsIntLiteral(equality.E1, out var value) && value == 1);

    var result = await Reduce(declarations +
      "method M(guard:bool) ensures (guard ==> Read(1) == 1) && Read(1) == 1 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofObligations);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Contains(result.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite &&
      obligation.Expression is BinaryExpr { E0: FunctionCallExpr call } equality &&
      call.Function.IsRecursive && call.Function.Name == "Read" && call.Args.Count == 1 &&
      Expression.IsIntLiteral(call.Args[0], out var argument) && argument == 1 &&
      Expression.IsIntLiteral(equality.E1, out var value) && value == 1);
    // Session reimport reuses completed calculations and publishes the same dependency graph once.
    Assert.Equal(unguarded.QuantifierInstancesUsed, result.QuantifierInstancesUsed);
    Assert.Equal(unguarded.ProofCompositionNodesAdmitted, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount >= unguarded.ExpressionExpansionNodeCount);
  }

  // Recursive value calls use checked concrete equalities beyond the unchanged ordinary inline depth.
  [Fact]
  public async Task ComposesRecursiveConcreteValues() {
    const string source = "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method M() ensures Size([4,5,6,7,8]) == 5 {}";
    var ordinary = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, ordinary.Decision);
    Assert.Equal(ContractReductionDecision.True, composed.Decision);
    Assert.Contains(composed.ProofObligations, obligation => obligation.Expression is BinaryExpr {
      E0: FunctionCallExpr, E1: LiteralExpr
    });
    Assert.Equal(ContractReductionBudget.DefaultInlineDepthLimit, composed.InlineDepthLimit);
  }

  // A closed recursive predicate enters the concrete graph before ordinary inlining consumes its depth allowance.
  [Theory]
  [InlineData(1, ContractReductionDecision.True)]
  [InlineData(7, ContractReductionDecision.False)]
  public async Task ComposesRecursivePredicateWithConcreteValueDependency(int expected,
    ContractReductionDecision decision) {
    const string declarations = "datatype Parsed = Bad | Good(value:nat) " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "ghost predicate Parse(items:seq<int>, parsed:Parsed) { " +
      "if |items| == 0 then parsed == Bad else parsed == Good(Size(items)) } " +
      "ghost predicate Walk(groups:seq<seq<int>>, state:nat, result:nat) decreases |groups| { " +
      "if |groups| == 0 then result == state else exists parsed:Parsed :: Parse(groups[0], parsed) && " +
      "(match parsed case Bad => result == state case Good(value) => Walk(groups[1..], value, result)) } ";
    var source = declarations + "method M() ensures Walk([[3,4],[9]], 7, " + expected + ") {}";
    var ordinary = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, ordinary.Decision);
    Assert.Equal(decision, composed.Decision);
    if (decision == ContractReductionDecision.True) {
      Assert.Contains(composed.ProofObligations, obligation =>
        obligation.Kind == ContractReductionProofKind.Witness &&
        obligation.Expression.DescendantsAndSelf.OfType<FunctionCallExpr>()
          .Any(call => call.Function.Name == "Walk"));
      Assert.Contains(composed.ProofObligations, obligation =>
        obligation.Kind == ContractReductionProofKind.Prerequisite && obligation.Expression is BinaryExpr {
          E0: FunctionCallExpr { Function.Name: "Walk" }, E1: LiteralExpr { Value: true }
        });
    }
  }

  // The same recursive graph stays residual and publishes no partial certificate when its shared allowance is tiny.
  [Fact]
  public async Task RecursivePredicateAndValueGraphHonorsSharedBudget() {
    var result = await Reduce("datatype Parsed = Bad | Good(value:nat) " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "ghost predicate Parse(items:seq<int>, parsed:Parsed) { " +
      "if |items| == 0 then parsed == Bad else parsed == Good(Size(items)) } " +
      "ghost predicate Walk(groups:seq<seq<int>>, state:nat, result:nat) decreases |groups| { " +
      "if |groups| == 0 then result == state else exists parsed:Parsed :: Parse(groups[0], parsed) && " +
      "(match parsed case Bad => result == state case Good(value) => Walk(groups[1..], value, result)) } " +
      "method M() ensures Walk([[3,4],[9]], 7, 1) {}",
      new ContractReductionBudget(quantifierInstanceLimit: 1), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
  }

  // Equal-length concrete inputs with different contents cannot share a cached recursive value.
  [Fact]
  public async Task ConcreteCallIdentityIncludesArgumentContents() {
    var result = await Reduce("function Total(items:seq<int>):int { " +
      "if |items| == 0 then 0 else items[0] + Total(items[1..]) } " +
      "method M() ensures Total([1,2,3,4]) == 10 && Total([1,2,3,8]) == 14 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofObligations);
  }

  // Source-defined value functions retain their bodies even when their names match interpreter shortcuts.
  [Fact]
  public async Task ConcreteCallUsesOriginalValueDefinition() {
    var result = await Reduce("function Abs(n:int):int { n + 17 } function Middle(n:int):int { Abs(n) } " +
      "function Outer(n:int):int { Middle(n) } method M() ensures Outer(-2) == 15 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofObligations);
  }

  // A complete false-call certificate survives its negation but not an unknown enclosing guard.
  [Theory]
  [InlineData("!Outer(1)", true)]
  [InlineData("guard ==> !Outer(1)", false)]
  public async Task FalseConcreteCallCertificateRespectsOuterContext(string property, bool retained) {
    var result = await Reduce("predicate Leaf(n:int) { n == 0 } predicate Middle(n:int) { Leaf(n) } " +
      "predicate Outer(n:int) { Middle(n) } method M(guard:bool) ensures " + property + " {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(retained, result.ProofObligations.Any(obligation => obligation.Expression is BinaryExpr {
      E0: FunctionCallExpr, E1: LiteralExpr { Value: false }
    }));
  }

  // Identical active calls and growing call chains stop without publishing a partial parent certificate.
  [Theory]
  [InlineData("function Loop(n:nat):nat { Loop(n) }")]
  [InlineData("function Loop(n:nat):nat { Other(n) } function Other(n:nat):nat { Loop(n) }")]
  [InlineData("function Loop(n:nat):nat { Loop(n + 1) }")]
  public async Task ConcreteCallCyclesRemainResidual(string declaration) {
    var result = await Reduce(declaration + " method M() ensures Loop(0) == 0 {}",
      new ContractReductionBudget(quantifierInstanceLimit: 8), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.InRange(result.QuantifierInstancesUsed, 0U, 8U);
  }

  // Insufficient shared work leaves a recursive root residual and emits no incomplete dependency chain.
  [Fact]
  public async Task ConcreteCallBudgetIsShared() {
    var result = await Reduce("function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method M() ensures Size([1,2,3,4,5,6,7]) == 7 {}", new ContractReductionBudget(quantifierInstanceLimit: 2),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
  }

  // Constructor alternatives preserve field membership and reconstruct the complete original witness.
  [Theory]
  [InlineData(0, ContractReductionDecision.True)]
  [InlineData(-1, ContractReductionDecision.False)]
  public async Task ConstructorAlternativesRetainTypedFields(int value, ContractReductionDecision expected) {
    var result = await Reduce("datatype Choice = Missing | Found(items:seq<nat>) " +
      "method M() ensures exists choice:Choice :: choice.Found? && |choice.items| == 1 && choice.items[0] == " + value + " {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(expected, result.Decision);
    if (expected == ContractReductionDecision.True) { Assert.NotEmpty(result.ProofWitnesses); } else { Assert.Empty(result.ProofWitnesses); }
  }

  // Constructor fields without source-derived point values stay unbounded and therefore residual.
  [Fact]
  public async Task ConstructorAlternativesDoNotGuessScalarFields() {
    var result = await Reduce("datatype Choice = Missing | Found(value:int) " +
      "method M() ensures exists choice:Choice :: choice.Found? && choice.value * choice.value == 2 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofWitnesses);
  }

  // A discarded symbolic branch cannot publish a cached recursive call's certificate.
  [Fact]
  public async Task ConcreteCallCertificateRollsBackWithGuard() {
    var result = await Reduce("function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method M(guard:bool) ensures guard ==> Size([1,2,3,4]) == 4 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofObligations);
  }

  // Reusing a calculation after a discarded branch imports its full certificate into the live branch.
  [Fact]
  public async Task ConcreteCallCacheReimportsCertificate() {
    var result = await Reduce("function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } " +
      "method M(guard:bool) ensures (guard ==> Size([1,2,3,4]) == 4) && Size([1,2,3,4]) == 4 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.NotEmpty(result.ProofObligations);
  }

  // Concrete call arguments retain refinements inside sets, multisets, and both nested map positions.
  [Theory]
  [InlineData("set<map<nat,int>>", "{map[0 := 1]}", true)]
  [InlineData("set<map<nat,int>>", "{map[-1 := 1]}", false)]
  [InlineData("multiset<seq<nat>>", "multiset{[0]}", true)]
  [InlineData("multiset<seq<nat>>", "multiset{[-1]}", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{0}]", true)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{-1} := multiset{0}]", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{-1}]", false)]
  public async Task ConcreteCollectionArgumentsRetainNestedMembership(string type, string value, bool valid) {
    var result = await Reduce("function Leaf(items:" + type + "):int { 7 } " +
      "function Middle(items:" + type + "):int { Leaf(items) } " +
      "function Outer(items:" + type + "):int { Middle(items) } " +
      "method M() ensures Outer(" + value + ") == 7 {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(valid ? ContractReductionDecision.True : ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(valid, result.ProofObligations.Any());
  }

  // A source value cannot acquire nested collection refinements merely from its declared return type.
  [Theory]
  [InlineData("set<map<nat,int>>", "{map[0 := 1]}", true)]
  [InlineData("set<map<nat,int>>", "{map[-1 := 1]}", false)]
  [InlineData("multiset<seq<nat>>", "multiset{[0]}", true)]
  [InlineData("multiset<seq<nat>>", "multiset{[-1]}", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{0}]", true)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{-1} := multiset{0}]", false)]
  [InlineData("map<set<nat>,multiset<nat>>", "map[{0} := multiset{-1}]", false)]
  public async Task ConcreteCollectionResultsRetainNestedMembership(string type, string value, bool valid) {
    var result = await Reduce("function Leaf():" + type + " { " + value + " } " +
      "function Middle():" + type + " { Leaf() } function Outer():" + type + " { Middle() } " +
      "method M() ensures Outer() == " + value + " {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(valid ? ContractReductionDecision.True : ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(valid, result.ProofObligations.Any());
  }

  // An unresolved nested refinement leaves the concrete call residual without publishing its parent equality.
  [Fact]
  public async Task ConcreteCollectionMembershipMustComplete() {
    var result = await Reduce("ghost predicate {:opaque} Admitted(n:int) { n >= 0 } " +
      "type Restricted = n:int | Admitted(n) witness * " +
      "function Leaf():set<Restricted> { {0} } function Middle():set<Restricted> { Leaf() } " +
      "function Outer():set<Restricted> { Middle() } method M() ensures Outer() == {0} {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
  }

  // String argument membership checks every decoded character, including supplementary Unicode scalars.
  [Theory]
  [InlineData("'\\u03A9'", "\"\\u03A9\\u03A9\"", false, true)]
  [InlineData("'\\u03A9'", "\"\\u03A9x\"", false, false)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}\\U{03A9}\"", true, true)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}x\"", true, false)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F600}\"", true, true)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F601}\"", true, false)]
  public async Task ConcreteStringArgumentsRetainCharacterMembership(string character, string value,
    bool unicodeCharacters, bool valid) {
    var result = await Reduce("type RefinedChar = ch:char | ch == " + character + " witness " + character + " " +
      "function Leaf(items:seq<RefinedChar>):int { 7 } " +
      "function Middle(items:seq<RefinedChar>):int { Leaf(items) } " +
      "function Outer(items:seq<RefinedChar>):int { Middle(items) } " +
      "method M() ensures Outer(" + value + ") == 7 {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: unicodeCharacters);
    Assert.Equal(valid ? ContractReductionDecision.True : ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(valid, result.ProofObligations.Any());
  }

  // String results retain all character refinements before their enclosing call can publish an equality.
  [Theory]
  [InlineData("'\\u03A9'", "\"\\u03A9\\u03A9\"", false, true)]
  [InlineData("'\\u03A9'", "\"\\u03A9x\"", false, false)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}\\U{03A9}\"", true, true)]
  [InlineData("'\\U{03A9}'", "\"\\U{03A9}x\"", true, false)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F600}\"", true, true)]
  [InlineData("'\\U{1F600}'", "\"\\U{1F600}\\U{1F601}\"", true, false)]
  public async Task ConcreteStringResultsRetainCharacterMembership(string character, string value,
    bool unicodeCharacters, bool valid) {
    var result = await Reduce("type RefinedChar = ch:char | ch == " + character + " witness " + character + " " +
      "function Leaf():seq<RefinedChar> { " + value + " } " +
      "function Middle():seq<RefinedChar> { Leaf() } function Outer():seq<RefinedChar> { Middle() } " +
      "method M() ensures Outer() == " + value + " {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: unicodeCharacters);
    Assert.Equal(valid ? ContractReductionDecision.True : ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(valid, result.ProofObligations.Any());
  }

  // Identity character casts preserve encoded values in both character modes without inventing a different scalar.
  [Theory]
  [InlineData("('\\u03A9' as char) == '\\u03A9'", false, ContractReductionDecision.True)]
  [InlineData("('\\u03A9' as char) == 'x'", false, ContractReductionDecision.False)]
  [InlineData("('\\U{03A9}' as char) == '\\U{03A9}'", true, ContractReductionDecision.True)]
  [InlineData("('\\U{03A9}' as char) == 'x'", true, ContractReductionDecision.False)]
  [InlineData("('\\U{1F600}' as char) == '\\U{1F600}'", true, ContractReductionDecision.True)]
  [InlineData("('\\U{1F600}' as char) == '\\U{1F601}'", true, ContractReductionDecision.False)]
  public async Task IdentityCharacterConversionPreservesValue(string property, bool unicodeCharacters,
    ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures " + property + " {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: unicodeCharacters);
    Assert.Equal(expected, result.Decision);
  }

  // A conversion to a refined character remains guarded even when its operand is already a character literal.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task RefinedCharacterConversionDoesNotBecomeIdentity(bool unicodeCharacters) {
    var result = await Reduce("type OnlyA = ch:char | ch == 'a' witness 'a' " +
      "method M() ensures ('b' as OnlyA) == 'b' {}", new ContractReductionBudget(),
      composeNativeProof: true, unicodeCharacters: unicodeCharacters);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
  }

  // A value-returning inline body that stays symbolic cannot publish its concrete child's witness or equality.
  [Fact]
  public async Task IncompleteValueParentRollsBackCompleteChild() {
    var result = await Reduce("ghost function Leaf():int { if exists items:seq<int> :: |items| == 0 then 7 else 8 } " +
      "ghost function Middle(n:int, marker:int):int { if marker == 0 && Leaf() == 7 then n else 0 } " +
      "ghost function Outer(n:int, marker:int):int { Middle(n, marker) } " +
      "method M(n:int) ensures Outer(n, 0) == n {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);
  }

  // A later complete value call reimports a cached child's full certificate after an earlier parent discarded it.
  [Fact]
  public async Task CompleteValueParentReimportsDiscardedChild() {
    var result = await Reduce("ghost function Leaf():int { if exists items:seq<int> :: |items| == 0 then 7 else 8 } " +
      "ghost function Middle(n:int, marker:int):int { if marker == 0 && Leaf() == 7 then n else 0 } " +
      "ghost function Outer(n:int, marker:int):int { Middle(n, marker) } " +
      "ghost function Bridge():int { Leaf() } ghost function Live():int { Bridge() } " +
      "method M(n:int) ensures (Outer(n, 0), Live()) == (n, 7) {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Contains(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Witness);
    Assert.Contains(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Prerequisite &&
      obligation.Expression.DescendantsAndSelf.OfType<FunctionCallExpr>().Any(call => call.Function.Name == "Leaf"));
    Assert.DoesNotContain(result.ProofObligations, obligation =>
      obligation.Expression.DescendantsAndSelf.OfType<FunctionCallExpr>()
        .Any(call => call.Function.Name is "Outer" or "Middle"));
  }

  // The exact digit-width chain distinguishes the checked cast boundary from the identical uncast arithmetic.
  [Theory]
  [InlineData(true, 5, ContractReductionDecision.True)]
  [InlineData(true, 6, ContractReductionDecision.False)]
  [InlineData(false, 5, ContractReductionDecision.True)]
  [InlineData(false, 6, ContractReductionDecision.False)]
  public async Task SourceDerivedDigitWidthRelationCastAndArithmeticControl(bool useCast, int expectedWidth,
    ContractReductionDecision expected) {
    var source = SourceDerivedDigitWidthDeclarations(useCast) +
      "method M() ensures WidthArgsRelation([WidthArg(\"5\", 17)], 2, " +
      "WidthParse(false, \"\", -1, " + expectedWidth + ")) {}";
    var ordinary = await Reduce(source, new ContractReductionBudget());
    var composed = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, ordinary.Decision);
    Assert.Equal(expected, composed.Decision);
    Assert.Equal(ContractReductionBudget.DefaultQuantifierInstanceLimit, composed.QuantifierInstanceLimit);
    Assert.Equal(ContractReductionBudget.DefaultInlineDepthLimit, composed.InlineDepthLimit);
    if (!useCast) {
      return;
    }

    AssertCheckedIntegerSubsetConversion(composed);
    Assert.Contains(composed.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite && obligation.Expression is BinaryExpr {
        E0: FunctionCallExpr { Function.Name: "WidthArgsRelation" }, E1: LiteralExpr
      });
    if (expected == ContractReductionDecision.True) {
      Assert.Contains(composed.ProofObligations, obligation =>
        obligation.Kind == ContractReductionProofKind.Witness &&
        obligation.Expression.DescendantsAndSelf.OfType<FunctionCallExpr>()
          .Any(call => call.Function.Name == "PositiveNatRelation"));
    }
  }

  // Each closed digit-width call retains the checked nat conversion certificate from DigitValue.
  [Theory]
  [InlineData("DigitValue('5') == 5")]
  [InlineData("DecimalValue(\"5\") == 5")]
  [InlineData("PositiveNatRelation(\"5\", NatOk(5))")]
  public async Task CheckedSubsetConversionClosedDigitWidthChain(string property) {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures " + property + " {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    AssertAdjacentCheckedIntegerSubsetConversions(result);
  }

  // Both outcomes of the closed existential retain the checked nat conversion certificate used to decide them.
  [Theory]
  [InlineData(5, ContractReductionDecision.True)]
  [InlineData(6, ContractReductionDecision.False)]
  public async Task CheckedSubsetConversionExistentialDigitWidthSupport(int parsedValue,
    ContractReductionDecision expected) {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures exists parsed:NatParse :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(" + parsedValue + ") {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(expected, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    AssertAdjacentCheckedIntegerSubsetConversions(result);
  }

  // A closed owner that retains an unresolved arithmetic binder cannot publish its staged child certificates.
  [Fact]
  public async Task LiveExistentialSupportRollsBackResidualBody() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures exists parsed:NatParse, unknown:int :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(5) && unknown * unknown == 2 {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);
  }

  // Symbolic implication and conditional branches discard the completed false existential's conversion support.
  [Theory]
  [InlineData("guard ==> (exists parsed:NatParse :: PositiveNatRelation(\"5\", parsed) && parsed == NatOk(6))")]
  [InlineData("if guard then (exists parsed:NatParse :: PositiveNatRelation(\"5\", parsed) && parsed == NatOk(6)) else true")]
  public async Task LiveExistentialSupportRollsBackSymbolicBranch(string property) {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M(guard:bool) ensures " + property + " {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);
  }

  // An unreachable implication operand never contributes the existential's otherwise required conversion certificate.
  [Fact]
  public async Task LiveExistentialSupportSkipsDeadBranch() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures false ==> (exists parsed:NatParse :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(6)) {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A bounded remaining binder completes the live existential's staged conversion support and witness.
  [Fact]
  public async Task LiveExistentialSupportCompletesBoundedRemainingBinder() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures exists parsed:NatParse, index:int :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(5) && 0 <= index && index < 1 {}", new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.True(result.QuantifierInstancesUsed > 0);
    Assert.Contains(result.ProofWitnesses, witness => witness.DescendantsAndSelf.OfType<BinaryExpr>()
      .Any(binary => binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt &&
        Expression.IsIntLiteral(binary.E0.Resolved, out var index) && index == 0 &&
        Expression.IsIntLiteral(binary.E1.Resolved, out var upper) && upper == 1));
    AssertAdjacentCheckedIntegerSubsetConversions(result);
    Assert.Contains(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Witness &&
      result.ProofWitnesses.Any(witness => ReferenceEquals(witness, obligation.Expression)));
  }

  // An incomplete value parent discards bounded completion's support, including when recording exhausts its budget.
  [Fact]
  public async Task LiveExistentialSupportRollsBackIncompleteValueParent() {
    var source = SourceDerivedDigitWidthDeclarations(useCast: true) +
      "ghost function Outer(n:int, marker:int):int { if marker == 0 && " +
      "(exists parsed:NatParse, index:int :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(5) && 0 <= index && index < 1) then n else 0 } " +
      "method M(n:int) ensures Outer(n, 0) == n {}";
    var result = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);

    var exactLimit = result.SubstitutedExpressionNodeCount + result.ExpressionExpansionNodeCount;
    var limited = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: exactLimit - 1),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, limited.ExhaustionReasons);
    Assert.Empty(limited.ProofObligations);
    Assert.Empty(limited.ProofWitnesses);
    Assert.Equal(0U, limited.ProofCompositionNodesAdmitted);
    Assert.InRange(limited.ExpressionExpansionNodeCount, 1U, result.ExpressionExpansionNodeCount - 1);
  }

  // A false range leaves the term unreachable and cannot promote its conversion support through a Boolean result.
  [Fact]
  public async Task LiveExistentialSupportSkipsFalseRange() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures exists parsed:NatParse | false :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(5) {}", new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.False, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // An empty remaining domain cannot promote support staged before the first structural binder substitution.
  [Fact]
  public async Task LiveExistentialSupportRollsBackNestedEmptyDomain() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures exists parsed:NatParse, index:int | 0 <= index < 0 :: " +
      "PositiveNatRelation(\"5\", parsed) && parsed == NatOk(5) {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.False, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);
  }

  // Exhaustion of the shared allowance discards the existential's entire conversion/dependency bundle.
  [Fact]
  public async Task LiveExistentialSupportHonorsSharedBudget() {
    const string property = "method M() ensures exists parsed:NatParse :: PositiveNatRelation(\"5\", parsed) && " +
      "parsed == NatOk(6) {}";
    var source = SourceDerivedDigitWidthDeclarations(useCast: true) + property;
    var complete = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.False, complete.Decision);
    Assert.Empty(complete.ExhaustionReasons);
    AssertAdjacentCheckedIntegerSubsetConversions(complete);

    var limited = await Reduce(source, new ContractReductionBudget(quantifierInstanceLimit: 1),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, limited.ExhaustionReasons);
    Assert.Empty(limited.ProofObligations);
    Assert.Empty(limited.ProofWitnesses);
    Assert.Equal(0U, limited.ProofCompositionNodesAdmitted);
    Assert.True(limited.ExpressionExpansionNodeCount > 0);
    Assert.Equal(1U, limited.QuantifierInstancesUsed);
  }

  // Revealed custom and chained integer subsets receive the same checked membership and equality certificate.
  [Theory]
  [InlineData("type Positive = value:int | value > 0 witness 1 ", "Positive")]
  [InlineData("type Positive = value:int | value > 0 witness 1 " +
    "type Small = value:Positive | value < 10 witness 1 ", "Small")]
  public async Task CheckedIntegerSubsetConversionRetainsCompleteConstraintChain(string declarations,
    string targetType) {
    var result = await Reduce(declarations + "method M() ensures ((3 as " + targetType + ") as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    AssertCheckedIntegerSubsetConversion(result);
  }

  // An open generic subset or synonym target cannot export a closed conversion certificate.
  [Theory]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<T>")]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<T>")]
  public async Task CheckedIntegerSubsetConversionRejectsOpenTargetType(string declarations, string targetType) {
    var result = await Reduce(declarations +
      "method M<T>() ensures ((3 as " + targetType + ") as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // Closed instances of the same generic subset and synonym retain the checked certificate.
  [Theory]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 ", "Positive<bool>")]
  [InlineData("type Positive<T> = value:int | value > 0 witness 1 " +
    "type Alias<T> = Positive<int> ", "Alias<bool>")]
  public async Task CheckedIntegerSubsetConversionAcceptsClosedTargetType(string declarations, string targetType) {
    var result = await Reduce(declarations +
      "method M() ensures ((3 as " + targetType + ") as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    AssertCheckedIntegerSubsetConversion(result);
  }

  // Invalid, unresolved, and unsupported constrained conversions remain residual without proof artifacts.
  [Theory]
  [InlineData("", "((-1 as nat) as int) == -1")]
  [InlineData("type Positive = value:int | value > 0 witness 1 ", "((0 as Positive) as int) == 0")]
  [InlineData("ghost predicate {:opaque} Allowed(value:int) { value > 0 } " +
    "type Positive = value:int | Allowed(value) witness 1 ", "((3 as Positive) as int) == 3")]
  [InlineData("newtype PositiveBase = value:int | value > 0 witness 1 " +
    "type Small = value:PositiveBase | value < 10 witness 1 ", "((3 as Small) as int) == 3")]
  [InlineData("type Small = value:bv8 | value < 10 witness 0 ",
    "((((3 as bv8) as Small) as bv8) == (3 as bv8))")]
  [InlineData("type Unit = value:real | 0.0 <= value <= 1.0 witness 0.0 ",
    "((1.0 as Unit) as real) == 1.0")]
  [InlineData("type OnlyA = value:char | value == 'a' witness 'a' ",
    "(('b' as OnlyA) as char) == 'b'")]
  public async Task CheckedIntegerSubsetConversionRejectsInvalidOrUnsupportedTargets(string declarations,
    string property) {
    var result = await Reduce(declarations + "method M() ensures " + property + " {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A symbolic carrier cannot export a closed checked-conversion certificate.
  [Fact]
  public async Task CheckedIntegerSubsetConversionRejectsOpenCarrier() {
    var result = await Reduce("method M(value:int) ensures ((value as nat) as int) == value {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A subset outside the evaluator's effective visibility scope remains opaque to checked conversion.
  [Fact]
  public async Task CheckedIntegerSubsetConversionRejectsHiddenTarget() {
    var result = await Reduce("type Positive = value:int | value > 0 witness 1 " +
      "method M() ensures ((3 as Positive) as int) == 3 {}", new ContractReductionBudget(),
      composeNativeProof: true, emptyEffectiveScope: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A tiny shared allowance retains the full source-derived target and publishes no partial conversion certificate.
  [Fact]
  public async Task CheckedIntegerSubsetConversionHonorsSharedBudget() {
    var result = await Reduce(SourceDerivedDigitWidthDeclarations(useCast: true) +
      "method M() ensures WidthArgsRelation([WidthArg(\"5\", 17)], 2, WidthParse(false, \"\", -1, 5)) {}",
      new ContractReductionBudget(quantifierInstanceLimit: 1), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
  }

  // A symbolic implication branch cannot publish a conversion certificate that may never execute.
  [Fact]
  public async Task CheckedIntegerSubsetConversionRollsBackDeadBranch() {
    var result = await Reduce("type Positive = value:int | value > 0 witness 1 " +
      "method M(guard:bool, n:int) ensures guard ==> ((3 as Positive) as int) == n {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
  }

  // A nonconcrete value parent cannot publish the checked conversion completed inside its child.
  [Fact]
  public async Task CheckedIntegerSubsetConversionRollsBackIncompleteParent() {
    var result = await Reduce("type Positive = value:int | value > 0 witness 1 " +
      "ghost function Leaf():Positive { 3 as Positive } " +
      "ghost function Middle(n:int, marker:int):int { if marker == 0 && (Leaf() as int) == 3 then n else 0 } " +
      "ghost function Outer(n:int, marker:int):int { Middle(n, marker) } " +
      "method M(n:int) ensures Outer(n, 0) == n {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Equal(0U, result.ProofCompositionNodesAdmitted);
    Assert.True(result.ExpressionExpansionNodeCount > 0);
    Assert.True(result.QuantifierInstancesUsed > 0);
  }

  // The concrete no-argument leaf publishes the certificate that its incomplete symbolic parent must roll back.
  [Fact]
  public async Task CheckedSubsetConversionLeafProducesCertificateForRollback() {
    var result = await Reduce("type Positive = value:int | value > 0 witness 1 " +
      "ghost function Leaf():Positive { 3 as Positive } " +
      "method M() ensures (Leaf() as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Empty(result.ExhaustionReasons);
    AssertAdjacentCheckedIntegerSubsetConversions(result);
  }

  // A rejected subset cast discards its recursive operand's certificate while retaining the work charged for it.
  [Fact]
  public async Task FailedSubsetCastDiscardsOperandProofArtifacts() {
    const string declarations = "type Small = value:int | 0 <= value < 5 witness 0 " +
      "function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) } ";
    var operand = await Reduce(declarations + "method M() ensures Size([4,5,6,7,8]) == 5 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, operand.Decision);
    Assert.Contains(operand.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite && obligation.Expression is BinaryExpr {
        E0: FunctionCallExpr { Function.Name: "Size" }, E1: LiteralExpr
      });
    Assert.True(operand.ProofCompositionNodesAdmitted > 0);

    var valid = await Reduce(declarations + "method M() ensures ((Size([4,5,6,7]) as Small) as int) == 4 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, valid.Decision);
    AssertCheckedIntegerSubsetConversion(valid);
    Assert.Contains(valid.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Prerequisite && obligation.Expression is BinaryExpr {
        E0: FunctionCallExpr { Function.Name: "Size" }, E1: LiteralExpr
      });

    var failed = await Reduce(declarations + "method M() ensures ((Size([4,5,6,7,8]) as Small) as int) == 5 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, failed.Decision);
    Assert.Empty(failed.ProofObligations);
    Assert.Empty(failed.ProofWitnesses);
    Assert.Equal(0U, failed.ProofCompositionNodesAdmitted);
    Assert.True(failed.ExpressionExpansionNodeCount > 0);
    Assert.True(failed.QuantifierInstancesUsed > 0);
    Assert.Contains(failed.ReducedExpression.DescendantsAndSelf.OfType<ConversionExpr>(),
      conversion => conversion.ToType is UserDefinedType { Name: "Small" });
  }

  // A closed phantom alias preserves its raw target arguments and original expression type in adjacent certificates.
  [Fact]
  public async Task AliasSubsetCastPreservesOriginalTargetTypes() {
    var result = await Reduce("type Positive<T> = value:int | value > 0 witness 1 " +
      "type Alias<T> = Positive<int> " +
      "method M() ensures ((3 as Alias<bool>) as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, result.Decision);

    var original = Assert.Single(result.OriginalExpression.DescendantsAndSelf.OfType<ConversionExpr>()
      .Where(conversion => conversion.ToType is UserDefinedType { Name: "Alias" }));
    var originalTarget = Assert.IsType<UserDefinedType>(original.ToType);
    Assert.Equal("Alias", originalTarget.Name);
    Assert.IsType<BoolType>(Assert.Single(originalTarget.TypeArgs));
    var expandedTarget = Assert.IsType<UserDefinedType>(originalTarget.NormalizeExpandKeepConstraints());
    Assert.Equal("Positive", expandedTarget.Name);
    Assert.IsType<SubsetTypeDecl>(expandedTarget.ResolvedClass);
    Assert.IsType<IntType>(Assert.Single(expandedTarget.TypeArgs));

    Assert.Equal(2, result.ProofObligations.Count);
    Assert.All(result.ProofObligations, obligation =>
      Assert.Equal(ContractReductionProofKind.Prerequisite, obligation.Kind));
    var membership = Assert.IsType<TypeTestExpr>(result.ProofObligations[0].Expression);
    var equality = Assert.IsType<BinaryExpr>(result.ProofObligations[1].Expression);
    Assert.Equal(BinaryExpr.Opcode.Eq, equality.Op);
    var conversion = Assert.IsType<ConversionExpr>(equality.E0);
    var literal = Assert.IsType<LiteralExpr>(equality.E1);

    foreach (var target in new[] { membership.ToType, conversion.ToType }) {
      var alias = Assert.IsType<UserDefinedType>(target);
      Assert.Equal(originalTarget.Name, alias.Name);
      Assert.Same(originalTarget.ResolvedClass, alias.ResolvedClass);
      Assert.IsType<BoolType>(Assert.Single(alias.TypeArgs));
    }
    Assert.Same(original.Type, conversion.Type);
    Assert.Same(original.Type, literal.Type);
    Assert.NotSame(original, conversion);
    Assert.True(Expression.IsIntLiteral(original.E, out var originalValue));
    Assert.True(Expression.IsIntLiteral(conversion.E, out var preservedValue));
    Assert.True(Expression.IsIntLiteral(literal, out var convertedValue));
    Assert.True(Expression.IsIntLiteral(membership.E, out var carrierValue));
    Assert.Equal(originalValue, preservedValue);
    Assert.Equal(originalValue, convertedValue);
    Assert.Equal(originalValue, carrierValue);
    Assert.IsType<IntType>(membership.E.Type);
    Assert.IsType<BoolType>(membership.Type);
    Assert.IsType<BoolType>(equality.Type);
  }

  // Equal carriers retain both ordered membership/conversion pairs when the original operands differ.
  [Fact]
  public async Task SameCarrierSubsetConversionsRetainBothCertificatePairs() {
    var result = await Reduce("type Positive<T> = value:int | value > 0 witness 1 " +
      "type Alias<T> = Positive<int> " +
      "method M() ensures ((3 as Alias<bool>) as int) + (((1 + 2) as Alias<bool>) as int) == 6 {}",
      new ContractReductionBudget(), composeNativeProof: true);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.True(Expression.IsBoolLiteral(result.ReducedExpression, out var reducedValue));
    Assert.True(reducedValue);
    Assert.Empty(result.ProofWitnesses);

    var originalConversions = result.OriginalExpression.DescendantsAndSelf.OfType<ConversionExpr>()
      .Where(conversion => conversion.ToType is UserDefinedType { Name: "Alias" })
      .ToArray();
    Assert.Equal(2, originalConversions.Length);
    var literalOriginal = Assert.Single(originalConversions.Where(conversion =>
      Expression.IsIntLiteral(conversion.E, out var value) && (int)value == 3));
    var sumOriginal = Assert.Single(originalConversions.Where(conversion =>
      conversion.E.DescendantsAndSelf.OfType<BinaryExpr>()
        .Any(binary => binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Add)));
    Assert.NotSame(literalOriginal, sumOriginal);
    Assert.True(literalOriginal.ToType.Equals(sumOriginal.ToType, keepConstraints: true));
    Assert.True(Expression.IsIntLiteral(literalOriginal.E, out var literalOperand));
    Assert.Equal(3, (int)literalOperand);
    var originalSum = Assert.Single(sumOriginal.E.DescendantsAndSelf.OfType<BinaryExpr>()
      .Where(binary => binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Add));
    Assert.True(Expression.IsIntLiteral(originalSum.E0, out var leftOperand));
    Assert.True(Expression.IsIntLiteral(originalSum.E1, out var rightOperand));
    Assert.Equal(1, (int)leftOperand);
    Assert.Equal(2, (int)rightOperand);
    var orderedOriginals = new[] { literalOriginal, sumOriginal };

    Assert.Equal(4, result.ProofObligations.Count);
    Assert.All(result.ProofObligations, obligation =>
      Assert.Equal(ContractReductionProofKind.Prerequisite, obligation.Kind));
    var options = new DafnyOptions(DafnyOptions.Default);
    for (var index = 0; index < orderedOriginals.Length; index++) {
      var original = orderedOriginals[index];
      var membership = Assert.IsType<TypeTestExpr>(result.ProofObligations[index * 2].Expression);
      var equality = Assert.IsType<BinaryExpr>(result.ProofObligations[index * 2 + 1].Expression);
      Assert.Equal(BinaryExpr.Opcode.Eq, equality.Op);
      var conversion = Assert.IsType<ConversionExpr>(equality.E0);
      var convertedLiteral = Assert.IsType<LiteralExpr>(equality.E1);

      var originalTarget = Assert.IsType<UserDefinedType>(original.ToType);
      Assert.Equal("Alias", originalTarget.Name);
      Assert.IsType<BoolType>(Assert.Single(originalTarget.TypeArgs));
      var expandedTarget = Assert.IsType<UserDefinedType>(originalTarget.NormalizeExpandKeepConstraints());
      Assert.Equal("Positive", expandedTarget.Name);
      Assert.IsType<SubsetTypeDecl>(expandedTarget.ResolvedClass);
      Assert.IsType<IntType>(Assert.Single(expandedTarget.TypeArgs));
      foreach (var target in new[] { membership.ToType, conversion.ToType }) {
        var preservedTarget = Assert.IsType<UserDefinedType>(target);
        Assert.Equal(originalTarget.Name, preservedTarget.Name);
        Assert.Same(originalTarget.ResolvedClass, preservedTarget.ResolvedClass);
        Assert.IsType<BoolType>(Assert.Single(preservedTarget.TypeArgs));
        Assert.True(originalTarget.Equals(preservedTarget, keepConstraints: true));
      }

      Assert.NotSame(original, conversion);
      Assert.Same(original.Type, conversion.Type);
      Assert.Same(original.Type, convertedLiteral.Type);
      Assert.True(Expression.IsIntLiteral(membership.E, out var carrierValue));
      Assert.True(Expression.IsIntLiteral(convertedLiteral, out var convertedValue));
      Assert.Equal(3, (int)carrierValue);
      Assert.Equal(3, (int)convertedValue);
      Assert.IsType<IntType>(membership.E.Type);
      Assert.IsType<BoolType>(membership.Type);
      Assert.IsType<BoolType>(equality.Type);
      Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(options, original));
      Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(options, membership));
      Assert.Empty(FreeVariablesUtil.ComputeFreeVariables(options, equality));

      if (index == 0) {
        Assert.True(Expression.IsIntLiteral(conversion.E, out var preservedLiteral));
        Assert.Equal(3, (int)preservedLiteral);
      } else {
        var preservedSum = Assert.Single(conversion.E.DescendantsAndSelf.OfType<BinaryExpr>()
          .Where(binary => binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Add));
        Assert.True(Expression.IsIntLiteral(preservedSum.E0, out var preservedLeft));
        Assert.True(Expression.IsIntLiteral(preservedSum.E1, out var preservedRight));
        Assert.Equal(1, (int)preservedLeft);
        Assert.Equal(2, (int)preservedRight);
      }
    }
  }

  // One node short of a complete certificate pair publishes neither assertion and retains charged expansion work.
  [Fact]
  public async Task SubsetCertificatePairHonorsExpressionBudget() {
    const string source = "type Positive = value:int | value > 0 witness 1 " +
      "method M() ensures ((3 as Positive) as int) == 3 {}";
    var complete = await Reduce(source, new ContractReductionBudget(), composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, complete.Decision);
    Assert.Equal(2, complete.ProofObligations.Count);
    Assert.IsType<TypeTestExpr>(complete.ProofObligations[0].Expression);
    var completeEquality = Assert.IsType<BinaryExpr>(complete.ProofObligations[1].Expression);
    Assert.IsType<ConversionExpr>(completeEquality.E0);
    Assert.IsType<LiteralExpr>(completeEquality.E1);
    Assert.True(complete.ExpressionExpansionNodeCount > 1);

    var exactLimit = complete.SubstitutedExpressionNodeCount + complete.ExpressionExpansionNodeCount;
    var exact = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: exactLimit),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.True, exact.Decision);
    Assert.Equal(2, exact.ProofObligations.Count);
    Assert.Equal(complete.ExpressionExpansionNodeCount, exact.ExpressionExpansionNodeCount);
    Assert.DoesNotContain(ContractReductionExhaustionReason.ExpressionNodeLimit, exact.ExhaustionReasons);

    var limited = await Reduce(source, new ContractReductionBudget(expressionNodeLimit: exactLimit - 1),
      composeNativeProof: true);
    Assert.Equal(ContractReductionDecision.Residual, limited.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, limited.ExhaustionReasons);
    Assert.Empty(limited.ProofObligations);
    Assert.Empty(limited.ProofWitnesses);
    Assert.Equal(0U, limited.ProofCompositionNodesAdmitted);
    Assert.InRange(limited.ExpressionExpansionNodeCount, 1U, complete.ExpressionExpansionNodeCount - 1);
    Assert.Contains(limited.ReducedExpression.DescendantsAndSelf.OfType<ConversionExpr>(),
      conversion => conversion.ToType is UserDefinedType { Name: "Positive" });
  }

  // Implicit system imports permit builtin subsets, while an explicit empty scope retains its denial.
  [Theory]
  [InlineData(false, ContractReductionDecision.True)]
  [InlineData(true, ContractReductionDecision.Residual)]
  public async Task BuiltinSubsetConversionHonorsExplicitScope(bool emptyScope, ContractReductionDecision expected) {
    var result = await Reduce("method M() ensures ((3 as nat) as int) == 3 {}",
      new ContractReductionBudget(), composeNativeProof: true, emptyEffectiveScope: emptyScope);
    Assert.Equal(expected, result.Decision);
    if (emptyScope) {
      Assert.Empty(result.ProofObligations);
      Assert.Empty(result.ProofWitnesses);
    } else {
      AssertCheckedIntegerSubsetConversion(result);
    }
  }

  private static void AssertCheckedIntegerSubsetConversion(ContractReductionResult result) {
    var diagnostic = DescribeCheckedIntegerSubsetConversions(result);
    var membershipIndex = Enumerable.Range(0, result.ProofObligations.Count).FirstOrDefault(index =>
      result.ProofObligations[index] is {
        Kind: ContractReductionProofKind.Prerequisite,
        Expression: TypeTestExpr { E.Type: IntType } typeTest
      } &&
      typeTest.ToType.NormalizeExpandKeepConstraints().AsSubsetType != null, -1);
    Assert.True(membershipIndex >= 0, diagnostic);
    var membership = Assert.IsType<TypeTestExpr>(result.ProofObligations[membershipIndex].Expression);
    var equalityIndex = Enumerable.Range(membershipIndex + 1,
      result.ProofObligations.Count - membershipIndex - 1).FirstOrDefault(index =>
      result.ProofObligations[index] is {
        Kind: ContractReductionProofKind.Prerequisite,
        Expression: BinaryExpr { E0: ConversionExpr candidateConversion, E1: LiteralExpr }
      } &&
      candidateConversion.ToType.Equals(membership.ToType, keepConstraints: true) &&
      candidateConversion.Type.Equals(membership.ToType, keepConstraints: true), -1);
    Assert.True(equalityIndex > membershipIndex, diagnostic);
    var equality = Assert.IsType<BinaryExpr>(result.ProofObligations[equalityIndex].Expression);
    var conversion = Assert.IsType<ConversionExpr>(equality.E0);
    Assert.True(conversion.ToType.Equals(membership.ToType, keepConstraints: true), diagnostic);
    Assert.True(conversion.Type.Equals(membership.ToType, keepConstraints: true), diagnostic);
  }

  private static void AssertAdjacentCheckedIntegerSubsetConversions(ContractReductionResult result) {
    AssertCheckedIntegerSubsetConversion(result);
    var diagnostic = DescribeCheckedIntegerSubsetConversions(result);
    var membershipIndices = Enumerable.Range(0, result.ProofObligations.Count).Where(index =>
      result.ProofObligations[index] is {
        Kind: ContractReductionProofKind.Prerequisite,
        Expression: TypeTestExpr { E.Type: IntType } typeTest
      } &&
      typeTest.ToType.NormalizeExpandKeepConstraints().AsSubsetType != null).ToArray();
    var equalityIndices = Enumerable.Range(0, result.ProofObligations.Count).Where(index =>
      result.ProofObligations[index] is {
        Kind: ContractReductionProofKind.Prerequisite,
        Expression: BinaryExpr {
          Op: BinaryExpr.Opcode.Eq,
          E0: ConversionExpr { E.Type: IntType } candidateConversion,
          E1: LiteralExpr
        }
      } &&
      candidateConversion.ToType.NormalizeExpandKeepConstraints().AsSubsetType != null).ToArray();

    Assert.True(membershipIndices.Length > 0, diagnostic);
    Assert.True(equalityIndices.Length > 0, diagnostic);
    Assert.True(membershipIndices.Length == equalityIndices.Length, diagnostic);
    foreach (var membershipIndex in membershipIndices) {
      Assert.True(membershipIndex + 1 < result.ProofObligations.Count, diagnostic);
      var membershipObligation = result.ProofObligations[membershipIndex];
      Assert.Equal(ContractReductionProofKind.Prerequisite, membershipObligation.Kind);
      var membership = Assert.IsType<TypeTestExpr>(membershipObligation.Expression);
      Assert.IsType<IntType>(membership.E.Type);
      Assert.IsType<BoolType>(membership.Type);
      Assert.NotNull(membership.ToType.NormalizeExpandKeepConstraints().AsSubsetType);

      var equalityIndex = membershipIndex + 1;
      Assert.True(equalityIndices.Contains(equalityIndex), diagnostic);
      var equalityObligation = result.ProofObligations[equalityIndex];
      Assert.Equal(ContractReductionProofKind.Prerequisite, equalityObligation.Kind);
      Assert.True(equalityObligation.Expression is BinaryExpr, diagnostic);
      var equality = Assert.IsType<BinaryExpr>(equalityObligation.Expression);
      Assert.Equal(BinaryExpr.Opcode.Eq, equality.Op);
      var conversion = Assert.IsType<ConversionExpr>(equality.E0);
      var literal = Assert.IsType<LiteralExpr>(equality.E1);
      Assert.IsType<IntType>(conversion.E.Type);
      Assert.IsType<BoolType>(equality.Type);
      Assert.True(conversion.ToType.Equals(membership.ToType, keepConstraints: true), diagnostic);
      Assert.True(conversion.Type.Equals(membership.ToType, keepConstraints: true), diagnostic);
      Assert.True(literal.Type.Equals(membership.ToType, keepConstraints: true), diagnostic);
    }

    foreach (var equalityIndex in equalityIndices) {
      Assert.True(equalityIndex > 0, diagnostic);
      Assert.True(membershipIndices.Contains(equalityIndex - 1), diagnostic);
    }
  }

  private static string DescribeCheckedIntegerSubsetConversions(ContractReductionResult result) {
    var options = new DafnyOptions(DafnyOptions.Default);
    var descriptions = result.ProofObligations.Select((obligation, index) => {
      var expression = obligation.Expression;
      var conversion = expression is BinaryExpr { E0: ConversionExpr directConversion }
        ? directConversion
        : index + 1 < result.ProofObligations.Count &&
          result.ProofObligations[index + 1].Expression is BinaryExpr { E0: ConversionExpr adjacentConversion }
            ? adjacentConversion
            : null;
      var carrierType = expression is TypeTestExpr typeTest ? typeTest.E.Type : conversion?.E.Type;
      var targetType = expression is TypeTestExpr membership ? membership.ToType : conversion?.ToType;
      var subsetTarget = targetType?.NormalizeExpandKeepConstraints().AsSubsetType;
      var originalCastOperand = conversion == null
        ? "<none>"
        : Printer.ExprToString(options, conversion.E);
      return $"index={index};kind={obligation.Kind};astNodeClass={expression.GetType().Name};" +
        $"carrierTypeClass={carrierType?.GetType().Name ?? "<none>"};" +
        $"subsetTargetDeclIdentifier={subsetTarget?.FullDafnyName ?? "<none>"};" +
        $"originalCastOperand={originalCastOperand}";
    }).DefaultIfEmpty("index=<none>;kind=<none>;astNodeClass=<none>;carrierTypeClass=<none>;" +
      "subsetTargetDeclIdentifier=<none>;originalCastOperand=<none>");
    return "Checked integer subset conversion certificate diagnostics:\n" + string.Join("\n", descriptions);
  }

  private static string SourceDerivedDigitWidthDeclarations(bool useCast) =>
    "datatype NatParse = NatOk(value:nat) | NatErr " +
    "datatype WidthArg = WidthArg(text:string, tokenIndex:int) " +
    "datatype WidthParse = WidthParse(hasInvalid:bool, invalidText:string, invalidTokenIndex:int, width:nat) " +
    "function IsDigit(ch:char):bool { '0' <= ch <= '9' } " +
    "function DigitValue(ch:char):nat requires IsDigit(ch) { " +
    "((ch as int) - ('0' as int))" + (useCast ? " as nat" : "") + " } " +
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

  private static async Task<ContractReductionResult> Reduce(string source, ContractReductionBudget budget,
    bool composeNativeProof = false, bool unicodeCharacters = false, bool emptyEffectiveScope = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.UnicodeCharacters, unicodeCharacters);
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
    var originalNodes = original.DescendantsAndSelf
      .Select(expression => (Expression: expression, Resolved: expression.Resolved, Type: expression.Type,
        Origin: expression.Origin)).ToArray();
    var originalBindings = original.DescendantsAndSelf.OfType<LetExpr>()
      .SelectMany(let => let.LHSs).Where(pattern => pattern.Var != null)
      .Select(pattern => (Pattern: pattern, Variable: pattern.Var, Type: pattern.Var!.Type)).ToArray();
    var reducer = new ContractExpressionReducer(options, program.DefaultModuleDef, program.SystemModuleManager,
      emptyEffectiveScope ? new VisibilityScope("contract-subset-hidden-test") : null);
    var result = composeNativeProof
      ? reducer.ReduceForNativeProofComposition(original, budget: budget)
      : reducer.Reduce(original, budget: budget);
    Assert.Equal(before, Printer.ExprToString(options, original));
    foreach (var node in originalNodes) {
      Assert.Same(node.Resolved, node.Expression.Resolved);
      Assert.Same(node.Type, node.Expression.Type);
      Assert.Same(node.Origin, node.Expression.Origin);
    }
    foreach (var binding in originalBindings) {
      Assert.Same(binding.Variable, binding.Pattern.Var);
      Assert.Same(binding.Type, binding.Pattern.Var!.Type);
    }
    return result;
  }
}
