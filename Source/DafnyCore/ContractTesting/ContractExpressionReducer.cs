#nullable enable

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// Reduces a resolved contract expression after substituting concrete input facts. The reducer
/// always works on a detached resolved clone and never changes the supplied expression or its
/// declaring callable.
/// </summary>
public sealed class ContractExpressionReducer {
  private readonly DafnyOptions options;
  private readonly ModuleDefinition module;
  private readonly SystemModuleManager systemModuleManager;
  private readonly VisibilityScope effectiveScope;

  public ContractExpressionReducer(
    DafnyOptions options,
    ModuleDefinition module,
    SystemModuleManager systemModuleManager,
    VisibilityScope? effectiveScope = null) {
    this.options = options ?? throw new ArgumentNullException(nameof(options));
    this.module = module ?? throw new ArgumentNullException(nameof(module));
    this.systemModuleManager = systemModuleManager ??
      throw new ArgumentNullException(nameof(systemModuleManager));
    this.effectiveScope = effectiveScope ?? module.VisibilityScope;
  }

  public ContractReductionResult Reduce(
    Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null,
    ContractReductionBudget? budget = null) {
    ArgumentNullException.ThrowIfNull(originalExpression);
    if (!originalExpression.WasResolved() || originalExpression.Type == null) {
      throw new ArgumentException("Contract reduction requires a resolved, typed expression.",
        nameof(originalExpression));
    }

    budget ??= new ContractReductionBudget();
    var originalNodeCount = CountExpressionNodes(originalExpression);
    var substitutionMap = CopyAndValidateSubstitutions(substitutions);
    var substituter = new Substituter(null, substitutionMap, new Dictionary<TypeParameter, Type>(),
      null, systemModuleManager);
    var substitutedExpression = substituter.Substitute(originalExpression);
    var preservedSubstitutedExpression = CloneResolvedExpression(substitutedExpression);
    var substitutedNodeCount = CountExpressionNodes(preservedSubstitutedExpression);

    if (substitutedNodeCount > budget.ExpressionNodeLimit) {
      return CreateResult(originalExpression, preservedSubstitutedExpression, budget,
        [ContractReductionExhaustionReason.ExpressionNodeLimit], 0, originalNodeCount,
        substitutedNodeCount, substitutedNodeCount);
    }

    var workingExpression = CloneResolvedExpression(preservedSubstitutedExpression);
    var quantifierBudget = new QuantifierExpansionBudget(budget.QuantifierInstanceLimit);
    var evaluator = new PartialEvaluatorEngine(options, module, systemModuleManager,
      budget.InlineDepthLimit, effectiveScope, budget.QuantifierInstanceLimit,
      quantifierBudget, emitQuantifierOverflowResidual: true);
    var reducedExpression = evaluator.SimplifyExpression(workingExpression);
    var reducedNodeCount = CountExpressionNodes(reducedExpression);
    var exhaustionReasons = new List<ContractReductionExhaustionReason>();

    if (quantifierBudget.IsExhausted) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.QuantifierInstanceLimit);
    }
    if (evaluator.InlineDepthExhausted) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.InlineDepthLimit);
    }
    if (reducedNodeCount > budget.ExpressionNodeLimit) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.ExpressionNodeLimit);
      reducedExpression = preservedSubstitutedExpression;
      reducedNodeCount = substitutedNodeCount;
    }

    return CreateResult(originalExpression, reducedExpression, budget, exhaustionReasons,
      quantifierBudget.Used, originalNodeCount, substitutedNodeCount, reducedNodeCount);
  }

  private static ContractReductionResult CreateResult(
    Expression originalExpression,
    Expression reducedExpression,
    ContractReductionBudget budget,
    IReadOnlyList<ContractReductionExhaustionReason> exhaustionReasons,
    uint quantifierInstancesUsed,
    uint originalNodeCount,
    uint substitutedNodeCount,
    uint reducedNodeCount) {
    ContractReductionDecision decision;
    if (Expression.IsBoolLiteral(reducedExpression, out var value)) {
      decision = value ? ContractReductionDecision.True : ContractReductionDecision.False;
    } else {
      decision = ContractReductionDecision.Residual;
    }

    return new ContractReductionResult(originalExpression, reducedExpression, decision,
      exhaustionReasons, quantifierInstancesUsed, budget, originalNodeCount,
      substitutedNodeCount, reducedNodeCount);
  }

  private static Dictionary<IVariable, Expression> CopyAndValidateSubstitutions(
    IReadOnlyDictionary<IVariable, Expression>? substitutions) {
    var result = new Dictionary<IVariable, Expression>();
    if (substitutions == null) {
      return result;
    }

    foreach (var (variable, expression) in substitutions) {
      ArgumentNullException.ThrowIfNull(variable);
      ArgumentNullException.ThrowIfNull(expression);
      if (!expression.WasResolved() || expression.Type == null) {
        throw new ArgumentException($"The substitution for '{variable.Name}' must be resolved and typed.",
          nameof(substitutions));
      }
      result.Add(variable, expression);
    }
    return result;
  }

  private static Expression CloneResolvedExpression(Expression expression) {
    return new Cloner(cloneResolvedFields: true).CloneExpr(expression);
  }

  private static uint CountExpressionNodes(Expression expression) {
    var seen = new HashSet<Expression>();
    var pending = new Stack<Expression>();
    pending.Push(expression);
    while (pending.Count > 0) {
      var current = pending.Pop();
      if (!seen.Add(current)) {
        continue;
      }
      foreach (var child in current.SubExpressions) {
        pending.Push(child);
      }
    }
    return checked((uint)seen.Count);
  }
}
