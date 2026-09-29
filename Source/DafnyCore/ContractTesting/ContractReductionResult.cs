#nullable enable

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public enum ContractReductionDecision {
  True,
  False,
  Residual
}

public enum ContractReductionResidualKind {
  None,
  RequiresSolver,
  BudgetExhausted
}

public enum ContractReductionExhaustionReason {
  QuantifierInstanceLimit,
  InlineDepthLimit,
  ExpressionNodeLimit
}

/// <summary>Describes why a native proof-composition assertion was emitted.</summary>
public enum ContractReductionProofKind {
  Witness,
  Prerequisite,
  Predicate
}

/// <summary>An ordered expression that native verification must prove before the original target.</summary>
public sealed class ContractReductionProofObligation {
  public ContractReductionProofKind Kind { get; }
  public Expression Expression { get; }

  internal ContractReductionProofObligation(ContractReductionProofKind kind, Expression expression) {
    Kind = kind;
    Expression = expression;
  }
}

/// <summary>
/// Independent limits for reducing one resolved contract expression. Quantifier instances are
/// counted cumulatively across all quantifiers in the expression.
/// </summary>
public sealed class ContractReductionBudget {
  public const uint DefaultQuantifierInstanceLimit = 100;
  public const uint DefaultInlineDepthLimit = 2;
  public const uint DefaultExpressionNodeLimit = 10_000;

  public uint QuantifierInstanceLimit { get; }
  public uint InlineDepthLimit { get; }
  public uint ExpressionNodeLimit { get; }

  public ContractReductionBudget(
    uint quantifierInstanceLimit = DefaultQuantifierInstanceLimit,
    uint inlineDepthLimit = DefaultInlineDepthLimit,
    uint expressionNodeLimit = DefaultExpressionNodeLimit) {
    if (quantifierInstanceLimit == 0) {
      throw new ArgumentOutOfRangeException(nameof(quantifierInstanceLimit),
        "The quantifier instance limit must be positive.");
    }
    if (expressionNodeLimit == 0) {
      throw new ArgumentOutOfRangeException(nameof(expressionNodeLimit),
        "The expression node limit must be positive.");
    }

    QuantifierInstanceLimit = quantifierInstanceLimit;
    InlineDepthLimit = inlineDepthLimit;
    ExpressionNodeLimit = expressionNodeLimit;
  }
}

/// <summary>
/// The result of reducing a detached copy of a resolved contract expression.
/// </summary>
public sealed class ContractReductionResult {
  /// <summary>Concrete existential instances that require independent native proof before use.</summary>
  public IReadOnlyList<Expression> ProofWitnesses { get; internal set; } = Array.Empty<Expression>();
  /// <summary>Dependency-ordered assertions for the opt-in native proof-composition path.</summary>
  public IReadOnlyList<ContractReductionProofObligation> ProofObligations { get; internal set; } =
    Array.Empty<ContractReductionProofObligation>();
  public uint ProofCompositionNodesConsidered { get; internal set; }
  public uint ProofCompositionNodesAdmitted { get; internal set; }
  public ContractHeapReductionStatistics? HeapReduction { get; internal set; }
  public Expression OriginalExpression { get; }
  public Expression SubstitutedExpression { get; }
  public Expression ReducedExpression { get; }
  public Expression? ResidualExpression => Decision == ContractReductionDecision.Residual
    ? ReducedExpression
    : null;
  public ContractReductionDecision Decision { get; }
  public ContractReductionResidualKind ResidualKind { get; }
  public IReadOnlyList<ContractReductionExhaustionReason> ExhaustionReasons { get; }
  public bool HasResidual => Decision == ContractReductionDecision.Residual;
  public bool BudgetExhausted => ExhaustionReasons.Count > 0;
  public uint QuantifierInstancesUsed { get; }
  public uint QuantifierInstanceLimit { get; }
  public uint InlineDepthLimit { get; }
  public uint OriginalExpressionNodeCount { get; }
  public uint SubstitutedExpressionNodeCount { get; }
  public uint ReducedExpressionNodeCount { get; }
  public uint ExpressionExpansionNodeCount { get; }

  internal ContractReductionResult(
    Expression originalExpression,
    Expression substitutedExpression,
    Expression reducedExpression,
    ContractReductionDecision decision,
    IReadOnlyList<ContractReductionExhaustionReason> exhaustionReasons,
    uint quantifierInstancesUsed,
    ContractReductionBudget budget,
    uint originalExpressionNodeCount,
    uint substitutedExpressionNodeCount,
    uint reducedExpressionNodeCount,
    uint expressionExpansionNodeCount) {
    OriginalExpression = originalExpression;
    SubstitutedExpression = substitutedExpression;
    ReducedExpression = reducedExpression;
    Decision = decision;
    ExhaustionReasons = new List<ContractReductionExhaustionReason>(exhaustionReasons).AsReadOnly();
    QuantifierInstancesUsed = quantifierInstancesUsed;
    QuantifierInstanceLimit = budget.QuantifierInstanceLimit;
    InlineDepthLimit = budget.InlineDepthLimit;
    OriginalExpressionNodeCount = originalExpressionNodeCount;
    SubstitutedExpressionNodeCount = substitutedExpressionNodeCount;
    ReducedExpressionNodeCount = reducedExpressionNodeCount;
    ExpressionExpansionNodeCount = expressionExpansionNodeCount;
    ResidualKind = decision != ContractReductionDecision.Residual
      ? ContractReductionResidualKind.None
      : exhaustionReasons.Count > 0
        ? ContractReductionResidualKind.BudgetExhausted
        : ContractReductionResidualKind.RequiresSolver;
  }
}
