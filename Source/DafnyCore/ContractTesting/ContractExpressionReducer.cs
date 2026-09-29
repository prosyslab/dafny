#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;

namespace Microsoft.Dafny;

/// <summary>
/// Reduces a resolved contract expression after substituting concrete input facts. The reducer
/// always works on a detached resolved clone and never changes the supplied expression or its
/// declaring callable.
/// </summary>
public sealed class ContractExpressionReducer {
  /// <summary>Recognizes resolved values supported by concrete contract reduction.</summary>
  public static bool IsConcreteValue(Expression expression) => PartialEvaluatorEngine.IsContractConcreteValue(expression);

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
    return ReduceCore(originalExpression, substitutions, budget, null, false);
  }

  /// <summary>Reduces and prepares dependency-ordered assertions for native proof composition.</summary>
  public ContractReductionResult ReduceForNativeProofComposition(
    Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null,
    ContractReductionBudget? budget = null) {
    return ReduceCore(originalExpression, substitutions, budget, null, true);
  }

  /// <summary>Reduces with resolved entry/current facts while preserving the original expression.</summary>
  public ContractReductionResult ReduceWithHeap(Expression originalExpression, ContractHeapReductionContext heap,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null, ContractReductionBudget? budget = null) {
    ArgumentNullException.ThrowIfNull(heap);
    return ReduceCore(originalExpression, substitutions, budget, new ContractHeapReductionSession(heap), false);
  }

  private ContractReductionResult ReduceCore(Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions, ContractReductionBudget? budget,
    ContractHeapReductionSession? heap, bool composeNativeProof) {
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
      var reducedResidual = CloneResolvedExpression(preservedSubstitutedExpression);
      return CreateResult(originalExpression, preservedSubstitutedExpression,
        reducedResidual, budget,
        [ContractReductionExhaustionReason.ExpressionNodeLimit], 0, originalNodeCount,
        substitutedNodeCount, substitutedNodeCount, 0);
    }

    var workingExpression = CloneResolvedExpression(preservedSubstitutedExpression);
    var quantifierBudget = new QuantifierExpansionBudget(budget.QuantifierInstanceLimit);
    var expressionExpansionBudget = new ExpressionExpansionBudget(
      budget.ExpressionNodeLimit - substitutedNodeCount);
    var evaluator = new PartialEvaluatorEngine(options, module, systemModuleManager,
      budget.InlineDepthLimit, effectiveScope, budget.QuantifierInstanceLimit,
      quantifierBudget, emitQuantifierOverflowResidual: true,
      PartialEvaluationProfile.ContractConcrete, expressionExpansionBudget, heap,
      collectProofCompositionCandidates: composeNativeProof,
      detectEmptyQuantifierProduct: composeNativeProof,
      proofCompositionMode: composeNativeProof);
    var reducedExpression = evaluator.SimplifyExpression(workingExpression);
    var reducedNodeCount = CountExpressionNodes(reducedExpression);
    var composer = new NativeProofComposer(this, evaluator, budget, quantifierBudget, expressionExpansionBudget);
    if (composeNativeProof && heap == null) {
      composer.Compose(evaluator.ProofCompositionCandidates, evaluator.ProofWitnesses);
    }
    var exhaustionReasons = new List<ContractReductionExhaustionReason>();

    if (quantifierBudget.IsExhausted) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.QuantifierInstanceLimit);
    }
    if (evaluator.InlineDepthExhausted) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.InlineDepthLimit);
    }
    if (evaluator.ExpressionNodeLimitExhausted || reducedNodeCount > budget.ExpressionNodeLimit) {
      exhaustionReasons.Add(ContractReductionExhaustionReason.ExpressionNodeLimit);
      reducedExpression = CloneResolvedExpression(preservedSubstitutedExpression);
      reducedNodeCount = substitutedNodeCount;
    }

    var result = CreateResult(originalExpression, preservedSubstitutedExpression, reducedExpression,
      budget, exhaustionReasons,
      quantifierBudget.Used, originalNodeCount, substitutedNodeCount, reducedNodeCount,
      evaluator.ExpressionExpansionNodesReserved);
    result.HeapReduction = heap?.Statistics;
    result.ProofWitnesses = new List<Expression>(evaluator.ProofWitnesses).AsReadOnly();
    result.ProofObligations = composer.Obligations.AsReadOnly();
    result.ProofCompositionNodesConsidered = composer.NodesConsidered;
    result.ProofCompositionNodesAdmitted = composer.NodesAdmitted;
    return result;
  }

  /// <summary>Stages one reduction's proof obligations and publishes each root's certificate atomically.</summary>
  private sealed class NativeProofComposer {
    private readonly ContractExpressionReducer reducer;
    private readonly PartialEvaluatorEngine evaluator;
    private readonly ContractReductionBudget budget;
    private readonly QuantifierExpansionBudget quantifierBudget;
    private readonly ExpressionExpansionBudget expressionBudget;
    private readonly Dictionary<string, ContractPredicateReductionCandidate> candidatesByKey = new(StringComparer.Ordinal);
    private readonly HashSet<string> activeCandidateKeys = new(StringComparer.Ordinal);
    private readonly Dictionary<string, ProofNodeState> states = new(StringComparer.Ordinal);
    private readonly HashSet<string> admittedPrerequisites = new(StringComparer.Ordinal);

    internal List<ContractReductionProofObligation> Obligations { get; } = new();
    internal uint NodesConsidered { get; private set; }
    internal uint NodesAdmitted { get; private set; }

    internal NativeProofComposer(ContractExpressionReducer reducer, PartialEvaluatorEngine evaluator,
      ContractReductionBudget budget, QuantifierExpansionBudget quantifierBudget, ExpressionExpansionBudget expressionBudget) {
      this.reducer = reducer;
      this.evaluator = evaluator;
      this.budget = budget;
      this.quantifierBudget = quantifierBudget;
      this.expressionBudget = expressionBudget;
    }

    internal void Compose(IReadOnlyList<ContractPredicateReductionCandidate> candidates, IReadOnlyList<Expression> rootWitnesses) {
      foreach (var candidate in candidates) {
        var candidateKey = reducer.ProofExpressionKey(candidate.Call);
        candidatesByKey.TryAdd(candidateKey, candidate);
        activeCandidateKeys.Add(candidateKey);
      }
      var dependencyKeys = new HashSet<string>(StringComparer.Ordinal);
      foreach (var candidate in candidates) {
        foreach (var call in candidate.InstantiatedBody.DescendantsAndSelf.OfType<FunctionCallExpr>()) {
          var dependencyKey = reducer.ProofExpressionKey(call);
          if (activeCandidateKeys.Contains(dependencyKey) && dependencyKey != reducer.ProofExpressionKey(candidate.Call)) {
            dependencyKeys.Add(dependencyKey);
          }
        }
      }
      foreach (var candidate in candidates.Where(candidate => !dependencyKeys.Contains(reducer.ProofExpressionKey(candidate.Call)))) {
        // A nested dependency can be discovered only after earlier witnesses have
        // been staged. Keep their causal order and publish the complete certificate
        // atomically with the parent.
        TryCommit(transaction => TryComposeCandidate(candidate, transaction));
      }
      var emittedExpressions = Obligations.Select(obligation => reducer.ProofExpressionKey(obligation.Expression))
        .ToHashSet(StringComparer.Ordinal);
      foreach (var witness in rootWitnesses) {
        TryCommit(transaction => {
          if (!TryComposeWitnessDependencies(witness, transaction)) {
            return false;
          }
          if (!emittedExpressions.Contains(reducer.ProofExpressionKey(witness))) {
            transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Witness, witness));
          }
          return true;
        }, committed => emittedExpressions.UnionWith(committed.Select(obligation => reducer.ProofExpressionKey(obligation.Expression))));
      }
    }

    private bool TryCommit(Func<ProofTransaction, bool> compose,
      Action<IReadOnlyList<ContractReductionProofObligation>>? onCommit = null) {
      var transaction = new ProofTransaction(admittedPrerequisites);
      if (!compose(transaction)) {
        // Shared budgets are intentionally not rolled back. A staged node cannot stay
        // Complete after its certificate was discarded, or a later parent could reuse
        // a proof that was never emitted.
        foreach (var key in transaction.CompletedKeys) {
          states[key] = ProofNodeState.Failed;
        }
        return false;
      }
      Obligations.AddRange(transaction.Staged);
      admittedPrerequisites.UnionWith(transaction.Prerequisites);
      NodesAdmitted += transaction.NodesAdmitted;
      onCommit?.Invoke(transaction.Staged);
      return true;
    }

    private bool TryComposeCandidate(ContractPredicateReductionCandidate candidate, ProofTransaction transaction) {
      var candidateKey = reducer.ProofExpressionKey(candidate.Call);
      if (states.TryGetValue(candidateKey, out var state)) {
        return state == ProofNodeState.Complete;
      }
      states[candidateKey] = ProofNodeState.Processing;
      NodesConsidered++;
      var dependencyCalls = candidate.InstantiatedBody.DescendantsAndSelf.OfType<FunctionCallExpr>()
        .Select(call => (Call: call, Key: reducer.ProofExpressionKey(call)))
        .Where(dependency => dependency.Key != candidateKey && activeCandidateKeys.Contains(dependency.Key))
        .DistinctBy(dependency => dependency.Key)
        .ToList();
      foreach (var dependency in dependencyCalls) {
        if (!TryComposeCandidate(candidatesByKey[dependency.Key], transaction)) {
          return Fail();
        }
      }

      var completeDependencyKeys = dependencyCalls.Select(dependency => dependency.Key).ToHashSet(StringComparer.Ordinal);
      var stagedPrerequisites = new HashSet<string>(StringComparer.Ordinal);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(candidate.InstantiatedBody, conjuncts);
      foreach (var conjunct in conjuncts) {
        if (Expression.IsBoolLiteral(conjunct, out var value)) {
          if (!value) {
            return Fail();
          }
          continue;
        }
        var prerequisiteKey = reducer.ProofExpressionKey(conjunct);
        if (completeDependencyKeys.Contains(prerequisiteKey) || transaction.Prerequisites.Contains(prerequisiteKey) ||
            !stagedPrerequisites.Add(prerequisiteKey)) {
          continue;
        }
        if (!reducer.IsClosedProofExpression(conjunct) ||
            !reducer.TryReduceProofPrerequisite(conjunct, budget, quantifierBudget, expressionBudget,
              out var prerequisite, out var witnesses)) {
          return Fail();
        }
        foreach (var witness in witnesses) {
          if (!TryComposeWitnessDependencies(witness, transaction)) {
            return Fail();
          }
          transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Witness, witness));
        }
        // A leaf that reduces to true needs no partial-evaluator certificate: the
        // following parent assertion remains the native proof gate. Preserve an
        // explicit prerequisite when checked witness facts are needed to establish it.
        if (witnesses.Count > 0) {
          transaction.Staged.Add(new ContractReductionProofObligation(
            ContractReductionProofKind.Prerequisite, prerequisite));
        }
      }
      if (!TryReserveProofNode(candidate.Call, quantifierBudget, expressionBudget)) {
        return Fail();
      }
      transaction.Staged.Add(new ContractReductionProofObligation(
        ContractReductionProofKind.Predicate, candidate.Call));
      transaction.Prerequisites.UnionWith(stagedPrerequisites);
      transaction.NodesAdmitted++;
      states[candidateKey] = ProofNodeState.Complete;
      transaction.CompletedKeys.Add(candidateKey);
      return true;

      bool Fail() {
        states[candidateKey] = ProofNodeState.Failed;
        return false;
      }
    }

    private bool TryComposeWitnessDependencies(Expression witness, ProofTransaction transaction) {
      var calls = new List<FunctionCallExpr>();
      CollectPositiveConjunctPredicateCalls(witness, calls);
      foreach (var call in calls.DistinctBy(reducer.ProofExpressionKey)) {
        var key = reducer.ProofExpressionKey(call);
        if (!candidatesByKey.TryGetValue(key, out var candidate)) {
          if (!evaluator.TryCreateProofCompositionCandidate(call, out candidate)) {
            continue;
          }
          candidatesByKey.Add(key, candidate);
        }
        activeCandidateKeys.Add(key);
        if (!TryComposeCandidate(candidate, transaction)) {
          return false;
        }
      }
      return true;
    }
  }

  /// <summary>Obligations and prerequisites staged for one root until its certificate is complete.</summary>
  private sealed class ProofTransaction(IEnumerable<string> admittedPrerequisites) {
    internal List<ContractReductionProofObligation> Staged { get; } = new();
    internal HashSet<string> Prerequisites { get; } = new(admittedPrerequisites, StringComparer.Ordinal);
    internal HashSet<string> CompletedKeys { get; } = new(StringComparer.Ordinal);
    internal uint NodesAdmitted { get; set; }
  }

  private static void CollectPositiveConjunctPredicateCalls(Expression expression, List<FunctionCallExpr> calls) {
    expression = NormalizeProofExpression(expression);
    if (expression is FunctionCallExpr { Function: not null } functionCall &&
        functionCall.Type?.NormalizeExpand().IsBoolType == true) {
      calls.Add(functionCall);
      return;
    }
    if (expression is BinaryExpr binary &&
        (binary.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binary.Op == BinaryExpr.Opcode.And)) {
      CollectPositiveConjunctPredicateCalls(binary.E0, calls);
      CollectPositiveConjunctPredicateCalls(binary.E1, calls);
    }
  }

  private enum ProofNodeState {
    Processing,
    Complete,
    Failed
  }

  private bool TryReduceProofPrerequisite(
    Expression expression,
    ContractReductionBudget budget,
    QuantifierExpansionBudget quantifierBudget,
    ExpressionExpansionBudget expressionBudget,
    out Expression prerequisite,
    out IReadOnlyList<Expression> witnesses) {
    prerequisite = CloneResolvedExpression(expression);
    witnesses = Array.Empty<Expression>();
    if (!TryReserveProofNode(prerequisite, quantifierBudget, expressionBudget)) {
      return false;
    }
    var working = CloneResolvedExpression(prerequisite);
    if (!expressionBudget.TryReserve(working)) {
      return false;
    }
    var evaluator = new PartialEvaluatorEngine(options, module, systemModuleManager,
      budget.InlineDepthLimit, effectiveScope, budget.QuantifierInstanceLimit,
      quantifierBudget, emitQuantifierOverflowResidual: true,
      PartialEvaluationProfile.ContractConcrete, expressionBudget,
      detectEmptyQuantifierProduct: true,
      proofCompositionMode: true);
    var reduced = evaluator.SimplifyExpression(working);
    if (evaluator.ExpressionNodeLimitExhausted ||
        !Expression.IsBoolLiteral(reduced, out var value) || !value) {
      return false;
    }
    if (evaluator.ProofWitnesses.Any(witness => !IsClosedProofExpression(witness))) {
      return false;
    }
    witnesses = new List<Expression>(evaluator.ProofWitnesses).AsReadOnly();
    return true;
  }

  private static bool TryReserveProofNode(Expression expression,
    QuantifierExpansionBudget quantifierBudget, ExpressionExpansionBudget expressionBudget) {
    if (quantifierBudget.Remaining == 0) {
      quantifierBudget.MarkExhausted();
      return false;
    }
    if (!expressionBudget.TryReserve(expression)) {
      return false;
    }
    quantifierBudget.ConsumeInstance();
    return true;
  }

  private bool IsClosedProofExpression(Expression expression) =>
    PartialEvaluatorEngine.IsClosedProofExpression(options, expression);

  private string ProofExpressionKey(Expression expression) {
    expression = NormalizeProofExpression(expression);
    var declaration = expression is FunctionCallExpr functionCall && functionCall.Function != null
      ? RuntimeHelpers.GetHashCode(functionCall.Function).ToString()
      : "expression";
    return declaration + ":" + Printer.ExprToString(options, expression);
  }

  private static Expression NormalizeProofExpression(Expression expression) {
    while (true) {
      if (expression.Resolved != null && !ReferenceEquals(expression.Resolved, expression)) {
        expression = expression.Resolved;
        continue;
      }
      var normalized = QuantifierBounds.NormalizeForPattern(expression);
      if (ReferenceEquals(normalized, expression)) {
        return expression;
      }
      expression = normalized;
    }
  }

  private static ContractReductionResult CreateResult(
    Expression originalExpression,
    Expression substitutedExpression,
    Expression reducedExpression,
    ContractReductionBudget budget,
    IReadOnlyList<ContractReductionExhaustionReason> exhaustionReasons,
    uint quantifierInstancesUsed,
    uint originalNodeCount,
    uint substitutedNodeCount,
    uint reducedNodeCount,
    uint expressionExpansionNodeCount) {
    ContractReductionDecision decision;
    if (Expression.IsBoolLiteral(reducedExpression, out var value)) {
      decision = value ? ContractReductionDecision.True : ContractReductionDecision.False;
    } else {
      decision = ContractReductionDecision.Residual;
    }

    return new ContractReductionResult(originalExpression, substitutedExpression, reducedExpression, decision,
      exhaustionReasons, quantifierInstancesUsed, budget, originalNodeCount,
      substitutedNodeCount, reducedNodeCount, expressionExpansionNodeCount);
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
