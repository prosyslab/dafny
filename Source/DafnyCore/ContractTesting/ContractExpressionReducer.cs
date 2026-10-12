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
  public static bool IsConcreteValue(Expression expression) => IsConcreteValue(expression, null);

  /// <summary>Recognizes concrete resolved values while checking each recursive traversal step.</summary>
  public static bool IsConcreteValue(Expression expression, Action? cancellationCheck) =>
    PartialEvaluatorEngine.IsContractConcreteValue(expression, cancellationCheck);

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
    if (effectiveScope != null) {
      this.effectiveScope = effectiveScope;
    } else {
      // A module's resolved signature always includes the implicit system imports.
      this.effectiveScope = new VisibilityScope();
      this.effectiveScope.Augment(module.VisibilityScope);
      this.effectiveScope.Augment(systemModuleManager.systemNameInfo.VisibilityScope);
    }
  }

  public ContractReductionResult Reduce(
    Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null,
    ContractReductionBudget? budget = null,
    Action? cancellationCheck = null) {
    return ReduceCore(originalExpression, substitutions, budget, null, false, cancellationCheck);
  }

  /// <summary>Reduces and prepares dependency-ordered assertions for native proof composition.</summary>
  public ContractReductionResult ReduceForNativeProofComposition(
    Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null,
    ContractReductionBudget? budget = null,
    Action? cancellationCheck = null) {
    return ReduceCore(originalExpression, substitutions, budget, null, true, cancellationCheck);
  }

  /// <summary>Reduces with resolved entry/current facts while preserving the original expression.</summary>
  public ContractReductionResult ReduceWithHeap(Expression originalExpression, ContractHeapReductionContext heap,
    IReadOnlyDictionary<IVariable, Expression>? substitutions = null, ContractReductionBudget? budget = null,
    Action? cancellationCheck = null) {
    ArgumentNullException.ThrowIfNull(heap);
    return ReduceCore(originalExpression, substitutions, budget, new ContractHeapReductionSession(heap), false,
      cancellationCheck);
  }

  /// <summary>Projects captured heaps and prepares checked proof steps only for heap-independent expressions.</summary>
  public ContractReductionResult ReduceWithHeapForNativeProofComposition(Expression originalExpression,
    ContractHeapReductionContext heap, IReadOnlyDictionary<IVariable, Expression>? substitutions = null,
    ContractReductionBudget? budget = null, Action? cancellationCheck = null) {
    ArgumentNullException.ThrowIfNull(heap);
    return ReduceCore(originalExpression, substitutions, budget, new ContractHeapReductionSession(heap), true,
      cancellationCheck);
  }

  private ContractReductionResult ReduceCore(Expression originalExpression,
    IReadOnlyDictionary<IVariable, Expression>? substitutions, ContractReductionBudget? budget,
    ContractHeapReductionSession? heap, bool composeNativeProof, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    ArgumentNullException.ThrowIfNull(originalExpression);
    if (!originalExpression.WasResolved() || originalExpression.Type == null) {
      throw new ArgumentException("Contract reduction requires a resolved, typed expression.",
        nameof(originalExpression));
    }

    budget ??= new ContractReductionBudget();
    var originalNodeCount = CountExpressionNodes(originalExpression, cancellationCheck);
    var substitutionMap = CopyAndValidateSubstitutions(substitutions, cancellationCheck);
    var substituter = new ContractReductionSubstituter(null, substitutionMap,
      new Dictionary<TypeParameter, Type>(), null, systemModuleManager, cancellationCheck);
    var substitutedExpression = substituter.Substitute(originalExpression);
    var preservedSubstitutedExpression = CloneResolvedExpression(substitutedExpression, cancellationCheck);
    var substitutedNodeCount = CountExpressionNodes(preservedSubstitutedExpression, cancellationCheck);

    if (substitutedNodeCount > budget.ExpressionNodeLimit) {
      var reducedResidual = CloneResolvedExpression(preservedSubstitutedExpression, cancellationCheck);
      var residualResult = CreateResult(originalExpression, preservedSubstitutedExpression,
        reducedResidual, budget,
        [ContractReductionExhaustionReason.ExpressionNodeLimit], 0, originalNodeCount,
        substitutedNodeCount, substitutedNodeCount, 0);
      cancellationCheck?.Invoke();
      return residualResult;
    }

    var workingExpression = CloneResolvedExpression(preservedSubstitutedExpression, cancellationCheck);
    var quantifierBudget = new QuantifierExpansionBudget(budget.QuantifierInstanceLimit);
    var expressionExpansionBudget = new ExpressionExpansionBudget(
      budget.ExpressionNodeLimit - substitutedNodeCount, cancellationCheck);
    var evaluator = new PartialEvaluatorEngine(options, module, systemModuleManager,
      budget.InlineDepthLimit, effectiveScope, budget.QuantifierInstanceLimit,
      quantifierBudget, emitQuantifierOverflowResidual: true,
      PartialEvaluationProfile.ContractConcrete, expressionExpansionBudget, heap,
      collectProofCompositionCandidates: composeNativeProof,
      detectEmptyQuantifierProduct: composeNativeProof,
      proofCompositionMode: composeNativeProof,
      cancellationCheck: cancellationCheck);
    var reducedExpression = evaluator.SimplifyExpression(workingExpression);
    var reducedNodeCount = CountExpressionNodes(reducedExpression, cancellationCheck);
    var composer = new NativeProofComposer(this, evaluator, budget, quantifierBudget, expressionExpansionBudget,
      cancellationCheck);
    if (composeNativeProof) {
      composer.Compose(evaluator.ProofCompositionCandidates, evaluator.ProofWitnesses, evaluator.ProofPrerequisites,
        evaluator.ProofConcreteCalls);
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
      reducedExpression = CloneResolvedExpression(preservedSubstitutedExpression, cancellationCheck);
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
    cancellationCheck?.Invoke();
    return result;
  }

  /// <summary>Stages one reduction's proof obligations and publishes each root's certificate atomically.</summary>
  private sealed class NativeProofComposer {
    private readonly ContractExpressionReducer reducer;
    private readonly PartialEvaluatorEngine evaluator;
    private readonly ContractReductionBudget budget;
    private readonly QuantifierExpansionBudget quantifierBudget;
    private readonly ExpressionExpansionBudget expressionBudget;
    private readonly Action? cancellationCheck;
    private readonly Dictionary<string, ContractPredicateReductionCandidate> candidatesByKey = new(StringComparer.Ordinal);
    private readonly HashSet<string> activeCandidateKeys = new(StringComparer.Ordinal);
    private readonly Dictionary<string, ProofNodeState> states = new(StringComparer.Ordinal);
    private readonly HashSet<string> admittedPrerequisites = new(StringComparer.Ordinal);
    private readonly HashSet<ContractConcreteCallProof> admittedConcreteCalls = new(ReferenceEqualityComparer.Instance);

    internal List<ContractReductionProofObligation> Obligations { get; } = new();
    internal uint NodesConsidered { get; private set; }
    internal uint NodesAdmitted { get; private set; }

    internal NativeProofComposer(ContractExpressionReducer reducer, PartialEvaluatorEngine evaluator,
      ContractReductionBudget budget, QuantifierExpansionBudget quantifierBudget,
      ExpressionExpansionBudget expressionBudget, Action? cancellationCheck) {
      this.reducer = reducer;
      this.evaluator = evaluator;
      this.budget = budget;
      this.quantifierBudget = quantifierBudget;
      this.expressionBudget = expressionBudget;
      this.cancellationCheck = cancellationCheck;
    }

    internal void Compose(IReadOnlyList<ContractPredicateReductionCandidate> candidates, IReadOnlyList<Expression> rootWitnesses,
      IReadOnlyList<Expression> prerequisites, IReadOnlyList<ContractConcreteCallProof> concreteCalls) {
      foreach (var call in concreteCalls) {
        cancellationCheck?.Invoke();
        TryCommit(transaction => TryComposeConcreteCall(call, transaction));
      }
      // The evaluator emits ordered certificate transactions. Deduplicating individual
      // expressions here can remove one half of a later certificate pair.
      foreach (var prerequisite in prerequisites) {
        cancellationCheck?.Invoke();
        Obligations.Add(new ContractReductionProofObligation(ContractReductionProofKind.Prerequisite, prerequisite));
      }
      foreach (var candidate in candidates) {
        cancellationCheck?.Invoke();
        var candidateKey = ProofExpressionKey(candidate.Call);
        candidatesByKey.TryAdd(candidateKey, candidate);
        activeCandidateKeys.Add(candidateKey);
      }
      var dependencyKeys = new HashSet<string>(StringComparer.Ordinal);
      foreach (var candidate in candidates) {
        cancellationCheck?.Invoke();
        foreach (var call in ContractReductionTraversal.LogicalNodes(candidate.InstantiatedBody, cancellationCheck).OfType<FunctionCallExpr>()) {
          cancellationCheck?.Invoke();
          var dependencyKey = ProofExpressionKey(call);
          if (activeCandidateKeys.Contains(dependencyKey) && dependencyKey != ProofExpressionKey(candidate.Call)) {
            dependencyKeys.Add(dependencyKey);
          }
        }
      }
      foreach (var candidate in candidates.Where(candidate => !dependencyKeys.Contains(ProofExpressionKey(candidate.Call)))) {
        cancellationCheck?.Invoke();
        // A nested dependency can be discovered only after earlier witnesses have
        // been staged. Keep their causal order and publish the complete certificate
        // atomically with the parent.
        TryCommit(transaction => TryComposeCandidate(candidate, transaction));
      }
      var emittedExpressions = Obligations.Select(obligation => ProofExpressionKey(obligation.Expression))
        .ToHashSet(StringComparer.Ordinal);
      foreach (var witness in rootWitnesses) {
        cancellationCheck?.Invoke();
        TryCommit(transaction => {
          if (!TryComposeWitnessDependencies(witness, transaction)) {
            return false;
          }
          if (!emittedExpressions.Contains(ProofExpressionKey(witness))) {
            transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Witness, witness));
          }
          return true;
        }, committed => emittedExpressions.UnionWith(committed.Select(obligation => ProofExpressionKey(obligation.Expression))));
      }
    }

    private bool TryCommit(Func<ProofTransaction, bool> compose,
      Action<IReadOnlyList<ContractReductionProofObligation>>? onCommit = null) {
      var transaction = new ProofTransaction(admittedPrerequisites);
      cancellationCheck?.Invoke();
      if (!compose(transaction)) {
        // Shared budgets are intentionally not rolled back. A staged node cannot stay
        // Complete after its certificate was discarded, or a later parent could reuse
        // a proof that was never emitted.
        foreach (var key in transaction.CompletedKeys) {
          cancellationCheck?.Invoke();
          states[key] = ProofNodeState.Failed;
        }
        return false;
      }
      cancellationCheck?.Invoke();
      Obligations.AddRange(transaction.Staged);
      admittedPrerequisites.UnionWith(transaction.Prerequisites);
      admittedConcreteCalls.UnionWith(transaction.ConcreteCalls);
      NodesAdmitted += transaction.NodesAdmitted;
      onCommit?.Invoke(transaction.Staged);
      return true;
    }

    private bool TryComposeConcreteCall(ContractConcreteCallProof proof, ProofTransaction transaction) {
      cancellationCheck?.Invoke();
      if (admittedConcreteCalls.Contains(proof) || transaction.ConcreteCalls.Contains(proof)) { return true; }
      NodesConsidered++;
      foreach (var dependency in proof.Dependencies) {
        cancellationCheck?.Invoke();
        if (!TryComposeConcreteCall(dependency, transaction)) { return false; }
      }
      foreach (var prerequisite in proof.Prerequisites) {
        cancellationCheck?.Invoke();
        if (!reducer.IsClosedProofExpression(prerequisite, cancellationCheck)) { return false; }
        if (!Expression.IsBoolLiteral(prerequisite, out var holds) || !holds) {
          transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Prerequisite, prerequisite));
        }
      }
      foreach (var witness in proof.Witnesses) {
        cancellationCheck?.Invoke();
        if (!reducer.IsClosedProofExpression(witness, cancellationCheck)) { return false; }
        transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Witness, witness));
      }
      if (!TryReserveProofNode(proof.Equality, quantifierBudget, expressionBudget)) { return false; }
      transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Prerequisite, proof.Equality));
      transaction.ConcreteCalls.Add(proof);
      transaction.NodesAdmitted++;
      return true;
    }

    private bool TryComposeCandidate(ContractPredicateReductionCandidate candidate, ProofTransaction transaction) {
      cancellationCheck?.Invoke();
      var candidateKey = ProofExpressionKey(candidate.Call);
      if (states.TryGetValue(candidateKey, out var state)) {
        return state == ProofNodeState.Complete;
      }
      states[candidateKey] = ProofNodeState.Processing;
      NodesConsidered++;
      var dependencyCalls = ContractReductionTraversal.LogicalNodes(candidate.InstantiatedBody, cancellationCheck).OfType<FunctionCallExpr>()
        .Select(call => (Call: call, Key: ProofExpressionKey(call)))
        .Where(dependency => dependency.Key != candidateKey && activeCandidateKeys.Contains(dependency.Key))
        .DistinctBy(dependency => dependency.Key)
        .ToList();
      foreach (var dependency in dependencyCalls) {
        cancellationCheck?.Invoke();
        if (!TryComposeCandidate(candidatesByKey[dependency.Key], transaction)) {
          return Fail();
        }
      }

      var completeDependencyKeys = dependencyCalls.Select(dependency => dependency.Key).ToHashSet(StringComparer.Ordinal);
      var stagedPrerequisites = new HashSet<string>(StringComparer.Ordinal);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(candidate.InstantiatedBody, conjuncts, cancellationCheck);
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        if (Expression.IsBoolLiteral(conjunct, out var value)) {
          if (!value) {
            return Fail();
          }
          continue;
        }
        var prerequisiteKey = ProofExpressionKey(conjunct);
        if (completeDependencyKeys.Contains(prerequisiteKey) || transaction.Prerequisites.Contains(prerequisiteKey) ||
            !stagedPrerequisites.Add(prerequisiteKey)) {
          continue;
        }
        if (!reducer.IsClosedProofExpression(conjunct, cancellationCheck) ||
            !reducer.TryReduceProofPrerequisite(conjunct, budget, quantifierBudget, expressionBudget,
              evaluator.IsExplicitlyRevealed,
              cancellationCheck,
              out var prerequisite, out var witnesses, out var implications, out var concreteCalls)) {
          return Fail();
        }
        foreach (var call in concreteCalls) {
          cancellationCheck?.Invoke();
          if (!TryComposeConcreteCall(call, transaction)) { return Fail(); }
        }
        foreach (var implication in implications) {
          cancellationCheck?.Invoke();
          transaction.Staged.Add(new ContractReductionProofObligation(ContractReductionProofKind.Prerequisite, implication));
        }
        foreach (var witness in witnesses) {
          cancellationCheck?.Invoke();
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
      cancellationCheck?.Invoke();
      var calls = new List<FunctionCallExpr>();
      CollectPositiveConjunctPredicateCalls(witness, calls, cancellationCheck);
      foreach (var call in calls.DistinctBy(ProofExpressionKey)) {
        cancellationCheck?.Invoke();
        var key = ProofExpressionKey(call);
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

    private string ProofExpressionKey(Expression expression) {
      cancellationCheck?.Invoke();
      var key = reducer.ProofExpressionKey(expression, cancellationCheck);
      cancellationCheck?.Invoke();
      return key;
    }
  }

  /// <summary>Obligations and prerequisites staged for one root until its certificate is complete.</summary>
  private sealed class ProofTransaction(IEnumerable<string> admittedPrerequisites) {
    internal List<ContractReductionProofObligation> Staged { get; } = new();
    internal HashSet<string> Prerequisites { get; } = new(admittedPrerequisites, StringComparer.Ordinal);
    internal HashSet<string> CompletedKeys { get; } = new(StringComparer.Ordinal);
    internal HashSet<ContractConcreteCallProof> ConcreteCalls { get; } = new(ReferenceEqualityComparer.Instance);
    internal uint NodesAdmitted { get; set; }
  }

  private static void CollectPositiveConjunctPredicateCalls(Expression expression, List<FunctionCallExpr> calls,
    Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    expression = NormalizeProofExpression(expression, cancellationCheck);
    if (expression is FunctionCallExpr { Function: not null } functionCall &&
        functionCall.Type?.NormalizeExpand().IsBoolType == true) {
      calls.Add(functionCall);
      return;
    }
    if (expression is BinaryExpr binary &&
        (binary.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binary.Op == BinaryExpr.Opcode.And)) {
      CollectPositiveConjunctPredicateCalls(binary.E0, calls, cancellationCheck);
      CollectPositiveConjunctPredicateCalls(binary.E1, calls, cancellationCheck);
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
    Func<Function, bool> isExplicitlyRevealed,
    Action? cancellationCheck,
    out Expression prerequisite,
    out IReadOnlyList<Expression> witnesses,
    out IReadOnlyList<Expression> implications,
    out IReadOnlyList<ContractConcreteCallProof> concreteCalls) {
    cancellationCheck?.Invoke();
    prerequisite = CloneResolvedExpression(expression, cancellationCheck);
    witnesses = Array.Empty<Expression>();
    implications = Array.Empty<Expression>();
    concreteCalls = Array.Empty<ContractConcreteCallProof>();
    if (!TryReserveProofNode(prerequisite, quantifierBudget, expressionBudget)) {
      return false;
    }
    var working = CloneResolvedExpression(prerequisite, cancellationCheck);
    if (!expressionBudget.TryReserve(working)) {
      return false;
    }
    var evaluator = new PartialEvaluatorEngine(options, module, systemModuleManager,
      budget.InlineDepthLimit, effectiveScope, budget.QuantifierInstanceLimit,
      quantifierBudget, emitQuantifierOverflowResidual: true,
      PartialEvaluationProfile.ContractConcrete, expressionBudget,
      detectEmptyQuantifierProduct: true,
      proofCompositionMode: true, isExplicitlyRevealed: isExplicitlyRevealed,
      cancellationCheck: cancellationCheck);
    var reduced = evaluator.SimplifyExpression(working);
    if (evaluator.ExpressionNodeLimitExhausted ||
        !Expression.IsBoolLiteral(reduced, out var value) || !value) {
      return false;
    }
    if (evaluator.ProofWitnesses.Any(witness => !IsClosedProofExpression(witness, cancellationCheck))) {
      return false;
    }
    witnesses = new List<Expression>(evaluator.ProofWitnesses).AsReadOnly();
    implications = new List<Expression>(evaluator.ProofPrerequisites).AsReadOnly();
    concreteCalls = evaluator.ProofConcreteCalls.ToArray();
    cancellationCheck?.Invoke();
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

  private bool IsClosedProofExpression(Expression expression, Action? cancellationCheck) =>
    PartialEvaluatorEngine.IsClosedProofExpression(options, expression, cancellationCheck);

  private string ProofExpressionKey(Expression expression, Action? cancellationCheck) {
    expression = NormalizeProofExpression(expression, cancellationCheck);
    var declaration = expression is FunctionCallExpr functionCall && functionCall.Function != null
      ? RuntimeHelpers.GetHashCode(functionCall.Function).ToString()
      : "expression";
    var result = declaration + ":" + ContractReductionTraversal.PrintExpression(options, expression, cancellationCheck);
    return result;
  }

  private static Expression NormalizeProofExpression(Expression expression, Action? cancellationCheck) {
    while (true) {
      cancellationCheck?.Invoke();
      if (expression.Resolved != null && !ReferenceEquals(expression.Resolved, expression)) {
        expression = expression.Resolved;
        continue;
      }
      var normalized = QuantifierBounds.NormalizeForPattern(expression, cancellationCheck);
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
    IReadOnlyDictionary<IVariable, Expression>? substitutions, Action? cancellationCheck) {
    var result = new Dictionary<IVariable, Expression>();
    if (substitutions == null) {
      return result;
    }

    foreach (var (variable, expression) in substitutions) {
      cancellationCheck?.Invoke();
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

  private static Expression CloneResolvedExpression(Expression expression, Action? cancellationCheck) {
    return new ContractReductionCloner(cancellationCheck).CloneExpr(expression);
  }

  private static uint CountExpressionNodes(Expression expression, Action? cancellationCheck) {
    var seen = new HashSet<Expression>();
    var pending = new Stack<Expression>();
    pending.Push(expression);
    while (pending.Count > 0) {
      cancellationCheck?.Invoke();
      var current = pending.Pop();
      if (!seen.Add(current)) {
        continue;
      }
      foreach (var child in current.SubExpressions) {
        cancellationCheck?.Invoke();
        pending.Push(child);
      }
    }
    return checked((uint)seen.Count);
  }
}
