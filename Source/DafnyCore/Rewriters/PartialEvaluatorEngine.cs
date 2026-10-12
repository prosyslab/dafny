using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

namespace Microsoft.Dafny;

internal enum PartialEvaluationProfile {
  Default,
  ContractConcrete
}

internal sealed class ContractPredicateReductionCandidate {
  internal Expression Call { get; }
  internal Expression InstantiatedBody { get; }
  internal Expression ReducedBody { get; }

  internal ContractPredicateReductionCandidate(Expression call, Expression instantiatedBody, Expression reducedBody) {
    Call = call;
    InstantiatedBody = instantiatedBody;
    ReducedBody = reducedBody;
  }
}

// An immutable calculation certificate is separate from the transaction that emits its assertions.
internal sealed record ContractConcreteCallProof(
  Expression Value, IReadOnlyList<ContractConcreteCallProof> Dependencies,
  IReadOnlyList<Expression> Prerequisites, IReadOnlyList<Expression> Witnesses, Expression Equality);

internal sealed class ExpressionExpansionBudget {
  private readonly uint limit;
  private readonly Action cancellationCheck;

  internal uint Used { get; private set; }
  internal bool IsExhausted { get; private set; }

  internal ExpressionExpansionBudget(uint limit, Action cancellationCheck = null) {
    this.limit = limit;
    this.cancellationCheck = cancellationCheck;
  }

  internal bool TryReserve(Expression expression) {
    cancellationCheck?.Invoke();
    return TryReserveNodeCount(CountExpressionNodes(expression));
  }

  internal bool TryReserveSubstitution(Expression template,
    IReadOnlyDictionary<IVariable, Expression> substitutions, Expression receiver = null) {
    // Count occurrences rather than multiplying unrelated arguments into every node.
    // Traversing shared template subtrees at each use conservatively covers copies
    // made by Substituter; replacement expressions themselves are shared resolved ASTs.
    var sizes = new Dictionary<Expression, uint>();
    var pending = new Stack<Expression>();
    pending.Push(template);
    ulong upperBound = 0;
    while (pending.Count > 0) {
      cancellationCheck?.Invoke();
      var current = pending.Pop();
      Expression replacement = null;
      if (current is IdentifierExpr identifier) {
        substitutions.TryGetValue(identifier.Var, out replacement);
      } else if (current is ThisExpr) {
        replacement = receiver;
      }
      if (replacement != null) {
        if (!sizes.TryGetValue(replacement, out var size)) {
          size = CountExpressionNodes(replacement);
          sizes.Add(replacement, size);
        }
        upperBound += size;
      } else {
        upperBound++;
        foreach (var child in current.SubExpressions) {
          cancellationCheck?.Invoke();
          pending.Push(child);
        }
      }
      if (upperBound > limit - Used) {
        IsExhausted = true;
        return false;
      }
    }
    return TryReserveNodeCount((uint)upperBound);
  }

  private bool TryReserveNodeCount(uint nodeCount) {
    cancellationCheck?.Invoke();
    if (nodeCount > limit - Used) {
      IsExhausted = true;
      return false;
    }
    Used += nodeCount;
    return true;
  }

  private uint CountExpressionNodes(Expression expression) {
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

internal sealed partial class PartialEvaluatorEngine {
  private const uint DefaultPartialEvalUnrollCap = 100;
  private readonly DafnyOptions options;
  private readonly ModuleDefinition module;
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint inlineDepth;
  private readonly VisibilityScope effectiveScope;
  private readonly uint? quantifierUnrollCapOverride;
  private readonly QuantifierExpansionBudget quantifierExpansionBudget;
  private readonly bool emitQuantifierOverflowResidual;
  private readonly PartialEvaluationProfile evaluationProfile;
  private readonly ExpressionExpansionBudget expressionExpansionBudget;
  private readonly HelperFunctionInterpreter helperInterpreter;
  private readonly ContractHeapReductionSession heapReduction;
  private readonly bool collectProofCompositionCandidates;
  private readonly bool detectEmptyQuantifierProduct;
  private readonly bool proofCompositionMode;
  private readonly Func<Function, bool> isExplicitlyRevealed;
  private readonly ConcreteCallSession concreteCallSession;
  private readonly bool concreteCallBody;
  private readonly Action cancellationCheck;
  private readonly Dictionary<string, CachedLiteral> inlineCallCache = new(StringComparer.Ordinal);
  private readonly Dictionary<DatatypeCtor, uint> contractConcreteConstructorIds = new();
  private uint nextContractConcreteConstructorId;
  private QuantifierBounds quantifierBounds;

  internal HelperFunctionInterpreter HelperInterpreter => helperInterpreter;
  internal bool InlineDepthExhausted { get; private set; }
  internal bool UsesContractConcreteProfile => evaluationProfile == PartialEvaluationProfile.ContractConcrete;
  internal bool ExpressionNodeLimitExhausted => expressionExpansionBudget?.IsExhausted ?? false;
  internal uint ExpressionExpansionNodesReserved => expressionExpansionBudget?.Used ?? 0;
  internal List<Expression> ProofWitnesses { get; } = new();
  internal List<Expression> ProofPrerequisites { get; } = new();
  internal List<ContractPredicateReductionCandidate> ProofCompositionCandidates { get; } = new();
  internal List<ContractConcreteCallProof> ProofConcreteCalls { get; } = new();

  // ------------------- Construction and entry points -------------------

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth)
    : this(options, module, systemModuleManager, inlineDepth, null, null, null, false) {
  }

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth, VisibilityScope effectiveScope = null)
    : this(options, module, systemModuleManager, inlineDepth, effectiveScope, null, null, false) {
  }

  internal PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module,
    SystemModuleManager systemModuleManager, uint inlineDepth, VisibilityScope effectiveScope,
    uint? quantifierUnrollCap, QuantifierExpansionBudget quantifierExpansionBudget,
    bool emitQuantifierOverflowResidual,
    PartialEvaluationProfile evaluationProfile = PartialEvaluationProfile.Default,
    ExpressionExpansionBudget expressionExpansionBudget = null, ContractHeapReductionSession heapReduction = null,
    bool collectProofCompositionCandidates = false, bool detectEmptyQuantifierProduct = false,
    bool proofCompositionMode = false, Func<Function, bool> isExplicitlyRevealed = null,
    ConcreteCallSession concreteCallSession = null, bool concreteCallBody = false,
    Action cancellationCheck = null) {
    this.options = options;
    this.module = module;
    this.systemModuleManager = systemModuleManager;
    this.inlineDepth = inlineDepth;
    this.effectiveScope = effectiveScope ?? module.VisibilityScope;
    quantifierUnrollCapOverride = quantifierUnrollCap;
    this.quantifierExpansionBudget = quantifierExpansionBudget;
    this.emitQuantifierOverflowResidual = emitQuantifierOverflowResidual;
    this.evaluationProfile = evaluationProfile;
    this.expressionExpansionBudget = expressionExpansionBudget;
    this.heapReduction = heapReduction;
    this.collectProofCompositionCandidates = collectProofCompositionCandidates;
    this.detectEmptyQuantifierProduct = detectEmptyQuantifierProduct;
    this.proofCompositionMode = proofCompositionMode;
    this.isExplicitlyRevealed = isExplicitlyRevealed;
    this.concreteCallBody = concreteCallBody;
    this.cancellationCheck = cancellationCheck;
    this.concreteCallSession = concreteCallSession ?? (proofCompositionMode &&
      quantifierExpansionBudget != null && expressionExpansionBudget != null ? new ConcreteCallSession() : null);
    helperInterpreter = new HelperFunctionInterpreter(this, systemModuleManager);
  }

  private PartialEvalState CreateInitialState() {
    CheckForCancellation();
    // This state is shared across the traversal to limit inlining depth and detect inlining cycles.
    return new PartialEvalState((int)inlineDepth, new HashSet<Function>(), new HashSet<string>(StringComparer.Ordinal));
  }

  private PartialEvaluatorVisitor CreateVisitor() {
    CheckForCancellation();
    return new PartialEvaluatorVisitor(this);
  }

  internal void CheckForCancellation() {
    cancellationCheck?.Invoke();
  }

  internal Expression CloneResolvedExpression(Expression expression) {
    return new ContractReductionCloner(cancellationCheck).CloneExpr(expression);
  }

  internal ContractReductionSubstituter CreateSubstituter(Expression receiver,
    Dictionary<IVariable, Expression> substitutions, Dictionary<TypeParameter, Type> typeSubstitutions) {
    return new ContractReductionSubstituter(receiver, substitutions, typeSubstitutions,
      null, systemModuleManager, cancellationCheck);
  }

  /// <summary>
  /// Runs partial evaluation on a resolved callable. This is invoked by the rewriter, and it mutates
  /// the callable body in-place to simplify expressions and statements.
  /// </summary>
  public void PartialEvalEntry(ICallable callable) {
    CheckForCancellation();
    var state = CreateInitialState();
    var visitor = CreateVisitor();
    switch (callable) {
      case Function function when function.Body != null:
        function.Body = visitor.SimplifyExpression(function.Body, state);
        break;
      case MethodOrConstructor method when method.Body != null:
        visitor.Visit(method.Body, state);
        break;
    }
  }

  internal Expression SimplifyExpression(Expression expr) {
    CheckForCancellation();
    var state = CreateInitialState();
    var visitor = CreateVisitor();
    return visitor.SimplifyExpression(expr, state);
  }

  internal bool HasFreeTypeParametersIncludingUnexpandedArguments(Type type) {
    CheckForCancellation();
    var freeTypeParameters = new HashSet<TypeParameter>();
    CheckForCancellation();
    type.AddFreeTypeParameters(freeTypeParameters);
    CheckForCancellation();
    if (freeTypeParameters.Count != 0) {
      return true;
    }
    foreach (var typeArgument in type.TypeArgs) {
      CheckForCancellation();
      if (HasFreeTypeParametersIncludingUnexpandedArguments(typeArgument)) {
        return true;
      }
    }
    return false;
  }

  private bool TryGetRevealedIntegerSubsetTarget(Type targetType, out SubsetTypeDecl targetSubset) {
    targetSubset = null;
    var current = targetType;
    var visited = new HashSet<TypeSynonymDecl>();
    while (current != null) {
      CheckForCancellation();
      if (HasFreeTypeParametersIncludingUnexpandedArguments(current)) {
        return false;
      }
      current = current.Normalize();
      if (current is IntType) {
        return targetSubset != null;
      }
      if (current is not UserDefinedType userType) {
        return false;
      }
      if (userType.ResolvedClass is InternalTypeSynonymDecl or NewtypeDecl) {
        return false;
      }
      if (userType.ResolvedClass is not TypeSynonymDecl synonym ||
          !synonym.IsRevealedInScope(effectiveScope) || !visited.Add(synonym)) {
        return false;
      }
      if (synonym is SubsetTypeDecl subset) {
        targetSubset ??= subset;
      }
      current = synonym.RhsWithArgumentIgnoringScope(userType.TypeArgs);
    }
    return false;
  }

  // Every node receives the existing local inline allowance, but shares all work budgets.
  internal sealed class ConcreteCallSession {
    private sealed class Entry(FunctionCallExpr call) {
      internal readonly FunctionCallExpr Call = call;
      internal ContractConcreteCallProof Proof;
    }

    private readonly List<Entry> entries = new();

    private static bool SameCall(FunctionCallExpr left, FunctionCallExpr right, Action cancellationCheck = null) =>
      ReferenceEquals(left.Function, right.Function) && left.Type.Equals(right.Type, keepConstraints: true) &&
      SameTypes(left.TypeApplication_AtEnclosingClass, right.TypeApplication_AtEnclosingClass, cancellationCheck) &&
      SameTypes(left.TypeApplication_JustFunction, right.TypeApplication_JustFunction, cancellationCheck) &&
      left.Args.Count == right.Args.Count && left.Args.Zip(right.Args).All(pair =>
        pair.First.Type.Equals(pair.Second.Type, keepConstraints: true) &&
        AreContractConcreteExpressionsEqual(pair.First, pair.Second, cancellationCheck));

    private static bool SameTypes(IReadOnlyList<Type> left, IReadOnlyList<Type> right, Action cancellationCheck = null) =>
      left == null || right == null ? left == right : left.Count == right.Count &&
      left.Zip(right).All(pair => { cancellationCheck?.Invoke(); return pair.First.Equals(pair.Second, keepConstraints: true); });

    internal static Expression Membership(PartialEvaluatorEngine owner, Expression value, Type expected) {
      owner.CheckForCancellation();
      var constraint = ModuleResolver.GetImpliedTypeConstraint(value, expected);
      var concrete = NormalizeContractConcreteExpression(value, owner.cancellationCheck);
      if (concrete is SeqDisplayExpr sequence && expected.NormalizeExpand().AsSeqType is { } sequenceType) {
        foreach (var element in sequence.Elements) {
          owner.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, Membership(owner, element, sequenceType.Arg));
        }
      } else if (concrete is StringLiteralExpr && expected.NormalizeExpand().AsSeqType is { } stringType) {
        if (!owner.TryGetUnescapedStringCharacters(concrete, out var characters)) {
          return Expression.CreateAnd(constraint, new TypeTestExpr(value.Origin, value, expected) { Type = Type.Bool });
        }
        // Keep original indexed characters in native prerequisites; decoded length follows the active character mode.
        for (var index = 0; index < characters.Count; index++) {
          owner.CheckForCancellation();
          var element = new SeqSelectExpr(concrete.Origin, true, concrete,
            Expression.CreateIntLiteral(concrete.Origin, index), null) { Type = Type.Char };
          constraint = Expression.CreateAnd(constraint, Membership(owner, element, stringType.Arg));
        }
      } else if (concrete is SetDisplayExpr set && expected.NormalizeExpand().AsSetType is { } setType) {
        foreach (var element in set.Elements) {
          owner.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, Membership(owner, element, setType.Arg));
        }
      } else if (concrete is MultiSetDisplayExpr multiset && expected.NormalizeExpand().AsMultiSetType is { } multisetType) {
        foreach (var element in multiset.Elements) {
          owner.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, Membership(owner, element, multisetType.Arg));
        }
      } else if (concrete is MapDisplayExpr map && expected.NormalizeExpand().AsMapType is { } mapType &&
                 TryNormalizeContractConcreteMapEntries(map, out var entries, owner.cancellationCheck)) {
        foreach (var entry in entries) {
          owner.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, Membership(owner, entry.A, mapType.Domain));
          constraint = Expression.CreateAnd(constraint, Membership(owner, entry.B, mapType.Range));
        }
      } else if (concrete is DatatypeValue datatype && expected.NormalizeExpand() is UserDefinedType userType) {
        var typeMap = TypeParameter.SubstitutionMap(datatype.Ctor.EnclosingDatatype.TypeArgs, userType.TypeArgs);
        foreach (var pair in datatype.Arguments.Zip(datatype.Ctor.Formals)) {
          owner.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, Membership(owner, pair.First, pair.Second.Type.Subst(typeMap)));
        }
      }
      return constraint;
    }

    internal bool TryEvaluate(PartialEvaluatorEngine owner, FunctionCallExpr call, out ContractConcreteCallProof proof) {
      owner.CheckForCancellation();
      proof = null;
      var existing = entries.FirstOrDefault(entry => {
        owner.CheckForCancellation();
        return SameCall(entry.Call, call, owner.cancellationCheck);
      });
      if (existing != null) {
        // An active or failed calculation has no certificate and cannot justify a recursive cycle.
        proof = existing.Proof;
        return proof != null;
      }
      if (owner.inlineDepth == 0 || owner.quantifierExpansionBudget.Remaining == 0) {
        if (owner.quantifierExpansionBudget.Remaining == 0) { owner.quantifierExpansionBudget.MarkExhausted(); }
        return false;
      }
      owner.quantifierExpansionBudget.ConsumeInstance();
      if (!owner.expressionExpansionBudget.TryReserve(call)) { return false; }
      var clonedCall = (FunctionCallExpr)owner.CloneResolvedExpression(call);
      var entry = new Entry(clonedCall);
      entries.Add(entry);
      var substitutions = call.Function.Ins.Zip(call.Args).ToDictionary(pair => (IVariable)pair.First, pair => pair.Second);
      if (!owner.expressionExpansionBudget.TryReserveSubstitution(call.Function.Body, substitutions)) { return false; }
      var substituter = owner.CreateSubstituter(null, substitutions, call.GetTypeArgumentSubstitutions());
      var body = substituter.Substitute(owner.CloneResolvedExpression(call.Function.Body));
      var evaluator = new PartialEvaluatorEngine(owner.options, owner.module, owner.systemModuleManager,
        owner.inlineDepth, owner.effectiveScope, owner.quantifierUnrollCapOverride, owner.quantifierExpansionBudget,
        owner.emitQuantifierOverflowResidual, PartialEvaluationProfile.ContractConcrete, owner.expressionExpansionBudget,
        detectEmptyQuantifierProduct: true, proofCompositionMode: true,
        isExplicitlyRevealed: owner.IsExplicitlyRevealed, concreteCallSession: this, concreteCallBody: true,
        cancellationCheck: owner.cancellationCheck);
      var requirements = new List<Expression>();
      foreach (var pair in call.Args.Zip(call.Function.Ins)) {
        owner.CheckForCancellation();
        var argumentMembership = Membership(owner, pair.First, pair.Second.Type.Subst(call.GetTypeArgumentSubstitutions()));
        if (!owner.expressionExpansionBudget.TryReserve(argumentMembership)) { return false; }
        var checkedArgument = evaluator.SimplifyExpression(owner.CloneResolvedExpression(argumentMembership));
        if (!Expression.IsBoolLiteral(checkedArgument, out var valid) || !valid) { return false; }
        requirements.Add(argumentMembership);
      }
      foreach (var requirement in call.Function.Req) {
        owner.CheckForCancellation();
        if (!owner.expressionExpansionBudget.TryReserveSubstitution(requirement.E, substitutions)) { return false; }
        var originalRequirement = substituter.Substitute(owner.CloneResolvedExpression(requirement.E));
        var checkedRequirement = evaluator.SimplifyExpression(owner.CloneResolvedExpression(originalRequirement));
        if (!Expression.IsBoolLiteral(checkedRequirement, out var holds) || !holds) { return false; }
        requirements.Add(originalRequirement);
      }
      var value = evaluator.SimplifyExpression(body);
      if (!IsContractConcreteValue(value, owner.cancellationCheck) || evaluator.ExpressionNodeLimitExhausted ||
          evaluator.ProofWitnesses.Any(witness => !IsClosedProofExpression(owner.options, witness, owner.cancellationCheck))) { return false; }
      value = owner.CloneResolvedExpression(value);
      var equality = Expression.CreateEq(clonedCall, value, call.Type.NormalizeExpand());
      // In particular, a concrete value cannot acquire a subset type from the function's return type.
      var membership = Membership(owner, value, call.Type);
      var checkedMembership = evaluator.SimplifyExpression(owner.CloneResolvedExpression(membership));
      if (!Expression.IsBoolLiteral(checkedMembership, out var member) || !member) { return false; }
      if (!owner.expressionExpansionBudget.TryReserve(equality) ||
          !owner.expressionExpansionBudget.TryReserve(membership)) { return false; }
      entry.Proof = proof = new ContractConcreteCallProof(value, evaluator.ProofConcreteCalls.ToArray(),
        requirements.Concat(evaluator.ProofPrerequisites).Append(membership).ToArray(), evaluator.ProofWitnesses.ToArray(), equality);
      owner.CheckForCancellation();
      return true;
    }
  }

  // ------------------- Quantifier bounds / finite materialization -------------------

  private uint GetPartialEvalUnrollCap() {
    if (quantifierUnrollCapOverride.HasValue) {
      return quantifierUnrollCapOverride.Value;
    }
    var unrollBoundedQuantifiers = options.Get(CommonOptionBag.UnrollBoundedQuantifiers);
    return unrollBoundedQuantifiers ?? DefaultPartialEvalUnrollCap;
  }

  private uint GetRemainingQuantifierExpansionLimit() {
    return quantifierExpansionBudget?.Remaining ?? GetPartialEvalUnrollCap();
  }

  private bool HasQuantifierExpansionLimit() {
    return quantifierExpansionBudget != null || GetPartialEvalUnrollCap() > 0;
  }

  private void RecordQuantifierExpansion() {
    quantifierExpansionBudget?.ConsumeInstance();
  }

  private void RecordQuantifierExpansionExhaustion() {
    quantifierExpansionBudget?.MarkExhausted();
  }

  private QuantifierBounds GetQuantifierBounds() {
    if (quantifierBounds != null) {
      return quantifierBounds;
    }
    quantifierBounds = new QuantifierBounds(systemModuleManager, GetPartialEvalUnrollCap(), quantifierExpansionBudget,
      detectEmptyQuantifierProduct, cancellationCheck);
    return quantifierBounds;
  }

  /// <summary>
  /// Attempts to unroll a bounded quantifier into a finite boolean expression under the configured cap.
  /// </summary>
  internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, out Expression rewritten) {
    return TryUnrollQuantifier(quantifierExpr, SimplifyExpression, out rewritten);
  }

  internal bool TryUnrollQuantifier(
    QuantifierExpr quantifierExpr,
    Func<Expression, Expression> simplifyAfterSubst,
    out Expression rewritten) {
    return TryUnrollQuantifier(quantifierExpr, simplifyAfterSubst, out rewritten, emitOverflowResidual: true);
  }

  internal bool TryUnrollQuantifier(
    QuantifierExpr quantifierExpr,
    Func<Expression, Expression> simplifyAfterSubst,
    out Expression rewritten,
    bool emitOverflowResidual) {
    return GetQuantifierBounds().TryUnrollQuantifier(
      quantifierExpr,
      simplifyAfterSubst,
      out rewritten,
      emitOverflowResidual,
      UsesContractConcreteProfile ? TryReserveQuantifierInstanceExpansion : null);
  }

  private bool TryReserveQuantifierInstanceExpansion(
    Expression expression, IReadOnlyDictionary<IVariable, Expression> substitutions) {
    CheckForCancellation();
    return expressionExpansionBudget == null ||
           expressionExpansionBudget.TryReserveSubstitution(expression, substitutions);
  }

  internal uint GetQuantifierUnrollLimit() {
    return GetQuantifierBounds().MaxInstances;
  }

  /// <summary>
  /// If a finite set comprehension can be fully materialized under the configured cap, rewrite it to a set display.
  /// </summary>
  internal bool TryMaterializeSetComprehension(SetComprehension setComprehension, out SetDisplayExpr displayExpr) {
    displayExpr = null;
    if (!setComprehension.Finite) {
      return false;
    }
    if (!GetQuantifierBounds().TryMaterializeSetComprehension(setComprehension, SimplifyExpression, out var elements)) {
      return false;
    }
    displayExpr = new SetDisplayExpr(setComprehension.Origin, true, elements) { Type = setComprehension.Type };
    return true;
  }

  /// <summary>
  /// If a finite map comprehension can be fully materialized under the configured cap, rewrite it to a map display.
  /// </summary>
  private bool TryMaterializeMapComprehension(
    MapComprehension mapComprehension,
    PartialEvalState state,
    Func<Expression, PartialEvalState, Expression> simplifyExpression,
    out MapDisplayExpr mapDisplayExpr) {
    mapDisplayExpr = null;
    if (!mapComprehension.Finite) {
      return false;
    }
    if (!GetQuantifierBounds().TryMaterializeMapComprehension(
          mapComprehension,
          expr => simplifyExpression(expr, state),
          out var entries)) {
      return false;
    }

    mapDisplayExpr = new MapDisplayExpr(mapComprehension.Origin, true, entries) { Type = mapComprehension.Type };
    return true;
  }

  private static void AssertHasResolvedType(Expression expr) {
    if (expr == null) {
      return;
    }
    Contract.Assert(expr.Type != null, "PartialEvaluator produced an expression with null Type");
  }

  /// <summary>
  /// Simplifies a resolved binary expression after its operands have already been simplified.
  /// This method is intentionally local: it only performs folds that are obviously semantics-preserving.
  /// </summary>
  private Expression SimplifyBinary(BinaryExpr binary) {
    switch (binary.ResolvedOp) {
      case BinaryExpr.ResolvedOpcode.And:
      case BinaryExpr.ResolvedOpcode.Or:
      case BinaryExpr.ResolvedOpcode.Imp:
      case BinaryExpr.ResolvedOpcode.Iff:
        return SimplifyBooleanBinary(binary);
      case BinaryExpr.ResolvedOpcode.Add:
        return SimplifyIntBinary(binary, (a, b) => a + b, 0, BinaryExpr.ResolvedOpcode.Add);
      case BinaryExpr.ResolvedOpcode.Sub:
        return SimplifyIntBinary(binary, (a, b) => a - b, 0, BinaryExpr.ResolvedOpcode.Sub);
      case BinaryExpr.ResolvedOpcode.Mul:
        return SimplifyIntBinary(binary, (a, b) => a * b, 1, BinaryExpr.ResolvedOpcode.Mul);
      case BinaryExpr.ResolvedOpcode.Div:
      case BinaryExpr.ResolvedOpcode.Mod:
        return SimplifyIntDivMod(binary, binary.ResolvedOp);
      case BinaryExpr.ResolvedOpcode.Lt:
      case BinaryExpr.ResolvedOpcode.LtChar:
        return SimplifyOrderedComparison(binary, (a, b) => a < b);
      case BinaryExpr.ResolvedOpcode.Le:
      case BinaryExpr.ResolvedOpcode.LeChar:
        return SimplifyOrderedComparison(binary, (a, b) => a <= b);
      case BinaryExpr.ResolvedOpcode.Gt:
      case BinaryExpr.ResolvedOpcode.GtChar:
        return SimplifyOrderedComparison(binary, (a, b) => a > b);
      case BinaryExpr.ResolvedOpcode.Ge:
      case BinaryExpr.ResolvedOpcode.GeChar:
        return SimplifyOrderedComparison(binary, (a, b) => a >= b);
      case BinaryExpr.ResolvedOpcode.EqCommon:
        return SimplifyEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.NeqCommon:
        return SimplifyEquality(binary, false);
      case BinaryExpr.ResolvedOpcode.Concat:
        return SimplifySeqConcat(binary);
      case BinaryExpr.ResolvedOpcode.SeqEq:
        return SimplifySeqEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.SeqNeq:
        return SimplifySeqEquality(binary, false);
      case BinaryExpr.ResolvedOpcode.Prefix:
        return SimplifySeqPrefix(binary, false);
      case BinaryExpr.ResolvedOpcode.ProperPrefix:
        return SimplifySeqPrefix(binary, true);
      case BinaryExpr.ResolvedOpcode.SetEq:
        return SimplifySetEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.SetNeq:
        return SimplifySetEquality(binary, false);
      case BinaryExpr.ResolvedOpcode.InSet:
        return SimplifySetMembership(binary, true);
      case BinaryExpr.ResolvedOpcode.NotInSet:
        return SimplifySetMembership(binary, false);
      case BinaryExpr.ResolvedOpcode.Subset:
        return SimplifySetSubset(binary, binary.E0, binary.E1, false);
      case BinaryExpr.ResolvedOpcode.ProperSubset:
        return SimplifySetSubset(binary, binary.E0, binary.E1, true);
      case BinaryExpr.ResolvedOpcode.Superset:
        return SimplifySetSubset(binary, binary.E1, binary.E0, false);
      case BinaryExpr.ResolvedOpcode.ProperSuperset:
        return SimplifySetSubset(binary, binary.E1, binary.E0, true);
      case BinaryExpr.ResolvedOpcode.Disjoint:
        return SimplifySetDisjoint(binary);
      case BinaryExpr.ResolvedOpcode.Union:
        return SimplifySetUnion(binary);
      case BinaryExpr.ResolvedOpcode.Intersection:
        return SimplifySetIntersection(binary);
      case BinaryExpr.ResolvedOpcode.SetDifference:
        return SimplifySetDifference(binary);
      case BinaryExpr.ResolvedOpcode.MultiSetEq:
        return SimplifyMultiSetEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        return SimplifyMultiSetEquality(binary, false);
      case BinaryExpr.ResolvedOpcode.InMultiSet:
        return SimplifyMultiSetMembership(binary, true);
      case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        return SimplifyMultiSetMembership(binary, false);
      case BinaryExpr.ResolvedOpcode.MultiSubset:
        return SimplifyMultiSetSubset(binary, binary.E0, binary.E1, false);
      case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
        return SimplifyMultiSetSubset(binary, binary.E0, binary.E1, true);
      case BinaryExpr.ResolvedOpcode.MultiSuperset:
        return SimplifyMultiSetSubset(binary, binary.E1, binary.E0, false);
      case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
        return SimplifyMultiSetSubset(binary, binary.E1, binary.E0, true);
      case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
        return SimplifyMultiSetDisjoint(binary);
      case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        return SimplifyMultiSetUnion(binary);
      case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
        return SimplifyMultiSetIntersection(binary);
      case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        return SimplifyMultiSetDifference(binary);
      case BinaryExpr.ResolvedOpcode.InSeq:
        return SimplifySeqMembership(binary, true);
      case BinaryExpr.ResolvedOpcode.NotInSeq:
        return SimplifySeqMembership(binary, false);
      case BinaryExpr.ResolvedOpcode.InMap:
        return SimplifyMapMembership(binary, true);
      case BinaryExpr.ResolvedOpcode.NotInMap:
        return SimplifyMapMembership(binary, false);
      case BinaryExpr.ResolvedOpcode.MapEq:
        return SimplifyMapEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.MapNeq:
        return SimplifyMapEquality(binary, false);
      case BinaryExpr.ResolvedOpcode.MapMerge:
        return SimplifyMapMerge(binary);
      case BinaryExpr.ResolvedOpcode.MapSubtraction:
        return SimplifyMapSubtraction(binary);
      case BinaryExpr.ResolvedOpcode.BitwiseAnd:
      case BinaryExpr.ResolvedOpcode.BitwiseOr:
      case BinaryExpr.ResolvedOpcode.BitwiseXor:
      case BinaryExpr.ResolvedOpcode.LeftShift:
      case BinaryExpr.ResolvedOpcode.RightShift:
        return SimplifyBitvectorBinary(binary);
      default:
        return binary;
    }
  }

  // ------------------- Binary folding helpers -------------------

  private static Expression CreateBoolLiteral(IOrigin origin, bool value) {
    var literal = Expression.CreateBoolLiteral(origin, value);
    literal.Type = Type.Bool;
    return literal;
  }

  private Expression SimplifyBooleanBinary(BinaryExpr binary) {
    switch (binary.ResolvedOp) {
      case BinaryExpr.ResolvedOpcode.And:
        if (Expression.IsBoolLiteral(binary.E0, out var leftAnd)) {
          return leftAnd ? binary.E1 : CreateBoolLiteral(binary.Origin, false);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rightAnd)) {
          return rightAnd ? binary.E0 : CreateBoolLiteral(binary.Origin, false);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Or:
        if (Expression.IsBoolLiteral(binary.E0, out var leftOr)) {
          return leftOr ? CreateBoolLiteral(binary.Origin, true) : binary.E1;
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rightOr)) {
          return rightOr ? CreateBoolLiteral(binary.Origin, true) : binary.E0;
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Imp:
        if (Expression.IsBoolLiteral(binary.E0, out var leftImp)) {
          return leftImp ? binary.E1 : CreateBoolLiteral(binary.Origin, true);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rightImp)) {
          return rightImp ? CreateBoolLiteral(binary.Origin, true) : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Iff:
        if (Expression.IsBoolLiteral(binary.E0, out var leftIff)) {
          return leftIff ? binary.E1 : Expression.CreateNot(binary.Origin, binary.E1);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rightIff)) {
          return rightIff ? binary.E0 : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      default:
        return binary;
    }
  }

  private Expression SimplifyIntBinary(BinaryExpr binary, Func<BigInteger, BigInteger, BigInteger> op, int identity, BinaryExpr.ResolvedOpcode opcode) {
    if (TryGetReducedIntLiteral(binary.E0, out var left, cancellationCheck) && TryGetReducedIntLiteral(binary.E1, out var right, cancellationCheck)) {
      return CreateIntLiteral(binary.Origin, op(left, right));
    }

    if (TryGetReducedIntLiteral(binary.E0, out left, cancellationCheck) && left == identity && opcode == BinaryExpr.ResolvedOpcode.Add) {
      return binary.E1;
    }

    if (TryGetReducedIntLiteral(binary.E1, out right, cancellationCheck) && right == identity &&
        opcode is BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub) {
      return binary.E0;
    }

    if (opcode == BinaryExpr.ResolvedOpcode.Mul) {
      if (TryGetReducedIntLiteral(binary.E0, out left, cancellationCheck)) {
        if (left == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (left == 1) {
          return binary.E1;
        }
      }
      if (TryGetReducedIntLiteral(binary.E1, out right, cancellationCheck)) {
        if (right == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (right == 1) {
          return binary.E0;
        }
      }
    }

    if (opcode == BinaryExpr.ResolvedOpcode.Sub && ReferenceEquals(binary.E0, binary.E1)) {
      return CreateIntLiteral(binary.Origin, BigInteger.Zero);
    }

    return binary;
  }

  private Expression SimplifyIntDivMod(BinaryExpr binary, BinaryExpr.ResolvedOpcode opcode) {
    if (TryGetReducedIntLiteral(binary.E0, out var left, cancellationCheck) && TryGetReducedIntLiteral(binary.E1, out var right, cancellationCheck)) {
      if (right != 0) {
        if (opcode == BinaryExpr.ResolvedOpcode.Div) {
          // Match Dafny integer folding semantics: Euclidean division.
          var quotient = left / right;
          if (left < 0 && left != quotient * right) {
            quotient += right > 0 ? -1 : 1;
          }
          return CreateIntLiteral(binary.Origin, quotient);
        }
        if (opcode == BinaryExpr.ResolvedOpcode.Mod) {
          // Match Dafny integer folding semantics: Euclidean modulo.
          var divisor = BigInteger.Abs(right);
          var remainder = left % divisor;
          if (remainder < 0) {
            remainder += divisor;
          }
          return CreateIntLiteral(binary.Origin, remainder);
        }
      }
    }
    if (opcode == BinaryExpr.ResolvedOpcode.Div && TryGetReducedIntLiteral(binary.E1, out right, cancellationCheck) && right == 1) {
      return binary.E0;
    }
    if (opcode == BinaryExpr.ResolvedOpcode.Mod && TryGetReducedIntLiteral(binary.E1, out right, cancellationCheck) && right == 1) {
      return CreateIntLiteral(binary.Origin, BigInteger.Zero);
    }
    return binary;
  }

  private Expression SimplifyBitvectorBinary(BinaryExpr binary) {
    var bitvectorType = binary.Type.NormalizeExpand().AsBitVectorType;
    if (bitvectorType == null) {
      return binary;
    }

    if (!TryGetReducedIntLiteral(binary.E0, out var left, cancellationCheck) || !TryGetReducedIntLiteral(binary.E1, out var right, cancellationCheck)) {
      return binary;
    }

    switch (binary.ResolvedOp) {
      case BinaryExpr.ResolvedOpcode.BitwiseAnd:
        return CreateIntLiteral(binary.Origin, left & right, binary.Type);
      case BinaryExpr.ResolvedOpcode.BitwiseOr:
        return CreateIntLiteral(binary.Origin, left | right, binary.Type);
      case BinaryExpr.ResolvedOpcode.BitwiseXor:
        return CreateIntLiteral(binary.Origin, left ^ right, binary.Type);
      case BinaryExpr.ResolvedOpcode.LeftShift:
        if (right < 0 || right > bitvectorType.Width || right > int.MaxValue) {
          return binary;
        }
        return CreateIntLiteral(binary.Origin, (left << (int)right) & ConstantFolder.MaxBv(binary.Type), binary.Type);
      case BinaryExpr.ResolvedOpcode.RightShift:
        if (right < 0 || right > bitvectorType.Width || right > int.MaxValue) {
          return binary;
        }
        return CreateIntLiteral(binary.Origin, left >> (int)right, binary.Type);
      default:
        return binary;
    }
  }

  private Expression SimplifyOrderedComparison(BinaryExpr binary, Func<BigInteger, BigInteger, bool> op) {
    if (TryGetIntLiteralOrCharLiteral(binary.E0, out var left, cancellationCheck) &&
        TryGetIntLiteralOrCharLiteral(binary.E1, out var right, cancellationCheck)) {
      return Expression.CreateBoolLiteral(binary.Origin, op(left, right));
    }
    return binary;
  }

  private static bool TryGetIntLiteralOrCharLiteral(Expression expr, out BigInteger value, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = default;
    if (TryGetReducedIntLiteral(expr, out var intLiteral, cancellationCheck)) {
      value = intLiteral;
      return true;
    }
    if (TryGetCharLiteral(expr, out var charLiteral, cancellationCheck)) {
      value = charLiteral;
      return true;
    }
    return false;
  }

  private Expression SimplifyEquality(BinaryExpr binary, bool isEq) {
    if (Expression.IsBoolLiteral(binary.E0, out var leftBool) && Expression.IsBoolLiteral(binary.E1, out var rightBool)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftBool == rightBool : leftBool != rightBool);
    }
    if (TryGetReducedIntLiteral(binary.E0, out var leftInt, cancellationCheck) && TryGetReducedIntLiteral(binary.E1, out var rightInt, cancellationCheck)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftInt == rightInt : leftInt != rightInt);
    }
    if (TryGetCharLiteral(binary.E0, out var leftChar, cancellationCheck) && TryGetCharLiteral(binary.E1, out var rightChar, cancellationCheck)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftChar == rightChar : leftChar != rightChar);
    }
    if (TryGetTupleLiteral(binary.E0, out var leftTuple) &&
        TryGetTupleLiteral(binary.E1, out var rightTuple) &&
        AllElementsAreLiterals(leftTuple.Arguments, cancellationCheck) &&
        AllElementsAreLiterals(rightTuple.Arguments, cancellationCheck)) {
      var equal = TupleLiteralsEqual(leftTuple, rightTuple, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    if (UsesContractConcreteProfile &&
        IsContractConcreteValue(binary.E0, cancellationCheck) && IsContractConcreteValue(binary.E1, cancellationCheck)) {
      var equal = AreContractConcreteExpressionsEqual(binary.E0, binary.E1, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private bool TrySimplifyContractConstructorEquality(BinaryExpr binary, out Expression replacement) {
    replacement = null;
    if (!UsesContractConcreteProfile || binary.ResolvedOp != BinaryExpr.ResolvedOpcode.EqCommon ||
        NormalizeContractConcreteExpression(binary.E0, cancellationCheck) is not DatatypeValue { Ctor: { } leftCtor } left ||
        NormalizeContractConcreteExpression(binary.E1, cancellationCheck) is not DatatypeValue { Ctor: { } rightCtor } right ||
        leftCtor.EnclosingDatatype is not IndDatatypeDecl ||
        !ReferenceEquals(leftCtor.EnclosingDatatype, rightCtor.EnclosingDatatype) ||
        !left.Type.NormalizeExpand().Equals(right.Type.NormalizeExpand()) ||
        leftCtor.IsGhost || rightCtor.IsGhost ||
        leftCtor.Formals.Any(formal => { CheckForCancellation(); return formal.IsGhost; }) ||
        rightCtor.Formals.Any(formal => { CheckForCancellation(); return formal.IsGhost; })) {
      return false;
    }
    if (!ReferenceEquals(leftCtor, rightCtor)) {
      replacement = CreateBoolLiteral(binary.Origin, false);
      return true;
    }
    if (left.Arguments.Count != leftCtor.Formals.Count || right.Arguments.Count != leftCtor.Formals.Count ||
        !left.Arguments.Zip(right.Arguments).All(arguments => {
          CheckForCancellation();
          return arguments.First.Type.NormalizeExpand().Equals(arguments.Second.Type.NormalizeExpand());
        })) {
      return false;
    }

    // Constructor injectivity is exact even when a field contains an existential variable.
    // Keep the equalities visible to point elimination, without selecting any field value.
    Expression fields = CreateBoolLiteral(binary.Origin, true);
    foreach (var (leftArgument, rightArgument) in left.Arguments.Zip(right.Arguments)) {
      cancellationCheck?.Invoke();
      fields = Expression.CreateAnd(fields,
        Expression.CreateEq(leftArgument, rightArgument, leftArgument.Type.NormalizeExpand()));
    }
    if (expressionExpansionBudget != null && !expressionExpansionBudget.TryReserve(fields)) {
      return false;
    }
    replacement = fields;
    return true;
  }

  private Expression SimplifySeqConcat(BinaryExpr binary) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out var leftVerbatim) &&
        TryGetStringLiteral(binary.E1, out var rightString, out var rightVerbatim)) {
      if (leftString.Length == 0) {
        return binary.E1;
      }
      if (rightString.Length == 0) {
        return binary.E0;
      }
      return CreateStringLiteral(binary.Origin, leftString + rightString, binary.Type, leftVerbatim && rightVerbatim);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq, cancellationCheck) && AllElementsAreLiterals(rightSeq, cancellationCheck)) {
      if (leftSeq.Elements.Count == 0) {
        return binary.E1;
      }
      if (rightSeq.Elements.Count == 0) {
        return binary.E0;
      }
      var merged = new List<Expression>(leftSeq.Elements.Count + rightSeq.Elements.Count);
      merged.AddRange(leftSeq.Elements);
      merged.AddRange(rightSeq.Elements);
      return CreateSeqDisplayLiteral(binary.Origin, merged, binary.Type);
    }

    return binary;
  }

  private Expression SimplifySeqEquality(BinaryExpr binary, bool isEq) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out var leftVerbatim) &&
        TryGetStringLiteral(binary.E1, out var rightString, out var rightVerbatim)) {
      var equal = StringLiteralsSemanticallyEqual(leftString, leftVerbatim, rightString, rightVerbatim, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq, cancellationCheck) && AllElementsAreLiterals(rightSeq, cancellationCheck)) {
      var equal = SeqDisplayLiteralsEqual(leftSeq, rightSeq, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    if (UsesContractConcreteProfile &&
        binary.E0 is SeqDisplayExpr && binary.E1 is SeqDisplayExpr &&
        IsContractConcreteValue(binary.E0, cancellationCheck) && IsContractConcreteValue(binary.E1, cancellationCheck)) {
      var equal = AreContractConcreteExpressionsEqual(binary.E0, binary.E1, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    if ((TryGetCharSeqDisplayLiteral(binary.E0, out var leftChars) && TryGetUnescapedStringCharacters(binary.E1, out var rightChars)) ||
        (TryGetUnescapedStringCharacters(binary.E0, out leftChars) && TryGetCharSeqDisplayLiteral(binary.E1, out rightChars))) {
      var equal = CodePointSequencesEqual(leftChars, rightChars, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    return binary;
  }

  private Expression SimplifySeqPrefix(BinaryExpr binary, bool properPrefix) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out var leftVerbatim) &&
        TryGetStringLiteral(binary.E1, out var rightString, out var rightVerbatim)) {
      var leftCodePoints = GetSemanticStringCodePoints(leftString, leftVerbatim, cancellationCheck);
      var rightCodePoints = GetSemanticStringCodePoints(rightString, rightVerbatim, cancellationCheck);
      var isPrefix = CodePointSequenceHasPrefix(leftCodePoints, rightCodePoints, out var isProper, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, properPrefix ? isProper : isPrefix);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq, cancellationCheck) && AllElementsAreLiterals(rightSeq, cancellationCheck)) {
      var isPrefix = SeqDisplayIsPrefix(leftSeq, rightSeq, out var isProper, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, properPrefix ? isProper : isPrefix);
    }

    return binary;
  }

  private Expression SimplifySetEquality(BinaryExpr binary, bool isEq) {
    if (TryGetSetDisplayLiteral(binary.E0, out var leftSet) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightSet) &&
        AllElementsAreLiterals(leftSet.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightSet.Elements, cancellationCheck)) {
      var equal = SetDisplayLiteralsEqual(leftSet, rightSet, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private Expression SimplifySetMembership(BinaryExpr binary, bool isIn) {
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (TryGetSetDisplayLiteral(binary.E1, out var setDisplay) &&
        AllElementsAreLiterals(setDisplay.Elements, cancellationCheck) &&
        IsLiteralLike(binary.E0, cancellationCheck)) {
      var contains = ContainsLiteralElement(setDisplay.Elements, binary.E0, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private Expression SimplifySetSubset(BinaryExpr binary, Expression left, Expression right, bool proper) {
    if (LiteralExpr.IsEmptySet(left)) {
      if (!proper) {
        return CreateBoolLiteral(binary.Origin, true);
      }
      if (TryGetSetDisplayLiteral(right, out var rightDisplay)) {
        return CreateBoolLiteral(binary.Origin, rightDisplay.Elements.Count > 0);
      }
      return binary;
    }
    if (LiteralExpr.IsEmptySet(right) && TryGetSetDisplayLiteral(left, out var leftDisplay)) {
      return CreateBoolLiteral(binary.Origin, leftDisplay.Elements.Count == 0);
    }
    if (TryGetSetDisplayLiteral(left, out leftDisplay) &&
        TryGetSetDisplayLiteral(right, out var rightDisplayLiteral) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplayLiteral.Elements, cancellationCheck)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements, cancellationCheck);
      var rightDistinct = new LiteralSet(rightDisplayLiteral.Elements, cancellationCheck);
      var isSubset = leftDistinct.Elements.All(element => rightDistinct.Contains(element));
      var isProper = isSubset && leftDistinct.Count < rightDistinct.Count;
      return CreateBoolLiteral(binary.Origin, proper ? isProper : isSubset);
    }
    return binary;
  }

  private Expression SimplifySetDisjoint(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0) || LiteralExpr.IsEmptySet(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, true);
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements, cancellationCheck);
      var rightDistinct = new LiteralSet(rightDisplay.Elements, cancellationCheck);
      var disjoint = leftDistinct.Elements.All(element => !rightDistinct.Contains(element));
      return CreateBoolLiteral(binary.Origin, disjoint);
    }
    return binary;
  }

  private Expression SimplifySetUnion(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0)) {
      return binary.E1;
    }
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E0;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var merged = new LiteralSet(leftDisplay.Elements, cancellationCheck);
      foreach (var element in rightDisplay.Elements) {
        cancellationCheck?.Invoke();
        merged.Add(element);
      }
      return CreateSetDisplayLiteral(binary.Origin, merged.Elements, binary.Type);
    }
    return binary;
  }

  private Expression SimplifySetIntersection(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0)) {
      return binary.E0;
    }
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E1;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements, cancellationCheck);
      var rightDistinct = new LiteralSet(rightDisplay.Elements, cancellationCheck);
      var intersection = new List<Expression>();
      foreach (var element in leftDistinct.Elements) {
        cancellationCheck?.Invoke();
        if (rightDistinct.Contains(element)) {
          intersection.Add(element);
        }
      }
      return CreateSetDisplayLiteral(binary.Origin, intersection, binary.Type);
    }
    return binary;
  }

  private Expression SimplifySetDifference(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0) || LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E0;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return new SetDisplayExpr(binary.Origin, true, new List<Expression>()) { Type = binary.Type };
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements, cancellationCheck);
      var rightDistinct = new LiteralSet(rightDisplay.Elements, cancellationCheck);
      var difference = leftDistinct.Elements.Where(element => !rightDistinct.Contains(element)).ToList();
      return CreateSetDisplayLiteral(binary.Origin, difference, binary.Type);
    }
    return binary;
  }

  private Expression SimplifyMultiSetEquality(BinaryExpr binary, bool isEq) {
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var equal = MultiSetDisplayLiteralsEqual(leftDisplay, rightDisplay, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private Expression SimplifyMultiSetMembership(BinaryExpr binary, bool isIn) {
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (TryGetMultiSetDisplayLiteral(binary.E1, out var multiSetDisplay) &&
        AllElementsAreLiterals(multiSetDisplay.Elements, cancellationCheck) &&
        IsLiteralLike(binary.E0, cancellationCheck)) {
      var counts = BuildMultisetCountsDict(multiSetDisplay.Elements, cancellationCheck);
      var contains = counts.ContainsKey(binary.E0);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private Expression SimplifySeqMembership(BinaryExpr binary, bool isIn) {
    if (UsesContractConcreteProfile && binary.E1 is SeqDisplayExpr concreteSequence &&
        IsContractConcreteValue(binary.E0, cancellationCheck) && concreteSequence.Elements.All(value => IsContractConcreteValue(value, cancellationCheck))) {
      var contains = concreteSequence.Elements.Any(element => AreContractConcreteExpressionsEqual(element, binary.E0, cancellationCheck));
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    if (TryGetSeqDisplayLiteral(binary.E1, out var seqDisplay) &&
        AllElementsAreLiterals(seqDisplay.Elements, cancellationCheck) &&
        IsLiteralLike(binary.E0, cancellationCheck)) {
      var contains = ContainsLiteralElement(seqDisplay.Elements, binary.E0, cancellationCheck);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private Expression SimplifyMapMembership(BinaryExpr binary, bool isIn) {
    if (binary.E1 is MapDisplayExpr { Elements.Count: 0 }) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (binary.E1 is MapDisplayExpr mapDisplay &&
        AllElementsAreLiterals(mapDisplay, cancellationCheck) &&
        IsLiteralLike(binary.E0, cancellationCheck)) {
      var contains = mapDisplay.Elements.Any(e => AreLiteralExpressionsEqual(e.A, binary.E0, cancellationCheck));
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private Expression SimplifyMapEquality(BinaryExpr binary, bool isEq) {
    if (binary.E0 is not MapDisplayExpr leftMap || binary.E1 is not MapDisplayExpr rightMap) {
      return binary;
    }

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries, cancellationCheck) ||
        !TryNormalizeLiteralMapEntries(rightMap, out var rightEntries, cancellationCheck)) {
      if (UsesContractConcreteProfile && IsContractConcreteValue(leftMap, cancellationCheck) && IsContractConcreteValue(rightMap, cancellationCheck)) {
        var contractEqual = AreContractConcreteExpressionsEqual(leftMap, rightMap, cancellationCheck);
        return CreateBoolLiteral(binary.Origin, isEq ? contractEqual : !contractEqual);
      }
      return binary;
    }

    var rightByKey = new Dictionary<Expression, Expression>(LiteralExpressionEqualityComparer.For(cancellationCheck));
    foreach (var entry in rightEntries) {
      cancellationCheck?.Invoke();
      rightByKey[entry.A] = entry.B;
    }

    var equal = leftEntries.Count == rightEntries.Count;
    if (equal) {
      foreach (var entry in leftEntries) {
        cancellationCheck?.Invoke();
        if (!rightByKey.TryGetValue(entry.A, out var rightValue) ||
            !AreLiteralExpressionsEqual(entry.B, rightValue, cancellationCheck)) {
          equal = false;
          break;
        }
      }
    }

    return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
  }

  private Expression SimplifyMapMerge(BinaryExpr binary) {
    if (binary.E0 is not MapDisplayExpr leftMap || binary.E1 is not MapDisplayExpr rightMap) {
      return binary;
    }

    if (leftMap.Elements.Count == 0) {
      return binary.E1;
    }
    if (rightMap.Elements.Count == 0) {
      return binary.E0;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries, cancellationCheck) ||
        !TryNormalizeLiteralMapEntries(rightMap, out var rightEntries, cancellationCheck)) {
      return binary;
    }

    var merged = new List<MapDisplayEntry>(leftEntries);
    var indexByKey = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.For(cancellationCheck));
    for (var index = 0; index < merged.Count; index++) {
      cancellationCheck?.Invoke();
      indexByKey[merged[index].A] = index;
    }

    foreach (var entry in rightEntries) {

      cancellationCheck?.Invoke();
      if (indexByKey.TryGetValue(entry.A, out var existingIndex)) {
        merged[existingIndex] = new MapDisplayEntry(entry.A, entry.B);
      } else {
        indexByKey[entry.A] = merged.Count;
        merged.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }

    return CreateMapDisplayLiteral(binary.Origin, merged, binary.Type);
  }

  private Expression SimplifyMapSubtraction(BinaryExpr binary) {
    if (binary.E0 is not MapDisplayExpr leftMap || binary.E1 is not SetDisplayExpr rightKeySet) {
      return binary;
    }

    if (leftMap.Elements.Count == 0) {
      return binary.E0;
    }
    if (rightKeySet.Elements.Count == 0) {
      return binary.E0;
    }

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries, cancellationCheck) ||
        !AllElementsAreLiterals(rightKeySet.Elements, cancellationCheck)) {
      return binary;
    }

    var keysToRemove = new LiteralSet(rightKeySet.Elements, cancellationCheck);

    var remaining = new List<MapDisplayEntry>();
    foreach (var entry in leftEntries) {
      cancellationCheck?.Invoke();
      if (!keysToRemove.Contains(entry.A)) {
        remaining.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }

    return CreateMapDisplayLiteral(binary.Origin, remaining, binary.Type);
  }

  private Expression SimplifyMultiSetSubset(BinaryExpr binary, Expression left, Expression right, bool proper) {
    if (LiteralExpr.IsEmptyMultiset(left)) {
      if (!proper) {
        return CreateBoolLiteral(binary.Origin, true);
      }
      if (TryGetMultiSetDisplayLiteral(right, out var rightDisplay)) {
        return CreateBoolLiteral(binary.Origin, rightDisplay.Elements.Count > 0);
      }
      return binary;
    }
    if (LiteralExpr.IsEmptyMultiset(right) && TryGetMultiSetDisplayLiteral(left, out var leftDisplay)) {
      return CreateBoolLiteral(binary.Origin, leftDisplay.Elements.Count == 0);
    }
    if (TryGetMultiSetDisplayLiteral(left, out leftDisplay) &&
        TryGetMultiSetDisplayLiteral(right, out var rightDisplayLiteral) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplayLiteral.Elements, cancellationCheck)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements, cancellationCheck);
      var rightCounts = BuildMultisetCountsDict(rightDisplayLiteral.Elements, cancellationCheck);
      var isSubset = leftCounts.All(entry =>
        rightCounts.TryGetValue(entry.Key, out var rightCount) && entry.Value <= rightCount);
      var isProper = isSubset && leftCounts.Values.Sum() < rightCounts.Values.Sum();
      return CreateBoolLiteral(binary.Origin, proper ? isProper : isSubset);
    }
    return binary;
  }

  private Expression SimplifyMultiSetDisjoint(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0) || LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, true);
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements, cancellationCheck);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements, cancellationCheck);
      var disjoint = leftCounts.Keys.All(key => !rightCounts.ContainsKey(key));
      return CreateBoolLiteral(binary.Origin, disjoint);
    }
    return binary;
  }

  private Expression SimplifyMultiSetUnion(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0)) {
      return binary.E1;
    }
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E0;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var combined = BuildMultisetCountsDict(leftDisplay.Elements, cancellationCheck);
      foreach (var entry in BuildMultisetCountsDict(rightDisplay.Elements, cancellationCheck)) {
        cancellationCheck?.Invoke();
        combined.TryGetValue(entry.Key, out var existing);
        combined[entry.Key] = existing + entry.Value;
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(combined, cancellationCheck), binary.Type);
    }
    return binary;
  }

  private Expression SimplifyMultiSetIntersection(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0)) {
      return binary.E0;
    }
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E1;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements, cancellationCheck);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements, cancellationCheck);
      var intersection = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.For(cancellationCheck));
      foreach (var entry in leftCounts) {
        cancellationCheck?.Invoke();
        if (rightCounts.TryGetValue(entry.Key, out var rightCount)) {
          var count = Math.Min(entry.Value, rightCount);
          if (count > 0) {
            intersection[entry.Key] = count;
          }
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(intersection, cancellationCheck), binary.Type);
    }
    return binary;
  }

  private Expression SimplifyMultiSetDifference(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0) || LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E0;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return new MultiSetDisplayExpr(binary.Origin, new List<Expression>()) { Type = binary.Type };
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements, cancellationCheck) &&
        AllElementsAreLiterals(rightDisplay.Elements, cancellationCheck)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements, cancellationCheck);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements, cancellationCheck);
      var difference = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.For(cancellationCheck));
      foreach (var entry in leftCounts) {
        cancellationCheck?.Invoke();
        rightCounts.TryGetValue(entry.Key, out var rightCount);
        var count = entry.Value - rightCount;
        if (count > 0) {
          difference[entry.Key] = count;
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(difference, cancellationCheck), binary.Type);
    }
    return binary;
  }

  private static List<Expression> ExpandMultisetCountsDict(Dictionary<Expression, int> counts, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var elements = new List<Expression>();
    foreach (var entry in counts) {
      cancellationCheck?.Invoke();
      for (var i = 0; i < entry.Value; i++) {
        cancellationCheck?.Invoke();
        elements.Add(entry.Key);
      }
    }
    return elements;
  }

  // ------------------- Inlining and caching -------------------

  /// <summary>
  /// Attempts to inline a function call into its body and then simplify the result.
  /// The inliner is intentionally conservative:
  /// - only side-effect-free functions (no reads, not opaque, revealed in scope)
  /// - bounded by depth, and guarded against cycles via an inlining call stack
  /// - caches static calls that fold to a literal to avoid repeated work
  /// </summary>
  private bool TryInlineCall(FunctionCallExpr callExpr, PartialEvalState state, PartialEvaluatorVisitor visitor, out Expression inlined) {
    CheckForCancellation();
    inlined = null;
    var function = callExpr.Function;
    if (function == null || function.Body == null) {
      return false;
    }

    var is_revealed_in_effective_scope = function.IsRevealedInScope(effectiveScope);
    if ((BoogieGenerator.IsOpaque(function, options) && !IsExplicitlyRevealed(function)) ||
        !is_revealed_in_effective_scope) {
      return false;
    }

    var stateful = function.ReadsHeap;
    if (heapReduction != null && (callExpr.AtLabel != null ||
        !ContractHeapReductionContext.IsHeapIndependent(callExpr.Receiver, cancellationCheck) ||
        !callExpr.Args.All(argument => ContractHeapReductionContext.IsHeapIndependent(argument, cancellationCheck)))) {
      heapReduction.ResidualReasons.Add("uncaptured_call_argument_or_label");
      return false;
    }
    if (heapReduction == null && function.Reads.Expressions is { Count: > 0 }) { return false; }

    var requiresConcreteCall = concreteCallBody || state.Depth <= 0;
    if (proofCompositionMode && concreteCallSession != null && (requiresConcreteCall || function.IsRecursive) &&
        function.IsStatic && !function.ReadsHeap && callExpr.AtLabel == null &&
        callExpr.Args.All(value => IsContractConcreteValue(value, cancellationCheck)) && IsClosedProofExpression(options, callExpr, cancellationCheck)) {
      if (concreteCallSession.TryEvaluate(this, callExpr, out var proof)) {
        ProofConcreteCalls.Add(proof);
        inlined = CloneResolvedExpression(proof.Value);
        return true;
      }
      if (requiresConcreteCall) { return false; }
    }

    var hasInlineableArgument = callExpr.Args.Count == 0;
    for (var i = 0; i < callExpr.Args.Count; i++) {
      CheckForCancellation();
      if (IsInlineableArgument(callExpr.Args[i], cancellationCheck)) {
        hasInlineableArgument = true;
        break;
      }
    }
    if (!hasInlineableArgument && UsesContractConcreteProfile) {
      hasInlineableArgument = callExpr.Args.Any(value => IsContractConcreteValue(value, cancellationCheck));
    }
    if (!hasInlineableArgument && !(heapReduction != null && stateful)) {
      return false;
    }

    if (state.Depth <= 0) {
      InlineDepthExhausted = true;
      return false;
    }

    var allInlineableArguments = AreAllInlineableArguments(callExpr.Args, cancellationCheck);
    var allContractConcreteArguments = UsesContractConcreteProfile &&
      callExpr.Args.All(value => IsContractConcreteValue(value, cancellationCheck));
    var allEligibleArguments = allInlineableArguments || allContractConcreteArguments;
    var hasQuantifiedRecursiveBody = function.IsRecursive && ContainsQuantifierOrComprehension(function.Body, cancellationCheck);
    if (hasQuantifiedRecursiveBody && !allContractConcreteArguments) {
      return false;
    }

    if (function.IsRecursive && !allEligibleArguments && !HasCollectionLiteralArgument(callExpr.Args, cancellationCheck)) {
      return false;
    }

    // Composition needs the exact candidate/dependency provenance from every
    // eligible visit. A cached literal has no instantiated-body certificate.
    if (!proofCompositionMode && !collectProofCompositionCandidates && TryGetCachedInlinedLiteral(callExpr, state, out inlined)) {
      return true;
    }

    var callKey = BuildInlineCallCycleKey(callExpr, UsesContractConcreteProfile);
    if (!state.InlineCallStack.Add(callKey)) {
      return false;
    }
    var addedFunction = state.InlineStack.Add(function);
    if (!addedFunction) {
      var canContinueRecursiveInlining = function.IsRecursive &&
        (HasCollectionLiteralArgument(callExpr.Args, cancellationCheck) ||
         UsesContractConcreteProfile && hasQuantifiedRecursiveBody && allContractConcreteArguments);
      if (!allEligibleArguments && !canContinueRecursiveInlining) {
        state.InlineCallStack.Remove(callKey);
        return false;
      }
    }

    Expression proofCall = null;
    if (collectProofCompositionCandidates && UsesContractConcreteProfile && !function.ReadsHeap &&
        !function.IsRecursive && callExpr.Type?.NormalizeExpand().IsBoolType == true &&
        callExpr.Args.All(value => IsContractConcreteValue(value, cancellationCheck)) &&
        (expressionExpansionBudget == null || expressionExpansionBudget.TryReserve(callExpr))) {
      proofCall = CloneResolvedExpression(callExpr);
    }

    try {
      var substMap = new Dictionary<IVariable, Expression>(function.Ins.Count);
      for (var i = 0; i < function.Ins.Count; i++) {
        CheckForCancellation();
        substMap[function.Ins[i]] = callExpr.Args[i];
      }

      Expression receiverReplacement = function.IsStatic ? null : callExpr.Receiver;
      if (UsesContractConcreteProfile && expressionExpansionBudget != null) {
        if (!expressionExpansionBudget.TryReserveSubstitution(function.Body, substMap, receiverReplacement)) {
          return false;
        }
      }
      var typeMap = callExpr.GetTypeArgumentSubstitutions();
      var substituter = CreateSubstituter(receiverReplacement, substMap, typeMap);
      // Substituter may return unchanged source subtrees. Heap-aware reduction
      // must not let its mutable visitor rewrite any original definition.
      var template = UsesContractConcreteProfile || heapReduction != null
        ? CloneResolvedExpression(function.Body) : function.Body;
      var body = substituter.Substitute(template);
      Expression proofBody = null;
      if (proofCall != null &&
          (expressionExpansionBudget == null || expressionExpansionBudget.TryReserve(body))) {
        proofBody = CloneResolvedExpression(body);
      }
      if (stateful && heapReduction != null) { heapReduction.StatefulInlines++; }
      var proofArtifacts = visitor.MarkProofArtifacts();
      inlined = visitor.SimplifyExpression(body, state.WithDepth(state.Depth - 1));
      if (proofCompositionMode && !IsContractConcreteValue(inlined, cancellationCheck)) {
        // Only a live existential may provisionally own a residual Boolean body's closed support.
        visitor.RollbackIncompleteInline(proofArtifacts, inlined);
      }
      if (proofCall != null && proofBody != null && IsClosedProofExpression(options, proofCall, cancellationCheck) &&
          IsClosedProofExpression(options, proofBody, cancellationCheck)) {
        ProofCompositionCandidates.Add(new ContractPredicateReductionCandidate(proofCall, proofBody, inlined));
      }
      if (inlined is LiteralExpr literal) {
        CacheInlinedLiteral(callExpr, state, literal);
      }

      return true;
    }
    finally {
      if (addedFunction) {
        state.InlineStack.Remove(function);
      }
      state.InlineCallStack.Remove(callKey);
    }
  }

  /// <summary>Tests all heap epochs without rejecting variables bound by an enclosing expression.</summary>
  internal static bool IsHeapIndependentProofExpression(DafnyOptions options, Expression expression) =>
    IsHeapIndependentProofExpression(options, expression, null);

  internal static bool IsHeapIndependentProofExpression(DafnyOptions options, Expression expression, Action cancellationCheck) {
    cancellationCheck?.Invoke();
    var freeVariables = new HashSet<IVariable>();
    var usesHeap = false;
    var usesOldHeap = false;
    var heapLabels = new HashSet<Label>();
    Type usesThis = null;
    FreeVariablesUtil.ComputeFreeVariables(options, expression, freeVariables,
      ref usesHeap, ref usesOldHeap, heapLabels, ref usesThis, includeStatements: true, cancellationCheck: cancellationCheck);
    return !usesHeap && !usesOldHeap && heapLabels.Count == 0 && usesThis == null;
  }

  /// <summary>Recognizes pure expressions whose proof can be emitted outside any enclosing binder.</summary>
  internal static bool IsClosedProofExpression(DafnyOptions options, Expression expression) =>
    IsClosedProofExpression(options, expression, null);

  internal static bool IsClosedProofExpression(DafnyOptions options, Expression expression, Action cancellationCheck) {
    cancellationCheck?.Invoke();
    var freeVariables = new HashSet<IVariable>();
    var usesHeap = false;
    FreeVariablesUtil.ComputeFreeVariables(options, expression, freeVariables, ref usesHeap, includeStatements: true, cancellationCheck: cancellationCheck);
    return IsHeapIndependentProofExpression(options, expression, cancellationCheck) &&
      freeVariables.All(variable => { cancellationCheck?.Invoke(); return variable is not BoundVar; });
  }

  internal bool IsExplicitlyRevealed(Function function) =>
    (heapReduction?.Context.IsRevealed(function) ?? false) || (isExplicitlyRevealed?.Invoke(function) ?? false);

  internal bool TryCreateProofCompositionCandidate(FunctionCallExpr callExpr,
    out ContractPredicateReductionCandidate candidate) {
    CheckForCancellation();
    candidate = null;
    var function = callExpr.Function;
    if (!collectProofCompositionCandidates || function == null || function.Body == null ||
        function.IsRecursive || callExpr.Type?.NormalizeExpand().IsBoolType != true ||
        !callExpr.Args.All(value => IsContractConcreteValue(value, cancellationCheck)) || function.ReadsHeap ||
        BoogieGenerator.IsOpaque(function, options) && !IsExplicitlyRevealed(function) ||
        !function.IsRevealedInScope(effectiveScope)) {
      return false;
    }
    if (expressionExpansionBudget != null && !expressionExpansionBudget.TryReserve(callExpr)) {
      return false;
    }
    var proofCall = CloneResolvedExpression(callExpr);
    var substitutions = new Dictionary<IVariable, Expression>(function.Ins.Count);
    for (var i = 0; i < function.Ins.Count; i++) {
      CheckForCancellation();
      substitutions[function.Ins[i]] = callExpr.Args[i];
    }
    Expression receiver = function.IsStatic ? null : callExpr.Receiver;
    if (expressionExpansionBudget != null &&
        !expressionExpansionBudget.TryReserveSubstitution(function.Body, substitutions, receiver)) {
      return false;
    }
    var substituter = CreateSubstituter(receiver, substitutions, callExpr.GetTypeArgumentSubstitutions());
    var body = substituter.Substitute(function.Body);
    if (expressionExpansionBudget != null && !expressionExpansionBudget.TryReserve(body)) {
      return false;
    }
    var proofBody = CloneResolvedExpression(body);
    if (!IsClosedProofExpression(options, proofCall, cancellationCheck) || !IsClosedProofExpression(options, proofBody, cancellationCheck)) {
      return false;
    }
    candidate = new ContractPredicateReductionCandidate(proofCall, proofBody, proofBody);
    return true;
  }

  // ------------------- Inlined-literal cache -------------------

  private bool TryGetCachedInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, out Expression inlined) {
    inlined = null;
    if (heapReduction != null) { return false; }
    var function = callExpr.Function;
    if (function == null || !function.IsStatic) {
      return false;
    }

    if (!TryBuildInlineCallCacheKey(callExpr, state, out var key, cancellationCheck)) {
      return false;
    }

    if (!inlineCallCache.TryGetValue(key, out var cached)) {
      return false;
    }

    inlined = cached.CreateLiteral(callExpr.Origin);
    return true;
  }

  private void CacheInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, LiteralExpr literal) {
    if (heapReduction != null) { return; }
    var function = callExpr.Function;
    if (function == null || !function.IsStatic) {
      return;
    }

    if (!TryBuildInlineCallCacheKey(callExpr, state, out var key, cancellationCheck)) {
      return;
    }

    if (CachedLiteral.TryCreate(literal, out var cached, cancellationCheck)) {
      inlineCallCache.TryAdd(key, cached);
    }
  }

  // ------------------- Inlining cache keys -------------------

  private static bool TryBuildInlineCallCacheKey(FunctionCallExpr callExpr, PartialEvalState state, out string key, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    key = null;

    var function = callExpr.Function;
    if (function == null) {
      return false;
    }

    foreach (var arg in callExpr.Args) {

      cancellationCheck?.Invoke();
      if (!TryGetReducedIntLiteral(arg, out _, cancellationCheck) && !Expression.IsBoolLiteral(arg, out _) &&
          arg is not CharLiteralExpr && arg is not StringLiteralExpr) {
        return false;
      }
    }

    var stackKey = BuildInlineStackKey(state.InlineStack, function, cancellationCheck);
    var callKey = BuildInlineCallCacheCallKey(callExpr, cancellationCheck);

    key = $"{RuntimeHelpers.GetHashCode(function)}|d={state.Depth}|s={stackKey}|c={callKey}";
    return true;
  }

  // List.Sort wraps comparer exceptions; retain the query boundary's original cancellation exception.
  private static void SortWithCancellation<T>(List<T> values, Comparison<T> comparison, Action cancellationCheck) {
    cancellationCheck?.Invoke();
    try {
      values.Sort((left, right) => {
        cancellationCheck?.Invoke();
        return comparison(left, right);
      });
    } catch (InvalidOperationException exception) when (exception.InnerException is OperationCanceledException) {
      System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(exception.InnerException).Throw();
      throw;
    }
    cancellationCheck?.Invoke();
  }

  private static string BuildInlineStackKey(HashSet<Function> inlineStack, Function functionToExclude, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (inlineStack == null || inlineStack.Count == 0) {
      return "";
    }

    List<int> ids = null;
    foreach (var f in inlineStack) {
      cancellationCheck?.Invoke();
      if (ReferenceEquals(f, functionToExclude)) {
        continue;
      }
      ids ??= new List<int>();
      ids.Add(RuntimeHelpers.GetHashCode(f));
    }

    if (ids == null || ids.Count == 0) {
      return "";
    }

    SortWithCancellation(ids, (left, right) => left.CompareTo(right), cancellationCheck);
    return string.Join(",", ids);
  }

  /// <summary>
  /// Builds a cache-key fragment from a FunctionCallExpr's literal arguments and type applications,
  /// avoiding the expensive callExpr.ToString() which serializes the entire AST subtree.
  /// Only called when all args are known to be int or bool literals (checked by the caller's guard).
  /// </summary>
  private static string BuildInlineCallCacheCallKey(FunctionCallExpr callExpr, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var builder = new StringBuilder();
    for (var i = 0; i < callExpr.Args.Count; i++) {
      cancellationCheck?.Invoke();
      if (i > 0) {
        builder.Append(',');
      }
      var arg = callExpr.Args[i];
      if (TryGetReducedIntLiteral(arg, out var intVal, cancellationCheck)) {
        builder.Append('i').Append(intVal);
      } else if (Expression.IsBoolLiteral(arg, out var boolVal)) {
        builder.Append('b').Append(boolVal ? '1' : '0');
      } else if (arg is CharLiteralExpr charArg && charArg.Value is string charStr) {
        builder.Append('c').Append(charStr);
      } else if (arg is StringLiteralExpr strArg && strArg.Value is string strVal) {
        builder.Append('s').Append(strVal.Length).Append(':').Append(strVal);
      }
    }
    if (callExpr.TypeApplication_AtEnclosingClass is { Count: > 0 }) {
      builder.Append("|t=");
      for (var i = 0; i < callExpr.TypeApplication_AtEnclosingClass.Count; i++) {
        cancellationCheck?.Invoke();
        if (i > 0) {
          builder.Append(',');
        }
        builder.Append(callExpr.TypeApplication_AtEnclosingClass[i]);
      }
    }
    if (callExpr.TypeApplication_JustFunction is { Count: > 0 }) {
      builder.Append("|tf=");
      for (var i = 0; i < callExpr.TypeApplication_JustFunction.Count; i++) {
        cancellationCheck?.Invoke();
        if (i > 0) {
          builder.Append(',');
        }
        builder.Append(callExpr.TypeApplication_JustFunction[i]);
      }
    }
    return builder.ToString();
  }

  // ------------------- Literal constructors -------------------

  internal static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value) {
    return new LiteralExpr(origin, value) { Type = Type.Int };
  }

  private static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value, Type type) {
    return new LiteralExpr(origin, value) { Type = type };
  }

  internal static LiteralExpr CreateCharLiteral(IOrigin origin, string value, Type type) {
    return new CharLiteralExpr(origin, value) { Type = type };
  }

  internal static LiteralExpr CreateStringLiteral(IOrigin origin, string value, Type type, bool isVerbatim) {
    return new StringLiteralExpr(origin, value, isVerbatim) { Type = type };
  }

  internal static SeqDisplayExpr CreateSeqDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    return new SeqDisplayExpr(origin, elements) { Type = type };
  }

  private static SetDisplayExpr CreateSetDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    var setType = type.NormalizeExpand().AsSetType;
    return new SetDisplayExpr(origin, setType.Finite, elements) { Type = type };
  }

  private static MultiSetDisplayExpr CreateMultiSetDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    return new MultiSetDisplayExpr(origin, elements) { Type = type };
  }

  private static MapDisplayExpr CreateMapDisplayLiteral(IOrigin origin, List<MapDisplayEntry> elements, Type type) {
    var mapType = type.NormalizeExpand().AsMapType;
    return new MapDisplayExpr(origin, mapType.Finite, elements) { Type = type };
  }

  // ------------------- Literal extraction / parsing -------------------

  private static bool TryGetStringLiteral(Expression expr, out string value, out bool isVerbatim) {
    value = null;
    isVerbatim = false;
    if (expr is StringLiteralExpr stringLiteral) {
      value = stringLiteral.Value as string;
      isVerbatim = stringLiteral.IsVerbatim;
      return value != null;
    }
    return false;
  }

  private static bool TryGetCharLiteral(Expression expr, out char value, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = default;
    if (expr is not CharLiteralExpr charLiteral || charLiteral.Value is not string literal) {
      return false;
    }

    if (literal.Length == 1) {
      value = literal[0];
      return true;
    }

    if (literal.Length == 2 && literal[0] == '\\') {
      value = literal[1] switch {
        '0' => '\0',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '\\' => '\\',
        '\'' => '\'',
        '"' => '"',
        _ => default
      };
      return value != default || literal[1] == '0';
    }

    if (literal.StartsWith("\\u", StringComparison.Ordinal) && literal.Length == 6 &&
        TryParseHex(literal.AsSpan(2), out var utf16Code, cancellationCheck)) {
      value = (char)utf16Code;
      return true;
    }

    if (literal.StartsWith("\\U{", StringComparison.Ordinal) && literal.EndsWith("}", StringComparison.Ordinal)) {
      var hexSpan = literal.AsSpan(3, literal.Length - 4);
      if (TryParseHex(hexSpan, out var unicodeCode, cancellationCheck) && unicodeCode <= 0xFFFF) {
        value = (char)unicodeCode;
        return true;
      }
    }

    return false;
  }

  private static bool TryParseHex(ReadOnlySpan<char> hexSpan, out int value, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = 0;
    if (hexSpan.IsEmpty) {
      return false;
    }

    foreach (var ch in hexSpan) {

      cancellationCheck?.Invoke();
      int digit;
      if (ch is >= '0' and <= '9') {
        digit = ch - '0';
      } else if (ch is >= 'a' and <= 'f') {
        digit = ch - 'a' + 10;
      } else if (ch is >= 'A' and <= 'F') {
        digit = ch - 'A' + 10;
      } else {
        return false;
      }
      value = (value << 4) + digit;
    }

    return true;
  }

  private static bool TryGetSeqDisplayLiteral(Expression expr, out SeqDisplayExpr display) {
    display = expr as SeqDisplayExpr;
    return display != null;
  }

  private bool TryGetCharSeqDisplayLiteral(Expression expr, out List<int> codePoints) {
    codePoints = null;
    if (!TryGetSeqDisplayLiteral(expr, out var display)) {
      return false;
    }

    var result = new List<int>(display.Elements.Count);
    foreach (var element in display.Elements) {
      cancellationCheck?.Invoke();
      if (element is not CharLiteralExpr { Value: string literal }) {
        return false;
      }
      var characters = new List<int>();
      foreach (var character in Util.UnescapedCharacters(options, literal, false)) {
        CheckForCancellation();
        characters.Add(character);
      }
      if (characters.Count != 1) { return false; }
      result.Add(characters[0]);
    }

    codePoints = result;
    return true;
  }

  private bool TryGetUnescapedStringCharacters(Expression expr, out List<int> codePoints) {
    codePoints = null;
    if (!TryGetStringLiteral(expr, out var value, out var isVerbatim)) {
      return false;
    }

    codePoints = new List<int>();
    foreach (var codePoint in Util.UnescapedCharacters(options, value, isVerbatim)) {
      CheckForCancellation();
      codePoints.Add(codePoint);
    }
    return true;
  }

  private static bool TryGetTupleLiteral(Expression expr, out DatatypeValue tuple) {
    tuple = expr as DatatypeValue;
    if (tuple == null) {
      return false;
    }
    if (tuple.Ctor?.EnclosingDatatype is TupleTypeDecl) {
      return true;
    }
    return tuple.MemberName.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix, StringComparison.Ordinal);
  }

  // ------------------- Literal classification helpers -------------------

  private static bool AllElementsAreLiterals(SeqDisplayExpr display, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    return AllElementsAreLiterals(display.Elements, cancellationCheck);
  }

  private static bool TryGetSetDisplayLiteral(Expression expr, out SetDisplayExpr display) {
    display = expr as SetDisplayExpr;
    return display != null;
  }

  private static bool TryGetMultiSetDisplayLiteral(Expression expr, out MultiSetDisplayExpr display) {
    display = expr as MultiSetDisplayExpr;
    return display != null;
  }

  private static bool TryGetMapDisplayLiteral(Expression expr, out MapDisplayExpr display) {
    display = expr as MapDisplayExpr;
    return display != null;
  }

  private static bool AllElementsAreLiterals(IEnumerable<Expression> elements, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    return elements.All(value => IsLiteralLike(value, cancellationCheck));
  }

  private static bool AllElementsAreLiterals(MapDisplayExpr display, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    return display.Elements.All(entry => IsLiteralLike(entry.A, cancellationCheck) && IsLiteralLike(entry.B, cancellationCheck));
  }

  private static bool AllMapKeysAreLiterals(MapDisplayExpr display, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    return display.Elements.All(entry => IsLiteralLike(entry.A, cancellationCheck));
  }

  private static bool IsLiteralLike(Expression expr, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (expr is LiteralExpr) {
      return true;
    }
    if (expr is SeqDisplayExpr seqDisplay) {
      return AllElementsAreLiterals(seqDisplay.Elements, cancellationCheck);
    }
    if (expr is SetDisplayExpr setDisplay) {
      return AllElementsAreLiterals(setDisplay.Elements, cancellationCheck);
    }
    if (expr is MultiSetDisplayExpr multiSetDisplay) {
      return AllElementsAreLiterals(multiSetDisplay.Elements, cancellationCheck);
    }
    if (expr is MapDisplayExpr mapDisplay) {
      return AllElementsAreLiterals(mapDisplay, cancellationCheck);
    }
    if (TryGetTupleLiteral(expr, out var tuple)) {
      return AllElementsAreLiterals(tuple.Arguments, cancellationCheck);
    }
    return false;
  }

  // ------------------- Inlineability -------------------

  private static bool IsInlineableArgument(Expression expr, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    return IsLiteralLike(expr, cancellationCheck) || expr is LambdaExpr;
  }

  internal static bool AreAllInlineableArguments(IEnumerable<Expression> args) => AreAllInlineableArguments(args, null);

  internal static bool AreAllInlineableArguments(IEnumerable<Expression> args, Action cancellationCheck) {
    cancellationCheck?.Invoke();
    foreach (var arg in args) {
      cancellationCheck?.Invoke();
      if (!IsInlineableArgument(arg, cancellationCheck)) {
        return false;
      }
    }

    return true;
  }

  private static bool ContainsQuantifierOrComprehension(Expression expr, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (expr is QuantifierExpr or ComprehensionExpr) {
      return true;
    }

    foreach (var subExpression in expr.SubExpressions) {

      cancellationCheck?.Invoke();
      if (ContainsQuantifierOrComprehension(subExpression, cancellationCheck)) {
        return true;
      }
    }

    return false;
  }

  private static bool HasCollectionLiteralArgument(IEnumerable<Expression> args, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    foreach (var arg in args) {
      cancellationCheck?.Invoke();
      var normalized = QuantifierBounds.StripConcreteSyntax(arg, cancellationCheck);
      if (normalized is SeqDisplayExpr or SetDisplayExpr or MultiSetDisplayExpr or MapDisplayExpr or StringLiteralExpr) {
        return true;
      }
    }

    return false;
  }

  // ------------------- Literal equality helpers -------------------

  private static bool AreLiteralExpressionsEqual(Expression left, Expression right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (TryGetCharLiteral(left, out var leftChar, cancellationCheck) && TryGetCharLiteral(right, out var rightChar, cancellationCheck)) {
      return leftChar == rightChar;
    }
    if (left is StringLiteralExpr leftStringLiteral && right is StringLiteralExpr rightStringLiteral &&
        leftStringLiteral.Value is string leftStringValue && rightStringLiteral.Value is string rightStringValue) {
      return StringLiteralsSemanticallyEqual(
        leftStringValue,
        leftStringLiteral.IsVerbatim,
        rightStringValue,
        rightStringLiteral.IsVerbatim, cancellationCheck);
    }
    if (left is LiteralExpr leftLiteral && right is LiteralExpr rightLiteral) {
      return Equals(leftLiteral.Value, rightLiteral.Value);
    }
    if (left is SeqDisplayExpr leftSeq && right is SeqDisplayExpr rightSeq) {
      return SeqDisplayLiteralsEqual(leftSeq, rightSeq, cancellationCheck);
    }
    if (left is SetDisplayExpr leftSet && right is SetDisplayExpr rightSet) {
      return SetDisplayLiteralsEqual(leftSet, rightSet, cancellationCheck);
    }
    if (left is MultiSetDisplayExpr leftMulti && right is MultiSetDisplayExpr rightMulti) {
      return MultiSetDisplayLiteralsEqual(leftMulti, rightMulti, cancellationCheck);
    }
    if (left is MapDisplayExpr leftMap && right is MapDisplayExpr rightMap) {
      return MapDisplayLiteralsEqual(leftMap, rightMap, cancellationCheck);
    }
    if (TryGetTupleLiteral(left, out var leftTuple) && TryGetTupleLiteral(right, out var rightTuple)) {
      return TupleLiteralsEqual(leftTuple, rightTuple, cancellationCheck);
    }
    return false;
  }

  private static bool TryGetIntLiteralValue(Expression expr, out int value, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = default;
    if (!TryGetReducedIntLiteral(expr, out var literal, cancellationCheck)) {
      return false;
    }
    if (literal < 0 || literal > int.MaxValue) {
      return false;
    }
    value = (int)literal;
    return true;
  }

  private static bool SeqDisplayLiteralsEqual(SeqDisplayExpr left, SeqDisplayExpr right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (left.Elements.Count != right.Elements.Count) {
      return false;
    }
    for (var i = 0; i < left.Elements.Count; i++) {
      cancellationCheck?.Invoke();
      if (!AreLiteralExpressionsEqual(left.Elements[i], right.Elements[i], cancellationCheck)) {
        return false;
      }
    }
    return true;
  }

  private static bool CodePointSequencesEqual(IReadOnlyList<int> left, IReadOnlyList<int> right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (left.Count != right.Count) {
      return false;
    }
    for (var index = 0; index < left.Count; index++) {
      cancellationCheck?.Invoke();
      if (left[index] != right[index]) {
        return false;
      }
    }
    return true;
  }

  private static bool CodePointSequenceHasPrefix(IReadOnlyList<int> prefix, IReadOnlyList<int> sequence, out bool isProper, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    isProper = false;
    if (prefix.Count > sequence.Count) {
      return false;
    }
    for (var index = 0; index < prefix.Count; index++) {
      cancellationCheck?.Invoke();
      if (prefix[index] != sequence[index]) {
        return false;
      }
    }
    isProper = prefix.Count < sequence.Count;
    return true;
  }

  private static List<int> GetSemanticStringCodePoints(string value, bool isVerbatim, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var result = new List<int>();
    foreach (var codePoint in Util.UnescapedCharacters(DafnyOptions.DefaultImmutableOptions, value, isVerbatim)) {
      cancellationCheck?.Invoke();
      result.Add(codePoint);
    }
    return result;
  }

  private static bool StringLiteralsSemanticallyEqual(string leftValue, bool leftVerbatim, string rightValue, bool rightVerbatim, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var leftCodePoints = GetSemanticStringCodePoints(leftValue, leftVerbatim, cancellationCheck);
    var rightCodePoints = GetSemanticStringCodePoints(rightValue, rightVerbatim, cancellationCheck);
    return CodePointSequencesEqual(leftCodePoints, rightCodePoints, cancellationCheck);
  }

  private static int ComputeSemanticStringHash(string value, bool isVerbatim, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var hash = new HashCode();
    hash.Add(typeof(StringLiteralExpr));
    foreach (var codePoint in GetSemanticStringCodePoints(value, isVerbatim, cancellationCheck)) {
      cancellationCheck?.Invoke();
      hash.Add(codePoint);
    }
    return hash.ToHashCode();
  }

  private static bool TupleLiteralsEqual(DatatypeValue left, DatatypeValue right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (left.Arguments.Count != right.Arguments.Count) {
      return false;
    }
    for (var i = 0; i < left.Arguments.Count; i++) {
      cancellationCheck?.Invoke();
      if (!AreLiteralExpressionsEqual(left.Arguments[i], right.Arguments[i], cancellationCheck)) {
        return false;
      }
    }
    return true;
  }

  private static bool SetDisplayLiteralsEqual(SetDisplayExpr left, SetDisplayExpr right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (left.Elements.Count == 0 && right.Elements.Count == 0) {
      return true;
    }
    if (!AllElementsAreLiterals(left.Elements, cancellationCheck) || !AllElementsAreLiterals(right.Elements, cancellationCheck)) {
      return false;
    }
    var leftDistinct = new LiteralSet(left.Elements, cancellationCheck);
    var rightDistinct = new LiteralSet(right.Elements, cancellationCheck);
    if (leftDistinct.Count != rightDistinct.Count) {
      return false;
    }
    foreach (var element in leftDistinct.Elements) {
      cancellationCheck?.Invoke();
      if (!rightDistinct.Contains(element)) {
        return false;
      }
    }
    return true;
  }

  private static bool MultiSetDisplayLiteralsEqual(MultiSetDisplayExpr left, MultiSetDisplayExpr right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (!AllElementsAreLiterals(left.Elements, cancellationCheck) || !AllElementsAreLiterals(right.Elements, cancellationCheck)) {
      return false;
    }
    var leftCounts = BuildMultisetCountsDict(left.Elements, cancellationCheck);
    var rightCounts = BuildMultisetCountsDict(right.Elements, cancellationCheck);
    if (leftCounts.Count != rightCounts.Count) {
      return false;
    }
    foreach (var entry in leftCounts) {
      cancellationCheck?.Invoke();
      if (!rightCounts.TryGetValue(entry.Key, out var rightCount) || rightCount != entry.Value) {
        return false;
      }
    }
    return true;
  }

  private static bool MapDisplayLiteralsEqual(MapDisplayExpr left, MapDisplayExpr right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (!TryNormalizeLiteralMapEntries(left, out var leftEntries, cancellationCheck) ||
        !TryNormalizeLiteralMapEntries(right, out var rightEntries, cancellationCheck)) {
      return false;
    }
    if (leftEntries.Count != rightEntries.Count) {
      return false;
    }

    var rightByKey = new Dictionary<Expression, Expression>(LiteralExpressionEqualityComparer.For(cancellationCheck));
    foreach (var entry in rightEntries) {
      cancellationCheck?.Invoke();
      rightByKey[entry.A] = entry.B;
    }

    foreach (var entry in leftEntries) {

      cancellationCheck?.Invoke();
      if (!rightByKey.TryGetValue(entry.A, out var rightValue) ||
          !AreLiteralExpressionsEqual(entry.B, rightValue, cancellationCheck)) {
        return false;
      }
    }

    return true;
  }

  private static bool TryNormalizeLiteralMapEntries(MapDisplayExpr mapDisplay, out List<MapDisplayEntry> normalizedEntries, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    normalizedEntries = null;
    if (!AllElementsAreLiterals(mapDisplay, cancellationCheck)) {
      return false;
    }

    var entries = new List<MapDisplayEntry>(mapDisplay.Elements.Count);
    var indexByKey = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.For(cancellationCheck));
    foreach (var entry in mapDisplay.Elements) {
      cancellationCheck?.Invoke();
      if (indexByKey.TryGetValue(entry.A, out var existingIndex)) {
        entries[existingIndex] = new MapDisplayEntry(entry.A, entry.B);
      } else {
        indexByKey[entry.A] = entries.Count;
        entries.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }

    normalizedEntries = entries;
    return true;
  }

  private static bool ContainsLiteralElement(List<Expression> elements, Expression candidate, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    foreach (var existing in elements) {
      cancellationCheck?.Invoke();
      if (AreLiteralExpressionsEqual(existing, candidate, cancellationCheck)) {
        return true;
      }
    }
    return false;
  }

  // ------------------- Multiset element counting -------------------

  private static Dictionary<Expression, int> BuildMultisetCountsDict(IEnumerable<Expression> elements, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var counts = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.For(cancellationCheck));
    foreach (var element in elements) {
      cancellationCheck?.Invoke();
      counts.TryGetValue(element, out var count);
      counts[element] = count + 1;
    }
    return counts;
  }

  private static bool SeqDisplayIsPrefix(SeqDisplayExpr left, SeqDisplayExpr right, out bool isProper, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    isProper = false;
    if (left.Elements.Count > right.Elements.Count) {
      return false;
    }
    for (var i = 0; i < left.Elements.Count; i++) {
      cancellationCheck?.Invoke();
      if (!AreLiteralExpressionsEqual(left.Elements[i], right.Elements[i], cancellationCheck)) {
        return false;
      }
    }
    isProper = left.Elements.Count < right.Elements.Count;
    return true;
  }

  // ------------------- Inlining cycle keys and cached literals -------------------

  private string BuildInlineCallCycleKey(FunctionCallExpr callExpr, bool useContractConcreteIdentity) {
    var builder = new StringBuilder();
    builder.Append(RuntimeHelpers.GetHashCode(callExpr.Function));
    builder.Append("|r=");
    if (!callExpr.Function.IsStatic) {
      builder.Append(RuntimeHelpers.GetHashCode(callExpr.Receiver));
    }
    builder.Append("|a=");
    for (var i = 0; i < callExpr.Args.Count; i++) {
      cancellationCheck?.Invoke();
      var arg = callExpr.Args[i];
      if (useContractConcreteIdentity && IsContractConcreteValue(arg, cancellationCheck)) {
        AppendContractConcreteIdentity(builder, arg);
      } else if (TryGetReducedIntLiteral(arg, out var intValue, cancellationCheck)) {
        builder.Append("i").Append(intValue);
      } else if (Expression.IsBoolLiteral(arg, out var boolValue)) {
        builder.Append("b").Append(boolValue ? "1" : "0");
      } else if (arg is SeqDisplayExpr seqDisplay && AllElementsAreLiterals(seqDisplay.Elements, cancellationCheck)) {
        builder.Append("q").Append(seqDisplay.Elements.Count);
      } else if (arg is StringLiteralExpr stringLiteral && stringLiteral.Value is string stringValue) {
        builder.Append("s").Append(stringValue.Length).Append(":").Append(stringValue);
      } else {
        builder.Append("x");
      }
      if (i < callExpr.Args.Count - 1) {
        builder.Append(",");
      }
    }
    builder.Append("|t=");
    if (callExpr.TypeApplication_AtEnclosingClass != null) {
      builder.Append(string.Join(",", callExpr.TypeApplication_AtEnclosingClass.Select(t => { cancellationCheck?.Invoke(); var result = t.ToString(); cancellationCheck?.Invoke(); return result; })));
    }
    builder.Append("|tf=");
    if (callExpr.TypeApplication_JustFunction != null) {
      builder.Append(string.Join(",", callExpr.TypeApplication_JustFunction.Select(t => { cancellationCheck?.Invoke(); var result = t.ToString(); cancellationCheck?.Invoke(); return result; })));
    }
    return builder.ToString();
  }

  private static Expression NormalizeContractConcreteExpression(Expression expression, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    while (true) {
      cancellationCheck?.Invoke();
      if (expression is ConcreteSyntaxExpression { ResolvedExpression: not null } concreteSyntax) {
        expression = concreteSyntax.ResolvedExpression;
        continue;
      }
      if (expression is ConversionExpr conversionExpr &&
          TryEvaluateContractConcreteConversion(conversionExpr, out var convertedLiteral, cancellationCheck)) {
        expression = convertedLiteral;
        continue;
      }
      return expression;
    }
  }

  /// <summary>Reads an integer value without erasing an unchecked constrained conversion.</summary>
  internal static bool TryGetReducedIntLiteral(Expression expression, out BigInteger value, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    expression = NormalizeContractConcreteExpression(expression, cancellationCheck);
    // Expression.IsIntLiteral strips all casts, including rejected subset conversions.
    if (expression is LiteralExpr) {
      return Expression.IsIntLiteral(expression, out value);
    }
    value = default;
    return false;
  }

  private static bool TryEvaluateContractConcreteConversion(
    ConversionExpr conversionExpr, out LiteralExpr convertedLiteral, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    convertedLiteral = null;
    var targetType = conversionExpr.Type;
    if (targetType == null) {
      return false;
    }
    var constraintPreservingTargetType = targetType.NormalizeExpandKeepConstraints();
    if (constraintPreservingTargetType.AsSubsetType != null) {
      return false;
    }
    var unconstrainedTargetType = ConstantFolder.AsUnconstrainedType(constraintPreservingTargetType);
    if (unconstrainedTargetType == null ||
        unconstrainedTargetType is not IntType && !unconstrainedTargetType.IsBitVectorType && !unconstrainedTargetType.IsCharType) {
      return false;
    }

    var operand = NormalizeContractConcreteExpression(conversionExpr.E, cancellationCheck);
    if (operand is not LiteralExpr || operand.Type == null) {
      return false;
    }
    var operandType = operand.Type;
    if (!operandType.IsBitVectorType &&
        !operandType.IsNumericBased(Type.NumericPersuasion.Int) &&
        !operandType.IsCharType) {
      return false;
    }

    if (operand is CharLiteralExpr { Value: string encodedCharacter } &&
        operandType.NormalizeExpandKeepConstraints() is CharType &&
        constraintPreservingTargetType is CharType) {
      // Subset membership substitution introduces identity casts; preserve the literal's original character encoding.
      convertedLiteral = CreateCharLiteral(operand.Origin, encodedCharacter, targetType);
      return true;
    }

    // ConstantFolder interprets raw escaped character text as its first code unit.
    // Decode supported BMP literals explicitly; supplementary conversions remain native obligations.
    if (operandType.IsCharType) {
      if (!TryGetCharLiteral(operand, out var character, cancellationCheck) || unconstrainedTargetType.IsCharType ||
          unconstrainedTargetType.IsBitVectorType && character > ConstantFolder.MaxBv(unconstrainedTargetType)) {
        return false;
      }
      convertedLiteral = CreateIntLiteral(conversionExpr.Origin, character, targetType);
      return true;
    }
    if (unconstrainedTargetType.IsCharType) {
      if (!TryGetReducedIntLiteral(operand, out var scalar, cancellationCheck) || scalar < 0 || scalar > 0xFFFF ||
          scalar >= 0xD800 && scalar <= 0xDFFF) {
        return false;
      }
      // These scalar values are valid in both legacy and Unicode character modes.
      convertedLiteral = new CharLiteralExpr(conversionExpr.Origin,
        "\\U{" + ((int)scalar).ToString("X", System.Globalization.CultureInfo.InvariantCulture) + "}") { Type = targetType };
      return true;
    }

    var conversionToFold = ReferenceEquals(operand, conversionExpr.E)
      ? conversionExpr
      : new ConversionExpr(conversionExpr.Origin, operand, targetType) { Type = targetType };
    if (ConstantFolder.TryFoldInteger(conversionToFold) is not { } value) {
      return false;
    }

    convertedLiteral = CreateIntLiteral(conversionExpr.Origin, value, targetType);
    return true;
  }

  internal static bool IsContractConcreteValue(Expression expression) => IsContractConcreteValue(expression, null);

  internal static bool IsContractConcreteValue(Expression expression, Action cancellationCheck) {
    cancellationCheck?.Invoke();
    expression = NormalizeContractConcreteExpression(expression, cancellationCheck);
    if (expression is LiteralExpr) {
      return true;
    }
    if (expression is SeqDisplayExpr sequence) {
      return sequence.Elements.All(value => IsContractConcreteValue(value, cancellationCheck));
    }
    if (expression is SetDisplayExpr set) {
      return set.Elements.All(value => IsContractConcreteValue(value, cancellationCheck));
    }
    if (expression is MultiSetDisplayExpr multiset) {
      return multiset.Elements.All(value => IsContractConcreteValue(value, cancellationCheck));
    }
    if (expression is MapDisplayExpr map) {
      return map.Finite && map.Elements.All(entry =>
        IsContractConcreteValue(entry.A, cancellationCheck) && IsContractConcreteValue(entry.B, cancellationCheck));
    }
    return expression is DatatypeValue { Ctor: not null } datatype &&
           datatype.Arguments.All(value => IsContractConcreteValue(value, cancellationCheck));
  }

  private static bool AreContractConcreteExpressionsEqual(Expression left, Expression right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    left = NormalizeContractConcreteExpression(left, cancellationCheck);
    right = NormalizeContractConcreteExpression(right, cancellationCheck);
    if (left is DatatypeValue leftDatatype && right is DatatypeValue rightDatatype) {
      return ReferenceEquals(leftDatatype.Ctor, rightDatatype.Ctor) &&
             leftDatatype.Arguments.Count == rightDatatype.Arguments.Count &&
             leftDatatype.Arguments.Zip(rightDatatype.Arguments)
               .All(arguments => AreContractConcreteExpressionsEqual(arguments.First, arguments.Second, cancellationCheck));
    }
    if (left is SeqDisplayExpr leftSequence && right is SeqDisplayExpr rightSequence) {
      return leftSequence.Elements.Count == rightSequence.Elements.Count &&
             leftSequence.Elements.Zip(rightSequence.Elements)
               .All(elements => AreContractConcreteExpressionsEqual(elements.First, elements.Second, cancellationCheck));
    }
    if (left is SetDisplayExpr leftSet && right is SetDisplayExpr rightSet) {
      return ContractConcreteSetEquals(leftSet.Elements, rightSet.Elements, cancellationCheck);
    }
    if (left is MultiSetDisplayExpr leftMultiset && right is MultiSetDisplayExpr rightMultiset) {
      return ContractConcreteMultisetEquals(leftMultiset.Elements, rightMultiset.Elements, cancellationCheck);
    }
    if (left is MapDisplayExpr leftMap && right is MapDisplayExpr rightMap) {
      return ContractConcreteMapEquals(leftMap, rightMap, cancellationCheck);
    }
    return AreLiteralExpressionsEqual(left, right, cancellationCheck);
  }

  private static bool ContractConcreteSetEquals(IReadOnlyList<Expression> left, IReadOnlyList<Expression> right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var comparer = ContractConcreteExpressionEqualityComparer.For(cancellationCheck);
    return new HashSet<Expression>(left, comparer).SetEquals(new HashSet<Expression>(right, comparer));
  }

  private static bool ContractConcreteMultisetEquals(
    IReadOnlyList<Expression> left, IReadOnlyList<Expression> right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var comparer = ContractConcreteExpressionEqualityComparer.For(cancellationCheck);
    var counts = new Dictionary<Expression, int>(comparer);
    foreach (var expression in left) {
      cancellationCheck?.Invoke();
      counts.TryGetValue(expression, out var count);
      counts[expression] = count + 1;
    }
    foreach (var expression in right) {
      cancellationCheck?.Invoke();
      if (!counts.TryGetValue(expression, out var count)) {
        return false;
      }
      if (count == 1) {
        counts.Remove(expression);
      } else {
        counts[expression] = count - 1;
      }
    }
    return counts.Count == 0;
  }

  private static bool ContractConcreteMapEquals(MapDisplayExpr left, MapDisplayExpr right, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (!TryNormalizeContractConcreteMapEntries(left, out var leftEntries, cancellationCheck) ||
        !TryNormalizeContractConcreteMapEntries(right, out var rightEntries, cancellationCheck) ||
        leftEntries.Count != rightEntries.Count) {
      return false;
    }
    var rightByKey = new Dictionary<Expression, Expression>(ContractConcreteExpressionEqualityComparer.For(cancellationCheck));
    foreach (var entry in rightEntries) {
      cancellationCheck?.Invoke();
      rightByKey[entry.A] = entry.B;
    }
    return leftEntries.All(entry => rightByKey.TryGetValue(entry.A, out var rightValue) &&
                                    AreContractConcreteExpressionsEqual(entry.B, rightValue, cancellationCheck));
  }

  private static bool TryNormalizeContractConcreteMapEntries(
    MapDisplayExpr map, out List<MapDisplayEntry> normalizedEntries, Action cancellationCheck = null) {
    cancellationCheck?.Invoke();
    normalizedEntries = null;
    if (!IsContractConcreteValue(map, cancellationCheck)) {
      return false;
    }
    normalizedEntries = [];
    var indexByKey = new Dictionary<Expression, int>(ContractConcreteExpressionEqualityComparer.For(cancellationCheck));
    foreach (var entry in map.Elements) {
      cancellationCheck?.Invoke();
      if (indexByKey.TryGetValue(entry.A, out var existingIndex)) {
        normalizedEntries[existingIndex] = new MapDisplayEntry(entry.A, entry.B);
      } else {
        indexByKey[entry.A] = normalizedEntries.Count;
        normalizedEntries.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }
    return true;
  }

  private void AppendContractConcreteIdentity(StringBuilder builder, Expression expression) {
    expression = NormalizeContractConcreteExpression(expression, cancellationCheck);
    switch (expression) {
      case DatatypeValue datatype:
        builder.Append("d").Append(GetContractConcreteConstructorId(datatype.Ctor)).Append("[");
        AppendContractConcreteIdentities(builder, datatype.Arguments);
        builder.Append("]");
        return;
      case SeqDisplayExpr sequence:
        builder.Append("q[");
        AppendContractConcreteIdentities(builder, sequence.Elements);
        builder.Append("]");
        return;
      case SetDisplayExpr set:
        AppendOrderIndependentConcreteIdentity(builder, "e", set.Elements);
        return;
      case MultiSetDisplayExpr multiset:
        AppendOrderIndependentConcreteIdentity(builder, "u", multiset.Elements);
        return;
      case MapDisplayExpr map when TryNormalizeContractConcreteMapEntries(map, out var entries, cancellationCheck):
        var mapParts = entries.Select(entry => {
          var part = new StringBuilder();
          AppendContractConcreteIdentity(part, entry.A);
          part.Append("=");
          AppendContractConcreteIdentity(part, entry.B);
          return part.ToString();
        }).ToList();
        SortWithCancellation(mapParts, StringComparer.Ordinal.Compare, cancellationCheck);
        builder.Append("m{").Append(string.Join(";", mapParts)).Append("}");
        return;
      case StringLiteralExpr stringLiteral when stringLiteral.Value is string value:
        builder.Append("s").Append(value.Length).Append(":").Append(value)
          .Append(stringLiteral.IsVerbatim ? "v" : "e");
        return;
      case LiteralExpr literal:
        builder.Append("l").Append(literal.Value?.GetType().FullName).Append(":")
          .Append(literal.Value);
        return;
      default:
        builder.Append("x");
        return;
    }
  }

  private void AppendContractConcreteIdentities(StringBuilder builder, IEnumerable<Expression> expressions) {
    var first = true;
    foreach (var expression in expressions) {
      cancellationCheck?.Invoke();
      if (!first) {
        builder.Append(",");
      }
      AppendContractConcreteIdentity(builder, expression);
      first = false;
    }
  }

  private void AppendOrderIndependentConcreteIdentity(
    StringBuilder builder, string prefix, IEnumerable<Expression> expressions) {
    var parts = expressions.Select(expression => {
      var part = new StringBuilder();
      AppendContractConcreteIdentity(part, expression);
      return part.ToString();
    }).ToList();
    SortWithCancellation(parts, StringComparer.Ordinal.Compare, cancellationCheck);
    builder.Append(prefix).Append("{").Append(string.Join(";", parts)).Append("}");
  }

  private uint GetContractConcreteConstructorId(DatatypeCtor constructor) {
    if (contractConcreteConstructorIds.TryGetValue(constructor, out var id)) {
      return id;
    }
    id = nextContractConcreteConstructorId++;
    contractConcreteConstructorIds.Add(constructor, id);
    return id;
  }

  // ------------------- Cached literal representation -------------------

  private enum CachedLiteralKind {
    Int,
    Bool,
    Char,
    String
  }

  private readonly record struct CachedLiteral(CachedLiteralKind Kind, BigInteger IntValue, bool BoolValue, string StringValue, Type LiteralType) {
    public static bool TryCreate(LiteralExpr literal, out CachedLiteral cached, Action cancellationCheck = null) {
      cached = default;
      if (literal == null) {
        return false;
      }

      if (TryGetReducedIntLiteral(literal, out var intValue, cancellationCheck)) {
        cached = new CachedLiteral(CachedLiteralKind.Int, intValue, default, default, literal.Type);
        return true;
      }

      if (Expression.IsBoolLiteral(literal, out var boolValue)) {
        cached = new CachedLiteral(CachedLiteralKind.Bool, default, boolValue, default, literal.Type);
        return true;
      }

      if (literal is CharLiteralExpr charLiteral && charLiteral.Value is string charStr) {
        cached = new CachedLiteral(CachedLiteralKind.Char, default, default, charStr, literal.Type);
        return true;
      }

      if (literal is StringLiteralExpr stringLiteral && stringLiteral.Value is string strVal) {
        cached = new CachedLiteral(CachedLiteralKind.String, default, stringLiteral.IsVerbatim, strVal, literal.Type);
        return true;
      }

      return false;
    }

    public Expression CreateLiteral(IOrigin origin) {
      return Kind switch {
        CachedLiteralKind.Int => CreateIntLiteral(origin, IntValue, LiteralType),
        CachedLiteralKind.Bool => SetLiteralType(CreateBoolLiteral(origin, BoolValue), LiteralType),
        CachedLiteralKind.Char => CreateCharLiteral(origin, StringValue, LiteralType),
        CachedLiteralKind.String => CreateStringLiteral(origin, StringValue, LiteralType, BoolValue),
        _ => null
      };
    }

    private static Expression SetLiteralType(Expression literal, Type literalType) {
      literal.Type = literalType;
      return literal;
    }
  }

  // ------------------- Hash-based literal collections -------------------

  private sealed class ContractConcreteExpressionEqualityComparer : IEqualityComparer<Expression> {
    public static readonly ContractConcreteExpressionEqualityComparer Instance = new();
    private readonly Action cancellationCheck;

    private ContractConcreteExpressionEqualityComparer(Action cancellationCheck = null) {
      this.cancellationCheck = cancellationCheck;
    }

    internal static ContractConcreteExpressionEqualityComparer For(Action cancellationCheck) =>
      cancellationCheck == null ? Instance : new ContractConcreteExpressionEqualityComparer(cancellationCheck);

    public bool Equals(Expression x, Expression y) {
      cancellationCheck?.Invoke();
      if (ReferenceEquals(x, y)) {
        return true;
      }
      return x != null && y != null && AreContractConcreteExpressionsEqual(x, y, cancellationCheck);
    }

    public int GetHashCode(Expression expression) {
      cancellationCheck?.Invoke();
      if (expression == null) {
        return 0;
      }
      expression = NormalizeContractConcreteExpression(expression, cancellationCheck);
      if (expression is DatatypeValue datatype) {
        var hash = new HashCode();
        hash.Add(typeof(DatatypeValue));
        hash.Add(datatype.Ctor);
        foreach (var argument in datatype.Arguments) {
          cancellationCheck?.Invoke();
          hash.Add(GetHashCode(argument));
        }
        return hash.ToHashCode();
      }
      if (expression is SeqDisplayExpr sequence) {
        var hash = new HashCode();
        hash.Add(typeof(SeqDisplayExpr));
        foreach (var element in sequence.Elements) {
          cancellationCheck?.Invoke();
          hash.Add(GetHashCode(element));
        }
        return hash.ToHashCode();
      }
      if (expression is SetDisplayExpr set) {
        return ComputeOrderIndependentHash(typeof(SetDisplayExpr),
          new HashSet<Expression>(set.Elements, this));
      }
      if (expression is MultiSetDisplayExpr multiset) {
        var counts = new Dictionary<Expression, int>(this);
        foreach (var element in multiset.Elements) {
          cancellationCheck?.Invoke();
          counts.TryGetValue(element, out var count);
          counts[element] = count + 1;
        }
        return ComputeOrderIndependentHash(typeof(MultiSetDisplayExpr), counts.Select(entry =>
          HashCode.Combine(GetHashCode(entry.Key), entry.Value)));
      }
      if (expression is MapDisplayExpr map && TryNormalizeContractConcreteMapEntries(map, out var entries, cancellationCheck)) {
        return ComputeOrderIndependentHash(typeof(MapDisplayExpr), entries.Select(entry =>
          HashCode.Combine(GetHashCode(entry.A), GetHashCode(entry.B))));
      }
      return LiteralExpressionEqualityComparer.For(cancellationCheck).GetHashCode(expression);
    }

    private int ComputeOrderIndependentHash(System.Type expressionType, IEnumerable<Expression> expressions) {
      return ComputeOrderIndependentHash(expressionType,
        expressions.Select(GetHashCode));
    }

    private int ComputeOrderIndependentHash(System.Type expressionType, IEnumerable<int> hashes) {
      var count = 0;
      var sum = 0;
      var xor = 0;
      foreach (var hash in hashes) {
        cancellationCheck?.Invoke();
        count++;
        sum = unchecked(sum + hash);
        xor ^= hash;
      }
      return HashCode.Combine(expressionType, count, sum, xor);
    }
  }

  private sealed class LiteralExpressionEqualityComparer : IEqualityComparer<Expression> {
    public static readonly LiteralExpressionEqualityComparer Instance = new();
    private readonly Action cancellationCheck;

    private LiteralExpressionEqualityComparer(Action cancellationCheck = null) {
      this.cancellationCheck = cancellationCheck;
    }

    internal static LiteralExpressionEqualityComparer For(Action cancellationCheck) =>
      cancellationCheck == null ? Instance : new LiteralExpressionEqualityComparer(cancellationCheck);

    public bool Equals(Expression x, Expression y) {
      cancellationCheck?.Invoke();
      if (ReferenceEquals(x, y)) {
        return true;
      }
      if (x == null || y == null) {
        return false;
      }
      return AreLiteralExpressionsEqual(x, y, cancellationCheck);
    }

    public int GetHashCode(Expression expr) {
      cancellationCheck?.Invoke();
      if (expr == null) {
        return 0;
      }
      return ComputeHash(expr);
    }

    private int ComputeHash(Expression expr) {
      cancellationCheck?.Invoke();
      if (expr is CharLiteralExpr && TryGetCharLiteral(expr, out var ch, cancellationCheck)) {
        return HashCode.Combine(typeof(CharLiteralExpr), (int)ch);
      }
      if (expr is StringLiteralExpr stringLiteral && stringLiteral.Value is string stringValue) {
        return ComputeSemanticStringHash(stringValue, stringLiteral.IsVerbatim, cancellationCheck);
      }
      if (expr is LiteralExpr lit) {
        return HashCode.Combine(typeof(LiteralExpr), lit.Value);
      }
      if (expr is SeqDisplayExpr seq) {
        var hash = new HashCode();
        hash.Add(typeof(SeqDisplayExpr));
        foreach (var e in seq.Elements) {
          cancellationCheck?.Invoke();
          hash.Add(ComputeHash(e));
        }
        return hash.ToHashCode();
      }
      if (expr is SetDisplayExpr setDisplay) {
        if (!AllElementsAreLiterals(setDisplay.Elements, cancellationCheck)) {
          return typeof(SetDisplayExpr).GetHashCode();
        }
        // Order-independent hash based on distinct literal elements.
        var distinct = new LiteralSet(setDisplay.Elements, cancellationCheck);
        var sum = 0;
        var xor = 0;
        foreach (var element in distinct.Elements) {
          cancellationCheck?.Invoke();
          var elementHash = ComputeHash(element);
          sum = unchecked(sum + elementHash);
          xor ^= elementHash;
        }
        return HashCode.Combine(typeof(SetDisplayExpr), distinct.Count, sum, xor);
      }
      if (expr is MultiSetDisplayExpr multiSetDisplay) {
        if (!AllElementsAreLiterals(multiSetDisplay.Elements, cancellationCheck)) {
          return typeof(MultiSetDisplayExpr).GetHashCode();
        }
        // Order-independent hash based on literal element multiplicities.
        var counts = BuildMultisetCountsDict(multiSetDisplay.Elements, cancellationCheck);
        var sum = 0;
        var xor = 0;
        var totalCount = 0;
        foreach (var entry in counts) {
          cancellationCheck?.Invoke();
          var entryHash = HashCode.Combine(ComputeHash(entry.Key), entry.Value);
          sum = unchecked(sum + entryHash);
          xor ^= entryHash;
          totalCount += entry.Value;
        }
        return HashCode.Combine(typeof(MultiSetDisplayExpr), counts.Count, totalCount, sum, xor);
      }
      if (expr is MapDisplayExpr mapDisplay) {
        if (!TryNormalizeLiteralMapEntries(mapDisplay, out var normalizedEntries, cancellationCheck)) {
          return typeof(MapDisplayExpr).GetHashCode();
        }
        var sum = 0;
        var xor = 0;
        foreach (var entry in normalizedEntries) {
          cancellationCheck?.Invoke();
          var entryHash = HashCode.Combine(ComputeHash(entry.A), ComputeHash(entry.B));
          sum = unchecked(sum + entryHash);
          xor ^= entryHash;
        }
        return HashCode.Combine(typeof(MapDisplayExpr), normalizedEntries.Count, sum, xor);
      }
      if (TryGetTupleLiteral(expr, out var datatype)) {
        var hash = new HashCode();
        hash.Add(typeof(DatatypeValue));
        hash.Add(datatype.Ctor);
        foreach (var arg in datatype.Arguments) {
          cancellationCheck?.Invoke();
          hash.Add(ComputeHash(arg));
        }
        return hash.ToHashCode();
      }
      return 0;
    }
  }

  private struct LiteralSet {
    public readonly List<Expression> Elements;
    private readonly HashSet<Expression> set;
    private readonly Action cancellationCheck;

    public LiteralSet(IEnumerable<Expression> source, Action cancellationCheck = null) {
      this.cancellationCheck = cancellationCheck;
      set = new HashSet<Expression>(LiteralExpressionEqualityComparer.For(cancellationCheck));
      Elements = new List<Expression>();
      foreach (var e in source) {
        cancellationCheck?.Invoke();
        if (set.Add(e)) {
          Elements.Add(e);
        }
      }
    }

    public int Count => Elements.Count;
    public bool Contains(Expression expr) => set.Contains(expr);

    public void Add(Expression expr) {
      if (set.Add(expr)) {
        Elements.Add(expr);
      }
    }
  }
}
