#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

internal sealed class QuantifierExpansionBudget {
  internal uint Limit { get; }
  internal uint Used { get; private set; }
  internal uint Remaining => Used >= Limit ? 0 : Limit - Used;
  internal bool IsExhausted { get; private set; }

  internal QuantifierExpansionBudget(uint limit) {
    if (limit == 0) {
      throw new ArgumentOutOfRangeException(nameof(limit), "The quantifier instance limit must be positive.");
    }
    Limit = limit;
  }

  internal void ConsumeInstance() {
    if (Used < Limit) {
      Used++;
    }
  }

  internal void MarkExhausted() {
    IsExhausted = true;
  }
}

/// <summary>
/// Shared helpers for discovering bounds, inferring concrete domains, and materializing
/// set/map comprehensions for bounded quantifier unrolling and partial evaluation.
/// </summary>
internal sealed class QuantifierBounds {
  private const string PartialUnrollMarkerAttributeName = "_partial_unroll";
  private const int CharDomainCardinality = 0x10000;
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint maxInstances;
  private readonly QuantifierExpansionBudget? expansionBudget;
  private readonly bool detectEmptyProduct;
  private readonly Action? cancellationCheck;

  internal uint MaxInstances => maxInstances;

  internal QuantifierBounds(SystemModuleManager systemModuleManager, uint maxInstances,
    QuantifierExpansionBudget? expansionBudget = null, bool detectEmptyProduct = false,
    Action? cancellationCheck = null) {
    this.systemModuleManager = systemModuleManager ?? throw new ArgumentNullException(nameof(systemModuleManager));
    this.maxInstances = maxInstances;
    this.expansionBudget = expansionBudget;
    this.detectEmptyProduct = detectEmptyProduct;
    this.cancellationCheck = cancellationCheck;
  }

  private void CheckForCancellation() {
    cancellationCheck?.Invoke();
  }

  internal sealed class ConcreteDomain {
    public BigInteger Size { get; }
    private readonly Func<IEnumerable<Expression>> enumeratorFactory;

    public ConcreteDomain(BigInteger size, Func<IEnumerable<Expression>> enumeratorFactory) {
      Size = size;
      this.enumeratorFactory = enumeratorFactory ?? throw new ArgumentNullException(nameof(enumeratorFactory));
    }

    public IEnumerable<Expression> Enumerate() => enumeratorFactory();
  }

  // === Expression normalization & pattern helpers ===
  internal static Expression StripConcreteSyntax(Expression expr) => StripConcreteSyntax(expr, null);

  internal static Expression NormalizeForPattern(Expression expr) => NormalizeForPattern(expr, null);

  internal static Expression GetImpliedTypeConstraint(BoundVar boundVar) => GetImpliedTypeConstraint(boundVar, null);

  internal static Expression ConjoinWithImpliedTypeConstraints(IReadOnlyList<BoundVar> boundVars, Expression? range, IOrigin origin) => ConjoinWithImpliedTypeConstraints(boundVars, range, origin, null);

  internal static Expression GetLogicalBodyWithImpliedTypeConstraints(QuantifierExpr quantifierExpr) => GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, null);

  internal static void CollectConjuncts(Expression expr, List<Expression> conjuncts) => CollectConjuncts(expr, conjuncts, null);

  internal static void CollectDisjuncts(Expression expr, List<Expression> disjuncts) => CollectDisjuncts(expr, disjuncts, null);

  internal static bool IsBoundVar(Expression? expr, BoundVar boundVar) => IsBoundVar(expr, boundVar, null);

  internal static void EnsureExpressionType(Expression expr, Type type) {
    ExpressionRewriteUtil.EnsureExpressionType(expr, type);
  }

  internal static Expression StripConcreteSyntax(Expression expr, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    return ExpressionRewriteUtil.StripConcreteSyntax(expr);
  }

  internal static Expression NormalizeForPattern(Expression expr, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    expr = StripConcreteSyntax(expr, cancellationCheck);
    if (expr is ChainingExpression chainingExpression) {
      expr = chainingExpression.E;
    }
    if (expr is ParensExpression parens && parens.ResolvedExpression != null) {
      expr = parens.ResolvedExpression;
    }
    if (expr is ConversionExpr conversionExpr) {
      var fromType = conversionExpr.E.Type?.NormalizeExpandKeepConstraints();
      var toType = conversionExpr.Type?.NormalizeExpandKeepConstraints();
      if (fromType != null && toType != null && toType.AsSubsetType == null && toType.AsNewtype == null &&
          fromType.Equals(toType, keepConstraints: true)) {
        expr = conversionExpr.E;
      }
    }
    return expr;
  }

  internal static Expression GetImpliedTypeConstraint(BoundVar boundVar, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    var constraint = ModuleResolver.GetImpliedTypeConstraint(boundVar, boundVar.Type);
    constraint.Type ??= Type.Bool;
    return constraint;
  }

  internal static Expression ConjoinWithImpliedTypeConstraints(IReadOnlyList<BoundVar> boundVars, Expression? range, IOrigin origin, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    Expression? combined = range;
    foreach (var boundVar in boundVars) {
      cancellationCheck?.Invoke();
      var constraint = GetImpliedTypeConstraint(boundVar, cancellationCheck);
      if (Expression.IsBoolLiteral(constraint, out var isTrue) && isTrue) {
        continue;
      }

      combined = combined == null ? constraint : Expression.CreateAnd(constraint, combined);
      combined.Type = Type.Bool;
    }

    if (combined == null) {
      combined = Expression.CreateBoolLiteral(origin, true);
      combined.Type = Type.Bool;
    } else {
      combined.Type ??= Type.Bool;
    }

    return combined;
  }

  internal static Expression GetLogicalBodyWithImpliedTypeConstraints(QuantifierExpr quantifierExpr, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    var effectiveRange = ConjoinWithImpliedTypeConstraints(quantifierExpr.BoundVars, quantifierExpr.Range, quantifierExpr.Origin, cancellationCheck);
    if (Expression.IsBoolLiteral(effectiveRange, out var rangeValue) && rangeValue) {
      quantifierExpr.Term.Type ??= Type.Bool;
      return quantifierExpr.Term;
    }

    var logicalBody = quantifierExpr is ExistsExpr
      ? Expression.CreateAnd(effectiveRange, quantifierExpr.Term)
      : Expression.CreateImplies(effectiveRange, quantifierExpr.Term);
    logicalBody.Type = Type.Bool;
    return logicalBody;
  }

  internal static void CollectConjuncts(Expression expr, List<Expression> conjuncts, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is BinaryExpr binaryExpr && IsConjunction(binaryExpr)) {
      CollectConjuncts(binaryExpr.E0, conjuncts, cancellationCheck);
      CollectConjuncts(binaryExpr.E1, conjuncts, cancellationCheck);
      return;
    }
    conjuncts.Add(expr);
  }

  internal static void CollectDisjuncts(Expression expr, List<Expression> disjuncts, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is BinaryExpr binaryExpr &&
        (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Or || binaryExpr.Op == BinaryExpr.Opcode.Or)) {
      CollectDisjuncts(binaryExpr.E0, disjuncts, cancellationCheck);
      CollectDisjuncts(binaryExpr.E1, disjuncts, cancellationCheck);
      return;
    }
    disjuncts.Add(expr);
  }

  internal static bool IsBoundVar(Expression? expr, BoundVar boundVar, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    if (expr == null) {
      return false;
    }
    expr = NormalizeForPattern(expr, cancellationCheck);
    return expr is IdentifierExpr identifierExpr && (identifierExpr.Var == boundVar || identifierExpr.Name == boundVar.Name);
  }

  private static bool IsConjunction(BinaryExpr binaryExpr) {
    return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binaryExpr.Op == BinaryExpr.Opcode.And;
  }

  private static bool IsImplication(BinaryExpr binaryExpr) {
    return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp || binaryExpr.Op == BinaryExpr.Opcode.Imp;
  }

  // === Literal helpers (structural equality, dedup) ===
  private static bool IsLiteralExpression(Expression expr, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    expr = StripConcreteSyntax(expr, cancellationCheck);
    switch (expr) {
      case LiteralExpr:
        return true;
      case DisplayExpression displayExpression:
        return displayExpression.Elements.All(value => IsLiteralExpression(value, cancellationCheck));
      case MapDisplayExpr mapDisplayExpr:
        return mapDisplayExpr.Elements.All(entry => IsLiteralExpression(entry.A, cancellationCheck) && IsLiteralExpression(entry.B, cancellationCheck));
      case DatatypeValue datatypeValue:
        return datatypeValue.Arguments.All(value => IsLiteralExpression(value, cancellationCheck));
      default:
        return false;
    }
  }

  private static bool LiteralStructuralEquals(Expression left, Expression right, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    left = StripConcreteSyntax(left, cancellationCheck);
    right = StripConcreteSyntax(right, cancellationCheck);
    if (ReferenceEquals(left, right)) {
      return true;
    }
    switch (left) {
      case StringLiteralExpr leftString when right is StringLiteralExpr rightString
        && leftString.Value is string leftStringValue
        && rightString.Value is string rightStringValue:
        return StringLiteralsSemanticallyEqual(leftStringValue, leftString.IsVerbatim, rightStringValue, rightString.IsVerbatim, cancellationCheck);
      case LiteralExpr leftLiteral when right is LiteralExpr rightLiteral:
        return leftLiteral.GetType() == rightLiteral.GetType() && Equals(leftLiteral.Value, rightLiteral.Value);
      case DisplayExpression leftDisplay when right is DisplayExpression rightDisplay:
        if (leftDisplay.GetType() != rightDisplay.GetType() || leftDisplay.Elements.Count != rightDisplay.Elements.Count) {
          return false;
        }
        for (var i = 0; i < leftDisplay.Elements.Count; i++) {
          cancellationCheck?.Invoke();
          if (!LiteralStructuralEquals(leftDisplay.Elements[i], rightDisplay.Elements[i], cancellationCheck)) {
            return false;
          }
        }
        return true;
      case MapDisplayExpr leftMap when right is MapDisplayExpr rightMap:
        if (leftMap.Finite != rightMap.Finite || leftMap.Elements.Count != rightMap.Elements.Count) {
          return false;
        }
        for (var i = 0; i < leftMap.Elements.Count; i++) {
          cancellationCheck?.Invoke();
          var leftEntry = leftMap.Elements[i];
          var rightEntry = rightMap.Elements[i];
          if (!LiteralStructuralEquals(leftEntry.A, rightEntry.A, cancellationCheck) || !LiteralStructuralEquals(leftEntry.B, rightEntry.B, cancellationCheck)) {
            return false;
          }
        }
        return true;
      case DatatypeValue leftDatatype when right is DatatypeValue rightDatatype:
        if (leftDatatype.DatatypeName != rightDatatype.DatatypeName ||
            leftDatatype.MemberName != rightDatatype.MemberName ||
            leftDatatype.Arguments.Count != rightDatatype.Arguments.Count) {
          return false;
        }
        for (var i = 0; i < leftDatatype.Arguments.Count; i++) {
          cancellationCheck?.Invoke();
          if (!LiteralStructuralEquals(leftDatatype.Arguments[i], rightDatatype.Arguments[i], cancellationCheck)) {
            return false;
          }
        }
        return true;
      default:
        return false;
    }
  }

  private sealed class LiteralExpressionStructuralComparer : IEqualityComparer<Expression> {
    public static readonly LiteralExpressionStructuralComparer Instance = new();
    private readonly Action? cancellationCheck;

    private LiteralExpressionStructuralComparer(Action? cancellationCheck = null) {
      this.cancellationCheck = cancellationCheck;
    }

    internal static LiteralExpressionStructuralComparer For(Action? cancellationCheck) =>
      cancellationCheck == null ? Instance : new LiteralExpressionStructuralComparer(cancellationCheck);

    public bool Equals(Expression? x, Expression? y) {
      cancellationCheck?.Invoke();
      if (ReferenceEquals(x, y)) {
        return true;
      }
      if (x == null || y == null) {
        return false;
      }
      return LiteralStructuralEquals(x, y, cancellationCheck);
    }

    public int GetHashCode(Expression obj) {
      cancellationCheck?.Invoke();
      if (obj == null) {
        return 0;
      }
      return ComputeHash(obj);
    }

    private int ComputeHash(Expression expr) {
      cancellationCheck?.Invoke();
      expr = StripConcreteSyntax(expr, cancellationCheck);
      if (expr is StringLiteralExpr stringLiteral && stringLiteral.Value is string stringValue) {
        return ComputeSemanticStringHash(stringValue, stringLiteral.IsVerbatim, cancellationCheck);
      }
      if (expr is LiteralExpr literal) {
        return HashCode.Combine(literal.GetType(), literal.Value);
      }
      if (expr is DisplayExpression display) {
        var hash = new HashCode();
        hash.Add(display.GetType());
        hash.Add(display.Elements.Count);
        foreach (var element in display.Elements) {
          cancellationCheck?.Invoke();
          hash.Add(ComputeHash(element));
        }
        return hash.ToHashCode();
      }
      if (expr is MapDisplayExpr mapDisplay) {
        var hash = new HashCode();
        hash.Add(typeof(MapDisplayExpr));
        hash.Add(mapDisplay.Finite);
        hash.Add(mapDisplay.Elements.Count);
        foreach (var entry in mapDisplay.Elements) {
          cancellationCheck?.Invoke();
          hash.Add(ComputeHash(entry.A));
          hash.Add(ComputeHash(entry.B));
        }
        return hash.ToHashCode();
      }
      if (expr is DatatypeValue datatype) {
        var hash = new HashCode();
        hash.Add(typeof(DatatypeValue));
        hash.Add(datatype.DatatypeName);
        hash.Add(datatype.MemberName);
        hash.Add(datatype.Arguments.Count);
        foreach (var arg in datatype.Arguments) {
          cancellationCheck?.Invoke();
          hash.Add(ComputeHash(arg));
        }
        return hash.ToHashCode();
      }
      return expr.GetType().GetHashCode();
    }
  }

  private static List<int> GetSemanticStringCodePoints(string value, bool isVerbatim, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var result = new List<int>();
    foreach (var codePoint in Util.UnescapedCharacters(DafnyOptions.DefaultImmutableOptions, value, isVerbatim)) {
      cancellationCheck?.Invoke();
      result.Add(codePoint);
    }
    return result;
  }

  private static bool StringLiteralsSemanticallyEqual(string leftValue, bool leftVerbatim, string rightValue, bool rightVerbatim, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var leftCodePoints = GetSemanticStringCodePoints(leftValue, leftVerbatim, cancellationCheck);
    var rightCodePoints = GetSemanticStringCodePoints(rightValue, rightVerbatim, cancellationCheck);
    if (leftCodePoints.Count != rightCodePoints.Count) {
      return false;
    }
    for (var index = 0; index < leftCodePoints.Count; index++) {
      cancellationCheck?.Invoke();
      if (leftCodePoints[index] != rightCodePoints[index]) {
        return false;
      }
    }
    return true;
  }

  private static int ComputeSemanticStringHash(string value, bool isVerbatim, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var hash = new HashCode();
    hash.Add(typeof(StringLiteralExpr));
    foreach (var codePoint in GetSemanticStringCodePoints(value, isVerbatim, cancellationCheck)) {
      cancellationCheck?.Invoke();
      hash.Add(codePoint);
    }
    return hash.ToHashCode();
  }

  private static bool AddUniqueLiteral(List<Expression> uniques, HashSet<Expression> uniqueSet, Expression candidate, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var normalized = StripConcreteSyntax(candidate, cancellationCheck);
    if (!uniqueSet.Add(normalized)) {
      return false;
    }
    uniques.Add(normalized);
    return true;
  }

  private bool TryAddUniqueLiteral(List<Expression> uniques, HashSet<Expression> uniqueSet,
    Expression candidate, uint? cap) {
    if (AddUniqueLiteral(uniques, uniqueSet, candidate, cancellationCheck)) {
      if (cap.HasValue && uniques.Count > cap.Value) {
        return false;
      }
    }
    return true;
  }

  private static List<Expression> DeduplicateLiterals(List<Expression> elements, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var results = new List<Expression>();
    var uniqueSet = new HashSet<Expression>(LiteralExpressionStructuralComparer.For(cancellationCheck));
    foreach (var element in elements) {
      cancellationCheck?.Invoke();
      AddUniqueLiteral(results, uniqueSet, element, cancellationCheck);
    }
    return results;
  }

  // === Public/Internal entrypoints ===
  /// <summary>
  /// Unroll a quantifier into a boolean expression when all bound variables have concrete, finite domains.
  /// Returns false if any bound is non-concrete or the quantifier is split/unsupported. When the
  /// domain product exceeds the instance cap, partially unroll up to the cap and keep the original
  /// quantifier to cover the remaining domain.
  /// </summary>
  internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, Func<Expression, Expression> simplifyAfterSubst,
    out Expression rewritten, bool emitOverflowResidual = true,
    Func<Expression, IReadOnlyDictionary<IVariable, Expression>, bool>? reserveInstanceExpansion = null,
    Action<IReadOnlyDictionary<IVariable, Expression>>? onExistentialWitness = null) {
    CheckForCancellation();
    rewritten = quantifierExpr;

    if (quantifierExpr.SplitQuantifier != null || quantifierExpr.SplitQuantifierExpression != null) {
      return false;
    }
    if (Attributes.Contains(quantifierExpr.Attributes, PartialUnrollMarkerAttributeName)) {
      return false;
    }

    var bounds = TryGetBoundsOrDiscover(quantifierExpr.BoundVars, quantifierExpr.Bounds,
      () => GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, cancellationCheck), quantifierExpr is ExistsExpr, cancellationCheck);
    if (bounds == null || bounds.Count != quantifierExpr.BoundVars.Count) {
      return false;
    }

    var isForall = quantifierExpr is ForallExpr;
    var isExists = quantifierExpr is ExistsExpr;
    if (!isForall && !isExists) {
      return false;
    }

    // We only unroll when all bound variables range over concrete, finite domains.
    var domains = new ConcreteDomain[quantifierExpr.BoundVars.Count];
    var allConcrete = true;
    for (var i = 0; i < quantifierExpr.BoundVars.Count; i++) {
      CheckForCancellation();
      var bv = quantifierExpr.BoundVars[i];
      var bound = bounds[i];
      if (!TryGetConcreteDomain(bv, bound, simplifyAfterSubst, out var domain)) {
        allConcrete = false;
        break;
      }
      domains[i] = domain;
    }

    if (!allConcrete &&
        !TryGetConcreteIntDomainsFromPools(quantifierExpr.BoundVars, bounds, out domains) &&
        !TryGetConcreteIntDomainsFromLogicalBody(quantifierExpr, out domains) &&
        !TryGetConcreteCharDomainsFromLogicalBody(quantifierExpr, out domains)) {
      return false;
    }

    // Domain product within cap means full unroll; otherwise we partially unroll up to the cap.
    // Contract reduction supplies a shared budget so nested and sibling quantifiers consume one
    // cumulative allowance. Rewriter callers keep the historical per-quantifier cap.
    var effectiveMaxInstances = expansionBudget?.Remaining ?? maxInstances;
    var hasInstanceLimit = expansionBudget != null || maxInstances > 0;
    var exceedsMaxInstances = false;
    var size = BigInteger.One;
    for (var i = 0; i < domains.Length; i++) {
      CheckForCancellation();
      var domainSize = domains[i].Size;
      if (domainSize <= BigInteger.Zero) {
        rewritten = Expression.CreateBoolLiteral(quantifierExpr.Origin, isForall);
        rewritten.Type = Type.Bool;
        return true;
      }

      if (!exceedsMaxInstances) {
        size *= domainSize;
        if (hasInstanceLimit && size > effectiveMaxInstances) {
          exceedsMaxInstances = true;
        }
      }
    }

    // Use the original logical body and simplify per-instance after substitution. This naturally drops
    // guaranteed bounds like 0 <= i < N from the instantiated formula.
    var logicalBody = GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, cancellationCheck);
    if (logicalBody.Type == null) {
      logicalBody.Type = Type.Bool;
    }

    Expression accumulator = Expression.CreateBoolLiteral(quantifierExpr.Origin, isForall);
    accumulator.Type = Type.Bool;

    if (exceedsMaxInstances && effectiveMaxInstances == 0) {
      if (!emitOverflowResidual) {
        return false;
      }
      expansionBudget?.MarkExhausted();
      MarkQuantifierAsPartiallyUnrolled(quantifierExpr);
      rewritten = quantifierExpr;
      return true;
    }

    void AddInstance(Expression instance) {
      CheckForCancellation();
      if (Expression.IsBoolLiteral(instance, out var b)) {
        if (isForall && !b) {
          accumulator = Expression.CreateBoolLiteral(instance.Origin, false);
          accumulator.Type = Type.Bool;
        } else if (isExists && b) {
          accumulator = Expression.CreateBoolLiteral(instance.Origin, true);
          accumulator.Type = Type.Bool;
        }
        return;
      }

      accumulator = isForall
        ? Expression.CreateAnd(accumulator, instance)
        : Expression.CreateOr(accumulator, instance);
    }

    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();

    bool IsShortCircuited() =>
      Expression.IsBoolLiteral(accumulator, out var b) && ((isForall && !b) || (isExists && b));

    uint instanceCount = 0;
    bool reachedInstanceCap = false;
    bool reachedExpressionNodeLimit = false;

    bool HandleInstance(Substituter substituter) {
      CheckForCancellation();
      if (reserveInstanceExpansion != null && !reserveInstanceExpansion(logicalBody, substMap)) {
        reachedExpressionNodeLimit = true;
        return true;
      }
      expansionBudget?.ConsumeInstance();
      var inst = substituter.Substitute(logicalBody);
      inst = simplifyAfterSubst(inst);
      if (isExists && Expression.IsBoolLiteral(inst, out var holds) && holds) {
        // The enumeration reuses this map; a consumer retaining an assignment must copy it.
        onExistentialWitness?.Invoke(substMap);
      }
      AddInstance(inst);
      instanceCount++;
      if (expansionBudget != null ? expansionBudget.Remaining == 0 :
          hasInstanceLimit && instanceCount >= effectiveMaxInstances) {
        reachedInstanceCap = true;
      }
      return true;
    }

    if (!TryEnumerateAssignments(
          quantifierExpr.BoundVars,
          domains,
          substMap,
          typeMap,
          HandleInstance,
          () => IsShortCircuited() || reachedInstanceCap || reachedExpressionNodeLimit)) {
      return false;
    }
    if (reachedExpressionNodeLimit) {
      rewritten = quantifierExpr;
      return true;
    }
    if (expansionBudget != null && reachedInstanceCap && new BigInteger(instanceCount) < size) {
      exceedsMaxInstances = true;
    }
    if (exceedsMaxInstances && !IsShortCircuited()) {
      if (!emitOverflowResidual) {
        return false;
      }
      expansionBudget?.MarkExhausted();
      MarkQuantifierAsPartiallyUnrolled(quantifierExpr);
      rewritten = isForall
        ? Expression.CreateAnd(accumulator, quantifierExpr)
        : Expression.CreateOr(accumulator, quantifierExpr);
      rewritten.Type = Type.Bool;
      return true;
    }

    rewritten = accumulator;
    return true;
  }

  private static void MarkQuantifierAsPartiallyUnrolled(QuantifierExpr quantifierExpr) {
    if (Attributes.Contains(quantifierExpr.Attributes, PartialUnrollMarkerAttributeName)) {
      return;
    }
    quantifierExpr.Attributes = new Attributes(
      quantifierExpr.Origin,
      PartialUnrollMarkerAttributeName,
      new List<Expression>(),
      quantifierExpr.Attributes);
  }

  /// <summary>
  /// Materialize a finite set expression into its elements, honoring the optional cap.
  /// Returns false when the set is non-finite, non-materializable, or exceeds the cap.
  /// </summary>
  internal bool TryMaterializeSetElements(Expression setExpr, uint? materializationCap, Func<Expression, Expression> simplify,
    out List<Expression> elements) {
    CheckForCancellation();
    elements = null!;
    var resolved = StripConcreteSyntax(setExpr, cancellationCheck);

    if (resolved is SetDisplayExpr setDisplay) {
      if (materializationCap.HasValue && setDisplay.Elements.Count > materializationCap.Value) {
        return false;
      }
      elements = new List<Expression>();
      foreach (var element in setDisplay.Elements) {
        CheckForCancellation();
        elements.Add(element);
      }
      return true;
    }

    if (resolved is SetComprehension setComprehension) {
      return TryMaterializeSetComprehension(setComprehension, simplify, out elements);
    }

    return false;
  }

  /// <summary>
  /// Materialize a finite set comprehension into its elements when all bound variables have concrete domains.
  /// Returns false if bounds are missing, range is non-boolean, or the enumeration exceeds the instance cap.
  /// </summary>
  internal bool TryMaterializeSetComprehension(SetComprehension setComprehension, Func<Expression, Expression> simplify,
    out List<Expression> elements) {
    CheckForCancellation();
    elements = null!;

    if (!setComprehension.Finite) {
      return false;
    }

    var effectiveRange = ConjoinWithImpliedTypeConstraints(setComprehension.BoundVars, setComprehension.Range, setComprehension.Origin, cancellationCheck);
    var bounds = TryGetBoundsOrDiscover(setComprehension.BoundVars, setComprehension.Bounds,
      () => effectiveRange, polarity: true, cancellationCheck);
    if (bounds == null || bounds.Count != setComprehension.BoundVars.Count) {
      return false;
    }
    if (bounds.Any(bound => { CheckForCancellation(); return bound == null; })) {
      if (setComprehension.Range == null) {
        return false;
      }
      var discovered = ModuleResolver.DiscoverBestBounds_MultipleVars(setComprehension.BoundVars, effectiveRange, true);
      if (discovered == null || discovered.Count != setComprehension.BoundVars.Count) {
        return false;
      }
      bounds = discovered;
    }

    var domains = new ConcreteDomain[setComprehension.BoundVars.Count];
    for (var i = 0; i < setComprehension.BoundVars.Count; i++) {
      CheckForCancellation();
      var bv = setComprehension.BoundVars[i];
      var bound = bounds[i];
      ConcreteDomain domain;
      if (bv.Type.NormalizeExpand().IsCharType &&
          TryGetConcreteCharDomainFromRange(effectiveRange, bv, out var charDomain)) {
        domain = charDomain;
      } else if (!TryGetConcreteDomain(bv, bound, simplify, out domain)) {
        return false;
      }
      domains[i] = domain;
    }

    if (!IsDomainProductWithinMaxInstances(domains)) {
      return false;
    }

    var results = new List<Expression>();
    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();
    var range = effectiveRange;
    var term = setComprehension.Term;

    bool HandleInstance(Substituter substituter) {
      CheckForCancellation();
      if (maxInstances > 0 && results.Count >= maxInstances) {
        return false;
      }
      if (!TryEvaluateRangeToBool(range, substituter, simplify, out var rangeValue)) {
        return false;
      }
      if (!rangeValue) {
        return true;
      }

      var termInst = simplify(substituter.Substitute(term));
      termInst = StripConcreteSyntax(termInst, cancellationCheck);
      results.Add(termInst);
      return true;
    }

    if (!TryEnumerateAssignments(setComprehension.BoundVars, domains, substMap, typeMap, HandleInstance)) {
      return false;
    }

    var elementType = setComprehension.Type.NormalizeExpand().AsSetType?.Arg;
    if (elementType != null) {
      foreach (var element in results) {
        CheckForCancellation();
        EnsureExpressionType(element, elementType);
      }
    }
    elements = results;
    return true;
  }

  /// <summary>
  /// Materialize a finite map comprehension into display entries when all bound variables have concrete domains.
  /// Returns false if keys are non-literal, ranges are non-boolean, or enumeration exceeds the instance cap.
  /// </summary>
  internal bool TryMaterializeMapComprehension(MapComprehension mapComprehension, Func<Expression, Expression> simplify,
    out List<MapDisplayEntry> entries) {
    CheckForCancellation();
    entries = null!;
    if (!mapComprehension.Finite) {
      return false;
    }

    var effectiveRange = ConjoinWithImpliedTypeConstraints(mapComprehension.BoundVars, mapComprehension.Range, mapComprehension.Origin, cancellationCheck);
    var bounds = TryGetBoundsOrDiscover(mapComprehension.BoundVars, mapComprehension.Bounds,
      () => effectiveRange, polarity: true, cancellationCheck);
    if (bounds == null || bounds.Count != mapComprehension.BoundVars.Count) {
      return false;
    }

    var domains = new ConcreteDomain[mapComprehension.BoundVars.Count];
    for (var i = 0; i < mapComprehension.BoundVars.Count; i++) {
      CheckForCancellation();
      var bv = mapComprehension.BoundVars[i];
      var bound = bounds[i];
      if (!TryGetConcreteDomain(bv, bound, simplify, out var domain)) {
        return false;
      }
      domains[i] = domain;
    }

    if (!IsDomainProductWithinMaxInstances(domains)) {
      return false;
    }

    var resultEntries = new List<MapDisplayEntry>();
    var keyIndexByLiteral = new Dictionary<Expression, int>(LiteralExpressionStructuralComparer.For(cancellationCheck));
    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();

    var keyTemplate = mapComprehension.TermLeft;
    if (keyTemplate == null) {
      if (mapComprehension.BoundVars.Count != 1) {
        return false;
      }
      keyTemplate = new IdentifierExpr(mapComprehension.Origin, mapComprehension.BoundVars[0].Name) {
        Var = mapComprehension.BoundVars[0],
        Type = mapComprehension.BoundVars[0].Type
      };
    }

    bool HandleInstance(Substituter substituter) {
      CheckForCancellation();
      if (maxInstances > 0 && resultEntries.Count >= maxInstances) {
        return false;
      }
      if (!TryEvaluateRangeToBool(effectiveRange, substituter, simplify, out var rangeValue)) {
        return false;
      }
      if (!rangeValue) {
        return true;
      }

      var keyExpr = simplify(substituter.Substitute(keyTemplate));
      keyExpr = StripConcreteSyntax(keyExpr, cancellationCheck);
      if (!IsLiteralExpression(keyExpr, cancellationCheck)) {
        return false;
      }

      var valueExpr = simplify(substituter.Substitute(mapComprehension.Term));
      valueExpr = StripConcreteSyntax(valueExpr, cancellationCheck);

      if (keyIndexByLiteral.TryGetValue(keyExpr, out var existingIndex)) {
        if (!LiteralStructuralEquals(resultEntries[existingIndex].B, valueExpr, cancellationCheck)) {
          return false;
        }
        return true;
      }

      var nextIndex = resultEntries.Count;
      resultEntries.Add(new MapDisplayEntry(keyExpr, valueExpr));
      keyIndexByLiteral[keyExpr] = nextIndex;
      return true;
    }

    if (!TryEnumerateAssignments(mapComprehension.BoundVars, domains, substMap, typeMap, HandleInstance)) {
      return false;
    }

    entries = resultEntries;
    return true;
  }

  /// <summary>
  /// Materialize the key set of a finite map comprehension when all bound variables have concrete domains.
  /// Returns false if key expressions are non-literal, range is non-boolean, or enumeration exceeds the instance cap.
  /// </summary>
  private bool TryMaterializeMapComprehensionKeys(MapComprehension mapComprehension, Func<Expression, Expression> simplify,
    out List<Expression> keys) {
    CheckForCancellation();
    keys = null!;
    var effectiveRange = ConjoinWithImpliedTypeConstraints(mapComprehension.BoundVars, mapComprehension.Range, mapComprehension.Origin, cancellationCheck);
    var bounds = TryGetBoundsOrDiscover(mapComprehension.BoundVars, mapComprehension.Bounds,
      () => effectiveRange, polarity: true, cancellationCheck);
    if (bounds == null || bounds.Count != mapComprehension.BoundVars.Count) {
      return false;
    }

    var domains = new ConcreteDomain[mapComprehension.BoundVars.Count];
    for (var i = 0; i < mapComprehension.BoundVars.Count; i++) {
      CheckForCancellation();
      var boundVar = mapComprehension.BoundVars[i];
      var boundPool = bounds[i];
      if (!TryGetConcreteDomain(boundVar, boundPool, simplify, out var concreteDomain)) {
        return false;
      }
      domains[i] = concreteDomain;
    }

    if (!IsDomainProductWithinMaxInstances(domains)) {
      return false;
    }

    Expression keyTemplate;
    if (mapComprehension.TermLeft != null) {
      keyTemplate = mapComprehension.TermLeft;
    } else if (mapComprehension.BoundVars.Count == 1) {
      var boundVar = mapComprehension.BoundVars[0];
      keyTemplate = new IdentifierExpr(boundVar.Origin, boundVar) { Type = boundVar.Type };
    } else {
      return false;
    }

    var resultKeys = new List<Expression>();
    var resultKeySet = new HashSet<Expression>(LiteralExpressionStructuralComparer.For(cancellationCheck));
    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();
    var range = effectiveRange;

    bool HandleInstance(Substituter substituter) {
      CheckForCancellation();
      if (!TryEvaluateRangeToBool(range, substituter, simplify, out var rangeValue)) {
        return false;
      }
      if (!rangeValue) {
        return true;
      }

      var keyInst = simplify(substituter.Substitute(keyTemplate));
      keyInst = StripConcreteSyntax(keyInst, cancellationCheck);
      if (!IsLiteralExpression(keyInst, cancellationCheck)) {
        return false;
      }
      var cap = maxInstances == 0 ? (uint?)null : maxInstances;
      return TryAddUniqueLiteral(resultKeys, resultKeySet, keyInst, cap);
    }

    if (!TryEnumerateAssignments(mapComprehension.BoundVars, domains, substMap, typeMap, HandleInstance)) {
      return false;
    }

    keys = resultKeys;
    return true;
  }

  // === Seq domain extraction entrypoints ===
  /// <summary>
  /// Detect a constraint of the form |seqVar| == N with a non-negative int literal.
  /// Returns false when the expression is not an equality or the length is not a concrete int literal.
  /// </summary>
  internal bool TryGetSeqLengthConstraint(Expression expr, BoundVar seqVar, out int length) {
    length = default;
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is not BinaryExpr binaryExpr) {
      return false;
    }
    var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
    if (!isEq) {
      return false;
    }

    if (TryGetSeqLength(binaryExpr.E0, seqVar, out var lengthValue, cancellationCheck) &&
        TryGetIntLiteralValue(binaryExpr.E1, out var lengthLiteral, cancellationCheck)) {
      length = lengthLiteral;
      return lengthValue;
    }

    if (TryGetSeqLength(binaryExpr.E1, seqVar, out var lengthValueAlt, cancellationCheck) &&
        TryGetIntLiteralValue(binaryExpr.E0, out var lengthLiteralAlt, cancellationCheck)) {
      length = lengthLiteralAlt;
      return lengthValueAlt;
    }

    return false;
  }

  /// <summary>
  /// Try to infer a concrete element domain for seqVar based on a forall index range and term constraints.
  /// Returns false when the pattern does not match or the domain is not concrete.
  /// </summary>
  internal bool TryGetElementDomainConstraint(ForallExpr forallExpr, BoundVar seqVar, int length, out List<Expression> domain) {
    domain = null!;
    if (forallExpr.BoundVars.Count != 1) {
      return false;
    }

    var indexVar = forallExpr.BoundVars[0];
    if (forallExpr.Range == null || !TryGetIndexRange(forallExpr.Range, indexVar, length)) {
      return false;
    }

    var term = NormalizeForPattern(forallExpr.Term, cancellationCheck);
    if (TryGetSetMembershipDomain(term, seqVar, indexVar, out domain, cancellationCheck)) {
      return true;
    }
    if (TryGetOrEqualityDomain(term, seqVar, indexVar, out domain, cancellationCheck)) {
      return true;
    }
    if (TryGetIntRangeDomain(term, seqVar, indexVar, out domain, cancellationCheck)) {
      return true;
    }

    return false;
  }

  // === Seq domain extraction helpers ===
  private static bool TryGetSeqLength(Expression expr, BoundVar seqVar, out bool matched, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    matched = false;
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is not UnaryOpExpr unaryExpr) {
      return false;
    }
    if (unaryExpr.ResolvedOp != UnaryOpExpr.ResolvedOpcode.SeqLength) {
      return false;
    }
    matched = IsBoundVar(unaryExpr.E, seqVar, cancellationCheck);
    return true;
  }

  private static bool TryGetIntLiteralValue(Expression expr, out int value, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = default;
    if (!PartialEvaluatorEngine.TryGetReducedIntLiteral(expr, out var literal, cancellationCheck)) {
      return false;
    }
    if (literal < 0 || literal > int.MaxValue) {
      return false;
    }
    value = (int)literal;
    return true;
  }

  private bool TryGetIndexRange(Expression rangeExpr, BoundVar indexVar, int length) {
    cancellationCheck?.Invoke();
    var indexType = indexVar.Type.NormalizeExpandKeepConstraints();
    var isNat = indexType.AsSubsetType == systemModuleManager.NatDecl;
    if (indexType is not IntType && !isNat) {
      // A refined index type can omit positions even when its explicit range looks complete.
      return false;
    }
    var conjuncts = new List<Expression>();
    CollectConjuncts(rangeExpr, conjuncts, cancellationCheck);
    BigInteger? lower = isNat ? BigInteger.Zero : null;
    BigInteger? upper = null;
    foreach (var conjunct in conjuncts) {
      cancellationCheck?.Invoke();
      var normalized = NormalizeForPattern(conjunct, cancellationCheck);
      if (normalized is not BinaryExpr binaryExpr) {
        return false;
      }
      var isGe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge || binaryExpr.Op == BinaryExpr.Opcode.Ge;
      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      if (!isGe && !isGt && !isLe && !isLt) {
        return false;
      }

      BigInteger endpoint;
      if (IsBoundVar(binaryExpr.E0, indexVar, cancellationCheck) &&
          PartialEvaluatorEngine.TryGetReducedIntLiteral(binaryExpr.E1, out endpoint, cancellationCheck)) {
        // The comparison already has the index on the left.
      } else if (IsBoundVar(binaryExpr.E1, indexVar, cancellationCheck) &&
                 PartialEvaluatorEngine.TryGetReducedIntLiteral(binaryExpr.E0, out endpoint, cancellationCheck)) {
        (isGe, isLe) = (isLe, isGe);
        (isGt, isLt) = (isLt, isGt);
      } else {
        return false;
      }

      // Intersect inclusive integer endpoints; every conjunct must preserve exactly the valid index domain.
      if (isGe || isGt) {
        var inclusiveLower = endpoint + (isGt ? BigInteger.One : BigInteger.Zero);
        lower = lower == null ? inclusiveLower : BigInteger.Max(lower.Value, inclusiveLower);
      } else {
        var inclusiveUpper = endpoint - (isLt ? BigInteger.One : BigInteger.Zero);
        upper = upper == null ? inclusiveUpper : BigInteger.Min(upper.Value, inclusiveUpper);
      }
    }

    return lower == BigInteger.Zero && upper == new BigInteger(length) - BigInteger.One;
  }

  private static bool TryGetSetMembershipDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    domain = null!;
    if (term is not BinaryExpr binaryExpr) {
      return false;
    }
    var isInSet = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet;
    if (!isInSet) {
      return false;
    }
    if (!TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _, cancellationCheck) ||
        NormalizeForPattern(binaryExpr.E1, cancellationCheck) is not SetDisplayExpr setDisplay) {
      return false;
    }
    if (!setDisplay.Elements.All(value => IsLiteralExpression(value, cancellationCheck))) {
      return false;
    }
    domain = DeduplicateLiterals(setDisplay.Elements, cancellationCheck);
    return domain.Count > 0;
  }

  private static bool TryGetOrEqualityDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    domain = null!;
    var disjuncts = new List<Expression>();
    CollectDisjuncts(term, disjuncts, cancellationCheck);
    var elements = new List<Expression>();
    foreach (var disjunct in disjuncts) {
      cancellationCheck?.Invoke();
      var normalized = NormalizeForPattern(disjunct, cancellationCheck);
      if (normalized is not BinaryExpr binaryExpr) {
        return false;
      }
      var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
      if (!isEq) {
        return false;
      }
      if (TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _, cancellationCheck) && IsLiteralExpression(binaryExpr.E1, cancellationCheck)) {
        elements.Add(binaryExpr.E1);
        continue;
      }
      if (TryGetSeqSelect(binaryExpr.E1, seqVar, indexVar, out _, cancellationCheck) && IsLiteralExpression(binaryExpr.E0, cancellationCheck)) {
        elements.Add(binaryExpr.E0);
        continue;
      }
      return false;
    }

    domain = DeduplicateLiterals(elements, cancellationCheck);
    return domain.Count > 0;
  }

  private static bool TryGetIntRangeDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    domain = null!;
    var seqType = seqVar.Type.NormalizeExpand().AsSeqType;
    if (seqType == null || !seqType.Arg.IsNumericBased(Type.NumericPersuasion.Int)) {
      return false;
    }
    var conjuncts = new List<Expression>();
    CollectConjuncts(term, conjuncts, cancellationCheck);
    BigInteger? lower = null;
    BigInteger? upper = null;
    foreach (var conjunct in conjuncts) {
      cancellationCheck?.Invoke();
      var normalized = NormalizeForPattern(conjunct, cancellationCheck);
      if (normalized is not BinaryExpr binaryExpr) {
        continue;
      }
      var isGe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge || binaryExpr.Op == BinaryExpr.Opcode.Ge;
      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      if (!isGe && !isGt && !isLe && !isLt) {
        continue;
      }

      if (TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _, cancellationCheck) &&
          PartialEvaluatorEngine.TryGetReducedIntLiteral(binaryExpr.E1, out var rightLiteral, cancellationCheck)) {
        if (isGe || isGt) {
          var candidate = isGt ? rightLiteral + 1 : rightLiteral;
          lower = lower == null ? candidate : BigInteger.Max(lower.Value, candidate);
          continue;
        }
        if (isLe || isLt) {
          var candidate = isLt ? rightLiteral : rightLiteral + 1;
          upper = upper == null ? candidate : BigInteger.Min(upper.Value, candidate);
          continue;
        }
      }

      if (TryGetSeqSelect(binaryExpr.E1, seqVar, indexVar, out _, cancellationCheck) &&
          PartialEvaluatorEngine.TryGetReducedIntLiteral(binaryExpr.E0, out var leftLiteral, cancellationCheck)) {
        if (isLe || isLt) {
          var candidate = isLt ? leftLiteral + 1 : leftLiteral;
          lower = lower == null ? candidate : BigInteger.Max(lower.Value, candidate);
          continue;
        }
        if (isGe || isGt) {
          var candidate = isGt ? leftLiteral : leftLiteral + 1;
          upper = upper == null ? candidate : BigInteger.Min(upper.Value, candidate);
          continue;
        }
      }

      continue;
    }

    if (lower == null || upper == null || lower.Value >= upper.Value) {
      return false;
    }

    var elements = new List<Expression>();
    for (var value = lower.Value; value < upper.Value; value++) {
      cancellationCheck?.Invoke();
      elements.Add(new LiteralExpr(seqVar.Origin, value) { Type = seqType.Arg });
    }

    domain = DeduplicateLiterals(elements, cancellationCheck);
    return domain.Count > 0;
  }

  // === Quantifier/comprehension enumeration helpers ===
  private bool IsDomainProductWithinMaxInstances(ConcreteDomain[] domains) {
    CheckForCancellation();
    if (maxInstances == 0) {
      return true;
    }
    var size = BigInteger.One;
    foreach (var domain in domains) {
      CheckForCancellation();
      size *= domain.Size;
      if (size > maxInstances) {
        return false;
      }
    }
    return true;
  }

  private bool TryEvaluateRangeToBool(Expression? range, Substituter substituter,
    Func<Expression, Expression> simplify, out bool value) {
    CheckForCancellation();
    value = true;
    if (range == null) {
      return true;
    }

    var rangeInst = simplify(substituter.Substitute(range));
    rangeInst = StripConcreteSyntax(rangeInst, cancellationCheck);
    return Expression.IsBoolLiteral(rangeInst, out value);
  }

  private bool TryEnumerateAssignments(IReadOnlyList<BoundVar> boundVars, ConcreteDomain[] domains,
    Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap,
    Func<Substituter, bool> onComplete, Func<bool>? shouldStopEarly = null) {
    var substituter = new ContractReductionSubstituter(null, substMap, typeMap, null, null, cancellationCheck);

    bool Enumerate(int varIndex) {
      CheckForCancellation();
      if (shouldStopEarly?.Invoke() == true) {
        return true;
      }

      if (varIndex == domains.Length) {
        return onComplete(substituter);
      }

      var boundVar = boundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        CheckForCancellation();
        if (shouldStopEarly?.Invoke() == true) {
          return true;
        }

        EnsureExpressionType(value, boundVar.Type);
        substMap[boundVar] = value;
        if (!Enumerate(varIndex + 1)) {
          return false;
        }

        if (shouldStopEarly?.Invoke() == true) {
          return true;
        }
      }
      return true;
    }

    return Enumerate(0);
  }

  private static bool TryGetSeqSelect(Expression expr, BoundVar seqVar, BoundVar indexVar, out SeqSelectExpr selectExpr, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    selectExpr = null!;
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is not SeqSelectExpr seqSelect) {
      return false;
    }
    if (!IsBoundVar(seqSelect.Seq, seqVar, cancellationCheck)) {
      return false;
    }
    if (seqSelect.SelectOne && IsBoundVar(seqSelect.E0, indexVar, cancellationCheck)) {
      selectExpr = seqSelect;
      return true;
    }
    return false;
  }

  // === Concrete domain inference (int/char) ===
  private readonly record struct IntBoundConstraint(int TargetIndex, int? SourceIndex, BigInteger Offset, bool IsLower);

  private bool TryGetConcreteIntDomainsFromPools(IReadOnlyList<BoundVar> boundVars, IReadOnlyList<BoundedPool?> bounds,
    out ConcreteDomain[] domains) {
    domains = Array.Empty<ConcreteDomain>();
    if (boundVars.Count != bounds.Count) {
      return false;
    }

    var boundVarIndices = new Dictionary<BoundVar, int>();
    var isNat = new bool[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      var bv = boundVars[i];
      if (!TryGetIntOrNatType(bv, out var isNatType)) {
        return false;
      }
      isNat[i] = isNatType;
      boundVarIndices[bv] = i;
    }

    var constraints = new List<IntBoundConstraint>();
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      if (bounds[i] is not IntBoundedPool intPool) {
        return false;
      }
      if (intPool.LowerBound != null) {
        if (!TryGetVarPlusConstant(intPool.LowerBound, boundVarIndices, out var sourceIndex, out var offset, cancellationCheck)) {
          return false;
        }
        constraints.Add(new IntBoundConstraint(i, sourceIndex, offset, true));
      }
      if (intPool.UpperBound != null) {
        if (!TryGetVarPlusConstant(intPool.UpperBound, boundVarIndices, out var sourceIndex, out var offset, cancellationCheck)) {
          return false;
        }
        constraints.Add(new IntBoundConstraint(i, sourceIndex, offset, false));
      }
    }

    return TryComputeConcreteIntDomains(boundVars, isNat, constraints, out domains);
  }

  private bool TryGetConcreteIntDomainsFromLogicalBody(QuantifierExpr quantifierExpr, out ConcreteDomain[] domains) {
    domains = Array.Empty<ConcreteDomain>();
    var boundVars = quantifierExpr.BoundVars;
    var boundVarIndices = new Dictionary<BoundVar, int>();
    var isNat = new bool[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      var bv = boundVars[i];
      if (!TryGetIntOrNatType(bv, out var isNatType)) {
        return false;
      }
      isNat[i] = isNatType;
      boundVarIndices[bv] = i;
    }

    var logicalBody = GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, cancellationCheck);
    Expression rangeExpr = logicalBody;
    if (quantifierExpr is ForallExpr) {
      Expression? accumulatedRange = null;
      var remainingBody = logicalBody;
      while (NormalizeForPattern(remainingBody, cancellationCheck) is BinaryExpr implication && IsImplication(implication)) {
        cancellationCheck?.Invoke();
        accumulatedRange = accumulatedRange == null
          ? implication.E0
          : Expression.CreateAnd(accumulatedRange, implication.E0);
        remainingBody = implication.E1;
      }
      if (accumulatedRange != null) {
        rangeExpr = accumulatedRange;
      }
    }

    var conjuncts = new List<Expression>();
    CollectConjuncts(rangeExpr, conjuncts, cancellationCheck);

    var constraints = new List<IntBoundConstraint>();
    foreach (var conjunct in conjuncts) {
      cancellationCheck?.Invoke();
      var resolved = NormalizeForPattern(conjunct, cancellationCheck);
      if (resolved is not BinaryExpr binaryExpr) {
        continue;
      }
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      var isGe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge || binaryExpr.Op == BinaryExpr.Opcode.Ge;
      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;

      Expression leftExpr;
      Expression rightExpr;
      bool isStrict;
      if (isLe || isLt) {
        leftExpr = binaryExpr.E0;
        rightExpr = binaryExpr.E1;
        isStrict = isLt;
      } else if (isGe || isGt) {
        // Normalize >= and > constraints into <= and < form.
        leftExpr = binaryExpr.E1;
        rightExpr = binaryExpr.E0;
        isStrict = isGt;
      } else {
        continue;
      }
      if (!TryGetVarPlusConstant(leftExpr, boundVarIndices, out var leftIndex, out var leftConst, cancellationCheck) ||
          !TryGetVarPlusConstant(rightExpr, boundVarIndices, out var rightIndex, out var rightConst, cancellationCheck)) {
        continue;
      }
      if (leftIndex.HasValue) {
        var upperOffset = rightConst - leftConst + (isStrict ? 0 : 1);
        constraints.Add(new IntBoundConstraint(leftIndex.Value, rightIndex, upperOffset, false));
      }
      if (rightIndex.HasValue) {
        var lowerOffset = leftConst - rightConst + (isStrict ? 1 : 0);
        constraints.Add(new IntBoundConstraint(rightIndex.Value, leftIndex, lowerOffset, true));
      }
    }

    return TryComputeConcreteIntDomains(boundVars, isNat, constraints, out domains);
  }

  private bool TryGetConcreteCharDomainsFromLogicalBody(QuantifierExpr quantifierExpr, out ConcreteDomain[] domains) {
    domains = Array.Empty<ConcreteDomain>();
    var boundVars = quantifierExpr.BoundVars;
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      if (!boundVars[i].Type.NormalizeExpand().IsCharType) {
        return false;
      }
    }

    var logicalBody = GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, cancellationCheck);
    Expression rangeExpr = logicalBody;
    if (quantifierExpr is ForallExpr && logicalBody is BinaryExpr impExpr && IsImplication(impExpr)) {
      rangeExpr = impExpr.E0;
    }

    var charDomains = new ConcreteDomain[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      if (!TryGetConcreteCharDomainFromRange(rangeExpr, boundVars[i], out var domain)) {
        return false;
      }
      charDomains[i] = domain;
    }

    domains = charDomains;
    return true;
  }

  /// <summary>
  /// Build a concrete character domain from a disjunction of range constraints.
  /// Returns false if the range cannot be parsed into finite char bounds or exceeds the instance cap.
  /// </summary>
  private bool TryGetConcreteCharDomainFromRange(Expression rangeExpr, BoundVar boundVar, out ConcreteDomain domain) {
    domain = null!;
    if (rangeExpr == null) {
      return false;
    }

    var disjuncts = new List<Expression>();
    var normalizedRange = NormalizeForPattern(rangeExpr, cancellationCheck);
    if (normalizedRange is ChainingExpression chainingExpression) {
      normalizedRange = chainingExpression.E;
    }
    CollectDisjuncts(normalizedRange, disjuncts, cancellationCheck);
    var ranges = new List<(int Lower, int Upper)>();
    foreach (var disjunct in disjuncts) {
      cancellationCheck?.Invoke();
      if (!TryExtractCharRangeFromConjuncts(disjunct, boundVar, out var lower, out var upper)) {
        return false;
      }
      if (lower >= upper) {
        continue;
      }
      ranges.Add((lower, upper));
    }

    if (ranges.Count == 0) {
      return false;
    }

    var elements = new List<Expression>();
    foreach (var (lower, upper) in ranges) {
      cancellationCheck?.Invoke();
      for (var codePoint = lower; codePoint < upper; codePoint++) {
        cancellationCheck?.Invoke();
        if (maxInstances > 0 && elements.Count >= maxInstances) {
          return false;
        }
        var value = (char)codePoint;
        elements.Add(new CharLiteralExpr(boundVar.Origin, value.ToString()) { Type = boundVar.Type });
      }
    }

    var size = new BigInteger(elements.Count);
    domain = new ConcreteDomain(size, () => EnumerateSetElements(elements, boundVar.Type));
    return true;
  }

  private bool TryExtractCharRangeFromConjuncts(Expression expr, BoundVar boundVar, out int lower, out int upper) {
    lower = default;
    upper = default;
    var hasLower = false;
    var hasUpper = false;
    var conjuncts = new List<Expression>();
    var normalizedExpr = NormalizeForPattern(expr, cancellationCheck);
    if (normalizedExpr is ChainingExpression chainingExpression) {
      normalizedExpr = chainingExpression.E;
    }
    CollectConjuncts(normalizedExpr, conjuncts, cancellationCheck);
    foreach (var conjunct in conjuncts) {
      cancellationCheck?.Invoke();
      var normalized = NormalizeForPattern(conjunct, cancellationCheck);
      if (normalized is not BinaryExpr binaryExpr) {
        continue;
      }
      if (!TryGetCharBound(binaryExpr, boundVar, out var boundLower, out var boundUpper) &&
          !TryGetCharBoundFallback(binaryExpr, boundVar, out boundLower, out boundUpper)) {
        continue;
      }
      if (boundLower.HasValue) {
        if (!hasLower || boundLower.Value > lower) {
          lower = boundLower.Value;
          hasLower = true;
        }
      }
      if (boundUpper.HasValue) {
        if (!hasUpper || boundUpper.Value < upper) {
          upper = boundUpper.Value;
          hasUpper = true;
        }
      }
    }

    return hasLower && hasUpper;
  }

  private bool TryGetCharBound(BinaryExpr binaryExpr, BoundVar boundVar, out int? lower, out int? upper) {
    lower = null;
    upper = null;

    if (!TryGetCharBoundOperand(binaryExpr.E0, boundVar, out var leftIsVar, out var leftLiteral) ||
        !TryGetCharBoundOperand(binaryExpr.E1, boundVar, out var rightIsVar, out var rightLiteral)) {
      return false;
    }
    if (leftIsVar == rightIsVar) {
      return false;
    }

    var resolvedOp = binaryExpr.ResolvedOp;
    if (resolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq) {
      var value = leftIsVar ? rightLiteral : leftLiteral;
      if (!value.HasValue) {
        return false;
      }
      lower = value.Value;
      upper = value.Value + 1;
      return true;
    }

    var isLess = resolvedOp == BinaryExpr.ResolvedOpcode.Lt ||
                 resolvedOp == BinaryExpr.ResolvedOpcode.LtChar ||
                 binaryExpr.Op == BinaryExpr.Opcode.Lt;
    var isLe = resolvedOp == BinaryExpr.ResolvedOpcode.Le ||
               resolvedOp == BinaryExpr.ResolvedOpcode.LeChar ||
               binaryExpr.Op == BinaryExpr.Opcode.Le;
    var isGreater = resolvedOp == BinaryExpr.ResolvedOpcode.Gt ||
                    resolvedOp == BinaryExpr.ResolvedOpcode.GtChar ||
                    binaryExpr.Op == BinaryExpr.Opcode.Gt;
    var isGe = resolvedOp == BinaryExpr.ResolvedOpcode.Ge ||
               resolvedOp == BinaryExpr.ResolvedOpcode.GeChar ||
               binaryExpr.Op == BinaryExpr.Opcode.Ge;
    if (!isLess && !isLe && !isGreater && !isGe) {
      return false;
    }

    if (leftIsVar) {
      if (!rightLiteral.HasValue) {
        return false;
      }
      if (isLess) {
        upper = rightLiteral.Value;
      } else if (isLe) {
        upper = rightLiteral.Value + 1;
      } else if (isGreater) {
        lower = rightLiteral.Value + 1;
      } else {
        lower = rightLiteral.Value;
      }
      return true;
    }

    if (!leftLiteral.HasValue) {
      return false;
    }
    if (isLess) {
      lower = leftLiteral.Value + 1;
    } else if (isLe) {
      lower = leftLiteral.Value;
    } else if (isGreater) {
      upper = leftLiteral.Value;
    } else {
      upper = leftLiteral.Value + 1;
    }
    return true;
  }

  private bool TryGetCharBoundFallback(BinaryExpr binaryExpr, BoundVar boundVar, out int? lower, out int? upper) {
    lower = null;
    upper = null;
    var resolvedOp = binaryExpr.ResolvedOp;
    var isLess = resolvedOp == BinaryExpr.ResolvedOpcode.LtChar || resolvedOp == BinaryExpr.ResolvedOpcode.Lt ||
                 binaryExpr.Op == BinaryExpr.Opcode.Lt;
    var isLe = resolvedOp == BinaryExpr.ResolvedOpcode.LeChar || resolvedOp == BinaryExpr.ResolvedOpcode.Le ||
               binaryExpr.Op == BinaryExpr.Opcode.Le;
    var isGreater = resolvedOp == BinaryExpr.ResolvedOpcode.GtChar || resolvedOp == BinaryExpr.ResolvedOpcode.Gt ||
                    binaryExpr.Op == BinaryExpr.Opcode.Gt;
    var isGe = resolvedOp == BinaryExpr.ResolvedOpcode.GeChar || resolvedOp == BinaryExpr.ResolvedOpcode.Ge ||
               binaryExpr.Op == BinaryExpr.Opcode.Ge;
    if (!isLess && !isLe && !isGreater && !isGe) {
      return false;
    }

    if (TryGetCharLiteral(binaryExpr.E0, out var leftLiteral, cancellationCheck) && IsBoundVarName(binaryExpr.E1, boundVar, cancellationCheck)) {
      if (isLess) {
        lower = leftLiteral + 1;
      } else if (isLe) {
        lower = leftLiteral;
      } else if (isGreater) {
        upper = leftLiteral;
      } else {
        upper = leftLiteral + 1;
      }
      return true;
    }

    if (TryGetCharLiteral(binaryExpr.E1, out var rightLiteral, cancellationCheck) && IsBoundVarName(binaryExpr.E0, boundVar, cancellationCheck)) {
      if (isLess) {
        upper = rightLiteral;
      } else if (isLe) {
        upper = rightLiteral + 1;
      } else if (isGreater) {
        lower = rightLiteral + 1;
      } else {
        lower = rightLiteral;
      }
      return true;
    }

    return false;
  }

  private static bool IsBoundVarName(Expression expr, BoundVar boundVar, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (expr is IdentifierExpr identifierExpr) {
      return identifierExpr.Name == boundVar.Name;
    }
    return false;
  }

  private bool TryGetCharBoundOperand(Expression expr, BoundVar boundVar, out bool isVar, out int? literal) {
    isVar = false;
    literal = null;
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (expr is ConversionExpr conversionExpr) {
      var fromType = conversionExpr.E.Type?.NormalizeExpand();
      var toType = conversionExpr.Type?.NormalizeExpand();
      if (fromType != null && toType is IntType && fromType.IsCharType) {
        expr = NormalizeForPattern(conversionExpr.E, cancellationCheck);
      }
    }
    if (expr is IdentifierExpr identifierExpr &&
        (identifierExpr.Var == boundVar || identifierExpr.Name == boundVar.Name)) {
      isVar = true;
      return true;
    }
    if (PartialEvaluatorEngine.TryGetReducedIntLiteral(expr, out var intLiteral, cancellationCheck)) {
      if (intLiteral >= 0 && intLiteral <= 0xFFFF) {
        literal = (int)intLiteral;
        return true;
      }
      return false;
    }
    if (TryGetCharLiteral(expr, out var value, cancellationCheck)) {
      literal = value;
      return true;
    }
    return false;
  }

  private static bool TryGetCharLiteral(Expression expr, out int value, Action? cancellationCheck = null) {
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
      value = utf16Code;
      return true;
    }

    if (literal.StartsWith("\\U{", StringComparison.Ordinal) && literal.EndsWith("}", StringComparison.Ordinal)) {
      var hexSpan = literal.AsSpan(3, literal.Length - 4);
      if (TryParseHex(hexSpan, out var unicodeCode, cancellationCheck) && unicodeCode <= 0xFFFF) {
        value = unicodeCode;
        return true;
      }
    }

    return false;
  }

  private static bool TryParseHex(ReadOnlySpan<char> hexSpan, out int value, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    value = 0;
    if (hexSpan.IsEmpty) {
      return false;
    }
    foreach (var digit in hexSpan) {
      cancellationCheck?.Invoke();
      int digitValue;
      if (digit >= '0' && digit <= '9') {
        digitValue = digit - '0';
      } else if (digit >= 'a' && digit <= 'f') {
        digitValue = digit - 'a' + 10;
      } else if (digit >= 'A' && digit <= 'F') {
        digitValue = digit - 'A' + 10;
      } else {
        return false;
      }
      value = value * 16 + digitValue;
    }
    return true;
  }

  private bool TryComputeConcreteIntDomains(IReadOnlyList<BoundVar> boundVars, bool[] isNat,
    List<IntBoundConstraint> constraints, out ConcreteDomain[] domains) {
    var lowerBounds = new BigInteger?[boundVars.Count];
    var upperBounds = new BigInteger?[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      if (isNat[i]) {
        lowerBounds[i] = BigInteger.Zero;
      }
    }

    var changed = true;
    var passes = 0;
    var maxPasses = boundVars.Count * boundVars.Count + 5;
    while (changed && passes < maxPasses) {
      cancellationCheck?.Invoke();
      changed = false;
      passes++;
      foreach (var constraint in constraints) {
        cancellationCheck?.Invoke();
        if (constraint.IsLower) {
          var sourceValue = constraint.SourceIndex.HasValue ? lowerBounds[constraint.SourceIndex.Value] : (BigInteger?)BigInteger.Zero;
          if (sourceValue == null) {
            continue;
          }
          var candidate = sourceValue.Value + constraint.Offset;
          if (lowerBounds[constraint.TargetIndex] == null || candidate > lowerBounds[constraint.TargetIndex]!.Value) {
            lowerBounds[constraint.TargetIndex] = candidate;
            changed = true;
          }
        } else {
          var sourceValue = constraint.SourceIndex.HasValue ? upperBounds[constraint.SourceIndex.Value] : (BigInteger?)BigInteger.Zero;
          if (sourceValue == null) {
            continue;
          }
          var candidate = sourceValue.Value + constraint.Offset;
          if (upperBounds[constraint.TargetIndex] == null || candidate < upperBounds[constraint.TargetIndex]!.Value) {
            upperBounds[constraint.TargetIndex] = candidate;
            changed = true;
          }
        }
      }
    }

    // One empty factor makes the complete Cartesian product empty, even when
    // another factor has only relational (and therefore non-concrete) bounds.
    // Represent the product as empty so the caller returns the quantifier's
    // vacuous value before attempting enumeration.
    if (detectEmptyProduct && Enumerable.Range(0, boundVars.Count).Any(index => {
      cancellationCheck?.Invoke();
      return lowerBounds[index].HasValue && upperBounds[index].HasValue &&
        lowerBounds[index]!.Value >= upperBounds[index]!.Value;
    })) {
      domains = boundVars.Select(boundVar => {
        cancellationCheck?.Invoke();
        return new ConcreteDomain(BigInteger.Zero, () => Enumerable.Empty<Expression>());
      }).ToArray();
      return true;
    }

    domains = new ConcreteDomain[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      cancellationCheck?.Invoke();
      if (lowerBounds[i] == null || upperBounds[i] == null) {
        return false;
      }
      var lower = lowerBounds[i]!.Value;
      var upper = upperBounds[i]!.Value;
      if (isNat[i] && lower < 0) {
        return false;
      }
      var bv = boundVars[i];
      var size = upper - lower;
      domains[i] = new ConcreteDomain(size, () => EnumerateIntRange(bv, lower, upper));
    }

    return true;
  }

  private bool TryGetIntOrNatType(BoundVar boundVar, out bool isNat) {
    var subsetType = boundVar.Type.AsSubsetType;
    isNat = subsetType == systemModuleManager.NatDecl;
    var isInt = !isNat && boundVar.Type.NormalizeExpand() is IntType;
    return isNat || isInt;
  }

  private static bool TryGetVarPlusConstant(Expression expr, IReadOnlyDictionary<BoundVar, int> boundVarIndices,
    out int? varIndex, out BigInteger constant, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    expr = NormalizeForPattern(expr, cancellationCheck);
    if (PartialEvaluatorEngine.TryGetReducedIntLiteral(expr, out var literal, cancellationCheck)) {
      varIndex = null;
      constant = literal;
      return true;
    }
    if (expr is IdentifierExpr identifierExpr && identifierExpr.Var is BoundVar boundVar &&
        boundVarIndices.TryGetValue(boundVar, out var index)) {
      varIndex = index;
      constant = BigInteger.Zero;
      return true;
    }
    if (expr is BinaryExpr binaryExpr) {
      var isAdd = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Add || binaryExpr.Op == BinaryExpr.Opcode.Add;
      var isSub = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub || binaryExpr.Op == BinaryExpr.Opcode.Sub;
      if (!isAdd && !isSub) {
        varIndex = null;
        constant = default;
        return false;
      }
      if (!TryGetVarPlusConstant(binaryExpr.E0, boundVarIndices, out var leftIndex, out var leftConst, cancellationCheck) ||
          !TryGetVarPlusConstant(binaryExpr.E1, boundVarIndices, out var rightIndex, out var rightConst, cancellationCheck)) {
        varIndex = null;
        constant = default;
        return false;
      }
      if (leftIndex.HasValue && rightIndex.HasValue) {
        varIndex = null;
        constant = default;
        return false;
      }
      if (isAdd) {
        varIndex = leftIndex ?? rightIndex;
        constant = leftConst + rightConst;
        return true;
      }
      if (rightIndex.HasValue) {
        varIndex = null;
        constant = default;
        return false;
      }
      varIndex = leftIndex;
      constant = leftConst - rightConst;
      return true;
    }
    varIndex = null;
    constant = default;
    return false;
  }

  // === Concrete domain inference entrypoints ===
  /// <summary>
  /// Try to compute a concrete, finite domain for a bound variable based on its bounded pool.
  /// Returns false when the pool is non-finite, non-literal, or exceeds the instance cap.
  /// </summary>
  internal bool TryGetConcreteDomain(BoundVar bv, BoundedPool? bound, Func<Expression, Expression> simplify,
    out ConcreteDomain domain) {
    CheckForCancellation();
    domain = null!;

    if (bound == null) {
      return false;
    }

    if (TryGetConcreteIntDomain(bv, bound, out var lower, out var upper)) {
      var size = upper - lower;
      domain = new ConcreteDomain(size, () => EnumerateIntRange(bv, lower, upper));
      return true;
    }

    if (bound is BoolBoundedPool) {
      domain = new ConcreteDomain(2, () => EnumerateBooleanValues(bv.Type, bv.Origin));
      return true;
    }

    if (bound is CharBoundedPool) {
      if (maxInstances > 0 && CharDomainCardinality > maxInstances) {
        return false;
      }
      domain = new ConcreteDomain(CharDomainCardinality, () => EnumerateAllChars(bv.Type, bv.Origin));
      return true;
    }

    if (bound is ExactBoundedPool exactBoundedPool) {
      var value = StripConcreteSyntax(exactBoundedPool.E, cancellationCheck);
      if (!IsLiteralExpression(value, cancellationCheck)) {
        return false;
      }
      domain = new ConcreteDomain(BigInteger.One, () => new[] { value });
      return true;
    }

    if (bound is SetBoundedPool setPool) {
      if (!setPool.IsFiniteCollection) {
        return false;
      }
      var materializationCap = maxInstances == 0 ? (uint?)null : maxInstances;
      if (!TryMaterializeSetElements(setPool.Set, materializationCap, simplify, out var elements)) {
        return false;
      }
      var size = new BigInteger(elements.Count);
      domain = new ConcreteDomain(size, () => EnumerateSetElements(elements, bv.Type));
      return true;
    }

    if (bound is SeqBoundedPool seqPool) {
      var resolved = StripConcreteSyntax(seqPool.Seq, cancellationCheck);
      if (resolved is SeqDisplayExpr seqDisplay) {
        var elements = new List<Expression>();
        var elementSet = new HashSet<Expression>(LiteralExpressionStructuralComparer.For(cancellationCheck));
        var cap = maxInstances == 0 ? (uint?)null : maxInstances;
        foreach (var element in seqDisplay.Elements) {
          CheckForCancellation();
          var value = StripConcreteSyntax(element, cancellationCheck);
          if (!IsLiteralExpression(value, cancellationCheck)) {
            return false;
          }
          if (!TryAddUniqueLiteral(elements, elementSet, value, cap)) {
            return false;
          }
        }
        var size = new BigInteger(elements.Count);
        domain = new ConcreteDomain(size, () => EnumerateSetElements(elements, bv.Type));
        return true;
      }
    }

    if (bound is MultiSetBoundedPool multisetPool) {
      var resolved = StripConcreteSyntax(multisetPool.MultiSet, cancellationCheck);
      if (resolved is MultiSetDisplayExpr multisetDisplay) {
        var elements = new List<Expression>();
        var elementSet = new HashSet<Expression>(LiteralExpressionStructuralComparer.For(cancellationCheck));
        var cap = maxInstances == 0 ? (uint?)null : maxInstances;
        foreach (var element in multisetDisplay.Elements) {
          CheckForCancellation();
          var value = StripConcreteSyntax(element, cancellationCheck);
          if (!IsLiteralExpression(value, cancellationCheck)) {
            return false;
          }
          if (!TryAddUniqueLiteral(elements, elementSet, value, cap)) {
            return false;
          }
        }
        var size = new BigInteger(elements.Count);
        domain = new ConcreteDomain(size, () => EnumerateSetElements(elements, bv.Type));
        return true;
      }
    }

    if (bound is MapBoundedPool mapPool) {
      if (!mapPool.IsFiniteCollection) {
        return false;
      }
      var resolved = StripConcreteSyntax(mapPool.Map, cancellationCheck);
      if (resolved is MapDisplayExpr mapDisplay) {
        if (!mapDisplay.Finite) {
          return false;
        }
        var keys = new List<Expression>();
        var keySet = new HashSet<Expression>(LiteralExpressionStructuralComparer.For(cancellationCheck));
        var cap = maxInstances == 0 ? (uint?)null : maxInstances;
        foreach (var entry in mapDisplay.Elements) {
          CheckForCancellation();
          var key = StripConcreteSyntax(entry.A, cancellationCheck);
          var value = StripConcreteSyntax(entry.B, cancellationCheck);
          if (!IsLiteralExpression(key, cancellationCheck) || !IsLiteralExpression(value, cancellationCheck)) {
            return false;
          }
          if (!TryAddUniqueLiteral(keys, keySet, key, cap)) {
            return false;
          }
        }
        var size = new BigInteger(keys.Count);
        domain = new ConcreteDomain(size, () => EnumerateSetElements(keys, bv.Type));
        return true;
      }

      if (resolved is MapComprehension mapComprehension) {
        if (!mapComprehension.Finite) {
          return false;
        }

        if (!TryMaterializeMapComprehensionKeys(mapComprehension, simplify, out var keys)) {
          return false;
        }

        var size = new BigInteger(keys.Count);
        domain = new ConcreteDomain(size, () => EnumerateSetElements(keys, bv.Type));
        return true;
      }
    }

    if (bound is SubSetBoundedPool subSetPool) {
      if (!subSetPool.IsFiniteCollection) {
        return false;
      }
      if (maxInstances > 0 && TryGetSetElementUpperBound(subSetPool.UpperBound, simplify, out var elementUpperBound)) {
        var maxElements = MaxSubsetElementCount(maxInstances, cancellationCheck);
        if (elementUpperBound > maxElements) {
          return false;
        }
      }
      var materializationCap = maxInstances == 0 ? (uint?)null : maxInstances;
      if (!TryMaterializeSetElements(subSetPool.UpperBound, materializationCap, simplify, out var elements)) {
        return false;
      }
      var setType = bv.Type.NormalizeExpand().AsSetType;
      if (setType == null) {
        return false;
      }
      var size = BigInteger.One << elements.Count;
      domain = new ConcreteDomain(size, () => EnumerateSubsets(bv.Origin, elements, setType));
      return true;
    }

    if (bound is DatatypeBoundedPool datatypePool) {
      if (!datatypePool.Decl.HasFinitePossibleValues) {
        return false;
      }

      var singletonCtors = datatypePool.Decl.Ctors
        .Where(ctor => { CheckForCancellation(); return ctor.Formals.Count == 0; })
        .ToList();
      if (singletonCtors.Count == 0) {
        return false;
      }
      if (maxInstances > 0 && singletonCtors.Count > maxInstances) {
        return false;
      }

      domain = new ConcreteDomain(singletonCtors.Count,
        () => EnumerateDatatypeSingletonConstructors(bv.Type, bv.Origin, datatypePool.Decl.Name, singletonCtors));
      return true;
    }

    return false;
  }

  // === Enumerators & small utilities ===
  private IEnumerable<Expression> EnumerateIntRange(BoundVar bv, BigInteger lower, BigInteger upper) {
    for (var v = lower; v < upper; v++) {
      CheckForCancellation();
      yield return new LiteralExpr(bv.Origin, v) { Type = bv.Type };
    }
  }

  private IEnumerable<Expression> EnumerateBooleanValues(Type boolType, IOrigin origin) {
    CheckForCancellation();
    var falseExpr = Expression.CreateBoolLiteral(origin, false);
    falseExpr.Type = boolType;
    yield return falseExpr;

    var trueExpr = Expression.CreateBoolLiteral(origin, true);
    trueExpr.Type = boolType;
    yield return trueExpr;
  }

  private IEnumerable<Expression> EnumerateAllChars(Type charType, IOrigin origin) {
    for (var codePoint = 0; codePoint < CharDomainCardinality; codePoint++) {
      CheckForCancellation();
      var charExpr = new CharLiteralExpr(origin, ((char)codePoint).ToString()) { Type = charType };
      yield return charExpr;
    }
  }

  private IEnumerable<Expression> EnumerateDatatypeSingletonConstructors(Type datatypeType, IOrigin origin,
    string datatypeName, IEnumerable<DatatypeCtor> constructors) {
    foreach (var constructor in constructors) {
      CheckForCancellation();
      var value = new DatatypeValue(origin, datatypeName, constructor.Name, new List<Expression>()) {
        Type = datatypeType,
        Ctor = constructor
      };
      yield return value;
    }
  }

  private IEnumerable<Expression> EnumerateSetElements(List<Expression> elements, Type elementType) {
    foreach (var element in elements) {
      CheckForCancellation();
      EnsureExpressionType(element, elementType);
      yield return element;
    }
  }

  private IEnumerable<Expression> EnumerateSubsets(IOrigin origin, List<Expression> elements, SetType setType) {
    var current = new List<Expression>();
    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, 0, current)) {
      CheckForCancellation();
      yield return subset;
    }
  }

  private IEnumerable<Expression> EnumerateSubsetsRecursive(IOrigin origin, List<Expression> elements, SetType setType, int index, List<Expression> current) {
    CheckForCancellation();
    if (index == elements.Count) {
      var subsetElements = new List<Expression>(current);
      foreach (var element in subsetElements) {
        CheckForCancellation();
        EnsureExpressionType(element, setType.Arg);
      }
      var subsetExpr = new SetDisplayExpr(origin, setType.Finite, subsetElements) { Type = setType };
      yield return subsetExpr;
      yield break;
    }

    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, index + 1, current)) {
      CheckForCancellation();
      yield return subset;
    }

    current.Add(elements[index]);
    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, index + 1, current)) {
      CheckForCancellation();
      yield return subset;
    }
    current.RemoveAt(current.Count - 1);
  }

  private bool TryGetSetElementUpperBound(Expression setExpr, Func<Expression, Expression> simplify, out BigInteger upperBound) {
    upperBound = default;
    var resolved = StripConcreteSyntax(setExpr, cancellationCheck);

    if (resolved is SetDisplayExpr setDisplay) {
      upperBound = setDisplay.Elements.Count;
      return true;
    }

    if (resolved is SetComprehension setComprehension) {
      return TryGetSetComprehensionUpperBound(setComprehension, simplify, out upperBound);
    }

    return false;
  }

  private bool TryGetSetComprehensionUpperBound(SetComprehension setComprehension, Func<Expression, Expression> simplify, out BigInteger upperBound) {
    upperBound = default;
    if (!setComprehension.Finite) {
      return false;
    }
    if (setComprehension.Bounds == null || setComprehension.Bounds.Count != setComprehension.BoundVars.Count) {
      return false;
    }

    var product = BigInteger.One;
    for (var i = 0; i < setComprehension.BoundVars.Count; i++) {
      cancellationCheck?.Invoke();
      var bv = setComprehension.BoundVars[i];
      var bound = setComprehension.Bounds[i];
      if (!TryGetConcreteIntDomain(bv, bound, out var lower, out var upper)) {
        return false;
      }
      var width = upper - lower;
      if (width <= BigInteger.Zero) {
        upperBound = BigInteger.Zero;
        return true;
      }
      product *= width;
    }

    upperBound = product;
    return true;
  }

  private static BigInteger MaxSubsetElementCount(uint maxInstances, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (maxInstances == 0) {
      return BigInteger.Zero;
    }
    var value = maxInstances;
    var count = 0;
    while (value > 1) {
      cancellationCheck?.Invoke();
      value >>= 1;
      count++;
    }
    return new BigInteger(count);
  }

  private bool TryGetConcreteIntDomain(BoundVar bv, BoundedPool? bound, out BigInteger lower, out BigInteger upper) {
    lower = default;
    upper = default;

    if (bound is not IntBoundedPool intPool) {
      return false;
    }

    var subsetType = bv.Type.AsSubsetType;
    var isNat = subsetType == systemModuleManager.NatDecl;
    var isInt = !isNat && bv.Type.NormalizeExpand() is IntType;
    if (!isNat && !isInt) {
      return false;
    }

    Expression upperBound = intPool.UpperBound;
    if (upperBound != null) {
      upperBound = StripConcreteSyntax(upperBound, cancellationCheck);
    }

    if (upperBound == null || !PartialEvaluatorEngine.TryGetReducedIntLiteral(upperBound, out upper, cancellationCheck)) {
      return false;
    }

    Expression lowerBound = intPool.LowerBound;
    if (lowerBound != null) {
      lowerBound = StripConcreteSyntax(lowerBound, cancellationCheck);
    }

    if (lowerBound == null) {
      if (!isNat) {
        return false;
      }
      lower = BigInteger.Zero;
    } else if (!PartialEvaluatorEngine.TryGetReducedIntLiteral(lowerBound, out lower, cancellationCheck)) {
      return false;
    }

    if (isNat && lower < 0) {
      return false;
    }

    return true;
  }

  // === Bounds discovery helpers ===
  private static List<BoundedPool?>? TryGetBoundsOrDiscover(
    List<BoundVar> boundVars,
    List<BoundedPool?>? existingBounds,
    Func<Expression?> getExpressionForDiscovery,
    bool polarity, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    var bounds = existingBounds;
    if (bounds == null || bounds.Count != boundVars.Count) {
      var expr = getExpressionForDiscovery();
      if (expr == null) {
        return null;
      }
      bounds = ModuleResolver.DiscoverBestBounds_MultipleVars(boundVars, expr, polarity);
    }
    return bounds;
  }
}
