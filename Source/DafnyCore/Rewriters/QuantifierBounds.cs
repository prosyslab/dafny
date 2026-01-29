#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

/// <summary>
/// Shared helpers for discovering bounds, inferring concrete domains, and materializing
/// set/map comprehensions for bounded quantifier unrolling and partial evaluation.
/// </summary>
internal sealed class QuantifierBounds {
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint maxInstances;

  internal uint MaxInstances => maxInstances;

  internal QuantifierBounds(SystemModuleManager systemModuleManager, uint maxInstances) {
    this.systemModuleManager = systemModuleManager ?? throw new ArgumentNullException(nameof(systemModuleManager));
    this.maxInstances = maxInstances;
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

  internal static void EnsureExpressionType(Expression expr, Type type) {
    ExpressionRewriteUtil.EnsureExpressionType(expr, type);
  }

  internal static Expression StripConcreteSyntax(Expression expr) {
    return ExpressionRewriteUtil.StripConcreteSyntax(expr);
  }

  internal static Expression NormalizeForPattern(Expression expr) {
    expr = StripConcreteSyntax(expr);
    if (expr is ChainingExpression chainingExpression) {
      expr = chainingExpression.E;
    }
    if (expr is ParensExpression parens && parens.ResolvedExpression != null) {
      expr = parens.ResolvedExpression;
    }
    if (expr is ConversionExpr conversionExpr) {
      var fromType = conversionExpr.E.Type?.NormalizeExpand();
      var toType = conversionExpr.Type?.NormalizeExpand();
      if (fromType != null && toType != null && fromType.Equals(toType)) {
        expr = conversionExpr.E;
      }
    }
    return expr;
  }

  internal static void CollectConjuncts(Expression expr, List<Expression> conjuncts) {
    expr = NormalizeForPattern(expr);
    if (expr is BinaryExpr binaryExpr && IsConjunction(binaryExpr)) {
      CollectConjuncts(binaryExpr.E0, conjuncts);
      CollectConjuncts(binaryExpr.E1, conjuncts);
      return;
    }
    conjuncts.Add(expr);
  }

  internal static void CollectDisjuncts(Expression expr, List<Expression> disjuncts) {
    expr = NormalizeForPattern(expr);
    if (expr is BinaryExpr binaryExpr &&
        (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Or || binaryExpr.Op == BinaryExpr.Opcode.Or)) {
      CollectDisjuncts(binaryExpr.E0, disjuncts);
      CollectDisjuncts(binaryExpr.E1, disjuncts);
      return;
    }
    disjuncts.Add(expr);
  }

  internal static bool IsBoundVar(Expression? expr, BoundVar boundVar) {
    if (expr == null) {
      return false;
    }
    expr = NormalizeForPattern(expr);
    return expr is IdentifierExpr identifierExpr && (identifierExpr.Var == boundVar || identifierExpr.Name == boundVar.Name);
  }

  private static bool IsConjunction(BinaryExpr binaryExpr) {
    return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binaryExpr.Op == BinaryExpr.Opcode.And;
  }

  private static bool IsImplication(BinaryExpr binaryExpr) {
    return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp || binaryExpr.Op == BinaryExpr.Opcode.Imp;
  }

  private static bool IsLiteralExpression(Expression expr) {
    expr = StripConcreteSyntax(expr);
    switch (expr) {
      case LiteralExpr:
        return true;
      case DisplayExpression displayExpression:
        return displayExpression.Elements.All(IsLiteralExpression);
      case MapDisplayExpr mapDisplayExpr:
        return mapDisplayExpr.Elements.All(entry => IsLiteralExpression(entry.A) && IsLiteralExpression(entry.B));
      case DatatypeValue datatypeValue:
        return datatypeValue.Arguments.All(IsLiteralExpression);
      default:
        return false;
    }
  }

  private static bool LiteralStructuralEquals(Expression left, Expression right) {
    left = StripConcreteSyntax(left);
    right = StripConcreteSyntax(right);
    if (ReferenceEquals(left, right)) {
      return true;
    }
    switch (left) {
      case LiteralExpr leftLiteral when right is LiteralExpr rightLiteral:
        return leftLiteral.GetType() == rightLiteral.GetType() && Equals(leftLiteral.Value, rightLiteral.Value);
      case DisplayExpression leftDisplay when right is DisplayExpression rightDisplay:
        if (leftDisplay.GetType() != rightDisplay.GetType() || leftDisplay.Elements.Count != rightDisplay.Elements.Count) {
          return false;
        }
        for (var i = 0; i < leftDisplay.Elements.Count; i++) {
          if (!LiteralStructuralEquals(leftDisplay.Elements[i], rightDisplay.Elements[i])) {
            return false;
          }
        }
        return true;
      case MapDisplayExpr leftMap when right is MapDisplayExpr rightMap:
        if (leftMap.Finite != rightMap.Finite || leftMap.Elements.Count != rightMap.Elements.Count) {
          return false;
        }
        for (var i = 0; i < leftMap.Elements.Count; i++) {
          var leftEntry = leftMap.Elements[i];
          var rightEntry = rightMap.Elements[i];
          if (!LiteralStructuralEquals(leftEntry.A, rightEntry.A) || !LiteralStructuralEquals(leftEntry.B, rightEntry.B)) {
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
          if (!LiteralStructuralEquals(leftDatatype.Arguments[i], rightDatatype.Arguments[i])) {
            return false;
          }
        }
        return true;
      default:
        return false;
    }
  }

  private static bool ContainsLiteral(List<Expression> elements, Expression candidate) {
    foreach (var element in elements) {
      if (LiteralStructuralEquals(element, candidate)) {
        return true;
      }
    }
    return false;
  }

  private readonly record struct IntBoundConstraint(int TargetIndex, int? SourceIndex, BigInteger Offset, bool IsLower);

  internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, Func<Expression, Expression> simplifyAfterSubst, out Expression rewritten) {
    rewritten = quantifierExpr;

    if (quantifierExpr.SplitQuantifier != null || quantifierExpr.SplitQuantifierExpression != null) {
      return false;
    }

    var bounds = TryGetBoundsOrDiscover(quantifierExpr.BoundVars, quantifierExpr.Bounds,
      () => quantifierExpr.LogicalBody(bypassSplitQuantifier: true), quantifierExpr is ExistsExpr);
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

    // Domain product must be within cap.
    var size = BigInteger.One;
    for (var i = 0; i < domains.Length; i++) {
      var domainSize = domains[i].Size;
      if (domainSize <= BigInteger.Zero) {
        rewritten = Expression.CreateBoolLiteral(quantifierExpr.Origin, isForall);
        rewritten.Type = Type.Bool;
        return true;
      }

      size *= domainSize;
      if (maxInstances > 0 && size > maxInstances) {
        return false;
      }
    }

    // Use the original logical body and simplify per-instance after substitution. This naturally drops
    // guaranteed bounds like 0 <= i < N from the instantiated formula.
    var logicalBody = quantifierExpr.LogicalBody(bypassSplitQuantifier: true);
    if (logicalBody.Type == null) {
      logicalBody.Type = Type.Bool;
    }

    Expression accumulator = Expression.CreateBoolLiteral(quantifierExpr.Origin, isForall);
    accumulator.Type = Type.Bool;

    void AddInstance(Expression instance) {
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

    void Enumerate(int varIndex) {
      if (IsShortCircuited()) {
        return;
      }

      if (varIndex == domains.Length) {
        var substituter = new Substituter(null, substMap, typeMap);
        var inst = substituter.Substitute(logicalBody);
        inst = simplifyAfterSubst(inst);
        AddInstance(inst);
        return;
      }

      var bv = quantifierExpr.BoundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        if (IsShortCircuited()) {
          return;
        }

        EnsureExpressionType(value, bv.Type);
        substMap[bv] = value;
        Enumerate(varIndex + 1);
      }
    }

    Enumerate(0);
    rewritten = accumulator;
    return true;
  }

  internal bool TryMaterializeSetElements(Expression setExpr, uint? materializationCap, Func<Expression, Expression> simplify,
    out List<Expression> elements) {
    elements = null!;
    var resolved = StripConcreteSyntax(setExpr);

    if (resolved is SetDisplayExpr setDisplay) {
      if (materializationCap.HasValue && setDisplay.Elements.Count > materializationCap.Value) {
        return false;
      }
      elements = setDisplay.Elements.ToList();
      return true;
    }

    if (resolved is SetComprehension setComprehension) {
      return TryMaterializeSetComprehension(setComprehension, simplify, out elements);
    }

    return false;
  }

  internal bool TryMaterializeSetComprehension(SetComprehension setComprehension, Func<Expression, Expression> simplify,
    out List<Expression> elements) {
    elements = null!;

    if (!setComprehension.Finite) {
      return false;
    }

    var bounds = TryGetBoundsOrDiscover(setComprehension.BoundVars, setComprehension.Bounds,
      () => setComprehension.Range, polarity: true);
    if (bounds == null || bounds.Count != setComprehension.BoundVars.Count) {
      return false;
    }
    if (bounds.Any(bound => bound == null)) {
      if (setComprehension.Range == null) {
        return false;
      }
      var discovered = ModuleResolver.DiscoverBestBounds_MultipleVars(setComprehension.BoundVars, setComprehension.Range, true);
      if (discovered == null || discovered.Count != setComprehension.BoundVars.Count) {
        return false;
      }
      bounds = discovered;
    }

    var domains = new ConcreteDomain[setComprehension.BoundVars.Count];
    for (var i = 0; i < setComprehension.BoundVars.Count; i++) {
      var bv = setComprehension.BoundVars[i];
      var bound = bounds[i];
      ConcreteDomain domain;
      if (bv.Type.NormalizeExpand().IsCharType && setComprehension.Range != null &&
          TryGetConcreteCharDomainFromRange(setComprehension.Range, bv, out var charDomain)) {
        domain = charDomain;
      } else if (!TryGetConcreteDomain(bv, bound, simplify, out domain)) {
        return false;
      }
      domains[i] = domain;
    }

    if (maxInstances > 0) {
      var size = BigInteger.One;
      foreach (var domain in domains) {
        size *= domain.Size;
        if (size > maxInstances) {
          return false;
        }
      }
    }

    var results = new List<Expression>();
    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();
    var range = setComprehension.Range;
    var term = setComprehension.Term;

    bool Enumerate(int varIndex) {
      if (varIndex == domains.Length) {
        if (maxInstances > 0 && results.Count >= maxInstances) {
          return false;
        }
        var substituter = new Substituter(null, substMap, typeMap);
        if (range != null) {
          var rangeInst = simplify(substituter.Substitute(range));
          rangeInst = StripConcreteSyntax(rangeInst);
          if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
            return false;
          }
          if (!rangeValue) {
            return true;
          }
        }

        var termInst = simplify(substituter.Substitute(term));
        termInst = StripConcreteSyntax(termInst);
        results.Add(termInst);
        return true;
      }

      var bv = setComprehension.BoundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        EnsureExpressionType(value, bv.Type);
        substMap[bv] = value;
        if (!Enumerate(varIndex + 1)) {
          return false;
        }
      }
      return true;
    }

    if (!Enumerate(0)) {
      return false;
    }

    var elementType = setComprehension.Type.NormalizeExpand().AsSetType?.Arg;
    if (elementType != null) {
      foreach (var element in results) {
        EnsureExpressionType(element, elementType);
      }
    }
    elements = results;
    return true;
  }

  internal bool TryMaterializeMapComprehension(MapComprehension mapComprehension, Func<Expression, Expression> simplify,
    out List<MapDisplayEntry> entries) {
    entries = null!;
    if (!mapComprehension.Finite) {
      return false;
    }

    var bounds = TryGetBoundsOrDiscover(mapComprehension.BoundVars, mapComprehension.Bounds,
      () => mapComprehension.Range, polarity: true);
    if (bounds == null || bounds.Count != mapComprehension.BoundVars.Count) {
      return false;
    }

    var domains = new ConcreteDomain[mapComprehension.BoundVars.Count];
    for (var i = 0; i < mapComprehension.BoundVars.Count; i++) {
      var bv = mapComprehension.BoundVars[i];
      var bound = bounds[i];
      if (!TryGetConcreteDomain(bv, bound, simplify, out var domain)) {
        return false;
      }
      domains[i] = domain;
    }

    if (maxInstances > 0) {
      var size = BigInteger.One;
      foreach (var domain in domains) {
        size *= domain.Size;
        if (size > maxInstances) {
          return false;
        }
      }
    }

    var resultEntries = new List<MapDisplayEntry>();
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

    bool Enumerate(int varIndex) {
      if (varIndex == domains.Length) {
        if (maxInstances > 0 && resultEntries.Count >= maxInstances) {
          return false;
        }
        var substituter = new Substituter(null, substMap, typeMap);
        if (mapComprehension.Range != null) {
          var rangeInst = simplify(substituter.Substitute(mapComprehension.Range));
          rangeInst = StripConcreteSyntax(rangeInst);
          if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
            return false;
          }
          if (!rangeValue) {
            return true;
          }
        }

        var keyExpr = simplify(substituter.Substitute(keyTemplate));
        keyExpr = StripConcreteSyntax(keyExpr);
        if (!IsLiteralExpression(keyExpr)) {
          return false;
        }

        var valueExpr = simplify(substituter.Substitute(mapComprehension.Term));
        valueExpr = StripConcreteSyntax(valueExpr);

        for (var i = 0; i < resultEntries.Count; i++) {
          if (LiteralStructuralEquals(resultEntries[i].A, keyExpr)) {
            if (!LiteralStructuralEquals(resultEntries[i].B, valueExpr)) {
              return false;
            }
            return true;
          }
        }

        resultEntries.Add(new MapDisplayEntry(keyExpr, valueExpr));
        return true;
      }

      var bv = mapComprehension.BoundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        if (maxInstances > 0 && resultEntries.Count >= maxInstances) {
          return false;
        }
        EnsureExpressionType(value, bv.Type);
        substMap[bv] = value;
        if (!Enumerate(varIndex + 1)) {
          return false;
        }
      }
      return true;
    }

    if (!Enumerate(0)) {
      return false;
    }

    entries = resultEntries;
    return true;
  }

  internal bool TryGetSeqLengthConstraint(Expression expr, BoundVar seqVar, out int length) {
    length = default;
    expr = NormalizeForPattern(expr);
    if (expr is not BinaryExpr binaryExpr) {
      return false;
    }
    var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
    if (!isEq) {
      return false;
    }

    if (TryGetSeqLength(binaryExpr.E0, seqVar, out var lengthValue) &&
        TryGetIntLiteralValue(binaryExpr.E1, out var lengthLiteral)) {
      length = lengthLiteral;
      return lengthValue;
    }

    if (TryGetSeqLength(binaryExpr.E1, seqVar, out var lengthValueAlt) &&
        TryGetIntLiteralValue(binaryExpr.E0, out var lengthLiteralAlt)) {
      length = lengthLiteralAlt;
      return lengthValueAlt;
    }

    return false;
  }

  internal bool TryGetElementDomainConstraint(ForallExpr forallExpr, BoundVar seqVar, int length, out List<Expression> domain) {
    domain = null!;
    if (forallExpr.BoundVars.Count != 1) {
      return false;
    }

    var indexVar = forallExpr.BoundVars[0];
    if (forallExpr.Range == null || !TryGetIndexRange(forallExpr.Range, indexVar, length)) {
      return false;
    }

    var term = NormalizeForPattern(forallExpr.Term);
    if (TryGetSetMembershipDomain(term, seqVar, indexVar, out domain)) {
      return true;
    }
    if (TryGetOrEqualityDomain(term, seqVar, indexVar, out domain)) {
      return true;
    }
    if (TryGetIntRangeDomain(term, seqVar, indexVar, out domain)) {
      return true;
    }

    return false;
  }

  private static bool TryGetSeqLength(Expression expr, BoundVar seqVar, out bool matched) {
    matched = false;
    expr = NormalizeForPattern(expr);
    if (expr is not UnaryOpExpr unaryExpr) {
      return false;
    }
    if (unaryExpr.ResolvedOp != UnaryOpExpr.ResolvedOpcode.SeqLength) {
      return false;
    }
    matched = IsBoundVar(unaryExpr.E, seqVar);
    return true;
  }

  private static bool TryGetIntLiteralValue(Expression expr, out int value) {
    value = default;
    if (!Expression.IsIntLiteral(expr, out var literal)) {
      return false;
    }
    if (literal < 0 || literal > int.MaxValue) {
      return false;
    }
    value = (int)literal;
    return true;
  }

  private bool TryGetIndexRange(Expression rangeExpr, BoundVar indexVar, int length) {
    var conjuncts = new List<Expression>();
    CollectConjuncts(rangeExpr, conjuncts);
    var hasLower = indexVar.Type.AsSubsetType == systemModuleManager.NatDecl;
    var hasUpper = false;
    foreach (var conjunct in conjuncts) {
      var normalized = NormalizeForPattern(conjunct);
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

      if (IsBoundVar(binaryExpr.E0, indexVar) && Expression.IsIntLiteral(binaryExpr.E1, out var rightLiteral)) {
        if (isLt && rightLiteral == length) {
          hasUpper = true;
          continue;
        }
        if (isLe && rightLiteral == length - 1) {
          hasUpper = true;
          continue;
        }
        if ((isGe || isGt) && rightLiteral == 0) {
          hasLower = true;
          continue;
        }
        return false;
      }

      if (IsBoundVar(binaryExpr.E1, indexVar) && Expression.IsIntLiteral(binaryExpr.E0, out var leftLiteral)) {
        if (isLe && leftLiteral == length - 1) {
          hasUpper = true;
          continue;
        }
        if (isLt && leftLiteral == length) {
          hasUpper = true;
          continue;
        }
        if ((isLe || isLt) && leftLiteral == 0) {
          hasLower = true;
          continue;
        }
        return false;
      }
      return false;
    }

    return hasUpper && (hasLower || length == 0);
  }

  private static bool TryGetSetMembershipDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain) {
    domain = null!;
    if (term is not BinaryExpr binaryExpr) {
      return false;
    }
    var isInSet = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet;
    if (!isInSet) {
      return false;
    }
    if (!TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _) ||
        NormalizeForPattern(binaryExpr.E1) is not SetDisplayExpr setDisplay) {
      return false;
    }
    if (!setDisplay.Elements.All(IsLiteralExpression)) {
      return false;
    }
    domain = DeduplicateLiterals(setDisplay.Elements);
    return domain.Count > 0;
  }

  private static bool TryGetOrEqualityDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain) {
    domain = null!;
    var disjuncts = new List<Expression>();
    CollectDisjuncts(term, disjuncts);
    var elements = new List<Expression>();
    foreach (var disjunct in disjuncts) {
      var normalized = NormalizeForPattern(disjunct);
      if (normalized is not BinaryExpr binaryExpr) {
        return false;
      }
      var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
      if (!isEq) {
        return false;
      }
      if (TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _) && IsLiteralExpression(binaryExpr.E1)) {
        elements.Add(binaryExpr.E1);
        continue;
      }
      if (TryGetSeqSelect(binaryExpr.E1, seqVar, indexVar, out _) && IsLiteralExpression(binaryExpr.E0)) {
        elements.Add(binaryExpr.E0);
        continue;
      }
      return false;
    }

    domain = DeduplicateLiterals(elements);
    return domain.Count > 0;
  }

  private static bool TryGetIntRangeDomain(Expression term, BoundVar seqVar, BoundVar indexVar,
    out List<Expression> domain) {
    domain = null!;
    var seqType = seqVar.Type.NormalizeExpand().AsSeqType;
    if (seqType == null || !seqType.Arg.IsNumericBased(Type.NumericPersuasion.Int)) {
      return false;
    }
    var conjuncts = new List<Expression>();
    CollectConjuncts(term, conjuncts);
    BigInteger? lower = null;
    BigInteger? upper = null;
    foreach (var conjunct in conjuncts) {
      var normalized = NormalizeForPattern(conjunct);
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

      if (TryGetSeqSelect(binaryExpr.E0, seqVar, indexVar, out _) &&
          Expression.IsIntLiteral(binaryExpr.E1, out var rightLiteral)) {
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

      if (TryGetSeqSelect(binaryExpr.E1, seqVar, indexVar, out _) &&
          Expression.IsIntLiteral(binaryExpr.E0, out var leftLiteral)) {
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

      return false;
    }

    if (lower == null || upper == null || lower.Value >= upper.Value) {
      return false;
    }

    var elements = new List<Expression>();
    for (var value = lower.Value; value < upper.Value; value++) {
      elements.Add(new LiteralExpr(seqVar.Origin, value) { Type = seqType.Arg });
    }

    domain = DeduplicateLiterals(elements);
    return domain.Count > 0;
  }

  private static List<Expression> DeduplicateLiterals(List<Expression> elements) {
    var results = new List<Expression>();
    foreach (var element in elements) {
      var normalized = NormalizeForPattern(element);
      if (!results.Any(existing => LiteralStructuralEquals(existing, normalized))) {
        results.Add(normalized);
      }
    }
    return results;
  }

  private static bool TryGetSeqSelect(Expression expr, BoundVar seqVar, BoundVar indexVar, out SeqSelectExpr selectExpr) {
    selectExpr = null!;
    expr = NormalizeForPattern(expr);
    if (expr is not SeqSelectExpr seqSelect) {
      return false;
    }
    if (!IsBoundVar(seqSelect.Seq, seqVar)) {
      return false;
    }
    if (seqSelect.SelectOne && IsBoundVar(seqSelect.E0, indexVar)) {
      selectExpr = seqSelect;
      return true;
    }
    return false;
  }

  private bool TryGetConcreteIntDomainsFromPools(IReadOnlyList<BoundVar> boundVars, IReadOnlyList<BoundedPool?> bounds,
    out ConcreteDomain[] domains) {
    domains = Array.Empty<ConcreteDomain>();
    if (boundVars.Count != bounds.Count) {
      return false;
    }

    var boundVarIndices = new Dictionary<BoundVar, int>();
    var isNat = new bool[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      var bv = boundVars[i];
      if (!TryGetIntOrNatType(bv, out var isNatType)) {
        return false;
      }
      isNat[i] = isNatType;
      boundVarIndices[bv] = i;
    }

    var constraints = new List<IntBoundConstraint>();
    for (var i = 0; i < boundVars.Count; i++) {
      if (bounds[i] is not IntBoundedPool intPool) {
        return false;
      }
      if (intPool.LowerBound != null) {
        if (!TryGetVarPlusConstant(intPool.LowerBound, boundVarIndices, out var sourceIndex, out var offset)) {
          return false;
        }
        constraints.Add(new IntBoundConstraint(i, sourceIndex, offset, true));
      }
      if (intPool.UpperBound != null) {
        if (!TryGetVarPlusConstant(intPool.UpperBound, boundVarIndices, out var sourceIndex, out var offset)) {
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
      var bv = boundVars[i];
      if (!TryGetIntOrNatType(bv, out var isNatType)) {
        return false;
      }
      isNat[i] = isNatType;
      boundVarIndices[bv] = i;
    }

    var logicalBody = quantifierExpr.LogicalBody(bypassSplitQuantifier: true);
    Expression rangeExpr = logicalBody;
    if (quantifierExpr is ForallExpr && logicalBody is BinaryExpr impExpr && IsImplication(impExpr)) {
      rangeExpr = impExpr.E0;
    }

    var conjuncts = new List<Expression>();
    CollectConjuncts(rangeExpr, conjuncts);

    var constraints = new List<IntBoundConstraint>();
    foreach (var conjunct in conjuncts) {
      var resolved = NormalizeForPattern(conjunct);
      if (resolved is not BinaryExpr binaryExpr) {
        continue;
      }
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      if (!isLe && !isLt) {
        continue;
      }
      if (!TryGetVarPlusConstant(binaryExpr.E0, boundVarIndices, out var leftIndex, out var leftConst) ||
          !TryGetVarPlusConstant(binaryExpr.E1, boundVarIndices, out var rightIndex, out var rightConst)) {
        continue;
      }
      var isStrict = isLt;
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
      if (!boundVars[i].Type.NormalizeExpand().IsCharType) {
        return false;
      }
    }

    var logicalBody = quantifierExpr.LogicalBody(bypassSplitQuantifier: true);
    Expression rangeExpr = logicalBody;
    if (quantifierExpr is ForallExpr && logicalBody is BinaryExpr impExpr && IsImplication(impExpr)) {
      rangeExpr = impExpr.E0;
    }

    var charDomains = new ConcreteDomain[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
      if (!TryGetConcreteCharDomainFromRange(rangeExpr, boundVars[i], out var domain)) {
        return false;
      }
      charDomains[i] = domain;
    }

    domains = charDomains;
    return true;
  }

  private bool TryGetConcreteCharDomainFromRange(Expression rangeExpr, BoundVar boundVar, out ConcreteDomain domain) {
    domain = null!;
    if (rangeExpr == null) {
      return false;
    }

    var disjuncts = new List<Expression>();
    var normalizedRange = NormalizeForPattern(rangeExpr);
    if (normalizedRange is ChainingExpression chainingExpression) {
      normalizedRange = chainingExpression.E;
    }
    CollectDisjuncts(normalizedRange, disjuncts);
    var ranges = new List<(int Lower, int Upper)>();
    foreach (var disjunct in disjuncts) {
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
      for (var codePoint = lower; codePoint < upper; codePoint++) {
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
    var normalizedExpr = NormalizeForPattern(expr);
    if (normalizedExpr is ChainingExpression chainingExpression) {
      normalizedExpr = chainingExpression.E;
    }
    CollectConjuncts(normalizedExpr, conjuncts);
    foreach (var conjunct in conjuncts) {
      var normalized = NormalizeForPattern(conjunct);
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

    if (TryGetCharLiteral(binaryExpr.E0, out var leftLiteral) && IsBoundVarName(binaryExpr.E1, boundVar)) {
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

    if (TryGetCharLiteral(binaryExpr.E1, out var rightLiteral) && IsBoundVarName(binaryExpr.E0, boundVar)) {
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

  private static bool IsBoundVarName(Expression expr, BoundVar boundVar) {
    if (expr is IdentifierExpr identifierExpr) {
      return identifierExpr.Name == boundVar.Name;
    }
    return false;
  }

  private bool TryGetCharBoundOperand(Expression expr, BoundVar boundVar, out bool isVar, out int? literal) {
    isVar = false;
    literal = null;
    expr = NormalizeForPattern(expr);
    if (expr is ConversionExpr conversionExpr) {
      var fromType = conversionExpr.E.Type?.NormalizeExpand();
      var toType = conversionExpr.Type?.NormalizeExpand();
      if (fromType != null && toType is IntType && fromType.IsCharType) {
        expr = NormalizeForPattern(conversionExpr.E);
      }
    }
    if (expr is IdentifierExpr identifierExpr &&
        (identifierExpr.Var == boundVar || identifierExpr.Name == boundVar.Name)) {
      isVar = true;
      return true;
    }
    if (Expression.IsIntLiteral(expr, out var intLiteral)) {
      if (intLiteral >= 0 && intLiteral <= 0xFFFF) {
        literal = (int)intLiteral;
        return true;
      }
      return false;
    }
    if (TryGetCharLiteral(expr, out var value)) {
      literal = value;
      return true;
    }
    return false;
  }

  private static bool TryGetCharLiteral(Expression expr, out int value) {
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
        TryParseHex(literal.AsSpan(2), out var utf16Code)) {
      value = utf16Code;
      return true;
    }

    if (literal.StartsWith("\\U{", StringComparison.Ordinal) && literal.EndsWith("}", StringComparison.Ordinal)) {
      var hexSpan = literal.AsSpan(3, literal.Length - 4);
      if (TryParseHex(hexSpan, out var unicodeCode) && unicodeCode <= 0xFFFF) {
        value = unicodeCode;
        return true;
      }
    }

    return false;
  }

  private static bool TryParseHex(ReadOnlySpan<char> hexSpan, out int value) {
    value = 0;
    if (hexSpan.IsEmpty) {
      return false;
    }
    foreach (var digit in hexSpan) {
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
      if (isNat[i]) {
        lowerBounds[i] = BigInteger.Zero;
      }
    }

    var changed = true;
    var passes = 0;
    var maxPasses = boundVars.Count * boundVars.Count + 5;
    while (changed && passes < maxPasses) {
      changed = false;
      passes++;
      foreach (var constraint in constraints) {
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

    domains = new ConcreteDomain[boundVars.Count];
    for (var i = 0; i < boundVars.Count; i++) {
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
    out int? varIndex, out BigInteger constant) {
    expr = NormalizeForPattern(expr);
    if (Expression.IsIntLiteral(expr, out var literal)) {
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
      if (!TryGetVarPlusConstant(binaryExpr.E0, boundVarIndices, out var leftIndex, out var leftConst) ||
          !TryGetVarPlusConstant(binaryExpr.E1, boundVarIndices, out var rightIndex, out var rightConst)) {
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

  internal bool TryGetConcreteDomain(BoundVar bv, BoundedPool? bound, Func<Expression, Expression> simplify,
    out ConcreteDomain domain) {
    domain = null!;

    if (bound == null) {
      return false;
    }

    if (TryGetConcreteIntDomain(bv, bound, out var lower, out var upper)) {
      var size = upper - lower;
      domain = new ConcreteDomain(size, () => EnumerateIntRange(bv, lower, upper));
      return true;
    }

    if (bound is ExactBoundedPool exactBoundedPool) {
      var value = StripConcreteSyntax(exactBoundedPool.E);
      if (!IsLiteralExpression(value)) {
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
      var resolved = StripConcreteSyntax(seqPool.Seq);
      if (resolved is SeqDisplayExpr seqDisplay) {
        var elements = new List<Expression>();
        foreach (var element in seqDisplay.Elements) {
          var value = StripConcreteSyntax(element);
          if (!IsLiteralExpression(value)) {
            return false;
          }
          if (!ContainsLiteral(elements, value)) {
            elements.Add(value);
            if (maxInstances > 0 && elements.Count > maxInstances) {
              return false;
            }
          }
        }
        var size = new BigInteger(elements.Count);
        domain = new ConcreteDomain(size, () => EnumerateSetElements(elements, bv.Type));
        return true;
      }
    }

    if (bound is MultiSetBoundedPool multisetPool) {
      var resolved = StripConcreteSyntax(multisetPool.MultiSet);
      if (resolved is MultiSetDisplayExpr multisetDisplay) {
        var elements = new List<Expression>();
        foreach (var element in multisetDisplay.Elements) {
          var value = StripConcreteSyntax(element);
          if (!IsLiteralExpression(value)) {
            return false;
          }
          if (!ContainsLiteral(elements, value)) {
            elements.Add(value);
            if (maxInstances > 0 && elements.Count > maxInstances) {
              return false;
            }
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
      var resolved = StripConcreteSyntax(mapPool.Map);
      if (resolved is MapDisplayExpr mapDisplay) {
        if (!mapDisplay.Finite) {
          return false;
        }
        var keys = new List<Expression>();
        foreach (var entry in mapDisplay.Elements) {
          var key = StripConcreteSyntax(entry.A);
          var value = StripConcreteSyntax(entry.B);
          if (!IsLiteralExpression(key) || !IsLiteralExpression(value)) {
            return false;
          }
          if (!ContainsLiteral(keys, key)) {
            keys.Add(key);
            if (maxInstances > 0 && keys.Count > maxInstances) {
              return false;
            }
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
        var maxElements = MaxSubsetElementCount(maxInstances);
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

    return false;
  }

  private bool TryMaterializeMapComprehensionKeys(MapComprehension mapComprehension, Func<Expression, Expression> simplify,
    out List<Expression> keys) {
    keys = null!;
    var bounds = mapComprehension.Bounds;
    if (bounds == null || bounds.Count != mapComprehension.BoundVars.Count) {
      if (mapComprehension.Range == null) {
        return false;
      }
      bounds = ModuleResolver.DiscoverBestBounds_MultipleVars(mapComprehension.BoundVars, mapComprehension.Range, true);
    }
    if (bounds == null || bounds.Count != mapComprehension.BoundVars.Count) {
      return false;
    }

    var domains = new ConcreteDomain[mapComprehension.BoundVars.Count];
    for (var i = 0; i < mapComprehension.BoundVars.Count; i++) {
      var boundVar = mapComprehension.BoundVars[i];
      var boundPool = bounds[i];
      if (!TryGetConcreteDomain(boundVar, boundPool, simplify, out var concreteDomain)) {
        return false;
      }
      domains[i] = concreteDomain;
    }

    if (maxInstances > 0) {
      var product = BigInteger.One;
      foreach (var concreteDomain in domains) {
        product *= concreteDomain.Size;
        if (product > maxInstances) {
          return false;
        }
      }
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
    var substMap = new Dictionary<IVariable, Expression>();
    var typeMap = new Dictionary<TypeParameter, Type>();
    var range = mapComprehension.Range;

    bool Enumerate(int varIndex) {
      if (varIndex == domains.Length) {
        var substituter = new Substituter(null, substMap, typeMap);
        if (range != null) {
          var rangeInst = simplify(substituter.Substitute(range));
          rangeInst = StripConcreteSyntax(rangeInst);
          if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
            return false;
          }
          if (!rangeValue) {
            return true;
          }
        }

        var keyInst = simplify(substituter.Substitute(keyTemplate));
        keyInst = StripConcreteSyntax(keyInst);
        if (!IsLiteralExpression(keyInst)) {
          return false;
        }
        if (!ContainsLiteral(resultKeys, keyInst)) {
          resultKeys.Add(keyInst);
          if (maxInstances > 0 && resultKeys.Count > maxInstances) {
            return false;
          }
        }
        return true;
      }

      var boundVar = mapComprehension.BoundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        EnsureExpressionType(value, boundVar.Type);
        substMap[boundVar] = value;
        if (!Enumerate(varIndex + 1)) {
          return false;
        }
      }
      return true;
    }

    if (!Enumerate(0)) {
      return false;
    }

    keys = resultKeys;
    return true;
  }

  private IEnumerable<Expression> EnumerateIntRange(BoundVar bv, BigInteger lower, BigInteger upper) {
    for (var v = lower; v < upper; v++) {
      yield return new LiteralExpr(bv.Origin, v) { Type = bv.Type };
    }
  }

  private static IEnumerable<Expression> EnumerateSetElements(List<Expression> elements, Type elementType) {
    foreach (var element in elements) {
      EnsureExpressionType(element, elementType);
      yield return element;
    }
  }

  private static IEnumerable<Expression> EnumerateSubsets(IOrigin origin, List<Expression> elements, SetType setType) {
    var current = new List<Expression>();
    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, 0, current)) {
      yield return subset;
    }
  }

  private static IEnumerable<Expression> EnumerateSubsetsRecursive(IOrigin origin, List<Expression> elements, SetType setType, int index, List<Expression> current) {
    if (index == elements.Count) {
      var subsetElements = new List<Expression>(current);
      foreach (var element in subsetElements) {
        EnsureExpressionType(element, setType.Arg);
      }
      var subsetExpr = new SetDisplayExpr(origin, setType.Finite, subsetElements) { Type = setType };
      yield return subsetExpr;
      yield break;
    }

    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, index + 1, current)) {
      yield return subset;
    }

    current.Add(elements[index]);
    foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, index + 1, current)) {
      yield return subset;
    }
    current.RemoveAt(current.Count - 1);
  }

  private bool TryGetSetElementUpperBound(Expression setExpr, Func<Expression, Expression> simplify, out BigInteger upperBound) {
    upperBound = default;
    var resolved = StripConcreteSyntax(setExpr);

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

  private static BigInteger MaxSubsetElementCount(uint maxInstances) {
    if (maxInstances == 0) {
      return BigInteger.Zero;
    }
    var value = maxInstances;
    var count = 0;
    while (value > 1) {
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
      upperBound = StripConcreteSyntax(upperBound);
    }

    if (upperBound == null || !Expression.IsIntLiteral(upperBound, out upper)) {
      return false;
    }

    Expression lowerBound = intPool.LowerBound;
    if (lowerBound != null) {
      lowerBound = StripConcreteSyntax(lowerBound);
    }

    if (lowerBound == null) {
      if (!isNat) {
        return false;
      }
      lower = BigInteger.Zero;
    } else if (!Expression.IsIntLiteral(lowerBound, out lower)) {
      return false;
    }

    if (isNat && lower < 0) {
      return false;
    }

    return true;
  }

  private static List<BoundedPool?>? TryGetBoundsOrDiscover(
    List<BoundVar> boundVars,
    List<BoundedPool?>? existingBounds,
    Func<Expression?> getExpressionForDiscovery,
    bool polarity) {
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

