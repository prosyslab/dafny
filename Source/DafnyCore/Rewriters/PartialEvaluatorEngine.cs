using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

namespace Microsoft.Dafny;

internal sealed partial class PartialEvaluatorEngine {
  private const uint DefaultPartialEvalUnrollCap = 100;
  private readonly DafnyOptions options;
  private readonly ModuleDefinition module;
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint inlineDepth;
  private readonly Dictionary<string, CachedLiteral> inlineCallCache = new(StringComparer.Ordinal);
  private UnrollBoundedQuantifiersRewriter.UnrollEngine boundedQuantifierUnroller;

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth) {
    this.options = options;
    this.module = module;
    this.systemModuleManager = systemModuleManager;
    this.inlineDepth = inlineDepth;
  }

  public void PartialEvalEntry(ICallable callable) {
    var state = new PartialEvalState((int)inlineDepth, new HashSet<Function>(), new HashSet<string>(StringComparer.Ordinal));
    var visitor = new PartialEvaluatorVisitor(this);
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
    var state = new PartialEvalState((int)inlineDepth, new HashSet<Function>(), new HashSet<string>(StringComparer.Ordinal));
    var visitor = new PartialEvaluatorVisitor(this);
    return visitor.SimplifyExpression(expr, state);
  }

  private uint GetPartialEvalUnrollCap() {
    return options.Options.OptionArguments.ContainsKey(CommonOptionBag.UnrollBoundedQuantifiers)
      ? options.Get(CommonOptionBag.UnrollBoundedQuantifiers)
      : DefaultPartialEvalUnrollCap;
  }

  private UnrollBoundedQuantifiersRewriter.UnrollEngine GetQuantifierUnroller() {
    if (boundedQuantifierUnroller != null) {
      return boundedQuantifierUnroller;
    }
    var maxInstances = GetPartialEvalUnrollCap();
    boundedQuantifierUnroller = new UnrollBoundedQuantifiersRewriter.UnrollEngine(systemModuleManager, maxInstances, this);
    return boundedQuantifierUnroller;
  }

  internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, out Expression rewritten) {
    return GetQuantifierUnroller().TryUnrollQuantifier(quantifierExpr, out rewritten);
  }

  internal bool TryMaterializeSetComprehension(SetComprehension setComprehension, out SetDisplayExpr displayExpr) {
    displayExpr = null;
    if (!setComprehension.Finite) {
      return false;
    }
    var unroller = GetQuantifierUnroller();
    if (!unroller.TryMaterializeSetComprehension(setComprehension, out var elements)) {
      return false;
    }
    displayExpr = new SetDisplayExpr(setComprehension.Origin, true, elements) { Type = setComprehension.Type };
    return true;
  }

  private bool TryMaterializeMapComprehension(
    MapComprehension mapComprehension,
    PartialEvalState state,
    Func<Expression, PartialEvalState, Expression> simplifyExpression,
    out MapDisplayExpr mapDisplayExpr) {
    mapDisplayExpr = null;
    if (!mapComprehension.Finite) {
      return false;
    }
    if (mapComprehension.Bounds == null || mapComprehension.Bounds.Count != mapComprehension.BoundVars.Count) {
      return false;
    }

    var unroller = GetQuantifierUnroller();
    var domains = new UnrollBoundedQuantifiersRewriter.UnrollEngine.ConcreteDomain[mapComprehension.BoundVars.Count];
    for (var i = 0; i < mapComprehension.BoundVars.Count; i++) {
      var bv = mapComprehension.BoundVars[i];
      var bound = mapComprehension.Bounds[i];
      if (!unroller.TryGetConcreteDomain(bv, bound, out var domain)) {
        return false;
      }
      domains[i] = domain;
    }

    var cap = unroller.MaxInstances;
    if (cap > 0) {
      var size = BigInteger.One;
      foreach (var domain in domains) {
        size *= domain.Size;
        if (size > cap) {
          return false;
        }
      }
    }

    var entries = new List<MapDisplayEntry>();
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
        if (cap > 0 && entries.Count >= cap) {
          return false;
        }
        var substituter = new Substituter(null, substMap, typeMap);
        if (mapComprehension.Range != null) {
          var rangeInst = simplifyExpression(substituter.Substitute(mapComprehension.Range), state);
          rangeInst = ExpressionRewriteUtil.StripConcreteSyntax(rangeInst);
          if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
            return false;
          }
          if (!rangeValue) {
            return true;
          }
        }

        var keyExpr = simplifyExpression(substituter.Substitute(keyTemplate), state);
        keyExpr = ExpressionRewriteUtil.StripConcreteSyntax(keyExpr);
        if (!IsLiteralLike(keyExpr)) {
          return false;
        }

        var valueExpr = simplifyExpression(substituter.Substitute(mapComprehension.Term), state);
        valueExpr = ExpressionRewriteUtil.StripConcreteSyntax(valueExpr);

        for (var i = 0; i < entries.Count; i++) {
          if (AreLiteralExpressionsEqual(entries[i].A, keyExpr)) {
            if (!AreLiteralExpressionsEqual(entries[i].B, valueExpr)) {
              return false;
            }
            return true;
          }
        }

        entries.Add(new MapDisplayEntry(keyExpr, valueExpr));
        return true;
      }

      var bv = mapComprehension.BoundVars[varIndex];
      foreach (var value in domains[varIndex].Enumerate()) {
        if (cap > 0 && entries.Count >= cap) {
          return false;
        }
        ExpressionRewriteUtil.EnsureExpressionType(value, bv.Type);
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

    mapDisplayExpr = new MapDisplayExpr(mapComprehension.Origin, true, entries) { Type = mapComprehension.Type };
    return true;
  }

  private static void AssertHasResolvedType(Expression expr) {
    if (expr == null) {
      return;
    }
    Contract.Assert(expr.Type != null, "PartialEvaluator produced an expression with null Type");
  }

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
        return SimplifyIntBinary(binary, (a, b) => b == 0 ? null : a / b);
      case BinaryExpr.ResolvedOpcode.Mod:
        return SimplifyIntBinary(binary, (a, b) => b == 0 ? null : a % b);
      case BinaryExpr.ResolvedOpcode.Lt:
        return SimplifyIntComparison(binary, (a, b) => a < b);
      case BinaryExpr.ResolvedOpcode.Le:
        return SimplifyIntComparison(binary, (a, b) => a <= b);
      case BinaryExpr.ResolvedOpcode.Gt:
        return SimplifyIntComparison(binary, (a, b) => a > b);
      case BinaryExpr.ResolvedOpcode.Ge:
        return SimplifyIntComparison(binary, (a, b) => a >= b);
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
      default:
        return binary;
    }
  }

  private static Expression CreateBoolLiteral(IOrigin origin, bool value) {
    var literal = Expression.CreateBoolLiteral(origin, value);
    literal.Type = Type.Bool;
    return literal;
  }

  private static Expression SimplifyBooleanBinary(BinaryExpr binary) {
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
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      return CreateIntLiteral(binary.Origin, op(left, right));
    }

    if (Expression.IsIntLiteral(binary.E0, out left) && left == identity && opcode == BinaryExpr.ResolvedOpcode.Add) {
      return binary.E1;
    }

    if (Expression.IsIntLiteral(binary.E1, out right) && right == identity &&
        opcode is BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub) {
      return binary.E0;
    }

    if (opcode == BinaryExpr.ResolvedOpcode.Mul) {
      if (Expression.IsIntLiteral(binary.E0, out left)) {
        if (left == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (left == 1) {
          return binary.E1;
        }
      }
      if (Expression.IsIntLiteral(binary.E1, out right)) {
        if (right == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (right == 1) {
          return binary.E0;
        }
      }
    }

    return binary;
  }

  private Expression SimplifyIntBinary(BinaryExpr binary, Func<BigInteger, BigInteger, BigInteger?> op) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      var result = op(left, right);
      if (result != null) {
        return CreateIntLiteral(binary.Origin, result.Value);
      }
    }
    return binary;
  }

  private Expression SimplifyIntComparison(BinaryExpr binary, Func<BigInteger, BigInteger, bool> op) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      return Expression.CreateBoolLiteral(binary.Origin, op(left, right));
    }
    return binary;
  }

  private static Expression SimplifyEquality(BinaryExpr binary, bool isEq) {
    if (Expression.IsBoolLiteral(binary.E0, out var leftBool) && Expression.IsBoolLiteral(binary.E1, out var rightBool)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftBool == rightBool : leftBool != rightBool);
    }
    if (Expression.IsIntLiteral(binary.E0, out var leftInt) && Expression.IsIntLiteral(binary.E1, out var rightInt)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftInt == rightInt : leftInt != rightInt);
    }
    if (TryGetCharLiteral(binary.E0, out var leftChar) && TryGetCharLiteral(binary.E1, out var rightChar)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftChar == rightChar : leftChar != rightChar);
    }
    if (TryGetTupleLiteral(binary.E0, out var leftTuple) &&
        TryGetTupleLiteral(binary.E1, out var rightTuple) &&
        AllElementsAreLiterals(leftTuple.Arguments) &&
        AllElementsAreLiterals(rightTuple.Arguments)) {
      var equal = TupleLiteralsEqual(leftTuple, rightTuple);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private static Expression SimplifySeqConcat(BinaryExpr binary) {
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
        AllElementsAreLiterals(leftSeq) && AllElementsAreLiterals(rightSeq)) {
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
    if (TryGetStringLiteral(binary.E0, out var leftString, out _) && TryGetStringLiteral(binary.E1, out var rightString, out _)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftString == rightString : leftString != rightString);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq) && AllElementsAreLiterals(rightSeq)) {
      var equal = SeqDisplayLiteralsEqual(leftSeq, rightSeq);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    if (TryGetCharSeqDisplayLiteral(binary.E0, out var leftChars) && TryGetUnescapedStringCharacters(binary.E1, out var rightChars) ||
        TryGetUnescapedStringCharacters(binary.E0, out leftChars) && TryGetCharSeqDisplayLiteral(binary.E1, out rightChars)) {
      var equal = CodePointSequencesEqual(leftChars, rightChars);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    return binary;
  }

  private static Expression SimplifySeqPrefix(BinaryExpr binary, bool properPrefix) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out _) && TryGetStringLiteral(binary.E1, out var rightString, out _)) {
      var isPrefix = rightString.StartsWith(leftString, StringComparison.Ordinal);
      var isProper = isPrefix && leftString.Length < rightString.Length;
      return CreateBoolLiteral(binary.Origin, properPrefix ? isProper : isPrefix);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq) && AllElementsAreLiterals(rightSeq)) {
      var isPrefix = SeqDisplayIsPrefix(leftSeq, rightSeq, out var isProper);
      return CreateBoolLiteral(binary.Origin, properPrefix ? isProper : isPrefix);
    }

    return binary;
  }

  private static Expression SimplifySetEquality(BinaryExpr binary, bool isEq) {
    if (TryGetSetDisplayLiteral(binary.E0, out var leftSet) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightSet) &&
        AllElementsAreLiterals(leftSet.Elements) &&
        AllElementsAreLiterals(rightSet.Elements)) {
      var equal = SetDisplayLiteralsEqual(leftSet, rightSet);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private static Expression SimplifySetMembership(BinaryExpr binary, bool isIn) {
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (TryGetSetDisplayLiteral(binary.E1, out var setDisplay) &&
        AllElementsAreLiterals(setDisplay.Elements) &&
        IsLiteralLike(binary.E0)) {
      var contains = ContainsLiteralElement(setDisplay.Elements, binary.E0);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private static Expression SimplifySetSubset(BinaryExpr binary, Expression left, Expression right, bool proper) {
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
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplayLiteral.Elements)) {
      var leftDistinct = DistinctLiteralElements(leftDisplay.Elements);
      var rightDistinct = DistinctLiteralElements(rightDisplayLiteral.Elements);
      var isSubset = leftDistinct.All(element => ContainsLiteralElement(rightDistinct, element));
      var isProper = isSubset && leftDistinct.Count < rightDistinct.Count;
      return CreateBoolLiteral(binary.Origin, proper ? isProper : isSubset);
    }
    return binary;
  }

  private static Expression SimplifySetDisjoint(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0) || LiteralExpr.IsEmptySet(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, true);
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftDistinct = DistinctLiteralElements(leftDisplay.Elements);
      var rightDistinct = DistinctLiteralElements(rightDisplay.Elements);
      var disjoint = leftDistinct.All(element => !ContainsLiteralElement(rightDistinct, element));
      return CreateBoolLiteral(binary.Origin, disjoint);
    }
    return binary;
  }

  private static Expression SimplifySetUnion(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0)) {
      return binary.E1;
    }
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var merged = DistinctLiteralElements(leftDisplay.Elements);
      foreach (var element in rightDisplay.Elements) {
        if (!ContainsLiteralElement(merged, element)) {
          merged.Add(element);
        }
      }
      return CreateSetDisplayLiteral(binary.Origin, merged, binary.Type);
    }
    return binary;
  }

  private static Expression SimplifySetIntersection(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0)) {
      return binary.E0;
    }
    if (LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E1;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftDistinct = DistinctLiteralElements(leftDisplay.Elements);
      var rightDistinct = DistinctLiteralElements(rightDisplay.Elements);
      var intersection = new List<Expression>();
      foreach (var element in leftDistinct) {
        if (ContainsLiteralElement(rightDistinct, element)) {
          intersection.Add(element);
        }
      }
      return CreateSetDisplayLiteral(binary.Origin, intersection, binary.Type);
    }
    return binary;
  }

  private static Expression SimplifySetDifference(BinaryExpr binary) {
    if (LiteralExpr.IsEmptySet(binary.E0) || LiteralExpr.IsEmptySet(binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftDistinct = DistinctLiteralElements(leftDisplay.Elements);
      var rightDistinct = DistinctLiteralElements(rightDisplay.Elements);
      var difference = leftDistinct.Where(element => !ContainsLiteralElement(rightDistinct, element)).ToList();
      return CreateSetDisplayLiteral(binary.Origin, difference, binary.Type);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetEquality(BinaryExpr binary, bool isEq) {
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var equal = MultiSetDisplayLiteralsEqual(leftDisplay, rightDisplay);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetMembership(BinaryExpr binary, bool isIn) {
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (TryGetMultiSetDisplayLiteral(binary.E1, out var multiSetDisplay) &&
        AllElementsAreLiterals(multiSetDisplay.Elements) &&
        IsLiteralLike(binary.E0)) {
      var counts = BuildMultisetCounts(multiSetDisplay.Elements);
      var contains = counts.Any(entry => AreLiteralExpressionsEqual(entry.Element, binary.E0) && entry.Count > 0);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private static Expression SimplifySeqMembership(BinaryExpr binary, bool isIn) {
    if (TryGetSeqDisplayLiteral(binary.E1, out var seqDisplay) &&
        AllElementsAreLiterals(seqDisplay.Elements) &&
        IsLiteralLike(binary.E0)) {
      var contains = ContainsLiteralElement(seqDisplay.Elements, binary.E0);
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetSubset(BinaryExpr binary, Expression left, Expression right, bool proper) {
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
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplayLiteral.Elements)) {
      var leftCounts = BuildMultisetCounts(leftDisplay.Elements);
      var rightCounts = BuildMultisetCounts(rightDisplayLiteral.Elements);
      var isSubset = leftCounts.All(entry => {
        var match = rightCounts.FirstOrDefault(candidate => AreLiteralExpressionsEqual(candidate.Element, entry.Element));
        return match != null && entry.Count <= match.Count;
      });
      var isProper = isSubset && leftCounts.Sum(entry => entry.Count) < rightCounts.Sum(entry => entry.Count);
      return CreateBoolLiteral(binary.Origin, proper ? isProper : isSubset);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetDisjoint(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0) || LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return CreateBoolLiteral(binary.Origin, true);
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftCounts = BuildMultisetCounts(leftDisplay.Elements);
      var rightCounts = BuildMultisetCounts(rightDisplay.Elements);
      var disjoint = leftCounts.All(entry => rightCounts.All(candidate => !AreLiteralExpressionsEqual(candidate.Element, entry.Element)));
      return CreateBoolLiteral(binary.Origin, disjoint);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetUnion(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0)) {
      return binary.E1;
    }
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E0;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var combined = BuildMultisetCounts(leftDisplay.Elements);
      foreach (var entry in BuildMultisetCounts(rightDisplay.Elements)) {
        var target = combined.FirstOrDefault(candidate => AreLiteralExpressionsEqual(candidate.Element, entry.Element));
        if (target == null) {
          combined.Add(new MultisetElementCount(entry.Element) { Count = entry.Count });
        } else {
          target.Count += entry.Count;
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCounts(combined), binary.Type);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetIntersection(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0)) {
      return binary.E0;
    }
    if (LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E1;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftCounts = BuildMultisetCounts(leftDisplay.Elements);
      var rightCounts = BuildMultisetCounts(rightDisplay.Elements);
      var intersection = new List<MultisetElementCount>();
      foreach (var entry in leftCounts) {
        var match = rightCounts.FirstOrDefault(candidate => AreLiteralExpressionsEqual(candidate.Element, entry.Element));
        if (match != null) {
          var count = Math.Min(entry.Count, match.Count);
          if (count > 0) {
            intersection.Add(new MultisetElementCount(entry.Element) { Count = count });
          }
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCounts(intersection), binary.Type);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetDifference(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0) || LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E0;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftCounts = BuildMultisetCounts(leftDisplay.Elements);
      var rightCounts = BuildMultisetCounts(rightDisplay.Elements);
      var difference = new List<MultisetElementCount>();
      foreach (var entry in leftCounts) {
        var match = rightCounts.FirstOrDefault(candidate => AreLiteralExpressionsEqual(candidate.Element, entry.Element));
        var count = entry.Count - (match?.Count ?? 0);
        if (count > 0) {
          difference.Add(new MultisetElementCount(entry.Element) { Count = count });
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCounts(difference), binary.Type);
    }
    return binary;
  }

  private static List<Expression> ExpandMultisetCounts(IEnumerable<MultisetElementCount> counts) {
    var elements = new List<Expression>();
    foreach (var entry in counts) {
      for (var i = 0; i < entry.Count; i++) {
        elements.Add(entry.Element);
      }
    }
    return elements;
  }

  private bool TryInlineCall(FunctionCallExpr callExpr, PartialEvalState state, PartialEvaluatorVisitor visitor, out Expression inlined) {
    inlined = null;
    var function = callExpr.Function;
    if (function == null || function.Body == null || state.Depth <= 0) {
      return false;
    }

    if (BoogieGenerator.IsOpaque(function, options) || !function.IsRevealedInScope(module.VisibilityScope)) {
      return false;
    }

    if (function.Reads.Expressions != null && function.Reads.Expressions.Count > 0) {
      return false;
    }

    var allLiteralArgs = true;
    for (var i = 0; i < callExpr.Args.Count; i++) {
      if (!IsInlineableArgument(callExpr.Args[i])) {
        allLiteralArgs = false;
        break;
      }
    }
    if (!allLiteralArgs) {
      return false;
    }

    if (TryGetCachedInlinedLiteral(callExpr, state, out inlined)) {
      return true;
    }

    var callKey = BuildInlineCallCycleKey(callExpr);
    if (!state.InlineCallStack.Add(callKey)) {
      return false;
    }
    var addedFunction = state.InlineStack.Add(function);

    try {
      var substMap = new Dictionary<IVariable, Expression>(function.Ins.Count);
      for (var i = 0; i < function.Ins.Count; i++) {
        substMap[function.Ins[i]] = callExpr.Args[i];
      }

      Expression receiverReplacement = function.IsStatic ? null : callExpr.Receiver;
      var typeMap = callExpr.GetTypeArgumentSubstitutions();
      var substituter = new Substituter(receiverReplacement, substMap, typeMap, null, systemModuleManager);
      var body = substituter.Substitute(function.Body);
      inlined = visitor.SimplifyExpression(body, state.WithDepth(state.Depth - 1));
      var postVisitor = new PartialEvaluatorVisitor(this);
      inlined = postVisitor.SimplifyExpression(inlined, state.WithDepth(0));

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

  private bool TryGetCachedInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, out Expression inlined) {
    inlined = null;
    var function = callExpr.Function;
    if (function == null || !function.IsStatic) {
      return false;
    }

    if (!TryBuildInlineCallCacheKey(callExpr, state, out var key)) {
      return false;
    }

    if (!inlineCallCache.TryGetValue(key, out var cached)) {
      return false;
    }

    inlined = cached.CreateLiteral(callExpr.Origin);
    return true;
  }

  private void CacheInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, LiteralExpr literal) {
    var function = callExpr.Function;
    if (function == null || !function.IsStatic) {
      return;
    }

    if (!TryBuildInlineCallCacheKey(callExpr, state, out var key)) {
      return;
    }

    if (CachedLiteral.TryCreate(literal, out var cached)) {
      inlineCallCache.TryAdd(key, cached);
    }
  }

  private static bool TryBuildInlineCallCacheKey(FunctionCallExpr callExpr, PartialEvalState state, out string key) {
    key = null;

    var function = callExpr.Function;
    if (function == null) {
      return false;
    }

    foreach (var arg in callExpr.Args) {
      if (!Expression.IsIntLiteral(arg, out _) && !Expression.IsBoolLiteral(arg, out _)) {
        return false;
      }
    }

    var stackKey = BuildInlineStackKey(state.InlineStack, function);
    var callKey = callExpr.ToString();

    key = $"{RuntimeHelpers.GetHashCode(function)}|d={state.Depth}|s={stackKey}|c={callKey}";
    return true;
  }

  private static string BuildInlineStackKey(HashSet<Function> inlineStack, Function functionToExclude) {
    if (inlineStack == null || inlineStack.Count == 0) {
      return "";
    }

    List<int> ids = null;
    foreach (var f in inlineStack) {
      if (ReferenceEquals(f, functionToExclude)) {
        continue;
      }
      ids ??= new List<int>();
      ids.Add(RuntimeHelpers.GetHashCode(f));
    }

    if (ids == null || ids.Count == 0) {
      return "";
    }

    ids.Sort();
    return string.Join(",", ids);
  }

  private static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value) {
    return new LiteralExpr(origin, value) { Type = Type.Int };
  }

  private static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value, Type type) {
    return new LiteralExpr(origin, value) { Type = type };
  }

  private static LiteralExpr CreateCharLiteral(IOrigin origin, char value, Type type) {
    return new CharLiteralExpr(origin, value.ToString()) { Type = type };
  }

  private static LiteralExpr CreateCharLiteral(IOrigin origin, string value, Type type) {
    return new CharLiteralExpr(origin, value) { Type = type };
  }

  private static LiteralExpr CreateStringLiteral(IOrigin origin, string value, Type type, bool isVerbatim) {
    return new StringLiteralExpr(origin, value, isVerbatim) { Type = type };
  }

  private static SeqDisplayExpr CreateSeqDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    return new SeqDisplayExpr(origin, elements) { Type = type };
  }

  private static SetDisplayExpr CreateSetDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    var setType = type.NormalizeExpand().AsSetType;
    return new SetDisplayExpr(origin, setType.Finite, elements) { Type = type };
  }

  private static MultiSetDisplayExpr CreateMultiSetDisplayLiteral(IOrigin origin, List<Expression> elements, Type type) {
    return new MultiSetDisplayExpr(origin, elements) { Type = type };
  }

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

  private static bool TryGetCharLiteral(Expression expr, out char value) {
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
      value = (char)utf16Code;
      return true;
    }

    if (literal.StartsWith("\\U{", StringComparison.Ordinal) && literal.EndsWith("}", StringComparison.Ordinal)) {
      var hexSpan = literal.AsSpan(3, literal.Length - 4);
      if (TryParseHex(hexSpan, out var unicodeCode) && unicodeCode <= 0xFFFF) {
        value = (char)unicodeCode;
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

    foreach (var ch in hexSpan) {
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

  private static bool TryGetCharSeqDisplayLiteral(Expression expr, out List<int> codePoints) {
    codePoints = null;
    if (!TryGetSeqDisplayLiteral(expr, out var display)) {
      return false;
    }

    var result = new List<int>(display.Elements.Count);
    foreach (var element in display.Elements) {
      if (!TryGetCharLiteral(element, out var ch)) {
        return false;
      }
      result.Add(ch);
    }

    codePoints = result;
    return true;
  }

  private bool TryGetUnescapedStringCharacters(Expression expr, out List<int> codePoints) {
    codePoints = null;
    if (!TryGetStringLiteral(expr, out var value, out var isVerbatim)) {
      return false;
    }

    codePoints = Util.UnescapedCharacters(options, value, isVerbatim).ToList();
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

  private static bool AllElementsAreLiterals(SeqDisplayExpr display) {
    return AllElementsAreLiterals(display.Elements);
  }

  private static bool TryGetSetDisplayLiteral(Expression expr, out SetDisplayExpr display) {
    display = expr as SetDisplayExpr;
    return display != null;
  }

  private static bool TryGetMultiSetDisplayLiteral(Expression expr, out MultiSetDisplayExpr display) {
    display = expr as MultiSetDisplayExpr;
    return display != null;
  }

  private static bool AllElementsAreLiterals(IEnumerable<Expression> elements) {
    return elements.All(IsLiteralLike);
  }

  private static bool AllElementsAreLiterals(MapDisplayExpr display) {
    return display.Elements.All(entry => IsLiteralLike(entry.A) && IsLiteralLike(entry.B));
  }

  private static bool IsLiteralLike(Expression expr) {
    if (expr is LiteralExpr) {
      return true;
    }
    if (expr is SeqDisplayExpr seqDisplay) {
      return AllElementsAreLiterals(seqDisplay.Elements);
    }
    if (expr is SetDisplayExpr setDisplay) {
      return AllElementsAreLiterals(setDisplay.Elements);
    }
    if (expr is MultiSetDisplayExpr multiSetDisplay) {
      return AllElementsAreLiterals(multiSetDisplay.Elements);
    }
    if (expr is MapDisplayExpr mapDisplay) {
      return AllElementsAreLiterals(mapDisplay);
    }
    if (TryGetTupleLiteral(expr, out var tuple)) {
      return AllElementsAreLiterals(tuple.Arguments);
    }
    return false;
  }

  private static bool IsInlineableArgument(Expression expr) {
    return IsLiteralLike(expr) || expr is LambdaExpr;
  }

  private static bool AreLiteralExpressionsEqual(Expression left, Expression right) {
    if (TryGetCharLiteral(left, out var leftChar) && TryGetCharLiteral(right, out var rightChar)) {
      return leftChar == rightChar;
    }
    if (left is LiteralExpr leftLiteral && right is LiteralExpr rightLiteral) {
      return Equals(leftLiteral.Value, rightLiteral.Value);
    }
    if (left is SeqDisplayExpr leftSeq && right is SeqDisplayExpr rightSeq) {
      return SeqDisplayLiteralsEqual(leftSeq, rightSeq);
    }
    if (left is SetDisplayExpr leftSet && right is SetDisplayExpr rightSet) {
      return SetDisplayLiteralsEqual(leftSet, rightSet);
    }
    if (left is MultiSetDisplayExpr leftMulti && right is MultiSetDisplayExpr rightMulti) {
      return MultiSetDisplayLiteralsEqual(leftMulti, rightMulti);
    }
    if (TryGetTupleLiteral(left, out var leftTuple) && TryGetTupleLiteral(right, out var rightTuple)) {
      return TupleLiteralsEqual(leftTuple, rightTuple);
    }
    return false;
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

  private static bool SeqDisplayLiteralsEqual(SeqDisplayExpr left, SeqDisplayExpr right) {
    if (left.Elements.Count != right.Elements.Count) {
      return false;
    }
    for (var i = 0; i < left.Elements.Count; i++) {
      if (!AreLiteralExpressionsEqual(left.Elements[i], right.Elements[i])) {
        return false;
      }
    }
    return true;
  }

  private static bool CodePointSequencesEqual(IReadOnlyList<int> left, IReadOnlyList<int> right) {
    if (left.Count != right.Count) {
      return false;
    }
    for (var index = 0; index < left.Count; index++) {
      if (left[index] != right[index]) {
        return false;
      }
    }
    return true;
  }

  private static bool TupleLiteralsEqual(DatatypeValue left, DatatypeValue right) {
    if (left.Arguments.Count != right.Arguments.Count) {
      return false;
    }
    for (var i = 0; i < left.Arguments.Count; i++) {
      if (!AreLiteralExpressionsEqual(left.Arguments[i], right.Arguments[i])) {
        return false;
      }
    }
    return true;
  }

  private static bool SetDisplayLiteralsEqual(SetDisplayExpr left, SetDisplayExpr right) {
    if (left.Elements.Count == 0 && right.Elements.Count == 0) {
      return true;
    }
    if (!AllElementsAreLiterals(left.Elements) || !AllElementsAreLiterals(right.Elements)) {
      return false;
    }
    var leftDistinct = DistinctLiteralElements(left.Elements);
    var rightDistinct = DistinctLiteralElements(right.Elements);
    if (leftDistinct.Count != rightDistinct.Count) {
      return false;
    }
    foreach (var element in leftDistinct) {
      if (!ContainsLiteralElement(rightDistinct, element)) {
        return false;
      }
    }
    return true;
  }

  private static bool MultiSetDisplayLiteralsEqual(MultiSetDisplayExpr left, MultiSetDisplayExpr right) {
    if (!AllElementsAreLiterals(left.Elements) || !AllElementsAreLiterals(right.Elements)) {
      return false;
    }
    var leftCounts = BuildMultisetCounts(left.Elements);
    var rightCounts = BuildMultisetCounts(right.Elements);
    if (leftCounts.Count != rightCounts.Count) {
      return false;
    }
    foreach (var entry in leftCounts) {
      var match = rightCounts.FirstOrDefault(candidate => AreLiteralExpressionsEqual(entry.Element, candidate.Element));
      if (match == null || match.Count != entry.Count) {
        return false;
      }
    }
    return true;
  }

  private static List<Expression> DistinctLiteralElements(IEnumerable<Expression> elements) {
    var distinct = new List<Expression>();
    foreach (var element in elements) {
      if (!ContainsLiteralElement(distinct, element)) {
        distinct.Add(element);
      }
    }
    return distinct;
  }

  private static bool ContainsLiteralElement(List<Expression> elements, Expression candidate) {
    foreach (var existing in elements) {
      if (AreLiteralExpressionsEqual(existing, candidate)) {
        return true;
      }
    }
    return false;
  }

  private sealed class MultisetElementCount {
    public MultisetElementCount(Expression element) {
      Element = element;
    }

    public Expression Element { get; }
    public int Count { get; set; }
  }

  private static List<MultisetElementCount> BuildMultisetCounts(IEnumerable<Expression> elements) {
    var counts = new List<MultisetElementCount>();
    foreach (var element in elements) {
      var existing = counts.FirstOrDefault(entry => AreLiteralExpressionsEqual(entry.Element, element));
      if (existing == null) {
        counts.Add(new MultisetElementCount(element) { Count = 1 });
      } else {
        existing.Count++;
      }
    }
    return counts;
  }

  private static bool SeqDisplayIsPrefix(SeqDisplayExpr left, SeqDisplayExpr right, out bool isProper) {
    isProper = false;
    if (left.Elements.Count > right.Elements.Count) {
      return false;
    }
    for (var i = 0; i < left.Elements.Count; i++) {
      if (!AreLiteralExpressionsEqual(left.Elements[i], right.Elements[i])) {
        return false;
      }
    }
    isProper = left.Elements.Count < right.Elements.Count;
    return true;
  }

  private static string BuildInlineCallCycleKey(FunctionCallExpr callExpr) {
    var builder = new StringBuilder();
    builder.Append(RuntimeHelpers.GetHashCode(callExpr.Function));
    builder.Append("|r=");
    if (!callExpr.Function.IsStatic) {
      builder.Append(callExpr.Receiver);
    }
    builder.Append("|a=");
    for (var i = 0; i < callExpr.Args.Count; i++) {
      var arg = callExpr.Args[i];
      if (Expression.IsIntLiteral(arg, out var intValue)) {
        builder.Append("i").Append(intValue);
      } else if (Expression.IsBoolLiteral(arg, out var boolValue)) {
        builder.Append("b").Append(boolValue ? "1" : "0");
      } else {
        builder.Append("x");
      }
      if (i < callExpr.Args.Count - 1) {
        builder.Append(",");
      }
    }
    builder.Append("|t=");
    if (callExpr.TypeApplication_AtEnclosingClass != null) {
      builder.Append(string.Join(",", callExpr.TypeApplication_AtEnclosingClass.Select(t => t.ToString())));
    }
    builder.Append("|tf=");
    if (callExpr.TypeApplication_JustFunction != null) {
      builder.Append(string.Join(",", callExpr.TypeApplication_JustFunction.Select(t => t.ToString())));
    }
    return builder.ToString();
  }

  private enum CachedLiteralKind {
    Int,
    Bool
  }

  private readonly record struct CachedLiteral(CachedLiteralKind Kind, BigInteger IntValue, bool BoolValue) {
    public static bool TryCreate(LiteralExpr literal, out CachedLiteral cached) {
      cached = default;
      if (literal == null) {
        return false;
      }

      if (Expression.IsIntLiteral(literal, out var intValue)) {
        cached = new CachedLiteral(CachedLiteralKind.Int, intValue, default);
        return true;
      }

      if (Expression.IsBoolLiteral(literal, out var boolValue)) {
        cached = new CachedLiteral(CachedLiteralKind.Bool, default, boolValue);
        return true;
      }

      return false;
    }

    public Expression CreateLiteral(IOrigin origin) {
      return Kind switch {
        CachedLiteralKind.Int => CreateIntLiteral(origin, IntValue),
        CachedLiteralKind.Bool => Expression.CreateBoolLiteral(origin, BoolValue),
        _ => null
      };
    }
  }
}
