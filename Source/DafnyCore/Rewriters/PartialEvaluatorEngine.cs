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
  private readonly VisibilityScope effectiveScope;
  private readonly HelperFunctionInterpreter helperInterpreter;
  private readonly Dictionary<string, CachedLiteral> inlineCallCache = new(StringComparer.Ordinal);
  private QuantifierBounds quantifierBounds;

  internal HelperFunctionInterpreter HelperInterpreter => helperInterpreter;

  // ------------------- Construction and entry points -------------------

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth)
    : this(options, module, systemModuleManager, inlineDepth, null) {
  }

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth, VisibilityScope effectiveScope = null) {
    this.options = options;
    this.module = module;
    this.systemModuleManager = systemModuleManager;
    this.inlineDepth = inlineDepth;
    this.effectiveScope = effectiveScope ?? module.VisibilityScope;
    helperInterpreter = new HelperFunctionInterpreter(this, systemModuleManager);
  }

  private PartialEvalState CreateInitialState() {
    // This state is shared across the traversal to limit inlining depth and detect inlining cycles.
    return new PartialEvalState((int)inlineDepth, new HashSet<Function>(), new HashSet<string>(StringComparer.Ordinal));
  }

  private PartialEvaluatorVisitor CreateVisitor() {
    return new PartialEvaluatorVisitor(this);
  }

  /// <summary>
  /// Runs partial evaluation on a resolved callable. This is invoked by the rewriter, and it mutates
  /// the callable body in-place to simplify expressions and statements.
  /// </summary>
  public void PartialEvalEntry(ICallable callable) {
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
    var state = CreateInitialState();
    var visitor = CreateVisitor();
    return visitor.SimplifyExpression(expr, state);
  }

  // ------------------- Quantifier bounds / finite materialization -------------------

  private uint GetPartialEvalUnrollCap() {
    var unrollBoundedQuantifiers = options.Get(CommonOptionBag.UnrollBoundedQuantifiers);
    return unrollBoundedQuantifiers ?? DefaultPartialEvalUnrollCap;
  }

  private QuantifierBounds GetQuantifierBounds() {
    if (quantifierBounds != null) {
      return quantifierBounds;
    }
    quantifierBounds = new QuantifierBounds(systemModuleManager, GetPartialEvalUnrollCap());
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
      emitOverflowResidual);
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

    if (opcode == BinaryExpr.ResolvedOpcode.Sub && ReferenceEquals(binary.E0, binary.E1)) {
      return CreateIntLiteral(binary.Origin, BigInteger.Zero);
    }

    return binary;
  }

  private Expression SimplifyIntDivMod(BinaryExpr binary, BinaryExpr.ResolvedOpcode opcode) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
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
    if (opcode == BinaryExpr.ResolvedOpcode.Div && Expression.IsIntLiteral(binary.E1, out right) && right == 1) {
      return binary.E0;
    }
    if (opcode == BinaryExpr.ResolvedOpcode.Mod && Expression.IsIntLiteral(binary.E1, out right) && right == 1) {
      return CreateIntLiteral(binary.Origin, BigInteger.Zero);
    }
    return binary;
  }

  private static Expression SimplifyBitvectorBinary(BinaryExpr binary) {
    var bitvectorType = binary.Type.NormalizeExpand().AsBitVectorType;
    if (bitvectorType == null) {
      return binary;
    }

    if (!Expression.IsIntLiteral(binary.E0, out var left) || !Expression.IsIntLiteral(binary.E1, out var right)) {
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
    if (TryGetIntLiteralOrCharLiteral(binary.E0, out var left) &&
        TryGetIntLiteralOrCharLiteral(binary.E1, out var right)) {
      return Expression.CreateBoolLiteral(binary.Origin, op(left, right));
    }
    return binary;
  }

  private static bool TryGetIntLiteralOrCharLiteral(Expression expr, out BigInteger value) {
    value = default;
    if (Expression.IsIntLiteral(expr, out var intLiteral)) {
      value = intLiteral;
      return true;
    }
    if (TryGetCharLiteral(expr, out var charLiteral)) {
      value = charLiteral;
      return true;
    }
    if (expr is ConversionExpr conversionExpr) {
      var fromType = conversionExpr.E.Type?.NormalizeExpand();
      var toType = conversionExpr.Type?.NormalizeExpand();
      if (fromType != null && toType is IntType && fromType.IsCharType &&
          TryGetCharLiteral(conversionExpr.E, out var convertedChar)) {
        value = convertedChar;
        return true;
      }
    }
    return false;
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
    if (TryGetStringLiteral(binary.E0, out var leftString, out var leftVerbatim) &&
        TryGetStringLiteral(binary.E1, out var rightString, out var rightVerbatim)) {
      var equal = StringLiteralsSemanticallyEqual(leftString, leftVerbatim, rightString, rightVerbatim);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq) && AllElementsAreLiterals(rightSeq)) {
      var equal = SeqDisplayLiteralsEqual(leftSeq, rightSeq);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    if ((TryGetCharSeqDisplayLiteral(binary.E0, out var leftChars) && TryGetUnescapedStringCharacters(binary.E1, out var rightChars)) ||
        (TryGetUnescapedStringCharacters(binary.E0, out leftChars) && TryGetCharSeqDisplayLiteral(binary.E1, out rightChars))) {
      var equal = CodePointSequencesEqual(leftChars, rightChars);
      return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
    }

    return binary;
  }

  private static Expression SimplifySeqPrefix(BinaryExpr binary, bool properPrefix) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out var leftVerbatim) &&
        TryGetStringLiteral(binary.E1, out var rightString, out var rightVerbatim)) {
      var leftCodePoints = GetSemanticStringCodePoints(leftString, leftVerbatim);
      var rightCodePoints = GetSemanticStringCodePoints(rightString, rightVerbatim);
      var isPrefix = CodePointSequenceHasPrefix(leftCodePoints, rightCodePoints, out var isProper);
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
      var leftDistinct = new LiteralSet(leftDisplay.Elements);
      var rightDistinct = new LiteralSet(rightDisplayLiteral.Elements);
      var isSubset = leftDistinct.Elements.All(element => rightDistinct.Contains(element));
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
      var leftDistinct = new LiteralSet(leftDisplay.Elements);
      var rightDistinct = new LiteralSet(rightDisplay.Elements);
      var disjoint = leftDistinct.Elements.All(element => !rightDistinct.Contains(element));
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
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var merged = new LiteralSet(leftDisplay.Elements);
      foreach (var element in rightDisplay.Elements) {
        merged.Add(element);
      }
      return CreateSetDisplayLiteral(binary.Origin, merged.Elements, binary.Type);
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
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements);
      var rightDistinct = new LiteralSet(rightDisplay.Elements);
      var intersection = new List<Expression>();
      foreach (var element in leftDistinct.Elements) {
        if (rightDistinct.Contains(element)) {
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
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return new SetDisplayExpr(binary.Origin, true, new List<Expression>()) { Type = binary.Type };
    }
    if (TryGetSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftDistinct = new LiteralSet(leftDisplay.Elements);
      var rightDistinct = new LiteralSet(rightDisplay.Elements);
      var difference = leftDistinct.Elements.Where(element => !rightDistinct.Contains(element)).ToList();
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
      var counts = BuildMultisetCountsDict(multiSetDisplay.Elements);
      var contains = counts.ContainsKey(binary.E0);
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

  private static Expression SimplifyMapMembership(BinaryExpr binary, bool isIn) {
    if (binary.E1 is MapDisplayExpr { Elements.Count: 0 }) {
      return CreateBoolLiteral(binary.Origin, !isIn);
    }
    if (binary.E1 is MapDisplayExpr mapDisplay &&
        AllElementsAreLiterals(mapDisplay) &&
        IsLiteralLike(binary.E0)) {
      var contains = mapDisplay.Elements.Any(e => AreLiteralExpressionsEqual(e.A, binary.E0));
      return CreateBoolLiteral(binary.Origin, isIn ? contains : !contains);
    }
    return binary;
  }

  private static Expression SimplifyMapEquality(BinaryExpr binary, bool isEq) {
    if (binary.E0 is not MapDisplayExpr leftMap || binary.E1 is not MapDisplayExpr rightMap) {
      return binary;
    }

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries) ||
        !TryNormalizeLiteralMapEntries(rightMap, out var rightEntries)) {
      return binary;
    }

    var rightByKey = new Dictionary<Expression, Expression>(LiteralExpressionEqualityComparer.Instance);
    foreach (var entry in rightEntries) {
      rightByKey[entry.A] = entry.B;
    }

    var equal = leftEntries.Count == rightEntries.Count;
    if (equal) {
      foreach (var entry in leftEntries) {
        if (!rightByKey.TryGetValue(entry.A, out var rightValue) ||
            !AreLiteralExpressionsEqual(entry.B, rightValue)) {
          equal = false;
          break;
        }
      }
    }

    return CreateBoolLiteral(binary.Origin, isEq ? equal : !equal);
  }

  private static Expression SimplifyMapMerge(BinaryExpr binary) {
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

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries) ||
        !TryNormalizeLiteralMapEntries(rightMap, out var rightEntries)) {
      return binary;
    }

    var merged = new List<MapDisplayEntry>(leftEntries);
    var indexByKey = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.Instance);
    for (var index = 0; index < merged.Count; index++) {
      indexByKey[merged[index].A] = index;
    }

    foreach (var entry in rightEntries) {
      if (indexByKey.TryGetValue(entry.A, out var existingIndex)) {
        merged[existingIndex] = new MapDisplayEntry(entry.A, entry.B);
      } else {
        indexByKey[entry.A] = merged.Count;
        merged.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }

    return CreateMapDisplayLiteral(binary.Origin, merged, binary.Type);
  }

  private static Expression SimplifyMapSubtraction(BinaryExpr binary) {
    if (binary.E0 is not MapDisplayExpr leftMap || binary.E1 is not SetDisplayExpr rightKeySet) {
      return binary;
    }

    if (leftMap.Elements.Count == 0) {
      return binary.E0;
    }
    if (rightKeySet.Elements.Count == 0) {
      return binary.E0;
    }

    if (!TryNormalizeLiteralMapEntries(leftMap, out var leftEntries) ||
        !AllElementsAreLiterals(rightKeySet.Elements)) {
      return binary;
    }

    var keysToRemove = new LiteralSet(rightKeySet.Elements);

    var remaining = new List<MapDisplayEntry>();
    foreach (var entry in leftEntries) {
      if (!keysToRemove.Contains(entry.A)) {
        remaining.Add(new MapDisplayEntry(entry.A, entry.B));
      }
    }

    return CreateMapDisplayLiteral(binary.Origin, remaining, binary.Type);
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
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements);
      var rightCounts = BuildMultisetCountsDict(rightDisplayLiteral.Elements);
      var isSubset = leftCounts.All(entry =>
        rightCounts.TryGetValue(entry.Key, out var rightCount) && entry.Value <= rightCount);
      var isProper = isSubset && leftCounts.Values.Sum() < rightCounts.Values.Sum();
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
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements);
      var disjoint = leftCounts.Keys.All(key => !rightCounts.ContainsKey(key));
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
      var combined = BuildMultisetCountsDict(leftDisplay.Elements);
      foreach (var entry in BuildMultisetCountsDict(rightDisplay.Elements)) {
        combined.TryGetValue(entry.Key, out var existing);
        combined[entry.Key] = existing + entry.Value;
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(combined), binary.Type);
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
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return binary.E0;
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements);
      var intersection = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.Instance);
      foreach (var entry in leftCounts) {
        if (rightCounts.TryGetValue(entry.Key, out var rightCount)) {
          var count = Math.Min(entry.Value, rightCount);
          if (count > 0) {
            intersection[entry.Key] = count;
          }
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(intersection), binary.Type);
    }
    return binary;
  }

  private static Expression SimplifyMultiSetDifference(BinaryExpr binary) {
    if (LiteralExpr.IsEmptyMultiset(binary.E0) || LiteralExpr.IsEmptyMultiset(binary.E1)) {
      return binary.E0;
    }
    if (ReferenceEquals(binary.E0, binary.E1)) {
      return new MultiSetDisplayExpr(binary.Origin, new List<Expression>()) { Type = binary.Type };
    }
    if (TryGetMultiSetDisplayLiteral(binary.E0, out var leftDisplay) &&
        TryGetMultiSetDisplayLiteral(binary.E1, out var rightDisplay) &&
        AllElementsAreLiterals(leftDisplay.Elements) &&
        AllElementsAreLiterals(rightDisplay.Elements)) {
      var leftCounts = BuildMultisetCountsDict(leftDisplay.Elements);
      var rightCounts = BuildMultisetCountsDict(rightDisplay.Elements);
      var difference = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.Instance);
      foreach (var entry in leftCounts) {
        rightCounts.TryGetValue(entry.Key, out var rightCount);
        var count = entry.Value - rightCount;
        if (count > 0) {
          difference[entry.Key] = count;
        }
      }
      return CreateMultiSetDisplayLiteral(binary.Origin, ExpandMultisetCountsDict(difference), binary.Type);
    }
    return binary;
  }

  private static List<Expression> ExpandMultisetCountsDict(Dictionary<Expression, int> counts) {
    var elements = new List<Expression>();
    foreach (var entry in counts) {
      for (var i = 0; i < entry.Value; i++) {
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
    inlined = null;
    var function = callExpr.Function;
    if (function == null || function.Body == null || state.Depth <= 0) {
      return false;
    }

    var is_revealed_in_effective_scope = function.IsRevealedInScope(effectiveScope);
    if (BoogieGenerator.IsOpaque(function, options) || !is_revealed_in_effective_scope) {
      return false;
    }

    if (function.Reads.Expressions != null && function.Reads.Expressions.Count > 0) {
      return false;
    }

    var hasInlineableArgument = callExpr.Args.Count == 0;
    for (var i = 0; i < callExpr.Args.Count; i++) {
      if (IsInlineableArgument(callExpr.Args[i])) {
        hasInlineableArgument = true;
        break;
      }
    }
    if (!hasInlineableArgument) {
      return false;
    }

    var allInlineableArguments = AreAllInlineableArguments(callExpr.Args);
    if (function.IsRecursive && ContainsQuantifierOrComprehension(function.Body)) {
      return false;
    }

    if (function.IsRecursive && !allInlineableArguments && !HasCollectionLiteralArgument(callExpr.Args)) {
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
    if (!addedFunction) {
      var canContinueRecursiveInlining = function.IsRecursive &&
        !ContainsQuantifierOrComprehension(function.Body) &&
        HasCollectionLiteralArgument(callExpr.Args);
      if ((!allInlineableArguments && !canContinueRecursiveInlining) ||
          ContainsQuantifierOrComprehension(function.Body)) {
        state.InlineCallStack.Remove(callKey);
        return false;
      }
    }

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

  // ------------------- Inlined-literal cache -------------------

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

  // ------------------- Inlining cache keys -------------------

  private static bool TryBuildInlineCallCacheKey(FunctionCallExpr callExpr, PartialEvalState state, out string key) {
    key = null;

    var function = callExpr.Function;
    if (function == null) {
      return false;
    }

    foreach (var arg in callExpr.Args) {
      if (!Expression.IsIntLiteral(arg, out _) && !Expression.IsBoolLiteral(arg, out _) &&
          arg is not CharLiteralExpr && arg is not StringLiteralExpr) {
        return false;
      }
    }

    var stackKey = BuildInlineStackKey(state.InlineStack, function);
    var callKey = BuildInlineCallCacheCallKey(callExpr);

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

  /// <summary>
  /// Builds a cache-key fragment from a FunctionCallExpr's literal arguments and type applications,
  /// avoiding the expensive callExpr.ToString() which serializes the entire AST subtree.
  /// Only called when all args are known to be int or bool literals (checked by the caller's guard).
  /// </summary>
  private static string BuildInlineCallCacheCallKey(FunctionCallExpr callExpr) {
    var builder = new StringBuilder();
    for (var i = 0; i < callExpr.Args.Count; i++) {
      if (i > 0) {
        builder.Append(',');
      }
      var arg = callExpr.Args[i];
      if (Expression.IsIntLiteral(arg, out var intVal)) {
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
        if (i > 0) {
          builder.Append(',');
        }
        builder.Append(callExpr.TypeApplication_AtEnclosingClass[i]);
      }
    }
    if (callExpr.TypeApplication_JustFunction is { Count: > 0 }) {
      builder.Append("|tf=");
      for (var i = 0; i < callExpr.TypeApplication_JustFunction.Count; i++) {
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

  // ------------------- Literal classification helpers -------------------

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

  private static bool TryGetMapDisplayLiteral(Expression expr, out MapDisplayExpr display) {
    display = expr as MapDisplayExpr;
    return display != null;
  }

  private static bool AllElementsAreLiterals(IEnumerable<Expression> elements) {
    return elements.All(IsLiteralLike);
  }

  private static bool AllElementsAreLiterals(MapDisplayExpr display) {
    return display.Elements.All(entry => IsLiteralLike(entry.A) && IsLiteralLike(entry.B));
  }

  private static bool AllMapKeysAreLiterals(MapDisplayExpr display) {
    return display.Elements.All(entry => IsLiteralLike(entry.A));
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

  // ------------------- Inlineability -------------------

  private static bool IsInlineableArgument(Expression expr) {
    return IsLiteralLike(expr) || expr is LambdaExpr;
  }

  internal static bool AreAllInlineableArguments(IEnumerable<Expression> args) {
    foreach (var arg in args) {
      if (!IsInlineableArgument(arg)) {
        return false;
      }
    }

    return true;
  }

  private static bool ContainsQuantifierOrComprehension(Expression expr) {
    if (expr is QuantifierExpr or ComprehensionExpr) {
      return true;
    }

    foreach (var subExpression in expr.SubExpressions) {
      if (ContainsQuantifierOrComprehension(subExpression)) {
        return true;
      }
    }

    return false;
  }

  private static bool HasCollectionLiteralArgument(IEnumerable<Expression> args) {
    foreach (var arg in args) {
      var normalized = QuantifierBounds.StripConcreteSyntax(arg);
      if (normalized is SeqDisplayExpr or SetDisplayExpr or MultiSetDisplayExpr or MapDisplayExpr or StringLiteralExpr) {
        return true;
      }
    }

    return false;
  }


  // ------------------- Literal equality helpers -------------------

  private static bool AreLiteralExpressionsEqual(Expression left, Expression right) {
    if (TryGetCharLiteral(left, out var leftChar) && TryGetCharLiteral(right, out var rightChar)) {
      return leftChar == rightChar;
    }
    if (left is StringLiteralExpr leftStringLiteral && right is StringLiteralExpr rightStringLiteral &&
        leftStringLiteral.Value is string leftStringValue && rightStringLiteral.Value is string rightStringValue) {
      return StringLiteralsSemanticallyEqual(
        leftStringValue,
        leftStringLiteral.IsVerbatim,
        rightStringValue,
        rightStringLiteral.IsVerbatim);
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
    if (left is MapDisplayExpr leftMap && right is MapDisplayExpr rightMap) {
      return MapDisplayLiteralsEqual(leftMap, rightMap);
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

  private static bool CodePointSequenceHasPrefix(IReadOnlyList<int> prefix, IReadOnlyList<int> sequence, out bool isProper) {
    isProper = false;
    if (prefix.Count > sequence.Count) {
      return false;
    }
    for (var index = 0; index < prefix.Count; index++) {
      if (prefix[index] != sequence[index]) {
        return false;
      }
    }
    isProper = prefix.Count < sequence.Count;
    return true;
  }

  private static List<int> GetSemanticStringCodePoints(string value, bool isVerbatim) {
    return Util.UnescapedCharacters(DafnyOptions.DefaultImmutableOptions, value, isVerbatim).ToList();
  }

  private static bool StringLiteralsSemanticallyEqual(string leftValue, bool leftVerbatim, string rightValue, bool rightVerbatim) {
    var leftCodePoints = GetSemanticStringCodePoints(leftValue, leftVerbatim);
    var rightCodePoints = GetSemanticStringCodePoints(rightValue, rightVerbatim);
    return CodePointSequencesEqual(leftCodePoints, rightCodePoints);
  }

  private static int ComputeSemanticStringHash(string value, bool isVerbatim) {
    var hash = new HashCode();
    hash.Add(typeof(StringLiteralExpr));
    foreach (var codePoint in GetSemanticStringCodePoints(value, isVerbatim)) {
      hash.Add(codePoint);
    }
    return hash.ToHashCode();
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
    var leftDistinct = new LiteralSet(left.Elements);
    var rightDistinct = new LiteralSet(right.Elements);
    if (leftDistinct.Count != rightDistinct.Count) {
      return false;
    }
    foreach (var element in leftDistinct.Elements) {
      if (!rightDistinct.Contains(element)) {
        return false;
      }
    }
    return true;
  }

  private static bool MultiSetDisplayLiteralsEqual(MultiSetDisplayExpr left, MultiSetDisplayExpr right) {
    if (!AllElementsAreLiterals(left.Elements) || !AllElementsAreLiterals(right.Elements)) {
      return false;
    }
    var leftCounts = BuildMultisetCountsDict(left.Elements);
    var rightCounts = BuildMultisetCountsDict(right.Elements);
    if (leftCounts.Count != rightCounts.Count) {
      return false;
    }
    foreach (var entry in leftCounts) {
      if (!rightCounts.TryGetValue(entry.Key, out var rightCount) || rightCount != entry.Value) {
        return false;
      }
    }
    return true;
  }

  private static bool MapDisplayLiteralsEqual(MapDisplayExpr left, MapDisplayExpr right) {
    if (!TryNormalizeLiteralMapEntries(left, out var leftEntries) ||
        !TryNormalizeLiteralMapEntries(right, out var rightEntries)) {
      return false;
    }
    if (leftEntries.Count != rightEntries.Count) {
      return false;
    }

    var rightByKey = new Dictionary<Expression, Expression>(LiteralExpressionEqualityComparer.Instance);
    foreach (var entry in rightEntries) {
      rightByKey[entry.A] = entry.B;
    }

    foreach (var entry in leftEntries) {
      if (!rightByKey.TryGetValue(entry.A, out var rightValue) ||
          !AreLiteralExpressionsEqual(entry.B, rightValue)) {
        return false;
      }
    }

    return true;
  }

  private static bool TryNormalizeLiteralMapEntries(MapDisplayExpr mapDisplay, out List<MapDisplayEntry> normalizedEntries) {
    normalizedEntries = null;
    if (!AllElementsAreLiterals(mapDisplay)) {
      return false;
    }

    var entries = new List<MapDisplayEntry>(mapDisplay.Elements.Count);
    var indexByKey = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.Instance);
    foreach (var entry in mapDisplay.Elements) {
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

  private static bool ContainsLiteralElement(List<Expression> elements, Expression candidate) {
    foreach (var existing in elements) {
      if (AreLiteralExpressionsEqual(existing, candidate)) {
        return true;
      }
    }
    return false;
  }

  // ------------------- Multiset element counting -------------------

  private static Dictionary<Expression, int> BuildMultisetCountsDict(IEnumerable<Expression> elements) {
    var counts = new Dictionary<Expression, int>(LiteralExpressionEqualityComparer.Instance);
    foreach (var element in elements) {
      counts.TryGetValue(element, out var count);
      counts[element] = count + 1;
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

  // ------------------- Inlining cycle keys and cached literals -------------------

  private static string BuildInlineCallCycleKey(FunctionCallExpr callExpr) {
    var builder = new StringBuilder();
    builder.Append(RuntimeHelpers.GetHashCode(callExpr.Function));
    builder.Append("|r=");
    if (!callExpr.Function.IsStatic) {
      builder.Append(RuntimeHelpers.GetHashCode(callExpr.Receiver));
    }
    builder.Append("|a=");
    for (var i = 0; i < callExpr.Args.Count; i++) {
      var arg = callExpr.Args[i];
      if (Expression.IsIntLiteral(arg, out var intValue)) {
        builder.Append("i").Append(intValue);
      } else if (Expression.IsBoolLiteral(arg, out var boolValue)) {
        builder.Append("b").Append(boolValue ? "1" : "0");
      } else if (arg is SeqDisplayExpr seqDisplay && AllElementsAreLiterals(seqDisplay.Elements)) {
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
      builder.Append(string.Join(",", callExpr.TypeApplication_AtEnclosingClass.Select(t => t.ToString())));
    }
    builder.Append("|tf=");
    if (callExpr.TypeApplication_JustFunction != null) {
      builder.Append(string.Join(",", callExpr.TypeApplication_JustFunction.Select(t => t.ToString())));
    }
    return builder.ToString();
  }

  // ------------------- Cached literal representation -------------------

  private enum CachedLiteralKind {
    Int,
    Bool,
    Char,
    String
  }

  private readonly record struct CachedLiteral(CachedLiteralKind Kind, BigInteger IntValue, bool BoolValue, string StringValue, Type LiteralType) {
    public static bool TryCreate(LiteralExpr literal, out CachedLiteral cached) {
      cached = default;
      if (literal == null) {
        return false;
      }

      if (Expression.IsIntLiteral(literal, out var intValue)) {
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

  private sealed class LiteralExpressionEqualityComparer : IEqualityComparer<Expression> {
    public static readonly LiteralExpressionEqualityComparer Instance = new();

    public bool Equals(Expression x, Expression y) {
      if (ReferenceEquals(x, y)) {
        return true;
      }
      if (x == null || y == null) {
        return false;
      }
      return AreLiteralExpressionsEqual(x, y);
    }

    public int GetHashCode(Expression expr) {
      if (expr == null) {
        return 0;
      }
      return ComputeHash(expr);
    }

    private static int ComputeHash(Expression expr) {
      if (expr is CharLiteralExpr && TryGetCharLiteral(expr, out var ch)) {
        return HashCode.Combine(typeof(CharLiteralExpr), (int)ch);
      }
      if (expr is StringLiteralExpr stringLiteral && stringLiteral.Value is string stringValue) {
        return ComputeSemanticStringHash(stringValue, stringLiteral.IsVerbatim);
      }
      if (expr is LiteralExpr lit) {
        return HashCode.Combine(typeof(LiteralExpr), lit.Value);
      }
      if (expr is SeqDisplayExpr seq) {
        var hash = new HashCode();
        hash.Add(typeof(SeqDisplayExpr));
        foreach (var e in seq.Elements) {
          hash.Add(ComputeHash(e));
        }
        return hash.ToHashCode();
      }
      if (expr is SetDisplayExpr setDisplay) {
        if (!AllElementsAreLiterals(setDisplay.Elements)) {
          return typeof(SetDisplayExpr).GetHashCode();
        }
        // Order-independent hash based on distinct literal elements.
        var distinct = new LiteralSet(setDisplay.Elements);
        var sum = 0;
        var xor = 0;
        foreach (var element in distinct.Elements) {
          var elementHash = ComputeHash(element);
          sum = unchecked(sum + elementHash);
          xor ^= elementHash;
        }
        return HashCode.Combine(typeof(SetDisplayExpr), distinct.Count, sum, xor);
      }
      if (expr is MultiSetDisplayExpr multiSetDisplay) {
        if (!AllElementsAreLiterals(multiSetDisplay.Elements)) {
          return typeof(MultiSetDisplayExpr).GetHashCode();
        }
        // Order-independent hash based on literal element multiplicities.
        var counts = BuildMultisetCountsDict(multiSetDisplay.Elements);
        var sum = 0;
        var xor = 0;
        var totalCount = 0;
        foreach (var entry in counts) {
          var entryHash = HashCode.Combine(ComputeHash(entry.Key), entry.Value);
          sum = unchecked(sum + entryHash);
          xor ^= entryHash;
          totalCount += entry.Value;
        }
        return HashCode.Combine(typeof(MultiSetDisplayExpr), counts.Count, totalCount, sum, xor);
      }
      if (expr is MapDisplayExpr mapDisplay) {
        if (!TryNormalizeLiteralMapEntries(mapDisplay, out var normalizedEntries)) {
          return typeof(MapDisplayExpr).GetHashCode();
        }
        var sum = 0;
        var xor = 0;
        foreach (var entry in normalizedEntries) {
          var entryHash = HashCode.Combine(ComputeHash(entry.A), ComputeHash(entry.B));
          sum = unchecked(sum + entryHash);
          xor ^= entryHash;
        }
        return HashCode.Combine(typeof(MapDisplayExpr), normalizedEntries.Count, sum, xor);
      }
      if (TryGetTupleLiteral(expr, out var tuple)) {
        var hash = new HashCode();
        hash.Add(typeof(DatatypeValue));
        foreach (var arg in tuple.Arguments) {
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

    public LiteralSet(IEnumerable<Expression> source) {
      set = new HashSet<Expression>(LiteralExpressionEqualityComparer.Instance);
      Elements = new List<Expression>();
      foreach (var e in source) {
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
