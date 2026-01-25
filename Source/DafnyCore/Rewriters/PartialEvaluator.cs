// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

namespace Microsoft.Dafny;

public class PartialEvaluator : IRewriter {
  private readonly Program program;

  public PartialEvaluator(Program program, ErrorReporter reporter) : base(reporter) {
    Contract.Requires(program != null);
    this.program = program;
  }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    var entryName = Reporter.Options.Get(CommonOptionBag.PartialEvalEntry);
    if (string.IsNullOrEmpty(entryName)) {
      return;
    }

    var inlineDepth = Reporter.Options.Get(CommonOptionBag.PartialEvalInlineDepth);
    var entryTargets = new List<ICallable>();
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      if (decl is Declaration declaration && declaration.Name == entryName) {
        entryTargets.Add(decl);
      }
    }

    if (entryTargets.Count == 0) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Partial evaluation entry '{entryName}' was not found in module '{moduleDefinition.Name}'.");
      return;
    }

    if (entryTargets.Count > 1) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Multiple callables named '{entryName}' found; partial evaluation will run on all matches.");
    }

    var evaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth);
    foreach (var target in entryTargets) {
      evaluator.PartialEvalEntry(target);
    }
  }
}

internal sealed class PartialEvaluatorEngine {
  private readonly DafnyOptions options;
  private readonly ModuleDefinition module;
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint inlineDepth;
  private readonly Dictionary<string, CachedLiteral> inlineCallCache = new(StringComparer.Ordinal);

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth) {
    this.options = options;
    this.module = module;
    this.systemModuleManager = systemModuleManager;
    this.inlineDepth = inlineDepth;
  }

  public void PartialEvalEntry(ICallable callable) {
    var state = new PartialEvalState((int)inlineDepth, new HashSet<Function>(), new HashSet<string>(StringComparer.Ordinal));
    var visitor = new PartialEvaluatorVisitor(this, inlineCallCache);
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
    var visitor = new PartialEvaluatorVisitor(this, inlineCallCache);
    return visitor.SimplifyExpression(expr, state);
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
        return SimplifyBooleanBinary(binary);
      case BinaryExpr.ResolvedOpcode.Or:
        return SimplifyBooleanBinary(binary);
      case BinaryExpr.ResolvedOpcode.Imp:
        return SimplifyBooleanBinary(binary);
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
      default:
        return binary;
    }
  }

  internal static Expression SimplifyBooleanExpression(Expression expr) {
    if (expr == null) {
      throw new ArgumentNullException(nameof(expr));
    }

    if (expr.Resolved != null && expr.Resolved != expr) {
      expr = expr.Resolved;
    }

    if (expr is ParensExpression parens && parens.ResolvedExpression != null) {
      expr = parens.ResolvedExpression;
    }

    switch (expr) {
      case UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot } unary: {
          unary.E = SimplifyBooleanExpression(unary.E);
          if (Expression.IsBoolLiteral(unary.E, out var boolValue)) {
            return CreateBoolLiteral(unary.Origin, !boolValue);
          }
          return unary;
        }
      case BinaryExpr binary: {
          binary.E0 = SimplifyBooleanExpression(binary.E0);
          binary.E1 = SimplifyBooleanExpression(binary.E1);

          if (binary.ResolvedOp is BinaryExpr.ResolvedOpcode.And or BinaryExpr.ResolvedOpcode.Or
              or BinaryExpr.ResolvedOpcode.Imp or BinaryExpr.ResolvedOpcode.Iff) {
            return SimplifyBooleanBinary(binary);
          }

          if (binary.ResolvedOp is BinaryExpr.ResolvedOpcode.EqCommon or BinaryExpr.ResolvedOpcode.NeqCommon) {
            return SimplifyEquality(binary, binary.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon);
          }

          if (binary.ResolvedOp is BinaryExpr.ResolvedOpcode.Le or BinaryExpr.ResolvedOpcode.Lt
              or BinaryExpr.ResolvedOpcode.Ge or BinaryExpr.ResolvedOpcode.Gt) {
            if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
              var value = binary.ResolvedOp switch {
                BinaryExpr.ResolvedOpcode.Le => left <= right,
                BinaryExpr.ResolvedOpcode.Lt => left < right,
                BinaryExpr.ResolvedOpcode.Ge => left >= right,
                BinaryExpr.ResolvedOpcode.Gt => left > right,
                _ => false
              };
              return CreateBoolLiteral(binary.Origin, value);
            }
          }

          return binary;
        }
      default:
        return expr;
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
        if (Expression.IsBoolLiteral(binary.E0, out var lAnd)) {
          return lAnd ? binary.E1 : CreateBoolLiteral(binary.Origin, false);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rAnd)) {
          return rAnd ? binary.E0 : CreateBoolLiteral(binary.Origin, false);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Or:
        if (Expression.IsBoolLiteral(binary.E0, out var lOr)) {
          return lOr ? CreateBoolLiteral(binary.Origin, true) : binary.E1;
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rOr)) {
          return rOr ? CreateBoolLiteral(binary.Origin, true) : binary.E0;
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Imp:
        if (Expression.IsBoolLiteral(binary.E0, out var lImp)) {
          return lImp ? binary.E1 : CreateBoolLiteral(binary.Origin, true);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rImp)) {
          return rImp ? CreateBoolLiteral(binary.Origin, true) : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Iff:
        if (Expression.IsBoolLiteral(binary.E0, out var lIff)) {
          return lIff ? binary.E1 : Expression.CreateNot(binary.Origin, binary.E1);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rIff)) {
          return rIff ? binary.E0 : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      default:
        return binary;
    }
  }

  private Expression SimplifyIntBinary(BinaryExpr binary, System.Func<BigInteger, BigInteger, BigInteger> op, int identity, BinaryExpr.ResolvedOpcode opcode) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      return CreateIntLiteral(binary.Origin, op(left, right));
    }

    if (Expression.IsIntLiteral(binary.E0, out left) && left == identity && opcode == BinaryExpr.ResolvedOpcode.Add) {
      return binary.E1;
    }

    if (Expression.IsIntLiteral(binary.E1, out right) && right == identity && opcode is BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub) {
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

  private static Expression SimplifySeqEquality(BinaryExpr binary, bool isEq) {
    if (TryGetStringLiteral(binary.E0, out var leftString, out _) && TryGetStringLiteral(binary.E1, out var rightString, out _)) {
      return CreateBoolLiteral(binary.Origin, isEq ? leftString == rightString : leftString != rightString);
    }

    if (TryGetSeqDisplayLiteral(binary.E0, out var leftSeq) && TryGetSeqDisplayLiteral(binary.E1, out var rightSeq) &&
        AllElementsAreLiterals(leftSeq) && AllElementsAreLiterals(rightSeq)) {
      var equal = SeqDisplayLiteralsEqual(leftSeq, rightSeq);
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
      var simplifiedArg = visitor.SimplifyExpression(callExpr.Args[i], state.WithDepth(0));
      callExpr.Args[i] = simplifiedArg;
      if (!IsLiteralLike(simplifiedArg)) {
        allLiteralArgs = false;
      }
    }
    if (!allLiteralArgs) {
      return false;
    }

    // Cache inlined results for pure, static calls with literal arguments, when the inlined body
    // simplifies all the way to an int/bool literal. This avoids redundant substitution+rewrite work
    // for repeated calls like f(5).
    if (visitor.TryGetCachedInlinedLiteral(callExpr, state, out inlined)) {
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
      // Re-simplify without allowing further inlining beyond the current budget.
      var postVisitor = new PartialEvaluatorVisitor(this, inlineCallCache);
      inlined = postVisitor.SimplifyExpression(inlined, state.WithDepth(0));

      if (inlined is LiteralExpr literal) {
        visitor.CacheInlinedLiteral(callExpr, state, literal);
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
    return false;
  }

  private static bool AreLiteralExpressionsEqual(Expression left, Expression right) {
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

  private sealed class PartialEvalState {
    public int Depth { get; }
    public HashSet<Function> InlineStack { get; }
    public HashSet<string> InlineCallStack { get; }

    public PartialEvalState(int depth, HashSet<Function> inlineStack, HashSet<string> inlineCallStack) {
      Depth = depth;
      InlineStack = inlineStack;
      InlineCallStack = inlineCallStack;
    }

    public PartialEvalState WithDepth(int depth) {
      return new PartialEvalState(depth, InlineStack, InlineCallStack);
    }
  }

  private sealed class PartialEvaluatorVisitor : TopDownVisitor<PartialEvalState> {
    private readonly PartialEvaluatorEngine engine;
    private readonly Dictionary<Expression, Expression> replacements = new();
    private readonly Dictionary<string, CachedLiteral> inlineCallCache;
    private List<Dictionary<IVariable, ConstValue>> constScopes = [];

    public PartialEvaluatorVisitor(PartialEvaluatorEngine engine, Dictionary<string, CachedLiteral> inlineCallCache = null) {
      this.engine = engine;
      this.inlineCallCache = inlineCallCache ?? new Dictionary<string, CachedLiteral>(System.StringComparer.Ordinal);
      constScopes.Add(new Dictionary<IVariable, ConstValue>());
    }

    public Expression SimplifyExpression(Expression expr, PartialEvalState state) {
      if (expr == null) {
        return null;
      }

      if (expr.Resolved != null && expr.Resolved != expr) {
        var resolvedResult = SimplifyExpression(expr.Resolved, state);
        if (!ReferenceEquals(resolvedResult, expr)) {
          AssertHasResolvedType(resolvedResult);
        }
        return resolvedResult;
      }

      Visit(expr, state);
      var result = GetReplacement(expr);
      if (!ReferenceEquals(result, expr)) {
        AssertHasResolvedType(result);
      }
      return result;
    }

    private Expression GetReplacement(Expression expr) {
      return replacements.TryGetValue(expr, out var replacement) ? replacement : expr;
    }

    private void SetReplacement(Expression original, Expression replacement) {
      if (!ReferenceEquals(original, replacement)) {
        replacements[original] = replacement;
      }
    }

    private void EnterScope() {
      constScopes.Add(new Dictionary<IVariable, ConstValue>());
    }

    private void ExitScope() {
      if (constScopes.Count > 1) {
        constScopes.RemoveAt(constScopes.Count - 1);
      } else {
        // The visitor always keeps a root scope.
        constScopes[0].Clear();
      }
    }

    private bool TryLookupConst(IVariable variable, out ConstValue value) {
      for (var i = constScopes.Count - 1; i >= 0; i--) {
        if (constScopes[i].TryGetValue(variable, out value)) {
          return true;
        }
      }

      value = default;
      return false;
    }

    private void SetConst(IVariable variable, ConstValue value) {
      constScopes[^1][variable] = value;
    }

    private void InvalidateConst(IVariable variable) {
      for (var i = constScopes.Count - 1; i >= 0; i--) {
        if (constScopes[i].Remove(variable)) {
          return;
        }
      }
    }

    private void InvalidateAssignedLocals(Statement stmt) {
      foreach (var ide in stmt.GetAssignedLocals()) {
        if (ide?.Var != null) {
          InvalidateConst(ide.Var);
        }
      }
    }

    private List<Dictionary<IVariable, ConstValue>> CloneConstScopes() {
      var snapshot = new List<Dictionary<IVariable, ConstValue>>(constScopes.Count);
      foreach (var scope in constScopes) {
        snapshot.Add(new Dictionary<IVariable, ConstValue>(scope));
      }
      return snapshot;
    }

    private static HashSet<IVariable> CollectAssignedLocalsDeep(Statement root) {
      var assigned = new HashSet<IVariable>();
      if (root == null) {
        return assigned;
      }

      var stack = new Stack<Statement>();
      stack.Push(root);
      while (stack.Count > 0) {
        var current = stack.Pop();
        foreach (var ide in current.GetAssignedLocals()) {
          if (ide?.Var != null) {
            assigned.Add(ide.Var);
          }
        }
        foreach (var child in current.SubStatements) {
          stack.Push(child);
        }
      }

      return assigned;
    }

    private void TryRecordLiteralLocalInitializers(VarDeclStmt varDeclStmt) {
      if (varDeclStmt.Assign is not AssignStatement assignStatement) {
        return;
      }

      // For var declarations, we only record locals that are initialized to int/bool literals.
      // This stays conservative and avoids having to define general value semantics.
      var resolvedStatements = assignStatement.ResolvedStatements;
      if (resolvedStatements == null) {
        return;
      }

      var declaredLocals = new HashSet<LocalVariable>(varDeclStmt.Locals);
      foreach (var s in resolvedStatements) {
        if (s is not SingleAssignStmt singleAssign) {
          continue;
        }

        if (singleAssign.Lhs.Resolved is not IdentifierExpr ide) {
          continue;
        }

        if (ide.Var is not LocalVariable local || !declaredLocals.Contains(local)) {
          continue;
        }

        if (singleAssign.Rhs is not ExprRhs exprRhs) {
          continue;
        }

        if (exprRhs.Expr is not LiteralExpr literal) {
          continue;
        }

        if (!ConstValue.TryCreate(literal, out var constValue)) {
          continue;
        }

        SetConst(ide.Var, constValue);
      }
    }

    internal bool TryGetCachedInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, out Expression inlined) {
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

    private static IEnumerable<string> TokenizeStringLiteral(string value, bool isVerbatim) {
      if (!isVerbatim) {
        return Util.TokensWithEscapes(value, false);
      }

      var tokens = new List<string>();
      for (var i = 0; i < value.Length; i++) {
        if (value[i] == '"' && i + 1 < value.Length && value[i + 1] == '"') {
          tokens.Add("\"\"");
          i++;
        } else {
          tokens.Add(value[i].ToString());
        }
      }
      return tokens;
    }

    private int GetUnescapedStringLength(string value, bool isVerbatim) {
      return Util.UnescapedCharacters(engine.options, value, isVerbatim).Count();
    }

    private bool TryGetUnescapedCharLiteral(string value, bool isVerbatim, int index, out string escapedValue) {
      escapedValue = null;
      var codePoints = Util.UnescapedCharacters(engine.options, value, isVerbatim).ToList();
      if (index < 0 || index >= codePoints.Count) {
        return false;
      }

      escapedValue = EscapeCharLiteral(codePoints[index], engine.options.Get(CommonOptionBag.UnicodeCharacters));
      return true;
    }

    private bool TryGetStringSliceLiteral(string value, bool isVerbatim, int start, int end, out string sliceValue) {
      sliceValue = null;
      if (start < 0 || end < start) {
        return false;
      }

      var tokens = TokenizeStringLiteral(value, isVerbatim)
        .Select(token => new {
          Token = token,
          UnescapedLength = Util.UnescapedCharacters(engine.options, token, isVerbatim).Count()
        })
        .ToList();

      var totalLength = tokens.Sum(token => token.UnescapedLength);
      if (end > totalLength) {
        return false;
      }

      var builder = new StringBuilder();
      var index = 0;
      foreach (var token in tokens) {
        var tokenStart = index;
        var tokenEnd = index + token.UnescapedLength;
        if (tokenEnd <= start) {
          index = tokenEnd;
          continue;
        }
        if (tokenStart >= end) {
          break;
        }

        var localStart = Math.Max(start, tokenStart) - tokenStart;
        var localEnd = Math.Min(end, tokenEnd) - tokenStart;
        if (token.UnescapedLength == 1) {
          builder.Append(token.Token);
        } else {
          builder.Append(token.Token.Substring(localStart, localEnd - localStart));
        }
        index = tokenEnd;
      }

      sliceValue = builder.ToString();
      return true;
    }

    private static string EscapeCharLiteral(int codePoint, bool unicodeChars) {
      switch (codePoint) {
        case 0:
          return "\\0";
        case 9:
          return "\\t";
        case 10:
          return "\\n";
        case 13:
          return "\\r";
        case 34:
          return "\\\"";
        case 39:
          return "\\\'";
        case 92:
          return "\\\\";
      }

      if (codePoint is >= 32 and <= 126) {
        return $"{Convert.ToChar(codePoint)}";
      }

      if (unicodeChars) {
        return $"\\U{{{codePoint:X4}}}";
      }

      if (codePoint <= 0xFFFF) {
        return $"\\u{codePoint:X4}";
      }

      return $"\\U{{{codePoint:X4}}}";
    }

    internal void CacheInlinedLiteral(FunctionCallExpr callExpr, PartialEvalState state, LiteralExpr literal) {
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

      // Keep caching conservative: we only memoize calls whose (already simplified) arguments are int/bool literals.
      // This covers the motivating case like f(5) while avoiding having to define a full AST hashing story.
      foreach (var arg in callExpr.Args) {
        if (!Expression.IsIntLiteral(arg, out _) && !Expression.IsBoolLiteral(arg, out _)) {
          return false;
        }
      }

      // The inlined result can depend on inlining context (depth and stack), so include it in the key.
      // IMPORTANT: Exclude the current function, because cache lookup happens before we push it on the stack,
      // while cache store happens after. Excluding it keeps lookup/store aligned.
      var stackKey = BuildInlineStackKey(state.InlineStack, function);

      // Use the printer-based representation of the call as a canonical-ish signature (includes name, receiver,
      // type arguments, and literal arguments). This avoids hand-rolling a structural hash for expressions.
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

    protected override bool VisitOneStmt(Statement stmt, ref PartialEvalState state) {
      switch (stmt) {
        case BlockStmt block:
          EnterScope();
          foreach (var s in block.Body) {
            Visit(s, state);
          }
          ExitScope();
          break;
        case IfStmt ifStmt:
          ifStmt.Guard = SimplifyExpression(ifStmt.Guard, state);
          if (Expression.IsBoolLiteral(ifStmt.Guard, out var cond)) {
            if (cond) {
              Visit(ifStmt.Thn, state);
            } else if (ifStmt.Els != null) {
              Visit(ifStmt.Els, state);
            }
          } else {
            // Visit both branches, but do so from the same incoming environment so that substitutions
            // within one branch do not affect the other.
            var incoming = CloneConstScopes();

            constScopes = CloneConstScopes();
            Visit(ifStmt.Thn, state);

            constScopes = incoming;
            if (ifStmt.Els != null) {
              constScopes = CloneConstScopes();
              Visit(ifStmt.Els, state);
            }

            // After the join, conservatively drop any locals assigned in either branch.
            constScopes = incoming;
            var assigned = CollectAssignedLocalsDeep(ifStmt.Thn);
            if (ifStmt.Els != null) {
              assigned.UnionWith(CollectAssignedLocalsDeep(ifStmt.Els));
            }
            foreach (var v in assigned) {
              InvalidateConst(v);
            }
          }
          break;
        case WhileStmt whileStmt:
          whileStmt.Guard = SimplifyExpression(whileStmt.Guard, state);
          foreach (var inv in whileStmt.Invariants) {
            inv.E = SimplifyExpression(inv.E, state);
          }
          if (whileStmt.Decreases?.Expressions != null) {
            for (var i = 0; i < whileStmt.Decreases.Expressions.Count; i++) {
              whileStmt.Decreases.Expressions[i] = SimplifyExpression(whileStmt.Decreases.Expressions[i], state);
            }
          }
          Visit(whileStmt.Body, state);
          // Be conservative across loops: assignments in the body may happen multiple times.
          if (whileStmt.Body != null) {
            foreach (var v in CollectAssignedLocalsDeep(whileStmt.Body)) {
              InvalidateConst(v);
            }
          }
          break;
        case AssertStmt assertStmt:
          assertStmt.Expr = SimplifyExpression(assertStmt.Expr, state);
          break;
        case AssumeStmt assumeStmt:
          assumeStmt.Expr = SimplifyExpression(assumeStmt.Expr, state);
          break;
        case ExpectStmt expectStmt:
          expectStmt.Expr = SimplifyExpression(expectStmt.Expr, state);
          if (expectStmt.Message != null) {
            expectStmt.Message = SimplifyExpression(expectStmt.Message, state);
          }
          break;
        case SingleAssignStmt assignStmt:
          if (assignStmt.Rhs is ExprRhs exprRhs) {
            exprRhs.Expr = SimplifyExpression(exprRhs.Expr, state);
          }
          InvalidateAssignedLocals(assignStmt);
          break;
        case CallStmt callStmt:
          callStmt.MethodSelect.Obj = SimplifyExpression(callStmt.MethodSelect.Obj, state);
          for (var i = 0; i < callStmt.Args.Count; i++) {
            callStmt.Args[i] = SimplifyExpression(callStmt.Args[i], state);
          }
          InvalidateAssignedLocals(callStmt);
          break;
        case VarDeclStmt varDeclStmt:
          if (varDeclStmt.Assign != null) {
            Visit(varDeclStmt.Assign, state);
          }
          TryRecordLiteralLocalInitializers(varDeclStmt);
          break;
        case AssignSuchThatStmt assignSuchThatStmt:
          assignSuchThatStmt.Expr = SimplifyExpression(assignSuchThatStmt.Expr, state);
          InvalidateAssignedLocals(assignSuchThatStmt);
          break;
        case ReturnStmt returnStmt:
          if (returnStmt.Rhss != null) {
            foreach (var rhs in returnStmt.Rhss) {
              if (rhs is ExprRhs returnExprRhs) {
                returnExprRhs.Expr = SimplifyExpression(returnExprRhs.Expr, state);
              }
            }
          }
          break;
        case HideRevealStmt hideRevealStmt:
          if (hideRevealStmt.Exprs != null) {
            for (var i = 0; i < hideRevealStmt.Exprs.Count; i++) {
              var exprToSimplify = hideRevealStmt.Exprs[i];
              if (exprToSimplify == null || !exprToSimplify.WasResolved()) {
                continue;
              }
              hideRevealStmt.Exprs[i] = SimplifyExpression(exprToSimplify, state);
            }
          }
          break;
        default:
          foreach (var sub in stmt.SubStatements) {
            Visit(sub, state);
          }
          break;
      }
      return false;
    }

    protected override bool VisitOneExpr(Expression expr, ref PartialEvalState state) {
      Expression result;
      switch (expr) {
        case ParensExpression parens:
          result = SimplifyExpression(parens.E, state);
          SetReplacement(parens, result);
          return false;
        case LiteralExpr:
          return false;
        case IdentifierExpr identifierExpr:
          if (identifierExpr.Var != null && TryLookupConst(identifierExpr.Var, out var constValue)) {
            result = constValue.CreateLiteral(identifierExpr.Origin, identifierExpr.Type);
            SetReplacement(identifierExpr, result);
          }
          return false;
        case UnaryOpExpr unary:
          unary.E = SimplifyExpression(unary.E, state);
          if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot &&
              Expression.IsBoolLiteral(unary.E, out var boolValue)) {
            result = Expression.CreateBoolLiteral(unary.Origin, !boolValue);
            SetReplacement(unary, result);
            return false;
          }
          if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SeqLength) {
            if (TryGetStringLiteral(unary.E, out var value, out var isVerbatim)) {
              result = CreateIntLiteral(unary.Origin, GetUnescapedStringLength(value, isVerbatim), unary.Type);
              SetReplacement(unary, result);
              return false;
            }
            if (TryGetSeqDisplayLiteral(unary.E, out var display)) {
              result = CreateIntLiteral(unary.Origin, display.Elements.Count, unary.Type);
              SetReplacement(unary, result);
              return false;
            }
          }
          if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SetCard) {
            if (TryGetSetDisplayLiteral(unary.E, out var display)) {
              if (display.Elements.Count <= 1 || AllElementsAreLiterals(display.Elements)) {
                var distinct = DistinctLiteralElements(display.Elements);
                result = CreateIntLiteral(unary.Origin, distinct.Count, unary.Type);
                SetReplacement(unary, result);
                return false;
              }
            }
          }
          if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.MultiSetCard) {
            if (TryGetMultiSetDisplayLiteral(unary.E, out var display)) {
              result = CreateIntLiteral(unary.Origin, display.Elements.Count, unary.Type);
              SetReplacement(unary, result);
              return false;
            }
          }
          return false;
        case BinaryExpr binary:
          binary.E0 = SimplifyExpression(binary.E0, state);
          binary.E1 = SimplifyExpression(binary.E1, state);
          result = engine.SimplifyBinary(binary);
          SetReplacement(binary, result);
          return false;
        case ITEExpr ite:
          ite.Test = SimplifyExpression(ite.Test, state);
          if (Expression.IsBoolLiteral(ite.Test, out var cond)) {
            result = SimplifyExpression(cond ? ite.Thn : ite.Els, state);
            SetReplacement(ite, result);
            return false;
          }
          ite.Thn = SimplifyExpression(ite.Thn, state);
          ite.Els = SimplifyExpression(ite.Els, state);
          return false;
        case FunctionCallExpr callExpr:
          callExpr.Receiver = SimplifyExpression(callExpr.Receiver, state);
          for (var i = 0; i < callExpr.Args.Count; i++) {
            callExpr.Args[i] = SimplifyExpression(callExpr.Args[i], state);
          }
          if (state.Depth > 0 && engine.TryInlineCall(callExpr, state, this, out var inlined)) {
            SetReplacement(callExpr, inlined);
            return false;
          }
          return false;
        case QuantifierExpr quantifierExpr:
          quantifierExpr.Range = quantifierExpr.Range == null
            ? null
            : SimplifyExpression(quantifierExpr.Range, state);
          quantifierExpr.Term = SimplifyExpression(quantifierExpr.Term, state);
          quantifierExpr.Bounds = SimplifyBounds(quantifierExpr.Bounds, state);
          return false;
        case LetExpr letExpr:
          for (var i = 0; i < letExpr.RHSs.Count; i++) {
            letExpr.RHSs[i] = SimplifyExpression(letExpr.RHSs[i], state);
          }
          if (letExpr.Exact) {
            EnterScope();
            try {
              var allLiteral = true;
              for (var i = 0; i < letExpr.LHSs.Count; i++) {
                var boundVar = letExpr.LHSs[i].Var;
                if (boundVar == null) {
                  allLiteral = false;
                  continue;
                }
                if (letExpr.RHSs[i] is LiteralExpr literal && ConstValue.TryCreate(literal, out var letConstValue)) {
                  SetConst(boundVar, letConstValue);
                } else {
                  allLiteral = false;
                }
              }
              var simplifiedBody = SimplifyExpression(letExpr.Body, state);
              letExpr.Body = simplifiedBody;
              if (allLiteral) {
                SetReplacement(letExpr, simplifiedBody);
              }
            }
            finally {
              ExitScope();
            }
          } else {
            letExpr.Body = SimplifyExpression(letExpr.Body, state);
          }
          return false;
        case SeqDisplayExpr seqDisplayExpr:
          for (var i = 0; i < seqDisplayExpr.Elements.Count; i++) {
            seqDisplayExpr.Elements[i] = SimplifyExpression(seqDisplayExpr.Elements[i], state);
          }
          return false;
        case SetDisplayExpr setDisplayExpr:
          for (var i = 0; i < setDisplayExpr.Elements.Count; i++) {
            setDisplayExpr.Elements[i] = SimplifyExpression(setDisplayExpr.Elements[i], state);
          }
          return false;
        case MultiSetDisplayExpr multiSetDisplayExpr:
          for (var i = 0; i < multiSetDisplayExpr.Elements.Count; i++) {
            multiSetDisplayExpr.Elements[i] = SimplifyExpression(multiSetDisplayExpr.Elements[i], state);
          }
          return false;
        case SeqSelectExpr seqSelectExpr:
          seqSelectExpr.Seq = SimplifyExpression(seqSelectExpr.Seq, state);
          if (seqSelectExpr.E0 != null) {
            seqSelectExpr.E0 = SimplifyExpression(seqSelectExpr.E0, state);
          }
          if (seqSelectExpr.E1 != null) {
            seqSelectExpr.E1 = SimplifyExpression(seqSelectExpr.E1, state);
          }
          if (seqSelectExpr.SelectOne) {
            if (TryGetStringLiteral(seqSelectExpr.Seq, out var strValue, out var strVerbatim) &&
                seqSelectExpr.E0 != null &&
                TryGetIntLiteralValue(seqSelectExpr.E0, out var index) &&
                TryGetUnescapedCharLiteral(strValue, strVerbatim, index, out var escapedChar)) {
              result = CreateCharLiteral(seqSelectExpr.Origin, escapedChar, seqSelectExpr.Type);
              SetReplacement(seqSelectExpr, result);
              return false;
            }
            if (TryGetSeqDisplayLiteral(seqSelectExpr.Seq, out var display) &&
                AllElementsAreLiterals(display) &&
                seqSelectExpr.E0 != null &&
                TryGetIntLiteralValue(seqSelectExpr.E0, out index) &&
                0 <= index && index < display.Elements.Count &&
                IsLiteralLike(display.Elements[index])) {
              SetReplacement(seqSelectExpr, display.Elements[index]);
              return false;
            }
            return false;
          }
          if (TryGetStringLiteral(seqSelectExpr.Seq, out var sourceString, out var sourceVerbatim)) {
            var unescapedLength = GetUnescapedStringLength(sourceString, sourceVerbatim);
            if (TryGetSliceBounds(seqSelectExpr, unescapedLength, out var start, out var end) &&
                TryGetStringSliceLiteral(sourceString, sourceVerbatim, start, end, out var slice)) {
              result = CreateStringLiteral(seqSelectExpr.Origin, slice, seqSelectExpr.Type, sourceVerbatim);
              SetReplacement(seqSelectExpr, result);
              return false;
            }
          }
          if (TryGetSeqDisplayLiteral(seqSelectExpr.Seq, out var sourceSeq) &&
              AllElementsAreLiterals(sourceSeq) &&
              TryGetSliceBounds(seqSelectExpr, sourceSeq.Elements.Count, out var seqStart, out var seqEnd)) {
            var sliced = sourceSeq.Elements.GetRange(seqStart, seqEnd - seqStart);
            result = CreateSeqDisplayLiteral(seqSelectExpr.Origin, sliced, seqSelectExpr.Type);
            SetReplacement(seqSelectExpr, result);
            return false;
          }
          return false;
        case SeqUpdateExpr seqUpdateExpr:
          seqUpdateExpr.Seq = SimplifyExpression(seqUpdateExpr.Seq, state);
          seqUpdateExpr.Index = SimplifyExpression(seqUpdateExpr.Index, state);
          seqUpdateExpr.Value = SimplifyExpression(seqUpdateExpr.Value, state);
          return false;
        default:
          return false;
      }
    }

    private static bool TryGetSliceBounds(SeqSelectExpr expr, int length, out int start, out int end) {
      start = 0;
      end = length;
      if (expr.E0 != null && !TryGetIntLiteralValue(expr.E0, out start)) {
        return false;
      }
      if (expr.E1 != null && !TryGetIntLiteralValue(expr.E1, out end)) {
        return false;
      }
      return 0 <= start && start <= end && end <= length;
    }

    private List<BoundedPool> SimplifyBounds(List<BoundedPool> bounds, PartialEvalState state) {
      if (bounds == null) {
        return null;
      }
      var changed = false;
      var newBounds = new List<BoundedPool>(bounds.Count);
      foreach (var bound in bounds) {
        var simplified = SimplifyBoundedPool(bound, state);
        if (!ReferenceEquals(simplified, bound)) {
          changed = true;
        }
        newBounds.Add(simplified);
      }
      return changed ? newBounds : bounds;
    }

    private BoundedPool SimplifyBoundedPool(BoundedPool bound, PartialEvalState state) {
      switch (bound) {
        case IntBoundedPool intPool: {
            var lower = intPool.LowerBound == null ? null : SimplifyExpression(intPool.LowerBound, state);
            var upper = intPool.UpperBound == null ? null : SimplifyExpression(intPool.UpperBound, state);
            if (lower != intPool.LowerBound || upper != intPool.UpperBound) {
              return new IntBoundedPool(lower, upper);
            }
            return bound;
          }
        case SetBoundedPool setPool: {
            var set = SimplifyExpression(setPool.Set, state);
            return set != setPool.Set
              ? new SetBoundedPool(set, setPool.BoundVariableType, setPool.CollectionElementType, setPool.IsFiniteCollection)
              : bound;
          }
        case SubSetBoundedPool subSet: {
            var upper = SimplifyExpression(subSet.UpperBound, state);
            return upper != subSet.UpperBound
              ? new SubSetBoundedPool(upper, subSet.IsFiniteCollection)
              : bound;
          }
        case SuperSetBoundedPool superSet: {
            var lower = SimplifyExpression(superSet.LowerBound, state);
            return lower != superSet.LowerBound
              ? new SuperSetBoundedPool(lower)
              : bound;
          }
        case SeqBoundedPool seqPool: {
            var seq = SimplifyExpression(seqPool.Seq, state);
            return seq != seqPool.Seq
              ? new SeqBoundedPool(seq, seqPool.BoundVariableType, seqPool.CollectionElementType)
              : bound;
          }
        case MapBoundedPool mapPool: {
            var map = SimplifyExpression(mapPool.Map, state);
            return map != mapPool.Map
              ? new MapBoundedPool(map, mapPool.BoundVariableType, mapPool.CollectionElementType, mapPool.IsFiniteCollection)
              : bound;
          }
        case MultiSetBoundedPool multiSetPool: {
            var multiset = SimplifyExpression(multiSetPool.MultiSet, state);
            return multiset != multiSetPool.MultiSet
              ? new MultiSetBoundedPool(multiset, multiSetPool.BoundVariableType, multiSetPool.CollectionElementType)
              : bound;
          }
        default:
          return bound;
      }
    }

    private readonly record struct ConstValue(CachedLiteralKind Kind, BigInteger IntValue, bool BoolValue) {
      public static bool TryCreate(LiteralExpr literal, out ConstValue cached) {
        cached = default;
        if (literal == null) {
          return false;
        }

        if (Expression.IsIntLiteral(literal, out var intValue)) {
          cached = new ConstValue(CachedLiteralKind.Int, intValue, default);
          return true;
        }

        if (Expression.IsBoolLiteral(literal, out var boolValue)) {
          cached = new ConstValue(CachedLiteralKind.Bool, default, boolValue);
          return true;
        }

        return false;
      }

      public Expression CreateLiteral(IOrigin origin, Type type) {
        // Preserve the resolved type from the original use site to avoid introducing null/incorrect types
        // (for example, when the variable is a subset type).
        return Kind switch {
          CachedLiteralKind.Int => new LiteralExpr(origin, IntValue) { Type = type },
          CachedLiteralKind.Bool => new LiteralExpr(origin, BoolValue) { Type = type },
          _ => null
        };
      }
    }
  }
}
