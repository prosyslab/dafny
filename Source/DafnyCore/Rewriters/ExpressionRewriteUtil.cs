#nullable enable

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// Shared helpers for rewriters that transform resolved expressions/statements.
/// Keep these small and dependency-free so they can be reused across rewriters.
/// </summary>
internal static class ExpressionRewriteUtil {
  internal static void RewriteExprInPlaceList(IList<Expression>? exprs, Func<Expression, Expression> rewriter) {
    if (exprs == null) {
      return;
    }
    for (var i = 0; i < exprs.Count; i++) {
      exprs[i] = rewriter(exprs[i]);
    }
  }

  internal static void RewriteFrameExprsInPlace(IList<FrameExpression>? exprs, Func<Expression, Expression> rewriter) {
    if (exprs == null) {
      return;
    }
    for (var i = 0; i < exprs.Count; i++) {
      // FrameExpression.E is derived (read-only). Mutate DesugaredExpression to affect E.
      exprs[i].DesugaredExpression = rewriter(exprs[i].E);
    }
  }

  internal static void RewriteAttributedExprsInPlace(IEnumerable<AttributedExpression> exprs, Func<Expression, Expression> rewriter) {
    foreach (var expr in exprs) {
      expr.E = rewriter(expr.E);
    }
  }

  internal static void EnsureExpressionType(Expression expr, Type type) {
    if (expr.Type == null) {
      expr.Type = type;
    }
  }

  internal static Expression StripConcreteSyntax(Expression expr) {
    if (expr is ConcreteSyntaxExpression concreteSyntaxExpression && concreteSyntaxExpression.ResolvedExpression != null) {
      return concreteSyntaxExpression.ResolvedExpression;
    }
    if (expr is ParensExpression parens && parens.ResolvedExpression != null) {
      return parens.ResolvedExpression;
    }
    return expr;
  }

  /// <summary>
  /// Recursively walks the expression tree, rewriting children bottom-up via type-specific field dispatch.
  /// For each node, first recurse into children, then call <paramref name="rewriter"/> on the node itself.
  /// Returns the (possibly replaced) expression.
  /// </summary>
  internal static Expression RewriteExpressionsInPlace(Expression? expr, Func<Expression, Expression> rewriter) {
    if (expr == null) {
      return null!;
    }

    switch (expr) {
      // Syntax wrappers: rewrite resolved expression in-place, keep wrapper stable.
      case ParensExpression parens:
        if (parens.E != null) {
          parens.E = RewriteExpressionsInPlace(parens.E, rewriter);
        }
        if (parens.ResolvedExpression != null) {
          parens.ResolvedExpression = RewriteExpressionsInPlace(parens.ResolvedExpression, rewriter);
        }
        return rewriter(expr);

      case ConcreteSyntaxExpression concreteSyntax:
        if (concreteSyntax.ResolvedExpression != null) {
          concreteSyntax.ResolvedExpression = RewriteExpressionsInPlace(concreteSyntax.ResolvedExpression, rewriter);
        }
        return rewriter(expr);

      // Leaf nodes: no children to recurse into.
      case LiteralExpr:
      case IdentifierExpr:
      case ThisExpr:
      case WildcardExpr:
        return rewriter(expr);

      // Binary/unary/conditional operators.
      case BinaryExpr binary:
        binary.E0 = RewriteExpressionsInPlace(binary.E0, rewriter);
        binary.E1 = RewriteExpressionsInPlace(binary.E1, rewriter);
        return rewriter(expr);

      case UnaryExpr unary:
        unary.E = RewriteExpressionsInPlace(unary.E, rewriter);
        return rewriter(expr);

      case ITEExpr ite:
        ite.Test = RewriteExpressionsInPlace(ite.Test, rewriter);
        ite.Thn = RewriteExpressionsInPlace(ite.Thn, rewriter);
        ite.Els = RewriteExpressionsInPlace(ite.Els, rewriter);
        return rewriter(expr);

      case TernaryExpr ternary:
        ternary.E0 = RewriteExpressionsInPlace(ternary.E0, rewriter);
        ternary.E1 = RewriteExpressionsInPlace(ternary.E1, rewriter);
        ternary.E2 = RewriteExpressionsInPlace(ternary.E2, rewriter);
        return rewriter(expr);

      // Comprehensions (quantifiers, set/map comprehensions, lambdas).
      case MapComprehension mapComp:
        if (mapComp.Range != null) {
          mapComp.Range = RewriteExpressionsInPlace(mapComp.Range, rewriter);
        }
        mapComp.Term = RewriteExpressionsInPlace(mapComp.Term, rewriter);
        if (mapComp.TermLeft != null) {
          mapComp.TermLeft = RewriteExpressionsInPlace(mapComp.TermLeft, rewriter);
        }
        return rewriter(expr);

      case ComprehensionExpr comprehension:
        if (comprehension.Range != null) {
          comprehension.Range = RewriteExpressionsInPlace(comprehension.Range, rewriter);
        }
        comprehension.Term = RewriteExpressionsInPlace(comprehension.Term, rewriter);
        return rewriter(expr);

      // Let expressions.
      case LetExpr letExpr:
        for (var i = 0; i < letExpr.RHSs.Count; i++) {
          letExpr.RHSs[i] = RewriteExpressionsInPlace(letExpr.RHSs[i], rewriter);
        }
        letExpr.Body = RewriteExpressionsInPlace(letExpr.Body, rewriter);
        return rewriter(expr);

      // Function/method calls and applications.
      case FunctionCallExpr callExpr:
        callExpr.Receiver = RewriteExpressionsInPlace(callExpr.Receiver, rewriter);
        for (var i = 0; i < callExpr.Bindings.ArgumentBindings.Count; i++) {
          callExpr.Bindings.ArgumentBindings[i].Actual =
            RewriteExpressionsInPlace(callExpr.Bindings.ArgumentBindings[i].Actual, rewriter);
        }
        return rewriter(expr);

      case ApplyExpr applyExpr:
        applyExpr.Function = RewriteExpressionsInPlace(applyExpr.Function, rewriter);
        for (var i = 0; i < applyExpr.Args.Count; i++) {
          applyExpr.Args[i] = RewriteExpressionsInPlace(applyExpr.Args[i], rewriter);
        }
        return rewriter(expr);

      case MemberSelectExpr memberSelect:
        memberSelect.Obj = RewriteExpressionsInPlace(memberSelect.Obj, rewriter);
        return rewriter(expr);

      // Collection operations.
      case SeqSelectExpr seqSelect:
        seqSelect.Seq = RewriteExpressionsInPlace(seqSelect.Seq, rewriter);
        if (seqSelect.E0 != null) {
          seqSelect.E0 = RewriteExpressionsInPlace(seqSelect.E0, rewriter);
        }
        if (seqSelect.E1 != null) {
          seqSelect.E1 = RewriteExpressionsInPlace(seqSelect.E1, rewriter);
        }
        return rewriter(expr);

      case SeqUpdateExpr seqUpdate:
        seqUpdate.Seq = RewriteExpressionsInPlace(seqUpdate.Seq, rewriter);
        seqUpdate.Index = RewriteExpressionsInPlace(seqUpdate.Index, rewriter);
        seqUpdate.Value = RewriteExpressionsInPlace(seqUpdate.Value, rewriter);
        return rewriter(expr);

      case SeqConstructionExpr seqConstruction:
        seqConstruction.N = RewriteExpressionsInPlace(seqConstruction.N, rewriter);
        seqConstruction.Initializer = RewriteExpressionsInPlace(seqConstruction.Initializer, rewriter);
        return rewriter(expr);

      case MultiSelectExpr multiSelect:
        multiSelect.Array = RewriteExpressionsInPlace(multiSelect.Array, rewriter);
        for (var i = 0; i < multiSelect.Indices.Count; i++) {
          multiSelect.Indices[i] = RewriteExpressionsInPlace(multiSelect.Indices[i], rewriter);
        }
        return rewriter(expr);

      // Display expressions (sequence, set, multiset literals).
      case MapDisplayExpr mapDisplay:
        for (var i = 0; i < mapDisplay.Elements.Count; i++) {
          mapDisplay.Elements[i].A = RewriteExpressionsInPlace(mapDisplay.Elements[i].A, rewriter);
          mapDisplay.Elements[i].B = RewriteExpressionsInPlace(mapDisplay.Elements[i].B, rewriter);
        }
        return rewriter(expr);

      case DisplayExpression display:
        for (var i = 0; i < display.Elements.Count; i++) {
          display.Elements[i] = RewriteExpressionsInPlace(display.Elements[i], rewriter);
        }
        return rewriter(expr);

      // Datatype constructors.
      case DatatypeValue datatypeValue:
        for (var i = 0; i < datatypeValue.Bindings.ArgumentBindings.Count; i++) {
          datatypeValue.Bindings.ArgumentBindings[i].Actual =
            RewriteExpressionsInPlace(datatypeValue.Bindings.ArgumentBindings[i].Actual, rewriter);
        }
        return rewriter(expr);

      // Misc expression types with mutable fields.
      case MultiSetFormingExpr multiSetForming:
        multiSetForming.E = RewriteExpressionsInPlace(multiSetForming.E, rewriter);
        return rewriter(expr);

      case BoxingCastExpr boxingCast:
        boxingCast.E = RewriteExpressionsInPlace(boxingCast.E, rewriter);
        return rewriter(expr);

      case UnboxingCastExpr unboxingCast:
        unboxingCast.E = RewriteExpressionsInPlace(unboxingCast.E, rewriter);
        return rewriter(expr);

      // StmtExpr: has both a statement and an expression.
      case StmtExpr stmtExpr:
        RewriteExpressionsInStmtInPlace(stmtExpr.S, rewriter);
        stmtExpr.E = RewriteExpressionsInPlace(stmtExpr.E, rewriter);
        return rewriter(expr);

      // Default fallback: best-effort traverse via SubExpressions (read-only, cannot replace parent field).
      default:
        foreach (var child in expr.SubExpressions) {
          if (child != null) {
            RewriteExpressionsInPlace(child, rewriter);
          }
        }
        return rewriter(expr);
    }
  }

  /// <summary>
  /// Recursively walks a statement tree, rewriting all expression fields in-place via type-specific dispatch
  /// and recursing into sub-statements.
  /// </summary>
  internal static void RewriteExpressionsInStmtInPlace(Statement? stmt, Func<Expression, Expression> exprRewriter) {
    if (stmt == null) {
      return;
    }

    switch (stmt) {
      case BlockStmt blockStmt:
        foreach (var s in blockStmt.Body) {
          RewriteExpressionsInStmtInPlace(s, exprRewriter);
        }
        break;

      case IfStmt ifStmt:
        if (ifStmt.Guard != null) {
          ifStmt.Guard = RewriteExpressionsInPlace(ifStmt.Guard, exprRewriter);
        }
        RewriteExpressionsInStmtInPlace(ifStmt.Thn, exprRewriter);
        RewriteExpressionsInStmtInPlace(ifStmt.Els, exprRewriter);
        break;

      case AlternativeStmt altStmt:
        foreach (var alt in altStmt.Alternatives) {
          alt.Guard = RewriteExpressionsInPlace(alt.Guard, exprRewriter);
          foreach (var s in alt.Body) {
            RewriteExpressionsInStmtInPlace(s, exprRewriter);
          }
        }
        break;

      case WhileStmt whileStmt:
        RewriteLoopSpecInPlace(whileStmt, exprRewriter);
        if (whileStmt.Guard != null) {
          whileStmt.Guard = RewriteExpressionsInPlace(whileStmt.Guard, exprRewriter);
        }
        RewriteExpressionsInStmtInPlace(whileStmt.Body, exprRewriter);
        break;

      case ForLoopStmt forLoop:
        RewriteLoopSpecInPlace(forLoop, exprRewriter);
        forLoop.Start = RewriteExpressionsInPlace(forLoop.Start, exprRewriter);
        if (forLoop.End != null) {
          forLoop.End = RewriteExpressionsInPlace(forLoop.End, exprRewriter);
        }
        RewriteExpressionsInStmtInPlace(forLoop.Body, exprRewriter);
        break;

      case OneBodyLoopStmt loopStmt:
        RewriteLoopSpecInPlace(loopStmt, exprRewriter);
        RewriteExpressionsInStmtInPlace(loopStmt.Body, exprRewriter);
        break;

      case AlternativeLoopStmt altLoop:
        RewriteLoopSpecInPlace(altLoop, exprRewriter);
        foreach (var alt in altLoop.Alternatives) {
          alt.Guard = RewriteExpressionsInPlace(alt.Guard, exprRewriter);
          foreach (var s in alt.Body) {
            RewriteExpressionsInStmtInPlace(s, exprRewriter);
          }
        }
        break;

      case AssertStmt assertStmt:
        assertStmt.Expr = RewriteExpressionsInPlace(assertStmt.Expr, exprRewriter);
        break;

      case AssumeStmt assumeStmt:
        assumeStmt.Expr = RewriteExpressionsInPlace(assumeStmt.Expr, exprRewriter);
        break;

      case ExpectStmt expectStmt:
        expectStmt.Expr = RewriteExpressionsInPlace(expectStmt.Expr, exprRewriter);
        if (expectStmt.Message != null) {
          expectStmt.Message = RewriteExpressionsInPlace(expectStmt.Message, exprRewriter);
        }
        break;

      case PrintStmt printStmt:
        for (var i = 0; i < printStmt.Args.Count; i++) {
          printStmt.Args[i] = RewriteExpressionsInPlace(printStmt.Args[i], exprRewriter);
        }
        break;

      case CallStmt callStmt:
        callStmt.MethodSelect.Obj = RewriteExpressionsInPlace(callStmt.MethodSelect.Obj, exprRewriter);
        for (var i = 0; i < callStmt.Bindings.ArgumentBindings.Count; i++) {
          callStmt.Bindings.ArgumentBindings[i].Actual =
            RewriteExpressionsInPlace(callStmt.Bindings.ArgumentBindings[i].Actual, exprRewriter);
        }
        break;

      case VarDeclStmt varDecl:
        RewriteExpressionsInStmtInPlace(varDecl.Assign, exprRewriter);
        break;

      case SingleAssignStmt singleAssign:
        singleAssign.Lhs = RewriteExpressionsInPlace(singleAssign.Lhs, exprRewriter);
        RewriteAssignmentRhsInPlace(singleAssign.Rhs, exprRewriter);
        break;

      case AssignStatement assignStmt:
        for (var i = 0; i < assignStmt.Lhss.Count; i++) {
          assignStmt.Lhss[i] = RewriteExpressionsInPlace(assignStmt.Lhss[i], exprRewriter);
        }
        for (var i = 0; i < assignStmt.Rhss.Count; i++) {
          RewriteAssignmentRhsInPlace(assignStmt.Rhss[i], exprRewriter);
        }
        break;

      case AssignSuchThatStmt assignSuchThat:
        for (var i = 0; i < assignSuchThat.Lhss.Count; i++) {
          assignSuchThat.Lhss[i] = RewriteExpressionsInPlace(assignSuchThat.Lhss[i], exprRewriter);
        }
        assignSuchThat.Expr = RewriteExpressionsInPlace(assignSuchThat.Expr, exprRewriter);
        break;

      case AssignOrReturnStmt assignOrReturn:
        for (var i = 0; i < assignOrReturn.Lhss.Count; i++) {
          assignOrReturn.Lhss[i] = RewriteExpressionsInPlace(assignOrReturn.Lhss[i], exprRewriter);
        }
        RewriteAssignmentRhsInPlace(assignOrReturn.Rhs, exprRewriter);
        for (var i = 0; i < assignOrReturn.Rhss.Count; i++) {
          RewriteAssignmentRhsInPlace(assignOrReturn.Rhss[i], exprRewriter);
        }
        break;

      case ReturnStmt returnStmt:
        RewriteExpressionsInStmtInPlace(returnStmt.HiddenUpdate, exprRewriter);
        break;

      case YieldStmt yieldStmt:
        RewriteExpressionsInStmtInPlace(yieldStmt.HiddenUpdate, exprRewriter);
        break;

      case ForallStmt forallStmt:
        forallStmt.Range = RewriteExpressionsInPlace(forallStmt.Range, exprRewriter);
        RewriteAttributedExprsInPlace(forallStmt.Ens, exprRewriter);
        RewriteExpressionsInStmtInPlace(forallStmt.Body, exprRewriter);
        break;

      case CalcStmt calcStmt:
        for (var i = 0; i < calcStmt.Lines.Count; i++) {
          calcStmt.Lines[i] = RewriteExpressionsInPlace(calcStmt.Lines[i], exprRewriter);
        }
        foreach (var hint in calcStmt.Hints) {
          RewriteExpressionsInStmtInPlace(hint, exprRewriter);
        }
        break;

      case HideRevealStmt hideRevealStmt:
        if (hideRevealStmt.Exprs != null) {
          for (var i = 0; i < hideRevealStmt.Exprs.Count; i++) {
            hideRevealStmt.Exprs[i] = RewriteExpressionsInPlace(hideRevealStmt.Exprs[i], exprRewriter);
          }
        }
        break;

      // Default fallback: best-effort via SubExpressions (read-only) and SubStatements.
      default:
        foreach (var subExpr in stmt.SubExpressions) {
          if (subExpr != null) {
            RewriteExpressionsInPlace(subExpr, exprRewriter);
          }
        }
        foreach (var subStmt in stmt.SubStatements) {
          RewriteExpressionsInStmtInPlace(subStmt, exprRewriter);
        }
        break;
    }
  }

  private static void RewriteLoopSpecInPlace(LoopStmt loopStmt, Func<Expression, Expression> exprRewriter) {
    foreach (var inv in loopStmt.Invariants) {
      inv.E = RewriteExpressionsInPlace(inv.E, exprRewriter);
    }
    var decreasesExprs = loopStmt.Decreases?.Expressions;
    if (decreasesExprs != null) {
      for (var i = 0; i < decreasesExprs.Count; i++) {
        decreasesExprs[i] = RewriteExpressionsInPlace(decreasesExprs[i], exprRewriter);
      }
    }
    RewriteFrameExprsInPlace(loopStmt.Mod?.Expressions, exprRewriter);
  }

  private static void RewriteAssignmentRhsInPlace(AssignmentRhs? rhs, Func<Expression, Expression> exprRewriter) {
    if (rhs is ExprRhs exprRhs) {
      exprRhs.Expr = RewriteExpressionsInPlace(exprRhs.Expr, exprRewriter);
    }
  }
}
