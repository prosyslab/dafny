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
}
