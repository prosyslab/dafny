#nullable enable

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// When verifying, expand bounded quantifiers over int/nat by enumerating all values when bounds are concrete.
/// Controlled by --unroll-bounded-quantifiers (per-quantifier max-instances cap).
/// </summary>
public sealed class UnrollBoundedQuantifiersRewriter : IRewriter {
  private readonly Program program;

  public UnrollBoundedQuantifiersRewriter(Program program, ErrorReporter reporter) : base(reporter) {
    this.program = program ?? throw new ArgumentNullException(nameof(program));
  }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    if (!Reporter.Options.Options.OptionArguments.ContainsKey(CommonOptionBag.UnrollBoundedQuantifiers)) {
      return;
    }
    var maxInstances = Reporter.Options.Get(CommonOptionBag.UnrollBoundedQuantifiers);
    var inlineDepth = Reporter.Options.Get(CommonOptionBag.PartialEvalInlineDepth);
    var effectiveScope = Type.GetScope() ?? moduleDefinition.VisibilityScope;
    var partialEvaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth, effectiveScope);
    var engine = new UnrollEngine(program.SystemModuleManager, maxInstances, partialEvaluator);
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      engine.Rewrite(decl);
    }
  }

  internal sealed class UnrollEngine {
    private readonly uint maxInstances;
    private readonly PartialEvaluatorEngine partialEvaluator;
    private readonly QuantifierBounds quantifierBounds;
    internal uint MaxInstances => maxInstances;

    internal UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances, PartialEvaluatorEngine partialEvaluator) {
      ArgumentNullException.ThrowIfNull(systemModuleManager);
      this.maxInstances = maxInstances;
      this.partialEvaluator = partialEvaluator ?? throw new ArgumentNullException(nameof(partialEvaluator));
      quantifierBounds = new QuantifierBounds(systemModuleManager, maxInstances);
    }

    public void Rewrite(ICallable decl) {
      switch (decl) {
        case Function { Body: not null } function:
          function.Body = RewriteExpr(function.Body);
          RewriteAttributedExprsInPlace(function.Req, RewriteExpr);
          RewriteAttributedExprsInPlace(function.Ens, RewriteExpr);
          RewriteFrameExprsInPlace(function.Reads.Expressions, RewriteExpr);
          RewriteExprInPlaceList(function.Decreases.Expressions, RewriteExpr);
          break;
        case MethodOrConstructor { Body: not null } method:
          RewriteAttributedExprsInPlace(method.Req, RewriteExpr);
          RewriteAttributedExprsInPlace(method.Ens, RewriteExpr);
          RewriteFrameExprsInPlace(method.Reads.Expressions, RewriteExpr);
          RewriteFrameExprsInPlace(method.Mod.Expressions, RewriteExpr);
          RewriteExprInPlaceList(method.Decreases.Expressions, RewriteExpr);
          RewriteStmt(method.Body);
          break;
        case IteratorDecl iterator:
          RewriteAttributedExprsInPlace(iterator.Requires, RewriteExpr);
          RewriteAttributedExprsInPlace(iterator.Ensures, RewriteExpr);
          RewriteFrameExprsInPlace(iterator.Reads.Expressions, RewriteExpr);
          RewriteFrameExprsInPlace(iterator.Modifies.Expressions, RewriteExpr);
          RewriteExprInPlaceList(iterator.Decreases.Expressions, RewriteExpr);
          RewriteAttributedExprsInPlace(iterator.YieldRequires, RewriteExpr);
          RewriteAttributedExprsInPlace(iterator.YieldEnsures, RewriteExpr);
          if (iterator.Body != null) {
            RewriteStmt(iterator.Body);
          }
          break;
      }
    }

    private static void RewriteExprInPlaceList(IList<Expression>? exprs, Func<Expression, Expression> rewriter) {
      ExpressionRewriteUtil.RewriteExprInPlaceList(exprs, rewriter);
    }

    private static void RewriteFrameExprsInPlace(IList<FrameExpression>? exprs, Func<Expression, Expression> rewriter) {
      ExpressionRewriteUtil.RewriteFrameExprsInPlace(exprs, rewriter);
    }

    private static void RewriteAttributedExprsInPlace(IEnumerable<AttributedExpression> exprs, Func<Expression, Expression> rewriter) {
      ExpressionRewriteUtil.RewriteAttributedExprsInPlace(exprs, rewriter);
    }

    // NOTE: This method is invoked via reflection in tests (BindingFlags.NonPublic).
    private Statement RewriteStmt(Statement stmt) {
      ArgumentNullException.ThrowIfNull(stmt);
      if (!ContainsQuantifier(stmt)) {
        return stmt;
      }
      ExpressionRewriteUtil.RewriteExpressionsInStmtInPlace(stmt, TryRewriteQuantifier);
      return stmt;
    }

    // NOTE: This method is invoked via reflection in tests (BindingFlags.NonPublic).
    private Expression RewriteExpr(Expression expr) {
      ArgumentNullException.ThrowIfNull(expr);
      if (!ContainsQuantifier(expr)) {
        return expr;
      }
      return ExpressionRewriteUtil.RewriteExpressionsInPlace(expr, TryRewriteQuantifier);
    }

    private Expression TryRewriteQuantifier(Expression expr) {
      if (expr is QuantifierExpr quantifierExpr &&
          quantifierBounds.TryUnrollQuantifier(quantifierExpr, partialEvaluator.SimplifyExpression, out var rewritten) &&
          !ReferenceEquals(rewritten, quantifierExpr) &&
          rewritten != null) {
        return rewritten;
      }
      return expr;
    }

    private static bool ContainsQuantifier(Statement stmt) {
      if (stmt == null) {
        return false;
      }
      foreach (var expr in stmt.SubExpressions) {
        if (ContainsQuantifier(expr)) {
          return true;
        }
      }
      foreach (var nested in stmt.SubStatements) {
        if (ContainsQuantifier(nested)) {
          return true;
        }
      }
      return false;
    }

    private static bool ContainsQuantifier(Expression expr) {
      if (expr == null) {
        return false;
      }
      if (expr is QuantifierExpr) {
        return true;
      }
      foreach (var subExpr in expr.SubExpressions) {
        if (ContainsQuantifier(subExpr)) {
          return true;
        }
      }
      return false;
    }

    internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, out Expression rewritten) {
      return quantifierBounds.TryUnrollQuantifier(quantifierExpr, partialEvaluator.SimplifyExpression, out rewritten);
    }
  }
}
