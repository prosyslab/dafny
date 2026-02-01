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
    var partialEvaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth);
    var engine = new UnrollEngine(program.SystemModuleManager, maxInstances, partialEvaluator);
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      engine.Rewrite(decl);
    }
  }

  internal sealed class UnrollEngine {
    private readonly uint maxInstances;
    private readonly PartialEvaluatorEngine partialEvaluator;
    private readonly QuantifierBounds quantifierBounds;
    private readonly UnrollCloner cloner;
    internal uint MaxInstances => maxInstances;

    internal UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances, PartialEvaluatorEngine partialEvaluator) {
      ArgumentNullException.ThrowIfNull(systemModuleManager);
      this.maxInstances = maxInstances;
      this.partialEvaluator = partialEvaluator ?? throw new ArgumentNullException(nameof(partialEvaluator));
      quantifierBounds = new QuantifierBounds(systemModuleManager, maxInstances);
      cloner = new UnrollCloner(quantifierBounds, partialEvaluator.SimplifyExpression);
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
          method.SetBody((BlockLikeStmt)RewriteStmt(method.Body));
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
            iterator.Body = (BlockStmt)RewriteStmt(iterator.Body);
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
      return cloner.CloneStmt(stmt, isReference: false);
    }

    // NOTE: This method is invoked via reflection in tests (BindingFlags.NonPublic).
    private Expression RewriteExpr(Expression expr) {
      ArgumentNullException.ThrowIfNull(expr);
      if (!ContainsQuantifier(expr)) {
        return expr;
      }
      return cloner.CloneExpr(expr);
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

    private sealed class UnrollCloner : Cloner {
      private readonly QuantifierBounds quantifierBounds;
      private readonly Func<Expression, Expression> simplifyAfterSubst;

      public UnrollCloner(QuantifierBounds quantifierBounds, Func<Expression, Expression> simplifyAfterSubst)
        : base(cloneLiteralModuleDefinition: false, cloneResolvedFields: true) {
        this.quantifierBounds = quantifierBounds ?? throw new ArgumentNullException(nameof(quantifierBounds));
        this.simplifyAfterSubst = simplifyAfterSubst ?? throw new ArgumentNullException(nameof(simplifyAfterSubst));
      }

      public override Expression CloneExpr(Expression expr) {
        if (expr == null) {
          return null!;
        }
        // Keep concrete syntax nodes stable; just rewrite their resolved expression.
        if (expr is ConcreteSyntaxExpression concreteSyntaxExpression) {
          if (concreteSyntaxExpression.ResolvedExpression != null) {
            var clonedResolved = CloneExpr(concreteSyntaxExpression.ResolvedExpression);
            if (clonedResolved != null) {
              concreteSyntaxExpression.ResolvedExpression = clonedResolved;
            }
          }
          return expr;
        }

        // Keep parentheses stable for tests and debugging.
        if (expr is ParensExpression parens) {
          if (parens.E != null) {
            var clonedE = CloneExpr(parens.E);
            if (clonedE != null) {
              parens.E = clonedE;
            }
          }
          if (parens.ResolvedExpression != null) {
            var clonedResolved = CloneExpr(parens.ResolvedExpression);
            if (clonedResolved != null) {
              parens.ResolvedExpression = clonedResolved;
            }
          }
          return expr;
        }

        if (expr is QuantifierExpr quantifierExpr &&
            quantifierBounds.TryUnrollQuantifier(quantifierExpr, simplifyAfterSubst, out var rewritten) &&
            !ReferenceEquals(rewritten, quantifierExpr)) {
          if (rewritten == null) {
            return expr;
          }
          return rewritten;
        }

        // Some internal/translation expressions do not implement ICloneable<Expression>.
        // Best-effort: traverse to rewrite nested quantifiers, but keep the node unchanged.
        if (expr is not ICloneable<Expression>) {
          foreach (var child in expr.SubExpressions) {
            if (child != null) {
              _ = CloneExpr(child);
            }
          }
          return expr;
        }

        return base.CloneExpr(expr);
      }
    }
  }
}
