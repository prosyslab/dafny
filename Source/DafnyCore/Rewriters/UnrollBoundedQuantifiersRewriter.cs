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
    private readonly SystemModuleManager systemModuleManager;
    private readonly uint maxInstances;
    private readonly PartialEvaluatorEngine partialEvaluator;
    private readonly QuantifierBounds quantifierBounds;
    internal uint MaxInstances => maxInstances;

    internal UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances, PartialEvaluatorEngine partialEvaluator) {
      this.systemModuleManager = systemModuleManager ?? throw new ArgumentNullException(nameof(systemModuleManager));
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

    private void RewriteStmt(Statement stmt) {
      switch (stmt) {
        case BlockStmt block:
          foreach (var s in block.Body) {
            RewriteStmt(s);
          }
          break;
        case DividedBlockStmt dividedBlock:
          foreach (var s in dividedBlock.BodyInit) {
            RewriteStmt(s);
          }
          foreach (var s in dividedBlock.BodyProper) {
            RewriteStmt(s);
          }
          break;
        case IfStmt ifStmt:
          if (ifStmt.Guard != null) {
            ifStmt.Guard = RewriteExpr(ifStmt.Guard);
          }
          RewriteStmt(ifStmt.Thn);
          if (ifStmt.Els != null) {
            RewriteStmt(ifStmt.Els);
          }
          break;
        case WhileStmt whileStmt:
          if (whileStmt.Guard != null) {
            whileStmt.Guard = RewriteExpr(whileStmt.Guard);
          }
          RewriteAttributedExprsInPlace(whileStmt.Invariants, RewriteExpr);
          if (whileStmt.Decreases?.Expressions != null) {
            RewriteExprInPlaceList(whileStmt.Decreases.Expressions, RewriteExpr);
          }
          if (whileStmt.Mod != null) {
            RewriteFrameExprsInPlace(whileStmt.Mod.Expressions, RewriteExpr);
          }
          if (whileStmt.Body != null) {
            RewriteStmt(whileStmt.Body);
          }
          break;
        case AlternativeLoopStmt alternativeLoop:
          if (alternativeLoop.Decreases?.Expressions != null) {
            RewriteExprInPlaceList(alternativeLoop.Decreases.Expressions, RewriteExpr);
          }
          foreach (var inv in alternativeLoop.Invariants) {
            inv.E = RewriteExpr(inv.E);
          }
          if (alternativeLoop.Mod != null) {
            RewriteFrameExprsInPlace(alternativeLoop.Mod.Expressions, RewriteExpr);
          }
          foreach (var alternative in alternativeLoop.Alternatives) {
            alternative.Guard = RewriteExpr(alternative.Guard);
            foreach (var s in alternative.Body) {
              RewriteStmt(s);
            }
          }
          break;
        case ForLoopStmt forLoop:
          if (forLoop.Start != null) {
            forLoop.Start = RewriteExpr(forLoop.Start);
          }
          if (forLoop.End != null) {
            forLoop.End = RewriteExpr(forLoop.End);
          }
          RewriteAttributedExprsInPlace(forLoop.Invariants, RewriteExpr);
          if (forLoop.Decreases?.Expressions != null) {
            RewriteExprInPlaceList(forLoop.Decreases.Expressions, RewriteExpr);
          }
          if (forLoop.Body != null) {
            RewriteStmt(forLoop.Body);
          }
          break;
        case ForallStmt forallStmt:
          if (forallStmt.Range != null) {
            forallStmt.Range = RewriteExpr(forallStmt.Range);
          }
          RewriteAttributedExprsInPlace(forallStmt.Ens, RewriteExpr);
          if (forallStmt.Body != null) {
            RewriteStmt(forallStmt.Body);
          }
          // Bounds are discovered during resolution; we still rewrite any expressions inside them (best-effort).
          RewriteBoundsInPlace(forallStmt.Bounds);
          break;
        case AssertStmt assertStmt:
          assertStmt.Expr = RewriteExpr(assertStmt.Expr);
          break;
        case AssumeStmt assumeStmt:
          assumeStmt.Expr = RewriteExpr(assumeStmt.Expr);
          break;
        case ExpectStmt expectStmt:
          expectStmt.Expr = RewriteExpr(expectStmt.Expr);
          if (expectStmt.Message != null) {
            expectStmt.Message = RewriteExpr(expectStmt.Message);
          }
          break;
        case SingleAssignStmt singleAssign: {
            singleAssign.Lhs = RewriteExpr(singleAssign.Lhs);
            if (singleAssign.Rhs is ExprRhs singleAssignExprRhs) {
              singleAssignExprRhs.Expr = RewriteExpr(singleAssignExprRhs.Expr);
            }
            break;
          }
        case AssignStatement assignStatement:
          RewriteExprInPlaceList(assignStatement.Lhss, RewriteExpr);
          foreach (var rhs in assignStatement.Rhss) {
            if (rhs is ExprRhs assignExprRhs) {
              assignExprRhs.Expr = RewriteExpr(assignExprRhs.Expr);
            }
          }
          break;
        case AssignSuchThatStmt assignSuchThat:
          RewriteExprInPlaceList(assignSuchThat.Lhss, RewriteExpr);
          assignSuchThat.Expr = RewriteExpr(assignSuchThat.Expr);
          break;
        case AssignOrReturnStmt assignOrReturn: {
            RewriteExprInPlaceList(assignOrReturn.Lhss, RewriteExpr);
            if (assignOrReturn.Rhs is ExprRhs assignOrReturnExprRhs) {
              assignOrReturnExprRhs.Expr = RewriteExpr(assignOrReturnExprRhs.Expr);
            }
            foreach (var orRhs in assignOrReturn.Rhss) {
              if (orRhs is ExprRhs orExprRhs) {
                orExprRhs.Expr = RewriteExpr(orExprRhs.Expr);
              }
            }
            break;
          }
        case CallStmt callStmt:
          RewriteExprInPlaceList(callStmt.Lhs, RewriteExpr);
          callStmt.MethodSelect.Obj = RewriteExpr(callStmt.MethodSelect.Obj);
          RewriteExprInPlaceList(callStmt.Args, RewriteExpr);
          break;
        case ReturnStmt returnStmt:
          if (returnStmt.Rhss != null) {
            foreach (var rhs in returnStmt.Rhss) {
              if (rhs is ExprRhs returnExprRhs) {
                returnExprRhs.Expr = RewriteExpr(returnExprRhs.Expr);
              }
            }
          }
          break;
        case ModifyStmt modifyStmt:
          RewriteFrameExprsInPlace(modifyStmt.Mod.Expressions, RewriteExpr);
          if (modifyStmt.Body != null) {
            RewriteStmt(modifyStmt.Body);
          }
          break;
        case PrintStmt printStmt:
          RewriteExprInPlaceList(printStmt.Args, RewriteExpr);
          break;
        case VarDeclStmt varDeclStmt:
          if (varDeclStmt.Assign != null) {
            RewriteStmt(varDeclStmt.Assign);
          }
          break;
        default:
          // Best-effort traversal for statement kinds not explicitly handled above.
          foreach (var e in stmt.SubExpressions) {
            _ = RewriteExpr(e);
          }
          foreach (var s in stmt.SubStatements) {
            RewriteStmt(s);
          }
          break;
      }
    }

    private void RewriteBoundsInPlace(List<BoundedPool?>? bounds) {
      if (bounds == null) {
        return;
      }
      for (var i = 0; i < bounds.Count; i++) {
        if (bounds[i] == null) {
          continue;
        }
        bounds[i] = RewriteBoundedPool(bounds[i]!);
      }
    }

    private BoundedPool RewriteBoundedPool(BoundedPool bound) {
      switch (bound) {
        case IntBoundedPool intPool: {
            var lower = intPool.LowerBound == null ? null : RewriteExpr(intPool.LowerBound);
            var upper = intPool.UpperBound == null ? null : RewriteExpr(intPool.UpperBound);
            return lower != intPool.LowerBound || upper != intPool.UpperBound
              ? new IntBoundedPool(lower, upper)
              : bound;
          }
        case SetBoundedPool setPool: {
            var set = RewriteExpr(setPool.Set);
            return set != setPool.Set
              ? new SetBoundedPool(set, setPool.BoundVariableType, setPool.CollectionElementType, setPool.IsFiniteCollection)
              : bound;
          }
        case SeqBoundedPool seqPool: {
            var seq = RewriteExpr(seqPool.Seq);
            return seq != seqPool.Seq
              ? new SeqBoundedPool(seq, seqPool.BoundVariableType, seqPool.CollectionElementType)
              : bound;
          }
        case MapBoundedPool mapPool: {
            var map = RewriteExpr(mapPool.Map);
            return map != mapPool.Map
              ? new MapBoundedPool(map, mapPool.BoundVariableType, mapPool.CollectionElementType, mapPool.IsFiniteCollection)
              : bound;
          }
        case MultiSetBoundedPool multiSetPool: {
            var multiset = RewriteExpr(multiSetPool.MultiSet);
            return multiset != multiSetPool.MultiSet
              ? new MultiSetBoundedPool(multiset, multiSetPool.BoundVariableType, multiSetPool.CollectionElementType)
              : bound;
          }
        case SubSetBoundedPool subSet: {
            var upper = RewriteExpr(subSet.UpperBound);
            return upper != subSet.UpperBound ? new SubSetBoundedPool(upper, subSet.IsFiniteCollection) : bound;
          }
        case SuperSetBoundedPool superSet: {
            var lower = RewriteExpr(superSet.LowerBound);
            return lower != superSet.LowerBound ? new SuperSetBoundedPool(lower) : bound;
          }
        default:
          return bound;
      }
    }

    // NOTE: This method is invoked via reflection in tests (BindingFlags.NonPublic).
    private Expression RewriteExpr(Expression expr) {
      if (expr == null) {
        throw new ArgumentNullException(nameof(expr));
      }

      // Preserve concrete syntax wrappers, but rewrite the resolved expression.
      if (expr is ConcreteSyntaxExpression concreteSyntaxExpression && concreteSyntaxExpression.ResolvedExpression != null) {
        concreteSyntaxExpression.ResolvedExpression = RewriteExpr(concreteSyntaxExpression.ResolvedExpression);
        return expr;
      }

      if (expr is ParensExpression parens) {
        parens.E = RewriteExpr(parens.E);
        if (parens.ResolvedExpression != null) {
          parens.ResolvedExpression = RewriteExpr(parens.ResolvedExpression);
        }
        return expr;
      }

      switch (expr) {
        case QuantifierExpr quantifierExpr:
          return TryUnrollQuantifier(quantifierExpr, out var rewritten) ? rewritten : RewriteQuantifierChildren(quantifierExpr);

        case UnaryOpExpr unary:
          unary.E = RewriteExpr(unary.E);
          return unary;

        case BinaryExpr binary:
          binary.E0 = RewriteExpr(binary.E0);
          binary.E1 = RewriteExpr(binary.E1);
          return binary;

        case TernaryExpr ternary:
          ternary.E0 = RewriteExpr(ternary.E0);
          ternary.E1 = RewriteExpr(ternary.E1);
          ternary.E2 = RewriteExpr(ternary.E2);
          return ternary;

        case ITEExpr ite:
          ite.Test = RewriteExpr(ite.Test);
          ite.Thn = RewriteExpr(ite.Thn);
          ite.Els = RewriteExpr(ite.Els);
          return ite;

        case LetExpr letExpr:
          for (var i = 0; i < letExpr.RHSs.Count; i++) {
            letExpr.RHSs[i] = RewriteExpr(letExpr.RHSs[i]);
          }
          letExpr.Body = RewriteExpr(letExpr.Body);
          return letExpr;

        case StmtExpr stmtExpr:
          RewriteStmt(stmtExpr.S);
          stmtExpr.E = RewriteExpr(stmtExpr.E);
          return stmtExpr;

        case OldExpr oldExpr:
          oldExpr.Expr = RewriteExpr(oldExpr.Expr);
          return oldExpr;

        case FunctionCallExpr functionCallExpr:
          functionCallExpr.Receiver = RewriteExpr(functionCallExpr.Receiver);
          RewriteExprInPlaceList(functionCallExpr.Args, RewriteExpr);
          return functionCallExpr;

        case MemberSelectExpr memberSelectExpr:
          memberSelectExpr.Obj = RewriteExpr(memberSelectExpr.Obj);
          return memberSelectExpr;

        case SeqSelectExpr seqSelectExpr:
          seqSelectExpr.Seq = RewriteExpr(seqSelectExpr.Seq);
          if (seqSelectExpr.E0 != null) {
            seqSelectExpr.E0 = RewriteExpr(seqSelectExpr.E0);
          }
          if (seqSelectExpr.E1 != null) {
            seqSelectExpr.E1 = RewriteExpr(seqSelectExpr.E1);
          }
          return seqSelectExpr;

        case MultiSelectExpr multiSelectExpr:
          multiSelectExpr.Array = RewriteExpr(multiSelectExpr.Array);
          RewriteExprInPlaceList(multiSelectExpr.Indices, RewriteExpr);
          return multiSelectExpr;

        case ApplyExpr applyExpr:
          applyExpr.Function = RewriteExpr(applyExpr.Function);
          RewriteExprInPlaceList(applyExpr.Args, RewriteExpr);
          return applyExpr;

        case TypeTestExpr typeTestExpr:
          typeTestExpr.E = RewriteExpr(typeTestExpr.E);
          return typeTestExpr;

        case ConversionExpr conversionExpr:
          conversionExpr.E = RewriteExpr(conversionExpr.E);
          return conversionExpr;

        case DecreasesToExpr decreasesToExpr:
          // OldExpressions/NewExpressions are read-only; just ensure nested expressions get traversed.
          foreach (var child in decreasesToExpr.SubExpressions) {
            _ = RewriteExpr(child);
          }
          return decreasesToExpr;

        case BoxingCastExpr boxingCastExpr:
          boxingCastExpr.E = RewriteExpr(boxingCastExpr.E);
          return boxingCastExpr;

        case UnboxingCastExpr unboxingCastExpr:
          unboxingCastExpr.E = RewriteExpr(unboxingCastExpr.E);
          return unboxingCastExpr;

        case FieldLocation fieldLocation:
          return fieldLocation;

        case DisplayExpression displayExpression:
          RewriteExprInPlaceList(displayExpression.Elements, RewriteExpr);
          return displayExpression;

        case MapDisplayExpr mapDisplayExpr:
          foreach (var entry in mapDisplayExpr.Elements) {
            entry.A = RewriteExpr(entry.A);
            entry.B = RewriteExpr(entry.B);
          }
          return mapDisplayExpr;

        case DatatypeValue datatypeValue:
          for (var i = 0; i < datatypeValue.Arguments.Count; i++) {
            datatypeValue.Arguments[i] = RewriteExpr(datatypeValue.Arguments[i]);
          }
          return datatypeValue;

        default:
          // Many expression nodes store their children only via SubExpressions; we still recurse to
          // ensure nested quantifiers get rewritten, even if we can't reassign back to a field.
          foreach (var child in expr.SubExpressions) {
            _ = RewriteExpr(child);
          }
          return expr;
      }
    }

    private Expression RewriteQuantifierChildren(QuantifierExpr quantifierExpr) {
      if (quantifierExpr.Range != null) {
        quantifierExpr.Range = RewriteExpr(quantifierExpr.Range);
      }
      quantifierExpr.Term = RewriteExpr(quantifierExpr.Term);
      RewriteBoundsInPlace(quantifierExpr.Bounds);
      return quantifierExpr;
    }

    internal bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, out Expression rewritten) {
      return quantifierBounds.TryUnrollQuantifier(quantifierExpr, partialEvaluator.SimplifyExpression, out rewritten);
    }
  }
}
