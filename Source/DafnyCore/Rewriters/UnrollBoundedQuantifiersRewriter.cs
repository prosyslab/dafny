#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

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
    var maxInstances = Reporter.Options.Get(CommonOptionBag.UnrollBoundedQuantifiers);
    var partialEvaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth: 2);
    var engine = new UnrollEngine(program.SystemModuleManager, maxInstances, partialEvaluator);
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      engine.Rewrite(decl);
    }
  }

  internal sealed class UnrollEngine {
    private readonly SystemModuleManager systemModuleManager;
    private readonly uint maxInstances;
    private readonly PartialEvaluatorEngine? partialEvaluator;

    internal UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances) {
      this.systemModuleManager = systemModuleManager ?? throw new ArgumentNullException(nameof(systemModuleManager));
      this.maxInstances = maxInstances;
      this.partialEvaluator = null;
    }

    internal UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances, PartialEvaluatorEngine partialEvaluator) {
      this.systemModuleManager = systemModuleManager ?? throw new ArgumentNullException(nameof(systemModuleManager));
      this.maxInstances = maxInstances;
      this.partialEvaluator = partialEvaluator ?? throw new ArgumentNullException(nameof(partialEvaluator));
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
      if (exprs == null) {
        return;
      }
      for (var i = 0; i < exprs.Count; i++) {
        exprs[i] = rewriter(exprs[i]);
      }
    }

    private static void RewriteFrameExprsInPlace(IList<FrameExpression>? exprs, Func<Expression, Expression> rewriter) {
      if (exprs == null) {
        return;
      }
      for (var i = 0; i < exprs.Count; i++) {
        // FrameExpression.E is derived (read-only). Mutate DesugaredExpression to affect E.
        exprs[i].DesugaredExpression = rewriter(exprs[i].E);
      }
    }

    private static void RewriteAttributedExprsInPlace(IEnumerable<AttributedExpression> exprs, Func<Expression, Expression> rewriter) {
      foreach (var expr in exprs) {
        expr.E = rewriter(expr.E);
      }
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

    private bool TryUnrollQuantifier(QuantifierExpr quantifierExpr, out Expression rewritten) {
      rewritten = quantifierExpr;

      if (quantifierExpr.SplitQuantifier != null || quantifierExpr.SplitQuantifierExpression != null) {
        return false;
      }

      if (quantifierExpr.Bounds == null || quantifierExpr.Bounds.Count != quantifierExpr.BoundVars.Count) {
        return false;
      }

      var isForall = quantifierExpr is ForallExpr;
      var isExists = quantifierExpr is ExistsExpr;
      if (!isForall && !isExists) {
        return false;
      }

      // We only unroll when all bound variables range over finite, concrete integer intervals.
      var domains = new (BigInteger Lower, BigInteger Upper, Type VarType)[quantifierExpr.BoundVars.Count];
      for (var i = 0; i < quantifierExpr.BoundVars.Count; i++) {
        var bv = quantifierExpr.BoundVars[i];
        var bound = quantifierExpr.Bounds[i];
        if (!TryGetConcreteIntDomain(bv, bound, out var lower, out var upper)) {
          return false;
        }
        domains[i] = (lower, upper, bv.Type);
      }

      // Domain product must be within cap.
      var size = BigInteger.One;
      for (var i = 0; i < domains.Length; i++) {
        var (lower, upper, _) = domains[i];
        var width = upper - lower;
        if (width <= BigInteger.Zero) {
          rewritten = Expression.CreateBoolLiteral(quantifierExpr.Origin, isForall);
          rewritten.Type = Type.Bool;
          return true;
        }

        size *= width;
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
          inst = partialEvaluator == null
            ? PartialEvaluatorEngine.SimplifyBooleanExpression(inst)
            : partialEvaluator.SimplifyExpression(inst);
          AddInstance(inst);
          return;
        }

        var (lower, upper, varType) = domains[varIndex];
        var bv = quantifierExpr.BoundVars[varIndex];
        for (var v = lower; v < upper; v++) {
          if (IsShortCircuited()) {
            return;
          }

          substMap[bv] = new LiteralExpr(bv.Origin, v) { Type = varType };
          Enumerate(varIndex + 1);
        }
      }

      Enumerate(0);

      rewritten = accumulator;
      return true;
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

      if (intPool.UpperBound == null || !Expression.IsIntLiteral(intPool.UpperBound, out upper)) {
        return false;
      }

      if (intPool.LowerBound == null) {
        if (!isNat) {
          return false;
        }
        lower = BigInteger.Zero;
      } else if (!Expression.IsIntLiteral(intPool.LowerBound, out lower)) {
        return false;
      }

      if (isNat && lower < 0) {
        // Nat is nonnegative; treat this as unsupported rather than trying to normalize.
        return false;
      }

      return true;
    }

  }
}
