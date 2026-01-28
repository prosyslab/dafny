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
    internal uint MaxInstances => maxInstances;

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
      rewritten = quantifierExpr;

      if (quantifierExpr.SplitQuantifier != null || quantifierExpr.SplitQuantifierExpression != null) {
        return false;
      }

      var bounds = quantifierExpr.Bounds;
      if (bounds == null || bounds.Count != quantifierExpr.BoundVars.Count) {
        var logicalBodyForBounds = quantifierExpr.LogicalBody(bypassSplitQuantifier: true);
        bounds = ModuleResolver.DiscoverBestBounds_MultipleVars(quantifierExpr.BoundVars, logicalBodyForBounds, quantifierExpr is ExistsExpr);
      }
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
        if (!TryGetConcreteDomain(bv, bound, out var domain)) {
          allConcrete = false;
          break;
        }
        domains[i] = domain;
      }
      if (!allConcrete &&
          !TryGetConcreteIntDomainsFromPools(quantifierExpr.BoundVars, bounds, out domains) &&
          !TryGetConcreteIntDomainsFromLogicalBody(quantifierExpr, out domains)) {
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
          inst = partialEvaluator.SimplifyExpression(inst);
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
        var resolved = NormalizeForLinearTerm(conjunct);
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

    private static void CollectConjuncts(Expression expr, List<Expression> conjuncts) {
      expr = NormalizeForLinearTerm(expr);
      if (expr is BinaryExpr binaryExpr && IsConjunction(binaryExpr)) {
        CollectConjuncts(binaryExpr.E0, conjuncts);
        CollectConjuncts(binaryExpr.E1, conjuncts);
        return;
      }
      conjuncts.Add(expr);
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
      expr = NormalizeForLinearTerm(expr);
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

    private static Expression NormalizeForLinearTerm(Expression expr) {
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

    private static bool IsConjunction(BinaryExpr binaryExpr) {
      return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binaryExpr.Op == BinaryExpr.Opcode.And;
    }

    private static bool IsImplication(BinaryExpr binaryExpr) {
      return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp || binaryExpr.Op == BinaryExpr.Opcode.Imp;
    }

    internal bool TryGetConcreteDomain(BoundVar bv, BoundedPool? bound, out ConcreteDomain domain) {
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
        if (!TryMaterializeSetElements(setPool.Set, materializationCap, out var elements)) {
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
            if (!TryGetConcreteDomain(boundVar, boundPool, out var concreteDomain)) {
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

          var keys = new List<Expression>();
          var substMap = new Dictionary<IVariable, Expression>();
          var typeMap = new Dictionary<TypeParameter, Type>();
          var range = mapComprehension.Range;

          bool Enumerate(int varIndex) {
            if (varIndex == domains.Length) {
              var substituter = new Substituter(null, substMap, typeMap);
              if (range != null) {
                var rangeInst = SimplifyForMaterialization(substituter.Substitute(range));
                rangeInst = StripConcreteSyntax(rangeInst);
                if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
                  return false;
                }
                if (!rangeValue) {
                  return true;
                }
              }

              var keyInst = SimplifyForMaterialization(substituter.Substitute(keyTemplate));
              keyInst = StripConcreteSyntax(keyInst);
              if (!IsLiteralExpression(keyInst)) {
                return false;
              }
              if (!ContainsLiteral(keys, keyInst)) {
                keys.Add(keyInst);
                if (maxInstances > 0 && keys.Count > maxInstances) {
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

          var size = new BigInteger(keys.Count);
          domain = new ConcreteDomain(size, () => EnumerateSetElements(keys, bv.Type));
          return true;
        }
      }

      if (bound is SubSetBoundedPool subSetPool) {
        if (!subSetPool.IsFiniteCollection) {
          return false;
        }
        if (maxInstances > 0 && TryGetSetElementUpperBound(subSetPool.UpperBound, out var elementUpperBound)) {
          var maxElements = MaxSubsetElementCount(maxInstances);
          if (elementUpperBound > maxElements) {
            return false;
          }
        }
        var materializationCap = maxInstances == 0 ? (uint?)null : maxInstances;
        if (!TryMaterializeSetElements(subSetPool.UpperBound, materializationCap, out var elements)) {
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

    private IEnumerable<Expression> EnumerateIntRange(BoundVar bv, BigInteger lower, BigInteger upper) {
      for (var v = lower; v < upper; v++) {
        yield return new LiteralExpr(bv.Origin, v) { Type = bv.Type };
      }
    }

    private IEnumerable<Expression> EnumerateSetElements(List<Expression> elements, Type elementType) {
      foreach (var element in elements) {
        EnsureExpressionType(element, elementType);
        yield return element;
      }
    }

    private IEnumerable<Expression> EnumerateSubsets(IOrigin origin, List<Expression> elements, SetType setType) {
      var current = new List<Expression>();
      foreach (var subset in EnumerateSubsetsRecursive(origin, elements, setType, 0, current)) {
        yield return subset;
      }
    }

    private IEnumerable<Expression> EnumerateSubsetsRecursive(IOrigin origin, List<Expression> elements, SetType setType, int index, List<Expression> current) {
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

    internal bool TryMaterializeSetElements(Expression setExpr, uint? maxInstances, out List<Expression> elements) {
      elements = null!;

      var resolved = StripConcreteSyntax(setExpr);

      if (resolved is SetDisplayExpr setDisplay) {
        if (maxInstances.HasValue && setDisplay.Elements.Count > maxInstances.Value) {
          return false;
        }
        elements = setDisplay.Elements.ToList();
        return true;
      }

      if (resolved is SetComprehension setComprehension) {
        return TryMaterializeSetComprehension(setComprehension, out elements);
      }

      return false;
    }

    internal bool TryMaterializeSetComprehension(SetComprehension setComprehension, out List<Expression> elements) {
      elements = null!;

      if (!setComprehension.Finite) {
        return false;
      }
      if (setComprehension.Bounds == null || setComprehension.Bounds.Count != setComprehension.BoundVars.Count) {
        return false;
      }

      var domains = new ConcreteDomain[setComprehension.BoundVars.Count];
      for (var i = 0; i < setComprehension.BoundVars.Count; i++) {
        var bv = setComprehension.BoundVars[i];
        var bound = setComprehension.Bounds[i];
        if (!TryGetConcreteDomain(bv, bound, out var domain)) {
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
            var rangeInst = SimplifyForMaterialization(substituter.Substitute(range));
            rangeInst = StripConcreteSyntax(rangeInst);
            if (!Expression.IsBoolLiteral(rangeInst, out var rangeValue)) {
              return false;
            }
            if (!rangeValue) {
              return true;
            }
          }

          var termInst = SimplifyForMaterialization(substituter.Substitute(term));
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

    private Expression SimplifyForMaterialization(Expression expr) {
      return partialEvaluator.SimplifyExpression(expr);
    }

    private bool TryGetSetElementUpperBound(Expression setExpr, out BigInteger upperBound) {
      upperBound = default;
      var resolved = StripConcreteSyntax(setExpr);

      if (resolved is SetDisplayExpr setDisplay) {
        upperBound = setDisplay.Elements.Count;
        return true;
      }

      if (resolved is SetComprehension setComprehension) {
        return TryGetSetComprehensionUpperBound(setComprehension, out upperBound);
      }

      return false;
    }

    private bool TryGetSetComprehensionUpperBound(SetComprehension setComprehension, out BigInteger upperBound) {
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
      // NormalizeExpand includes subset types that ultimately resolve to int/nat.
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
        // Nat is nonnegative; treat this as unsupported rather than trying to normalize.
        return false;
      }

      return true;
    }

  }
}
