// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

/// <summary>
/// Rewrites eligible bounded <c>forall</c> quantifiers into a finite conjunction of instances.
/// </summary>
/// <remarks>
/// This rewriter is driven by the <see cref="CommonOptionBag.UnrollBoundedQuantifiers"/> option.
/// When enabled, it looks for <see cref="ForallExpr"/> whose bound variables range over a
/// compile-time finite set of integers (currently: literal <c>int</c>/<c>nat</c> intervals), and
/// replaces the quantifier with an explicit conjunction of instantiated bodies, provided the
/// total number of instances does not exceed the configured maximum.
/// </remarks>
public class UnrollBoundedQuantifiersRewriter : IRewriter {
  private readonly SystemModuleManager systemModuleManager;

  /// <summary>
  /// Creates the rewriter and captures the <see cref="SystemModuleManager"/> needed for type checks
  /// (e.g., recognizing <c>nat</c>).
  /// </summary>
  public UnrollBoundedQuantifiersRewriter(Program program, ErrorReporter reporter) : base(reporter) {
    Contract.Requires(program != null);
    systemModuleManager = program.SystemModuleManager;
  }

  /// <summary>
  /// Applies the rewrite after resolution, when <see cref="Expression.Resolved"/> and quantifier
  /// bounds are available.
  /// </summary>
  /// <remarks>
  /// The rewrite is purely syntactic: it does not introduce new declarations, it only replaces
  /// expressions inside existing callables.
  /// </remarks>
  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    var maxInstances = Options.Get(CommonOptionBag.UnrollBoundedQuantifiers);
    if (maxInstances == 0) {
      return;
    }

    var rewriter = new UnrollEngine(systemModuleManager, maxInstances);
    foreach (var decl in ModuleDefinition.AllItersAndCallables(moduleDefinition.TopLevelDecls)) {
      rewriter.Rewrite(decl);
    }
  }

  private sealed class UnrollEngine {
    private readonly SystemModuleManager systemModuleManager;
    private readonly uint maxInstances;

    /// <summary>
    /// Creates an engine that unrolls bounded quantifiers up to <paramref name="maxInstances"/>.
    /// </summary>
    public UnrollEngine(SystemModuleManager systemModuleManager, uint maxInstances) {
      this.systemModuleManager = systemModuleManager;
      this.maxInstances = maxInstances;
    }

    /// <summary>
    /// Rewrites all expressions contained in the given callable (specs and body).
    /// </summary>
    public void Rewrite(ICallable decl) {
      switch (decl) {
        case Function function:
          RewriteFunction(function);
          break;
        case MethodOrConstructor method:
          RewriteMethod(method);
          break;
        case IteratorDecl iterator:
          RewriteIterator(iterator);
          break;
      }
    }

    /// <summary>
    /// Rewrites all expressions that appear in a function declaration (specs, body, and by-method body).
    /// </summary>
    private void RewriteFunction(Function function) {
      RewriteAttributedExprs(function.Req);
      RewriteAttributedExprs(function.Ens);
      RewriteSpecExpr(function.Decreases);
      RewriteSpecFrameExpr(function.Reads);
      function.Body = RewriteExpr(function.Body);
      if (function.ByMethodBody != null) {
        RewriteStmt(function.ByMethodBody);
      }
    }

    /// <summary>
    /// Rewrites all expressions that appear in a method/constructor declaration (specs and body).
    /// </summary>
    private void RewriteMethod(MethodOrConstructor method) {
      RewriteAttributedExprs(method.Req);
      RewriteAttributedExprs(method.Ens);
      RewriteSpecExpr(method.Decreases);
      RewriteSpecFrameExpr(method.Reads);
      RewriteSpecFrameExpr(method.Mod);
      if (method.Body != null) {
        RewriteStmt(method.Body);
      }
    }

    /// <summary>
    /// Rewrites all expressions that appear in an iterator declaration (specs and body).
    /// </summary>
    private void RewriteIterator(IteratorDecl iterator) {
      RewriteAttributedExprs(iterator.Requires);
      RewriteAttributedExprs(iterator.Ensures);
      RewriteAttributedExprs(iterator.YieldRequires);
      RewriteAttributedExprs(iterator.YieldEnsures);
      RewriteSpecExpr(iterator.Decreases);
      RewriteSpecFrameExpr(iterator.Reads);
      RewriteSpecFrameExpr(iterator.Modifies);
      if (iterator.Body != null) {
        RewriteStmt(iterator.Body);
      }
    }

    private void RewriteAttributedExprs(List<AttributedExpression> exprs) {
      if (exprs == null) {
        return;
      }
      for (var i = 0; i < exprs.Count; i++) {
        exprs[i].E = RewriteExpr(exprs[i].E);
      }
    }

    private void RewriteExprList(IList<Expression> expressions) {
      if (expressions == null) {
        return;
      }
      for (var i = 0; i < expressions.Count; i++) {
        expressions[i] = RewriteExpr(expressions[i]);
      }
    }

    private void RewriteFrameExpressionList(IList<FrameExpression> expressions) {
      if (expressions == null) {
        return;
      }
      for (var i = 0; i < expressions.Count; i++) {
        var frameExpr = expressions[i];
        var before = frameExpr.E;
        var rewritten = RewriteExpr(before);
        if (!ReferenceEquals(rewritten, before)) {
          frameExpr.DesugaredExpression = rewritten;
        }
      }
    }

    private void RewriteAssignmentRhs(AssignmentRhs rhs) {
      if (rhs is ExprRhs exprRhs) {
        exprRhs.Expr = RewriteExpr(exprRhs.Expr);
      }
    }

    private void RewriteAssignmentRhsList(IList<AssignmentRhs> rhss) {
      if (rhss == null) {
        return;
      }
      for (var i = 0; i < rhss.Count; i++) {
        RewriteAssignmentRhs(rhss[i]);
      }
    }

    private void RewriteSpecExpr(Specification<Expression> spec) {
      if (spec?.Expressions == null) {
        return;
      }
      RewriteExprList(spec.Expressions);
    }

    private void RewriteSpecFrameExpr(Specification<FrameExpression> spec) {
      if (spec?.Expressions == null) {
        return;
      }
      RewriteFrameExpressionList(spec.Expressions);
    }

    /// <summary>
    /// Rewrites all expressions contained within a statement by recursively traversing the AST.
    /// </summary>
    /// <remarks>
    /// This method performs an in-place traversal and updates child nodes as needed. The switch
    /// handles statement kinds with embedded expressions explicitly; the default case falls back to
    /// <see cref="Statement.SubStatements"/> to visit nested statements for other kinds.
    /// </remarks>
    private void RewriteStmt(Statement stmt) {
      switch (stmt) {
        case BlockStmt block:
          RewriteBlockStmt(block);
          return;
        case DividedBlockStmt divided:
          RewriteDividedBlockStmt(divided);
          return;
        case IfStmt ifStmt:
          RewriteIfStmt(ifStmt);
          return;
        case WhileStmt whileStmt:
          RewriteWhileStmt(whileStmt);
          return;
        case ForLoopStmt forLoopStmt:
          RewriteForLoopStmt(forLoopStmt);
          return;
        case AlternativeLoopStmt alternativeLoopStmt:
          RewriteAlternativeLoopStmt(alternativeLoopStmt);
          return;
        case ForallStmt forallStmt:
          RewriteForallStmt(forallStmt);
          return;
        case AssertStmt assertStmt:
          assertStmt.Expr = RewriteExpr(assertStmt.Expr);
          return;
        case AssumeStmt assumeStmt:
          assumeStmt.Expr = RewriteExpr(assumeStmt.Expr);
          return;
        case ExpectStmt expectStmt:
          RewriteExpectStmt(expectStmt);
          return;
        case ModifyStmt modifyStmt:
          RewriteModifyStmt(modifyStmt);
          return;
        case CallStmt callStmt:
          RewriteCallStmt(callStmt);
          return;
        case SingleAssignStmt assignStmt:
          RewriteAssignmentRhs(assignStmt.Rhs);
          return;
        case AssignStatement assignStmt:
          RewriteAssignStatement(assignStmt);
          return;
        case AssignSuchThatStmt assignSuchThatStmt:
          RewriteAssignSuchThatStmt(assignSuchThatStmt);
          return;
        case AssignOrReturnStmt assignOrReturnStmt:
          RewriteAssignStatement(assignOrReturnStmt);
          return;
        case ReturnStmt returnStmt:
          RewriteAssignmentRhsList(returnStmt.Rhss);
          return;
        case PrintStmt printStmt:
          RewriteExprList(printStmt.Args);
          return;
        case VarDeclStmt varDeclStmt:
          RewriteVarDeclStmt(varDeclStmt);
          return;
        default:
          RewriteSubStatements(stmt);
          return;
      }
    }

    private void RewriteBlockStmt(BlockStmt blockStmt) {
      RewriteStmtList(blockStmt.Body);
    }

    private void RewriteDividedBlockStmt(DividedBlockStmt dividedBlockStmt) {
      RewriteStmtList(dividedBlockStmt.BodyInit);
      RewriteStmtList(dividedBlockStmt.BodyProper);
    }

    private void RewriteIfStmt(IfStmt ifStmt) {
      ifStmt.Guard = RewriteExpr(ifStmt.Guard);
      RewriteStmt(ifStmt.Thn);
      if (ifStmt.Els != null) {
        RewriteStmt(ifStmt.Els);
      }
    }

    private void RewriteWhileStmt(WhileStmt whileStmt) {
      RewriteLoopSpec(whileStmt);
      whileStmt.Guard = RewriteExpr(whileStmt.Guard);
      RewriteStmt(whileStmt.Body);
    }

    private void RewriteForLoopStmt(ForLoopStmt forLoopStmt) {
      RewriteLoopSpec(forLoopStmt);
      forLoopStmt.Start = RewriteExpr(forLoopStmt.Start);
      if (forLoopStmt.End != null) {
        forLoopStmt.End = RewriteExpr(forLoopStmt.End);
      }
      if (forLoopStmt.Body != null) {
        RewriteStmt(forLoopStmt.Body);
      }
    }

    private void RewriteAlternativeLoopStmt(AlternativeLoopStmt alternativeLoopStmt) {
      RewriteLoopSpec(alternativeLoopStmt);
      foreach (var alt in alternativeLoopStmt.Alternatives) {
        alt.Guard = RewriteExpr(alt.Guard);
        RewriteStmtList(alt.Body);
      }
    }

    private void RewriteForallStmt(ForallStmt forallStmt) {
      forallStmt.Range = RewriteExpr(forallStmt.Range);
      RewriteAttributedExprs(forallStmt.Ens);
      RewriteExprList(forallStmt.EffectiveEnsuresClauses);
      if (forallStmt.Body != null) {
        RewriteStmt(forallStmt.Body);
      }
    }

    private void RewriteExpectStmt(ExpectStmt expectStmt) {
      expectStmt.Expr = RewriteExpr(expectStmt.Expr);
      if (expectStmt.Message != null) {
        expectStmt.Message = RewriteExpr(expectStmt.Message);
      }
    }

    private void RewriteModifyStmt(ModifyStmt modifyStmt) {
      RewriteFrameExpressionList(modifyStmt.Mod.Expressions);
      RewriteStmt(modifyStmt.Body);
    }

    private void RewriteCallStmt(CallStmt callStmt) {
      RewriteExprList(callStmt.Lhs);
      callStmt.MethodSelect.Obj = RewriteExpr(callStmt.MethodSelect.Obj);
      RewriteExprList(callStmt.Args);
    }

    private void RewriteAssignSuchThatStmt(AssignSuchThatStmt assignSuchThatStmt) {
      RewriteAssignStatement(assignSuchThatStmt);
      if (assignSuchThatStmt.Expr != null) {
        assignSuchThatStmt.Expr = RewriteExpr(assignSuchThatStmt.Expr);
      }
    }

    private void RewriteVarDeclStmt(VarDeclStmt varDeclStmt) {
      if (varDeclStmt.Assign != null) {
        RewriteStmt(varDeclStmt.Assign);
      }
    }

    private void RewriteSubStatements(Statement stmt) {
      foreach (var sub in stmt.SubStatements) {
        RewriteStmt(sub);
      }
    }

    private void RewriteStmtList(IEnumerable<Statement> statements) {
      foreach (var statement in statements) {
        RewriteStmt(statement);
      }
    }

    private void RewriteLoopSpec(LoopStmt loopStmt) {
      RewriteAttributedExprs(loopStmt.Invariants);
      RewriteSpecExpr(loopStmt.Decreases);
      RewriteSpecFrameExpr(loopStmt.Mod);
    }

    private void RewriteAssignStatement(ConcreteAssignStatement assignStmt) {
      for (var i = 0; i < assignStmt.Lhss.Count; i++) {
        assignStmt.Lhss[i] = RewriteExpr(assignStmt.Lhss[i]);
      }
      if (assignStmt is AssignStatement update) {
        RewriteAssignmentRhsList(update.Rhss);
      }
    }

    private Expression RewriteExpr(Expression expr) {
      if (expr == null) {
        return null;
      }

      expr = DereferenceResolved(expr);

      switch (expr) {
        case ParensExpression parens:
          return RewriteExpr(parens.E);
        case LiteralExpr:
        case ThisExpr:
        case IdentifierExpr:
        case WildcardExpr:
        case BoogieGenerator.BoogieWrapper:
        case FieldLocation:
        case LocalsObjectExpression:
          return expr;
        case UnaryOpExpr unary:
          return RewriteUnaryOpExpr(unary);
        case BinaryExpr binary:
          return RewriteBinaryExpr(binary);
        case TernaryExpr ternary:
          return RewriteTernaryExpr(ternary);
        case ITEExpr ite:
          return RewriteITEExpr(ite);
        case LetExpr letExpr:
          return RewriteLetExpr(letExpr);
        case QuantifierExpr quantifierExpr:
          return RewriteQuantifierExpr(quantifierExpr);
        case FunctionCallExpr callExpr:
          return RewriteFunctionCallExpr(callExpr);
        case ApplyExpr applyExpr:
          return RewriteApplyExpr(applyExpr);
        case MemberSelectExpr memberSelectExpr:
          return RewriteMemberSelectExpr(memberSelectExpr);
        case SeqSelectExpr seqSelectExpr:
          return RewriteSeqSelectExpr(seqSelectExpr);
        case SeqUpdateExpr seqUpdateExpr:
          return RewriteSeqUpdateExpr(seqUpdateExpr);
        case MultiSelectExpr multiSelectExpr:
          return RewriteMultiSelectExpr(multiSelectExpr);
        case SeqConstructionExpr seqConstructionExpr:
          return RewriteSeqConstructionExpr(seqConstructionExpr);
        case SeqDisplayExpr seqDisplayExpr:
          return RewriteSeqDisplayExpr(seqDisplayExpr);
        case SetDisplayExpr setDisplayExpr:
          return RewriteSetDisplayExpr(setDisplayExpr);
        case MultiSetDisplayExpr multiSetDisplayExpr:
          return RewriteMultiSetDisplayExpr(multiSetDisplayExpr);
        case MapDisplayExpr mapDisplayExpr:
          return RewriteMapDisplayExpr(mapDisplayExpr);
        case DatatypeValue datatypeValue:
          return RewriteDatatypeValue(datatypeValue);
        case ConversionExpr conversionExpr:
          return RewriteConversionExpr(conversionExpr);
        case TypeTestExpr typeTestExpr:
          return RewriteTypeTestExpr(typeTestExpr);
        case OldExpr oldExpr:
          return RewriteOldExpr(oldExpr);
        case UnchangedExpr unchangedExpr:
          return RewriteUnchangedExpr(unchangedExpr);
        case BoxingCastExpr boxingCastExpr:
          return RewriteBoxingCastExpr(boxingCastExpr);
        case UnboxingCastExpr unboxingCastExpr:
          return RewriteUnboxingCastExpr(unboxingCastExpr);
        case DecreasesToExpr decreasesToExpr:
          return RewriteDecreasesToExpr(decreasesToExpr);
        case StmtExpr stmtExpr:
          return RewriteStmtExpr(stmtExpr);
        case ConcreteSyntaxExpression concreteSyntaxExpression:
          return RewriteConcreteSyntaxExpression(concreteSyntaxExpression);
        default:
          return expr;
      }
    }

    /// <summary>
    /// Returns the resolved node for <paramref name="expr"/> when resolution created a distinct
    /// AST node, otherwise returns <paramref name="expr"/>.
    /// </summary>
    /// <remarks>
    /// The rewrite operates on resolved AST nodes to avoid rewriting wrappers that will be ignored
    /// downstream (and to ensure we see resolved operators like <see cref="BinaryExpr.ResolvedOp"/>).
    /// </remarks>
    private static Expression DereferenceResolved(Expression expr) {
      if (expr.Resolved != null && expr.Resolved != expr) {
        return expr.Resolved;
      }
      return expr;
    }

    private Expression RewriteUnaryOpExpr(UnaryOpExpr unaryOpExpr) {
      unaryOpExpr.E = RewriteExpr(unaryOpExpr.E);
      return unaryOpExpr;
    }

    private Expression RewriteBinaryExpr(BinaryExpr binaryExpr) {
      binaryExpr.E0 = RewriteExpr(binaryExpr.E0);
      binaryExpr.E1 = RewriteExpr(binaryExpr.E1);
      return binaryExpr;
    }

    private Expression RewriteTernaryExpr(TernaryExpr ternaryExpr) {
      ternaryExpr.E0 = RewriteExpr(ternaryExpr.E0);
      ternaryExpr.E1 = RewriteExpr(ternaryExpr.E1);
      ternaryExpr.E2 = RewriteExpr(ternaryExpr.E2);
      return ternaryExpr;
    }

    private Expression RewriteITEExpr(ITEExpr iteExpr) {
      iteExpr.Test = RewriteExpr(iteExpr.Test);
      iteExpr.Thn = RewriteExpr(iteExpr.Thn);
      iteExpr.Els = RewriteExpr(iteExpr.Els);
      return iteExpr;
    }

    private Expression RewriteLetExpr(LetExpr letExpr) {
      for (var i = 0; i < letExpr.RHSs.Count; i++) {
        letExpr.RHSs[i] = RewriteExpr(letExpr.RHSs[i]);
      }
      letExpr.Body = RewriteExpr(letExpr.Body);
      return letExpr;
    }

    private Expression RewriteQuantifierExpr(QuantifierExpr quantifierExpr) {
      quantifierExpr.Range = RewriteExpr(quantifierExpr.Range);
      quantifierExpr.Term = RewriteExpr(quantifierExpr.Term);
      quantifierExpr.Bounds = RewriteBounds(quantifierExpr.Bounds);
      if (quantifierExpr is ForallExpr forallExpr && TryUnrollForall(forallExpr, out var unrolled)) {
        return unrolled;
      }
      return quantifierExpr;
    }

    private Expression RewriteFunctionCallExpr(FunctionCallExpr functionCallExpr) {
      functionCallExpr.Receiver = RewriteExpr(functionCallExpr.Receiver);
      RewriteExprList(functionCallExpr.Args);
      return functionCallExpr;
    }

    private Expression RewriteApplyExpr(ApplyExpr applyExpr) {
      applyExpr.Function = RewriteExpr(applyExpr.Function);
      RewriteExprList(applyExpr.Args);
      return applyExpr;
    }

    private Expression RewriteMemberSelectExpr(MemberSelectExpr memberSelectExpr) {
      memberSelectExpr.Obj = RewriteExpr(memberSelectExpr.Obj);
      return memberSelectExpr;
    }

    private Expression RewriteSeqSelectExpr(SeqSelectExpr seqSelectExpr) {
      seqSelectExpr.Seq = RewriteExpr(seqSelectExpr.Seq);
      if (seqSelectExpr.E0 != null) {
        seqSelectExpr.E0 = RewriteExpr(seqSelectExpr.E0);
      }
      if (seqSelectExpr.E1 != null) {
        seqSelectExpr.E1 = RewriteExpr(seqSelectExpr.E1);
      }
      return seqSelectExpr;
    }

    private Expression RewriteSeqUpdateExpr(SeqUpdateExpr seqUpdateExpr) {
      seqUpdateExpr.Seq = RewriteExpr(seqUpdateExpr.Seq);
      seqUpdateExpr.Index = RewriteExpr(seqUpdateExpr.Index);
      seqUpdateExpr.Value = RewriteExpr(seqUpdateExpr.Value);
      return seqUpdateExpr;
    }

    private Expression RewriteMultiSelectExpr(MultiSelectExpr multiSelectExpr) {
      multiSelectExpr.Array = RewriteExpr(multiSelectExpr.Array);
      RewriteExprList(multiSelectExpr.Indices);
      return multiSelectExpr;
    }

    private Expression RewriteSeqConstructionExpr(SeqConstructionExpr seqConstructionExpr) {
      seqConstructionExpr.N = RewriteExpr(seqConstructionExpr.N);
      seqConstructionExpr.Initializer = RewriteExpr(seqConstructionExpr.Initializer);
      return seqConstructionExpr;
    }

    private Expression RewriteSeqDisplayExpr(SeqDisplayExpr seqDisplayExpr) {
      RewriteExprList(seqDisplayExpr.Elements);
      return seqDisplayExpr;
    }

    private Expression RewriteSetDisplayExpr(SetDisplayExpr setDisplayExpr) {
      RewriteExprList(setDisplayExpr.Elements);
      return setDisplayExpr;
    }

    private Expression RewriteMultiSetDisplayExpr(MultiSetDisplayExpr multiSetDisplayExpr) {
      RewriteExprList(multiSetDisplayExpr.Elements);
      return multiSetDisplayExpr;
    }

    private Expression RewriteMapDisplayExpr(MapDisplayExpr mapDisplayExpr) {
      foreach (var entry in mapDisplayExpr.Elements) {
        entry.A = RewriteExpr(entry.A);
        entry.B = RewriteExpr(entry.B);
      }
      return mapDisplayExpr;
    }

    private Expression RewriteDatatypeValue(DatatypeValue datatypeValue) {
      RewriteExprList(datatypeValue.Arguments);
      return datatypeValue;
    }

    private Expression RewriteConversionExpr(ConversionExpr conversionExpr) {
      conversionExpr.E = RewriteExpr(conversionExpr.E);
      return conversionExpr;
    }

    private Expression RewriteTypeTestExpr(TypeTestExpr typeTestExpr) {
      typeTestExpr.E = RewriteExpr(typeTestExpr.E);
      return typeTestExpr;
    }

    private Expression RewriteOldExpr(OldExpr oldExpr) {
      oldExpr.Expr = RewriteExpr(oldExpr.Expr);
      return oldExpr;
    }

    private Expression RewriteUnchangedExpr(UnchangedExpr unchangedExpr) {
      RewriteFrameExpressionList(unchangedExpr.Frame);
      return unchangedExpr;
    }

    private Expression RewriteBoxingCastExpr(BoxingCastExpr boxingCastExpr) {
      boxingCastExpr.E = RewriteExpr(boxingCastExpr.E);
      return boxingCastExpr;
    }

    private Expression RewriteUnboxingCastExpr(UnboxingCastExpr unboxingCastExpr) {
      unboxingCastExpr.E = RewriteExpr(unboxingCastExpr.E);
      return unboxingCastExpr;
    }

    private Expression RewriteDecreasesToExpr(DecreasesToExpr decreasesToExpr) {
      var oldChanged = false;
      var newChanged = false;
      var rewrittenOld = new List<Expression>(decreasesToExpr.OldExpressions.Count);
      foreach (var oldExpr in decreasesToExpr.OldExpressions) {
        var rewritten = RewriteExpr(oldExpr);
        if (!ReferenceEquals(rewritten, oldExpr)) {
          oldChanged = true;
        }
        rewrittenOld.Add(rewritten);
      }
      var rewrittenNew = new List<Expression>(decreasesToExpr.NewExpressions.Count);
      foreach (var newExpr in decreasesToExpr.NewExpressions) {
        var rewritten = RewriteExpr(newExpr);
        if (!ReferenceEquals(rewritten, newExpr)) {
          newChanged = true;
        }
        rewrittenNew.Add(rewritten);
      }
      if (!oldChanged && !newChanged) {
        return decreasesToExpr;
      }
      var updated = new DecreasesToExpr(decreasesToExpr.Origin, rewrittenOld, rewrittenNew, decreasesToExpr.AllowNoChange);
      if (decreasesToExpr.Type != null) {
        updated.Type = decreasesToExpr.Type;
      }
      return updated;
    }

    private Expression RewriteStmtExpr(StmtExpr stmtExpr) {
      stmtExpr.E = RewriteExpr(stmtExpr.E);
      RewriteStmt(stmtExpr.S);
      return stmtExpr;
    }

    private Expression RewriteConcreteSyntaxExpression(ConcreteSyntaxExpression concreteSyntaxExpression) {
      if (concreteSyntaxExpression.ResolvedExpression != null) {
        concreteSyntaxExpression.ResolvedExpression = RewriteExpr(concreteSyntaxExpression.ResolvedExpression);
      }
      return concreteSyntaxExpression;
    }

    /// <summary>
    /// Rewrites the expressions that appear inside quantifier bound pools.
    /// </summary>
    /// <remarks>
    /// Returns the original list when no element changes, to preserve sharing.
    /// </remarks>
    private List<BoundedPool> RewriteBounds(List<BoundedPool> bounds) {
      if (bounds == null) {
        return null;
      }
      var changed = false;
      var newBounds = new List<BoundedPool>(bounds.Count);
      foreach (var bound in bounds) {
        var rewritten = RewriteBoundedPool(bound);
        if (!ReferenceEquals(rewritten, bound)) {
          changed = true;
        }
        newBounds.Add(rewritten);
      }
      return changed ? newBounds : bounds;
    }

    /// <summary>
    /// Rewrites expressions embedded in a single <see cref="BoundedPool"/>, returning the original
    /// pool when unchanged.
    /// </summary>
    private BoundedPool RewriteBoundedPool(BoundedPool bound) {
      switch (bound) {
        case IntBoundedPool intPool: {
            var lower = intPool.LowerBound == null ? null : RewriteExpr(intPool.LowerBound);
            var upper = intPool.UpperBound == null ? null : RewriteExpr(intPool.UpperBound);
            if (lower != intPool.LowerBound || upper != intPool.UpperBound) {
              return new IntBoundedPool(lower, upper);
            }
            return bound;
          }
        case SetBoundedPool setPool: {
            var set = RewriteExpr(setPool.Set);
            return set != setPool.Set
              ? new SetBoundedPool(set, setPool.BoundVariableType, setPool.CollectionElementType, setPool.IsFiniteCollection)
              : bound;
          }
        case SubSetBoundedPool subSet: {
            var upper = RewriteExpr(subSet.UpperBound);
            return upper != subSet.UpperBound
              ? new SubSetBoundedPool(upper, subSet.IsFiniteCollection)
              : bound;
          }
        case SuperSetBoundedPool superSet: {
            var lower = RewriteExpr(superSet.LowerBound);
            return lower != superSet.LowerBound
              ? new SuperSetBoundedPool(lower)
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
        default:
          return bound;
      }
    }

    private bool IsNatType(Type type) {
      if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: var resolvedClass }) {
        return resolvedClass == systemModuleManager.NatDecl;
      }
      return false;
    }

    private static bool IsPlainIntType(Type type) {
      return type.NormalizeExpandKeepConstraints() is IntType;
    }

    /// <summary>
    /// Attempts to replace a bounded <c>forall</c> with a conjunction of its instances.
    /// </summary>
    /// <remarks>
    /// Succeeds only when every bound variable ranges over a literal integer interval and the
    /// cartesian product of intervals does not exceed the configured maximum.
    /// </remarks>
    private bool TryUnrollForall(ForallExpr forallExpr, out Expression unrolled) {
      unrolled = null;

      if (!TryGetIntervals(forallExpr, out var intervals, out var instanceCount)) {
        return false;
      }

      if (instanceCount == BigInteger.Zero) {
        unrolled = Expression.CreateBoolLiteral(forallExpr.Origin, true);
        return true;
      }

      unrolled = BuildUnrolledConjunction(forallExpr, intervals);
      return true;
    }

    /// <summary>
    /// Extracts literal half-open integer intervals for each bound variable and computes the total
    /// number of instances.
    /// </summary>
    /// <returns>
    /// <c>true</c> if all bounds are recognized as literal integer intervals and the computed
    /// instance count is at most the configured maximum; otherwise <c>false</c>.
    /// </returns>
    private bool TryGetIntervals(ForallExpr forallExpr,
      out (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[] intervals,
      out BigInteger instanceCount) {
      intervals = null;
      instanceCount = BigInteger.One;

      if (forallExpr.SplitQuantifier != null) {
        return false;
      }

      if (forallExpr.Bounds == null || forallExpr.Bounds.Count != forallExpr.BoundVars.Count) {
        return false;
      }

      intervals = new (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[forallExpr.BoundVars.Count];
      for (var i = 0; i < forallExpr.BoundVars.Count; i++) {
        var boundVar = forallExpr.BoundVars[i];
        if (!TryGetIntInterval(boundVar, forallExpr.Bounds[i], out var lower, out var upperExclusive)) {
          return false;
        }

        var length = upperExclusive - lower;
        if (length <= 0) {
          instanceCount = BigInteger.Zero;
        } else if (instanceCount != BigInteger.Zero) {
          instanceCount *= length;
          if (instanceCount > maxInstances) {
            return false;
          }
        }

        intervals[i] = (boundVar, lower, upperExclusive);
      }

      return true;
    }

    /// <summary>
    /// Recognizes a literal integer interval for one bound variable.
    /// </summary>
    /// <remarks>
    /// Currently supported forms:
    /// - <c>int</c>: both lower and upper must be integer literals
    /// - <c>nat</c>: lower may be omitted (defaults to 0) and upper must be an integer literal
    /// </remarks>
    private bool TryGetIntInterval(BoundVar boundVar, BoundedPool pool,
      out BigInteger lower, out BigInteger upperExclusive) {
      lower = BigInteger.Zero;
      upperExclusive = BigInteger.Zero;

      var isNat = IsNatType(boundVar.Type);
      if (!IsPlainIntType(boundVar.Type) && !isNat) {
        return false;
      }

      if (pool is not IntBoundedPool intPool || intPool.UpperBound == null) {
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

      if (!Expression.IsIntLiteral(intPool.UpperBound, out upperExclusive)) {
        return false;
      }

      return true;
    }

    /// <summary>
    /// Builds the conjunction that results from instantiating <paramref name="forallExpr"/> for
    /// every value in <paramref name="intervals"/>.
    /// </summary>
    private Expression BuildUnrolledConjunction(ForallExpr forallExpr,
      (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[] intervals) {
      var simplifiedBody = SimplifyForUnrolling(forallExpr, intervals);
      var substitutionMap = new Dictionary<IVariable, Expression>(forallExpr.BoundVars.Count);
      Expression conjunction = Expression.CreateBoolLiteral(forallExpr.Origin, true);
      var shouldStop = false;
      AddUnrolledInstances(0, intervals, simplifiedBody, substitutionMap, ref conjunction, ref shouldStop);
      return conjunction;
    }

    /// <summary>
    /// Produces a body expression that is better suited for unrolling by removing antecedent bound
    /// checks that are guaranteed by the enumeration intervals.
    /// </summary>
    private Expression SimplifyForUnrolling(ForallExpr forallExpr,
      (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[] intervals) {
      var logicalBody = forallExpr.LogicalBody();
      var intervalMap = CreateIntervalMap(intervals);
      return StripGuaranteedBounds(logicalBody, intervalMap);
    }

    private static Dictionary<BoundVar, (BigInteger Lower, BigInteger UpperExclusive)> CreateIntervalMap(
      (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[] intervals) {
      var result = new Dictionary<BoundVar, (BigInteger Lower, BigInteger UpperExclusive)>(intervals.Length);
      foreach (var interval in intervals) {
        result[interval.Var] = (interval.Lower, interval.UpperExclusive);
      }
      return result;
    }

    /// <summary>
    /// Adds one instantiated body per point in the cartesian product of <paramref name="intervals"/>
    /// to <paramref name="conjunction"/>.
    /// </summary>
    /// <remarks>
    /// This is a depth-first enumeration that short-circuits as soon as the conjunction becomes
    /// syntactically <c>false</c>.
    /// </remarks>
    private void AddUnrolledInstances(
      int intervalIndex,
      (BoundVar Var, BigInteger Lower, BigInteger UpperExclusive)[] intervals,
      Expression simplifiedBody,
      Dictionary<IVariable, Expression> substitutionMap,
      ref Expression conjunction,
      ref bool shouldStop) {
      if (shouldStop) {
        return;
      }
      if (intervalIndex == intervals.Length) {
        var instantiated = BoogieGenerator.Substitute(simplifiedBody, null, substitutionMap);
        conjunction = Expression.CreateAnd(conjunction, instantiated);
        if (Expression.IsBoolLiteral(conjunction, out var value) && !value) {
          shouldStop = true;
        }
        return;
      }

      var (boundVar, lower, upperExclusive) = intervals[intervalIndex];
      for (var value = lower; value < upperExclusive; value++) {
        substitutionMap[boundVar] = CreateTypedIntLiteral(boundVar, value);
        AddUnrolledInstances(intervalIndex + 1, intervals, simplifiedBody, substitutionMap, ref conjunction, ref shouldStop);
        if (shouldStop) {
          break;
        }
      }
    }

    private static LiteralExpr CreateTypedIntLiteral(BoundVar boundVar, BigInteger value) {
      return new LiteralExpr(boundVar.Origin, value) { Type = boundVar.Type };
    }

    /// <summary>
    /// Strips bound checks from the antecedent of an implication when those checks are guaranteed
    /// by the enumeration intervals.
    /// </summary>
    /// <remarks>
    /// Only expressions of the form <c>(A ==> B)</c> are simplified. The returned expression is
    /// semantically equivalent under the assumed enumeration of bound variables.
    /// </remarks>
    private Expression StripGuaranteedBounds(Expression expr,
      IReadOnlyDictionary<BoundVar, (BigInteger Lower, BigInteger UpperExclusive)> intervals) {
      if (expr is not BinaryExpr binary || binary.ResolvedOp != BinaryExpr.ResolvedOpcode.Imp) {
        return expr;
      }

      var antecedent = StripBoundChecksFromConjunction(binary.E0, intervals, out var changed);
      if (!changed) {
        return expr;
      }

      return Expression.CreateImplies(antecedent, binary.E1);
    }

    /// <summary>
    /// Removes guaranteed bound checks from a conjunction, returning a (possibly) smaller conjunction.
    /// </summary>
    private Expression StripBoundChecksFromConjunction(Expression expr,
      IReadOnlyDictionary<BoundVar, (BigInteger Lower, BigInteger UpperExclusive)> intervals,
      out bool changed) {
      var conjuncts = new List<Expression>();
      CollectConjuncts(expr, conjuncts);

      changed = false;
      var filtered = new List<Expression>(conjuncts.Count);
      foreach (var conjunct in conjuncts) {
        if (IsGuaranteedBoundCheck(conjunct, intervals)) {
          changed = true;
          continue;
        }
        filtered.Add(conjunct);
      }

      if (!changed) {
        return expr;
      }

      return BuildConjunctionOrTrue(expr.Origin, filtered);
    }

    private static Expression BuildConjunctionOrTrue(IOrigin origin, List<Expression> conjuncts) {
      if (conjuncts.Count == 0) {
        return Expression.CreateBoolLiteral(origin, true);
      }

      var result = conjuncts[0];
      for (var i = 1; i < conjuncts.Count; i++) {
        result = Expression.CreateAnd(result, conjuncts[i]);
      }
      return result;
    }

    private static void CollectConjuncts(Expression expr, List<Expression> conjuncts) {
      expr = Expression.StripParens(expr);
      if (expr is BinaryExpr binary && IsAndBinaryExpr(binary)) {
        CollectConjuncts(binary.E0, conjuncts);
        CollectConjuncts(binary.E1, conjuncts);
        return;
      }
      conjuncts.Add(expr);
    }

    private static bool IsAndBinaryExpr(BinaryExpr binaryExpr) {
      return binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.And || binaryExpr.Op == BinaryExpr.Opcode.And;
    }

    /// <summary>
    /// Returns <c>true</c> iff <paramref name="expr"/> is a comparison that is guaranteed by the
    /// interval bounds for the involved bound variable.
    /// </summary>
    private static bool IsGuaranteedBoundCheck(Expression expr,
      IReadOnlyDictionary<BoundVar, (BigInteger Lower, BigInteger UpperExclusive)> intervals) {
      expr = Expression.StripParens(expr);
      if (expr is not BinaryExpr binary) {
        return false;
      }

      if (!TryGetBoundVar(binary.E0, out var boundVar) && !TryGetBoundVar(binary.E1, out boundVar)) {
        return false;
      }

      if (!intervals.TryGetValue(boundVar, out var bounds)) {
        return false;
      }

      var left = Expression.StripParensAndCasts(binary.E0);
      var right = Expression.StripParensAndCasts(binary.E1);

      return IsLowerBoundCheck(binary.ResolvedOp, left, right, boundVar, bounds.Lower) ||
             IsUpperBoundCheck(binary.ResolvedOp, left, right, boundVar, bounds.UpperExclusive);
    }

    private static bool IsLowerBoundCheck(BinaryExpr.ResolvedOpcode opcode, Expression left, Expression right,
      BoundVar boundVar, BigInteger expectedLower) {
      return opcode switch {
        BinaryExpr.ResolvedOpcode.Le => IsIntLiteral(left, expectedLower) && IsSameBoundVar(right, boundVar),
        BinaryExpr.ResolvedOpcode.Ge => IsSameBoundVar(left, boundVar) && IsIntLiteral(right, expectedLower),
        _ => false
      };
    }

    private static bool IsUpperBoundCheck(BinaryExpr.ResolvedOpcode opcode, Expression left, Expression right,
      BoundVar boundVar, BigInteger expectedUpperExclusive) {
      return opcode switch {
        BinaryExpr.ResolvedOpcode.Lt => IsSameBoundVar(left, boundVar) && IsIntLiteral(right, expectedUpperExclusive),
        BinaryExpr.ResolvedOpcode.Gt => IsIntLiteral(left, expectedUpperExclusive) && IsSameBoundVar(right, boundVar),
        _ => false
      };
    }

    private static bool IsIntLiteral(Expression expr, BigInteger expectedValue) {
      return Expression.IsIntLiteral(expr, out var actual) && actual == expectedValue;
    }

    private static bool IsSameBoundVar(Expression expr, BoundVar boundVar) {
      return TryGetBoundVar(expr, out var actual) && actual == boundVar;
    }

    private static bool TryGetBoundVar(Expression expr, out BoundVar boundVar) {
      expr = Expression.StripParensAndCasts(expr);
      if (expr is IdentifierExpr identifier && identifier.Var is BoundVar resolvedBoundVar) {
        boundVar = resolvedBoundVar;
        return true;
      }
      boundVar = null;
      return false;
    }
  }
}
