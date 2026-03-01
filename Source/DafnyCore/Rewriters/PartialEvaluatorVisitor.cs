using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;

namespace Microsoft.Dafny;

internal sealed partial class PartialEvaluatorEngine {
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
    private const string PartialPeelMarkerAttributeName = "_partial_peel";
    private readonly PartialEvaluatorEngine engine;
    private readonly Dictionary<Expression, Expression> replacements = new();
    private List<Dictionary<IVariable, ConstValue>> constScopes = new() { new Dictionary<IVariable, ConstValue>() };

    public PartialEvaluatorVisitor(PartialEvaluatorEngine engine) {
      this.engine = engine;
    }

    // ------------------- Public entry point -------------------

    /// <summary>
    /// Simplifies an expression by recursively rewriting its sub-expressions and by opportunistically
    /// evaluating side-effect-free fragments (for example, literals, finite comprehensions, and safe inlining).
    /// </summary>
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

    // ------------------- Replacement tracking -------------------

    private Expression GetReplacement(Expression expr) {
      return replacements.TryGetValue(expr, out var replacement) ? replacement : expr;
    }

    private void SetReplacement(Expression original, Expression replacement) {
      if (!ReferenceEquals(original, replacement)) {
        replacements[original] = replacement;
      }
    }

    // ------------------- Constant propagation (scoped locals) -------------------

    private void EnterScope() {
      constScopes.Add(new Dictionary<IVariable, ConstValue>());
    }

    private void ExitScope() {
      if (constScopes.Count > 1) {
        constScopes.RemoveAt(constScopes.Count - 1);
      } else {
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

    private void InvalidateConsts(IEnumerable<IVariable> variables) {
      foreach (var variable in variables) {
        InvalidateConst(variable);
      }
    }

    private void InvalidateAssignedLocals(Statement stmt) {
      foreach (var ide in stmt.GetAssignedLocals()) {
        if (ide?.Var != null) {
          InvalidateConst(ide.Var);
        }
      }
    }

    private static List<Dictionary<IVariable, ConstValue>> CloneConstScopes(List<Dictionary<IVariable, ConstValue>> scopes) {
      var snapshot = new List<Dictionary<IVariable, ConstValue>>(scopes.Count);
      foreach (var scope in scopes) {
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

      var resolvedStatements = assignStatement.ResolvedStatements;
      if (resolvedStatements == null) {
        return;
      }

      var declaredLocals = new HashSet<LocalVariable>(varDeclStmt.Locals);
      foreach (var statement in resolvedStatements) {
        if (statement is not SingleAssignStmt singleAssign) {
          continue;
        }

        if (singleAssign.Lhs.Resolved is not IdentifierExpr identifierExpr) {
          continue;
        }

        if (identifierExpr.Var is not LocalVariable local || !declaredLocals.Contains(local)) {
          continue;
        }

        if (singleAssign.Rhs is not ExprRhs exprRhs) {
          continue;
        }

        var rhsExpr = exprRhs.Expr;
        if (!ConstValue.TryCreate(rhsExpr, out var constValue)) {
          continue;
        }

        SetConst(identifierExpr.Var, constValue);
      }
    }

    // ------------------- Statement rewriting -------------------

    protected override bool VisitOneStmt(Statement stmt, ref PartialEvalState state) {
      switch (stmt) {
        case BlockStmt block:
          VisitBlock(block, state);
          break;
        case IfStmt ifStmt:
          VisitIf(ifStmt, state);
          break;
        case WhileStmt whileStmt:
          VisitWhile(whileStmt, state);
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
          SimplifySingleAssign(assignStmt, state);
          break;
        case CallStmt callStmt:
          SimplifyCallStmt(callStmt, state);
          break;
        case VarDeclStmt varDeclStmt:
          SimplifyVarDeclStmt(varDeclStmt, state);
          break;
        case AssignSuchThatStmt assignSuchThatStmt:
          assignSuchThatStmt.Expr = SimplifyExpression(assignSuchThatStmt.Expr, state);
          InvalidateAssignedLocals(assignSuchThatStmt);
          break;
        case ReturnStmt returnStmt:
          SimplifyReturnStmt(returnStmt, state);
          break;
        case HideRevealStmt hideRevealStmt:
          SimplifyHideRevealStmt(hideRevealStmt, state);
          break;
        default:
          VisitSubStatements(stmt, state);
          break;
      }
      return false;
    }

    // ------------------- Statement rewriting: blocks and control flow -------------------

    private void VisitBlock(BlockStmt block, PartialEvalState state) {
      EnterScope();
      foreach (var statement in block.Body) {
        Visit(statement, state);
      }
      ExitScope();
    }

    private void VisitIf(IfStmt ifStmt, PartialEvalState state) {
      ifStmt.Guard = SimplifyExpression(ifStmt.Guard, state);
      if (Expression.IsBoolLiteral(ifStmt.Guard, out var cond)) {
        if (cond) {
          Visit(ifStmt.Thn, state);
        } else if (ifStmt.Els != null) {
          Visit(ifStmt.Els, state);
        }
        return;
      }

      VisitBranchesWithIsolatedScopes(ifStmt.Thn, ifStmt.Els, state);
    }

    /// <summary>
    /// Visits both branches starting from the same incoming constant environment.
    /// After visiting, any local assigned in either branch is invalidated, since its value is no longer stable.
    /// </summary>
    private void VisitBranchesWithIsolatedScopes(Statement thenBranch, Statement elseBranch, PartialEvalState state) {
      // Save the original reference. Each branch runs on its own clone so that branch-local propagation
      // cannot leak across branches or back into the incoming environment.
      var original = constScopes;

      constScopes = CloneConstScopes(original);
      Visit(thenBranch, state);

      if (elseBranch != null) {
        constScopes = CloneConstScopes(original);
        Visit(elseBranch, state);
      }

      constScopes = original;
      var assigned = CollectAssignedLocalsDeep(thenBranch);
      if (elseBranch != null) {
        assigned.UnionWith(CollectAssignedLocalsDeep(elseBranch));
      }
      InvalidateConsts(assigned);
    }

    private void VisitWhile(WhileStmt whileStmt, PartialEvalState state) {
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
      InvalidateAssignedLocalsDeep(whileStmt.Body);
    }

    private void InvalidateAssignedLocalsDeep(Statement statement) {
      if (statement == null) {
        return;
      }
      InvalidateConsts(CollectAssignedLocalsDeep(statement));
    }

    // ------------------- Statement rewriting: assignments and calls -------------------

    private void SimplifySingleAssign(SingleAssignStmt assignStmt, PartialEvalState state) {
      if (assignStmt.Rhs is ExprRhs exprRhs) {
        exprRhs.Expr = SimplifyExpression(exprRhs.Expr, state);
      }
      InvalidateAssignedLocals(assignStmt);
    }

    private void SimplifyCallStmt(CallStmt callStmt, PartialEvalState state) {
      callStmt.MethodSelect.Obj = SimplifyExpression(callStmt.MethodSelect.Obj, state);
      for (var i = 0; i < callStmt.Args.Count; i++) {
        callStmt.Args[i] = SimplifyExpression(callStmt.Args[i], state);
      }
      InvalidateAssignedLocals(callStmt);
    }

    private void SimplifyVarDeclStmt(VarDeclStmt varDeclStmt, PartialEvalState state) {
      if (varDeclStmt.Assign != null) {
        Visit(varDeclStmt.Assign, state);
      }
      TryRecordLiteralLocalInitializers(varDeclStmt);
    }

    // ------------------- Statement rewriting: misc -------------------

    private void SimplifyReturnStmt(ReturnStmt returnStmt, PartialEvalState state) {
      if (returnStmt.Rhss == null) {
        return;
      }
      foreach (var rhs in returnStmt.Rhss) {
        if (rhs is ExprRhs returnExprRhs) {
          returnExprRhs.Expr = SimplifyExpression(returnExprRhs.Expr, state);
        }
      }
    }

    private void SimplifyHideRevealStmt(HideRevealStmt hideRevealStmt, PartialEvalState state) {
      if (hideRevealStmt.Exprs == null) {
        return;
      }
      for (var i = 0; i < hideRevealStmt.Exprs.Count; i++) {
        var exprToSimplify = hideRevealStmt.Exprs[i];
        if (exprToSimplify == null || !exprToSimplify.WasResolved()) {
          continue;
        }
        hideRevealStmt.Exprs[i] = SimplifyExpression(exprToSimplify, state);
      }
    }

    private void VisitSubStatements(Statement stmt, PartialEvalState state) {
      foreach (var sub in stmt.SubStatements) {
        Visit(sub, state);
      }
    }

    // ------------------- String and character literal helpers -------------------

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

      var tokens = TokenizeStringLiteral(value, isVerbatim).ToList();
      var totalLength = 0;
      var tokenLengths = new int[tokens.Count];
      for (var i = 0; i < tokens.Count; i++) {
        var len = Util.UnescapedCharacters(engine.options, tokens[i], isVerbatim).Count();
        tokenLengths[i] = len;
        totalLength += len;
      }

      if (end > totalLength) {
        return false;
      }

      var builder = new StringBuilder();
      var index = 0;
      for (var i = 0; i < tokens.Count; i++) {
        var tokenStart = index;
        var tokenEnd = index + tokenLengths[i];
        if (tokenEnd <= start) {
          index = tokenEnd;
          continue;
        }
        if (tokenStart >= end) {
          break;
        }

        var localStart = Math.Max(start, tokenStart) - tokenStart;
        var localEnd = Math.Min(end, tokenEnd) - tokenStart;
        if (tokenLengths[i] == 1) {
          builder.Append(tokens[i]);
        } else {
          builder.Append(tokens[i].Substring(localStart, localEnd - localStart));
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

    // ------------------- Expression rewriting -------------------

    protected override bool VisitOneExpr(Expression expr, ref PartialEvalState state) {
      switch (expr) {
        case ParensExpression parens:
          return SimplifyParensExpr(parens, state);
        case LiteralExpr:
          return false;
        case IdentifierExpr identifierExpr:
          return SimplifyIdentifierExpr(identifierExpr);
        case UnaryOpExpr unary:
          return SimplifyUnaryExpr(unary, state);
        case BinaryExpr binary:
          return SimplifyBinaryExpr(binary, state);
        case ITEExpr ite:
          return SimplifyIteExpr(ite, state);
        case FunctionCallExpr callExpr:
          return SimplifyFunctionCallExpr(callExpr, state);
        case ApplyExpr applyExpr:
          return SimplifyApplyExpr(applyExpr, state);
        case MemberSelectExpr memberSelectExpr:
          return SimplifyMemberSelectExpr(memberSelectExpr, state);
        case QuantifierExpr quantifierExpr:
          return SimplifyQuantifierExpr(quantifierExpr, state);
        case SetComprehension setComprehension:
          return SimplifySetComprehension(setComprehension, state);
        case MapComprehension mapComprehension:
          return SimplifyMapComprehension(mapComprehension, state);
        case LetExpr letExpr:
          return SimplifyLetExpr(letExpr, state);
        case SeqDisplayExpr seqDisplayExpr:
          return SimplifySeqDisplayExpr(seqDisplayExpr, state);
        case StmtExpr stmtExpr:
          return SimplifyStmtExpr(stmtExpr, state);
        case DatatypeValue datatypeValue:
          return SimplifyDatatypeValue(datatypeValue, state);
        case SetDisplayExpr setDisplayExpr:
          return SimplifySetDisplayExpr(setDisplayExpr, state);
        case MultiSetDisplayExpr multiSetDisplayExpr:
          return SimplifyMultiSetDisplayExpr(multiSetDisplayExpr, state);
        case SeqSelectExpr seqSelectExpr:
          return SimplifySeqSelectExpr(seqSelectExpr, state);
        case SeqUpdateExpr seqUpdateExpr:
          return SimplifySeqUpdateExpr(seqUpdateExpr, state);
        default:
          return false;
      }
    }

    // ------------------- Expression rewriting: atoms and identifiers -------------------

    private bool SimplifyParensExpr(ParensExpression parens, PartialEvalState state) {
      var result = SimplifyExpression(parens.E, state);
      SetReplacement(parens, result);
      return false;
    }

    private bool SimplifyIdentifierExpr(IdentifierExpr identifierExpr) {
      if (identifierExpr.Var != null && TryLookupConst(identifierExpr.Var, out var constValue)) {
        var result = constValue.CreateExpression(identifierExpr.Type);
        SetReplacement(identifierExpr, result);
      }
      return false;
    }

    // ------------------- Expression rewriting: operators and conditionals -------------------

    private bool SimplifyUnaryExpr(UnaryOpExpr unary, PartialEvalState state) {
      unary.E = SimplifyExpression(unary.E, state);
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot &&
          Expression.IsBoolLiteral(unary.E, out var boolValue)) {
        var result = Expression.CreateBoolLiteral(unary.Origin, !boolValue);
        SetReplacement(unary, result);
        return false;
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SeqLength) {
        if (TryGetStringLiteral(unary.E, out var value, out var isVerbatim)) {
          var result = CreateIntLiteral(unary.Origin, GetUnescapedStringLength(value, isVerbatim), unary.Type);
          SetReplacement(unary, result);
          return false;
        }
        if (TryGetSeqDisplayLiteral(unary.E, out var display)) {
          var result = CreateIntLiteral(unary.Origin, display.Elements.Count, unary.Type);
          SetReplacement(unary, result);
          return false;
        }
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.SetCard) {
        if (unary.E is SetComprehension setComprehension &&
            TryRewriteIdentitySetComprehensionCardinality(setComprehension, state, out var symbolicCardinality)) {
          SetReplacement(unary, symbolicCardinality);
          return false;
        }
        if (TryGetSetDisplayLiteral(unary.E, out var display)) {
          if (display.Elements.Count <= 1 || AllElementsAreLiterals(display.Elements)) {
            var distinct = new LiteralSet(display.Elements);
            var result = CreateIntLiteral(unary.Origin, distinct.Count, unary.Type);
            SetReplacement(unary, result);
            return false;
          }
        }
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.MultiSetCard) {
        if (TryGetMultiSetDisplayLiteral(unary.E, out var display)) {
          var result = CreateIntLiteral(unary.Origin, display.Elements.Count, unary.Type);
          SetReplacement(unary, result);
          return false;
        }
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.MapCard) {
        if (TryGetMapDisplayLiteral(unary.E, out var display)) {
          if (display.Elements.Count <= 1 || AllMapKeysAreLiterals(display)) {
            var distinctKeys = new LiteralSet(display.Elements.Select(entry => entry.A));
            var result = CreateIntLiteral(unary.Origin, distinctKeys.Count, unary.Type);
            SetReplacement(unary, result);
            return false;
          }
        }
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot &&
          Expression.IsIntLiteral(unary.E, out var bitvectorValue) &&
          unary.Type.NormalizeExpand().AsBitVectorType is { } bitvectorType) {
        var mask = (BigInteger.One << bitvectorType.Width) - BigInteger.One;
        var result = CreateIntLiteral(unary.Origin, mask ^ bitvectorValue, unary.Type);
        SetReplacement(unary, result);
        return false;
      }
      return false;
    }

    private bool TryRewriteIdentitySetComprehensionCardinality(
      SetComprehension setComprehension,
      PartialEvalState state,
      out Expression rewritten) {
      rewritten = null;
      if (setComprehension.BoundVars.Count != 1) {
        return false;
      }

      var boundVar = setComprehension.BoundVars[0];
      if (!QuantifierBounds.IsBoundVar(setComprehension.Term, boundVar)) {
        return false;
      }

      if (ContainsForeignBoundVar(setComprehension.Range, boundVar)) {
        return false;
      }

      var hasFunctionCallInRange = ContainsAnyFunctionCall(setComprehension.Range);

      if (!TryGetFiniteIntBoundFromComprehension(setComprehension, out var lower, out var upper)) {
        return false;
      }

      if (lower > upper) {
        rewritten = CreateIntLiteral(setComprehension.Origin, BigInteger.Zero, Type.Int);
        return true;
      }

      var domainSize = upper - lower + BigInteger.One;
      if (domainSize > 64) {
        return false;
      }

      var simplificationState = state.WithDepth(Math.Max(0, state.Depth - 1));

      Expression cardExpr = CreateIntLiteral(setComprehension.Origin, BigInteger.Zero, Type.Int);
      for (var value = lower; value <= upper; value++) {
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(setComprehension.Origin, value, boundVar.Type)
        };
        var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
        var instantiatedRange = setComprehension.Range == null
          ? Expression.CreateBoolLiteral(setComprehension.Origin, true)
          : substituter.Substitute(setComprehension.Range);
        var simplifiedRange = SimplifyExpression(instantiatedRange, simplificationState);

        Expression addend;
        if (Expression.IsBoolLiteral(simplifiedRange, out var rangeValue)) {
          addend = CreateIntLiteral(setComprehension.Origin, rangeValue ? BigInteger.One : BigInteger.Zero, Type.Int);
        } else {
          addend = new ITEExpr(
            setComprehension.Origin,
            false,
            simplifiedRange,
            CreateIntLiteral(setComprehension.Origin, BigInteger.One, Type.Int),
            CreateIntLiteral(setComprehension.Origin, BigInteger.Zero, Type.Int)) {
            Type = Type.Int
          };
        }

        cardExpr = CreateResolvedIntBinary(
          setComprehension.Origin,
          BinaryExpr.Opcode.Add,
          BinaryExpr.ResolvedOpcode.Add,
          cardExpr,
          addend);
      }

      rewritten = SimplifyExpression(cardExpr, simplificationState);
      rewritten.Type ??= Type.Int;
      return true;
    }

    private static bool ContainsRecursiveFunctionCall(Expression expr) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is FunctionCallExpr functionCallExpr && functionCallExpr.Function != null && functionCallExpr.Function.IsRecursive) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {
        if (ContainsRecursiveFunctionCall(subExpression)) {
          return true;
        }
      }

      return false;
    }

    private static bool ContainsForeignBoundVar(Expression expr, BoundVar allowedBoundVar) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is IdentifierExpr identifierExpr &&
          identifierExpr.Var is BoundVar otherBoundVar &&
          otherBoundVar != allowedBoundVar) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {
        if (ContainsForeignBoundVar(subExpression, allowedBoundVar)) {
          return true;
        }
      }

      return false;
    }

    private static bool ContainsAnyFunctionCall(Expression expr) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is FunctionCallExpr || expr is ApplyExpr) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {
        if (ContainsAnyFunctionCall(subExpression)) {
          return true;
        }
      }

      return false;
    }

    private static bool TryGetFiniteIntBoundFromComprehension(
      SetComprehension setComprehension,
      out BigInteger lower,
      out BigInteger upper) {
      lower = default;
      upper = default;
      if (setComprehension.Bounds != null && setComprehension.Bounds.Count == 1 &&
          setComprehension.Bounds[0] is IntBoundedPool intPool &&
          intPool.LowerBound != null &&
          intPool.UpperBound != null) {
        var normalizedLower = QuantifierBounds.NormalizeForPattern(intPool.LowerBound);
        var normalizedUpper = QuantifierBounds.NormalizeForPattern(intPool.UpperBound);
        if (Expression.IsIntLiteral(normalizedLower, out lower) &&
            Expression.IsIntLiteral(normalizedUpper, out upper)) {
          return true;
        }
      }

      if (setComprehension.BoundVars.Count != 1 || setComprehension.Range == null) {
        return false;
      }

      var boundVar = setComprehension.BoundVars[0];
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(setComprehension.Range, conjuncts);

      BigInteger? lowerCandidate = null;
      BigInteger? upperCandidate = null;
      foreach (var conjunct in conjuncts) {
        if (TryMatchLowerBound(conjunct, boundVar, out var lowerBound)) {
          lowerCandidate = lowerCandidate == null ? lowerBound : BigInteger.Max(lowerCandidate.Value, lowerBound);
        }

        if (TryMatchUpperBound(conjunct, boundVar, out var upperBound)) {
          upperCandidate = upperCandidate == null ? upperBound : BigInteger.Min(upperCandidate.Value, upperBound);
        }
      }

      if (lowerCandidate == null || upperCandidate == null) {
        return false;
      }

      lower = lowerCandidate.Value;
      upper = upperCandidate.Value;
      return true;
    }

    private bool SimplifyBinaryExpr(BinaryExpr binary, PartialEvalState state) {
      binary.E0 = SimplifyExpression(binary.E0, state);
      binary.E1 = SimplifyExpression(binary.E1, state);
      var result = engine.SimplifyBinary(binary);
      SetReplacement(binary, result);
      return false;
    }

    private bool SimplifyIteExpr(ITEExpr ite, PartialEvalState state) {
      ite.Test = SimplifyExpression(ite.Test, state);
      if (Expression.IsBoolLiteral(ite.Test, out var cond)) {
        var result = SimplifyExpression(cond ? ite.Thn : ite.Els, state);
        SetReplacement(ite, result);
        return false;
      }
      ite.Thn = SimplifyExpression(ite.Thn, state);
      ite.Els = SimplifyExpression(ite.Els, state);
      return false;
    }

    // ------------------- Expression rewriting: calls and selection -------------------

    private bool SimplifyFunctionCallExpr(FunctionCallExpr callExpr, PartialEvalState state) {
      callExpr.Receiver = SimplifyExpression(callExpr.Receiver, state);
      for (var i = 0; i < callExpr.Args.Count; i++) {
        var simplifiedArg = SimplifyExpression(callExpr.Args[i], state);
        callExpr.Args[i] = simplifiedArg;
        if (i < callExpr.Bindings.ArgumentBindings.Count) {
          callExpr.Bindings.ArgumentBindings[i].Actual = simplifiedArg;
        }
      }
      if (TrySimplifyArbitraryElement(callExpr, out var simplifiedElement)) {
        SetReplacement(callExpr, simplifiedElement);
        return false;
      }
      if (state.Depth > 0 && engine.TryInlineCall(callExpr, state, this, out var inlined)) {
        SetReplacement(callExpr, inlined);
        return false;
      }
      return false;
    }

    private bool SimplifyApplyExpr(ApplyExpr applyExpr, PartialEvalState state) {
      applyExpr.Function = SimplifyExpression(applyExpr.Function, state);
      for (var i = 0; i < applyExpr.Args.Count; i++) {
        applyExpr.Args[i] = SimplifyExpression(applyExpr.Args[i], state);
      }

      if (applyExpr.Function is not LambdaExpr lambdaExpr) {
        return false;
      }

      if (lambdaExpr.Range != null || lambdaExpr.BoundVars.Count != applyExpr.Args.Count) {
        return false;
      }

      for (var i = 0; i < applyExpr.Args.Count; i++) {
        if (!IsInlineableArgument(applyExpr.Args[i])) {
          return false;
        }
      }

      var substMap = new Dictionary<IVariable, Expression>(lambdaExpr.BoundVars.Count);
      for (var i = 0; i < lambdaExpr.BoundVars.Count; i++) {
        substMap[lambdaExpr.BoundVars[i]] = applyExpr.Args[i];
      }

      var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
      var substituted = substituter.Substitute(lambdaExpr.Body);
      var simplified = SimplifyExpression(substituted, state);
      SetReplacement(applyExpr, simplified);
      return false;
    }

    private bool SimplifyMemberSelectExpr(MemberSelectExpr memberSelectExpr, PartialEvalState state) {
      memberSelectExpr.Obj = SimplifyExpression(memberSelectExpr.Obj, state);
      if (TryGetTupleLiteral(memberSelectExpr.Obj, out var tuple) &&
          int.TryParse(memberSelectExpr.MemberName, out var tupleIndex) &&
          0 <= tupleIndex && tupleIndex < tuple.Arguments.Count &&
          IsLiteralLike(tuple.Arguments[tupleIndex])) {
        SetReplacement(memberSelectExpr, tuple.Arguments[tupleIndex]);
      }
      return false;
    }

    // ------------------- Expression rewriting: quantifiers -------------------

    private bool SimplifyQuantifierExpr(QuantifierExpr quantifierExpr, PartialEvalState state) {
      quantifierExpr.Range = quantifierExpr.Range == null ? null : SimplifyExpression(quantifierExpr.Range, state);
      quantifierExpr.Term = SimplifyExpression(quantifierExpr.Term, state);
      quantifierExpr.Bounds = SimplifyBounds(quantifierExpr.Bounds, state);

      if (quantifierExpr is ForallExpr && Expression.IsBoolLiteral(quantifierExpr.Term, out var forallTermValue) && forallTermValue) {
        SetReplacement(quantifierExpr, Expression.CreateBoolLiteral(quantifierExpr.Origin, true));
        return false;
      }

      if (quantifierExpr is ExistsExpr && Expression.IsBoolLiteral(quantifierExpr.Term, out var existsTermValue) && !existsTermValue) {
        SetReplacement(quantifierExpr, Expression.CreateBoolLiteral(quantifierExpr.Origin, false));
        return false;
      }

      if (quantifierExpr.Range != null && Expression.IsBoolLiteral(quantifierExpr.Range, out var rangeValue) && !rangeValue) {
        var vacuous = Expression.CreateBoolLiteral(quantifierExpr.Origin, quantifierExpr is ForallExpr);
        vacuous.Type = Type.Bool;
        SetReplacement(quantifierExpr, vacuous);
        return false;
      }

      var logicalBody = quantifierExpr.LogicalBody(bypassSplitQuantifier: true);
      var hasRecursiveLogicalBody = logicalBody != null && ContainsRecursiveFunctionCall(logicalBody);

      if (!hasRecursiveLogicalBody &&
          quantifierExpr is ForallExpr forallExpr &&
          TrySimplifyForallByFiniteSupport(forallExpr, state, out var finiteSupportReplacement)) {
        SetReplacement(quantifierExpr, finiteSupportReplacement);
        return false;
      }

      if (quantifierExpr is ForallExpr peeledForall &&
          TryPeelLowerBoundedForall(peeledForall, state, out var peeledReplacement)) {
        SetReplacement(quantifierExpr, peeledReplacement);
        return false;
      }

      if (quantifierExpr is ExistsExpr existsExpr) {
        if (TrySimplifyExistsByPointAssignments(existsExpr, state, out var pointReplacement)) {
          SetReplacement(quantifierExpr, pointReplacement);
          return false;
        }
        if (TrySimplifyExistsByDisjunctivePointAssignments(existsExpr, state, out var disjunctivePointReplacement)) {
          SetReplacement(quantifierExpr, disjunctivePointReplacement);
          return false;
        }
        if (TrySimplifyExistsArithmetic(existsExpr, state, out var arithmeticReplacement)) {
          SetReplacement(quantifierExpr, arithmeticReplacement);
          return false;
        }
        if (TrySimplifyExistsSequence(existsExpr, state, out var sequenceReplacement)) {
          SetReplacement(quantifierExpr, sequenceReplacement);
          return false;
        }
      }

      var inlineDepthForUnrolledInstances = Math.Max(0, state.Depth - 1);
      if (!hasRecursiveLogicalBody &&
          engine.TryUnrollQuantifier(
            quantifierExpr,
            expr => SimplifyExpression(expr, state.WithDepth(inlineDepthForUnrolledInstances)),
            out var unrolled,
            emitOverflowResidual: false)) {
        SetReplacement(quantifierExpr, unrolled);
      }
      return false;
    }

    private bool TryPeelLowerBoundedForall(ForallExpr forallExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (forallExpr.BoundVars.Count != 1 || forallExpr.Range != null) {
        return false;
      }

      if (Attributes.Contains(forallExpr.Attributes, PartialPeelMarkerAttributeName)) {
        return false;
      }

      if (forallExpr.Term is not BinaryExpr implication ||
          implication.ResolvedOp != BinaryExpr.ResolvedOpcode.Imp) {
        return false;
      }

      var boundVar = forallExpr.BoundVars[0];
      var normalizedType = boundVar.Type?.NormalizeExpand();
      if (normalizedType == null || !normalizedType.IsNumericBased(Type.NumericPersuasion.Int)) {
        return false;
      }

      if (!TryMatchLowerBound(implication.E0, boundVar, out var inclusiveLowerBound)) {
        return false;
      }

      if (ContainsRecursiveFunctionCall(implication.E1)) {
        return false;
      }

      const int peelCount = 1;
      var simplifyState = state.WithDepth(Math.Max(0, state.Depth - 1));
      var instantiatedConjuncts = new List<Expression>(peelCount + 1);
      for (var offset = 0; offset < peelCount; offset++) {
        var value = inclusiveLowerBound + offset;
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(forallExpr.Origin, value, boundVar.Type)
        };
        var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
        var instantiatedBody = substituter.Substitute(implication.E1);
        var simplifiedBody = SimplifyExpression(instantiatedBody, simplifyState);
        if (Expression.IsBoolLiteral(simplifiedBody, out var bodyValue)) {
          if (!bodyValue) {
            replacement = Expression.CreateBoolLiteral(forallExpr.Origin, false);
            replacement.Type = Type.Bool;
            return true;
          }
          continue;
        }
        simplifiedBody.Type ??= Type.Bool;
        instantiatedConjuncts.Add(simplifiedBody);
      }

      var nextLowerBound = inclusiveLowerBound + peelCount;
      var boundVarExpr = new IdentifierExpr(forallExpr.Origin, boundVar.Name) {
        Var = boundVar,
        Type = boundVar.Type
      };
      var residualGuard = new BinaryExpr(
        forallExpr.Origin,
        BinaryExpr.Opcode.Ge,
        boundVarExpr,
        CreateIntLiteral(forallExpr.Origin, nextLowerBound, boundVar.Type)) {
        ResolvedOp = BinaryExpr.ResolvedOpcode.Ge,
        Type = Type.Bool
      };
      var residualTerm = Expression.CreateImplies(residualGuard, implication.E1);
      residualTerm.Type = Type.Bool;
      var residualAttributes = forallExpr.Attributes;
      if (!Attributes.Contains(residualAttributes, PartialPeelMarkerAttributeName)) {
        residualAttributes = new Attributes(
          forallExpr.Origin,
          PartialPeelMarkerAttributeName,
          new List<Expression>(),
          residualAttributes);
      }
      var residualForall = new ForallExpr(
        forallExpr.Origin,
        forallExpr.BoundVars,
        null,
        residualTerm,
        residualAttributes) {
        Bounds = forallExpr.Bounds,
        Type = Type.Bool
      };
      instantiatedConjuncts.Add(residualForall);

      replacement = CombineConjuncts(instantiatedConjuncts, forallExpr.Origin);
      replacement.Type ??= Type.Bool;
      return true;
    }

    private bool TrySimplifyExistsByPointAssignments(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (existsExpr.BoundVars.Count == 0) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts);

      var assignments = new Dictionary<BoundVar, Expression>();
      var consumedConjuncts = new HashSet<Expression>();
      foreach (var conjunct in conjuncts) {
        if (!TryGetExistsPointAssignment(conjunct, existsExpr.BoundVars, out var boundVar, out var assignedValue)) {
          continue;
        }

        if (assignments.ContainsKey(boundVar)) {
          return false;
        }

        assignments[boundVar] = assignedValue;
        consumedConjuncts.Add(conjunct);
      }

      if (assignments.Count != existsExpr.BoundVars.Count) {
        return false;
      }

      var residualConjuncts = new List<Expression>();
      foreach (var conjunct in conjuncts) {
        if (!consumedConjuncts.Contains(conjunct)) {
          residualConjuncts.Add(conjunct);
        }
      }

      var residual = CombineConjuncts(residualConjuncts, existsExpr.Origin);
      var substMap = new Dictionary<IVariable, Expression>(assignments.Count);
      foreach (var assignment in assignments) {
        substMap[assignment.Key] = assignment.Value;
      }

      var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
      var substituted = substituter.Substitute(residual);
      replacement = SimplifyExpression(substituted, state);
      replacement.Type ??= Type.Bool;
      return true;
    }

    private bool TrySimplifyExistsByDisjunctivePointAssignments(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (existsExpr.BoundVars.Count == 0) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts);

      Expression disjunctiveChoices = null;
      foreach (var conjunct in conjuncts) {
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct);
        if (normalized is BinaryExpr binaryExpr &&
            (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Or || binaryExpr.Op == BinaryExpr.Opcode.Or)) {
          disjunctiveChoices = normalized;
          break;
        }
      }

      if (disjunctiveChoices == null) {
        return false;
      }

      var branchExpressions = new List<Expression>();
      QuantifierBounds.CollectDisjuncts(disjunctiveChoices, branchExpressions);
      if (branchExpressions.Count == 0 || branchExpressions.Count > 16) {
        return false;
      }

      var nonChoiceConjuncts = new List<Expression>();
      foreach (var conjunct in conjuncts) {
        if (!ReferenceEquals(conjunct, disjunctiveChoices)) {
          nonChoiceConjuncts.Add(conjunct);
        }
      }

      var rewrittenDisjuncts = new List<Expression>();
      foreach (var branch in branchExpressions) {
        var branchConjuncts = new List<Expression>();
        QuantifierBounds.CollectConjuncts(branch, branchConjuncts);
        var branchAssignments = new Dictionary<BoundVar, Expression>();
        var consumedInBranch = new HashSet<Expression>();

        foreach (var branchConjunct in branchConjuncts) {
          if (!TryGetExistsPointAssignment(branchConjunct, existsExpr.BoundVars, out var boundVar, out var assignedValue)) {
            continue;
          }

          if (branchAssignments.ContainsKey(boundVar)) {
            return false;
          }

          branchAssignments[boundVar] = assignedValue;
          consumedInBranch.Add(branchConjunct);
        }

        if (branchAssignments.Count != existsExpr.BoundVars.Count) {
          return false;
        }

        var branchResidualConjuncts = new List<Expression>(nonChoiceConjuncts);
        foreach (var branchConjunct in branchConjuncts) {
          if (!consumedInBranch.Contains(branchConjunct)) {
            branchResidualConjuncts.Add(branchConjunct);
          }
        }

        var branchResidual = CombineConjuncts(branchResidualConjuncts, existsExpr.Origin);
        var substMap = new Dictionary<IVariable, Expression>(branchAssignments.Count);
        foreach (var assignment in branchAssignments) {
          substMap[assignment.Key] = assignment.Value;
        }

        var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
        var branchSubstituted = substituter.Substitute(branchResidual);
        var branchSimplified = SimplifyExpression(branchSubstituted, state);
        rewrittenDisjuncts.Add(branchSimplified);
      }

      var rewritten = CombineDisjuncts(rewrittenDisjuncts, existsExpr.Origin);
      replacement = SimplifyExpression(rewritten, state);
      replacement.Type ??= Type.Bool;
      return true;
    }

    private static bool TryGetExistsPointAssignment(Expression expr, IReadOnlyList<BoundVar> boundVars,
      out BoundVar boundVar, out Expression assignedValue) {
      boundVar = null;
      assignedValue = null;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
      if (!isEq) {
        return false;
      }

      if (TryFindMatchingBoundVar(binaryExpr.E0, boundVars, out boundVar) &&
          !ContainsAnyBoundVar(binaryExpr.E1, boundVars)) {
        assignedValue = binaryExpr.E1;
        return true;
      }

      if (TryFindMatchingBoundVar(binaryExpr.E1, boundVars, out boundVar) &&
          !ContainsAnyBoundVar(binaryExpr.E0, boundVars)) {
        assignedValue = binaryExpr.E0;
        return true;
      }

      boundVar = null;
      assignedValue = null;
      return false;
    }

    private static bool TryFindMatchingBoundVar(Expression expr, IReadOnlyList<BoundVar> boundVars, out BoundVar boundVar) {
      foreach (var candidate in boundVars) {
        if (QuantifierBounds.IsBoundVar(expr, candidate)) {
          boundVar = candidate;
          return true;
        }
      }

      boundVar = null;
      return false;
    }

    private static bool ContainsAnyBoundVar(Expression expr, IReadOnlyList<BoundVar> boundVars) {
      foreach (var boundVar in boundVars) {
        if (ContainsBoundVar(expr, boundVar)) {
          return true;
        }
      }

      return false;
    }


    private bool TrySimplifyForallByFiniteSupport(ForallExpr forallExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (forallExpr.BoundVars.Count != 1) {
        return false;
      }

      if (forallExpr.SplitQuantifier != null || forallExpr.SplitQuantifierExpression != null) {
        return false;
      }

      var boundVar = forallExpr.BoundVars[0];
      var normalizedType = boundVar.Type?.NormalizeExpand();
      if (normalizedType == null || !normalizedType.IsNumericBased(Type.NumericPersuasion.Int)) {
        return false;
      }

      var logicalBody = forallExpr.LogicalBody(bypassSplitQuantifier: true);
      if (logicalBody == null) {
        return false;
      }

      if (!ContainsBoundVar(logicalBody, boundVar)) {
        return false;
      }

      Expression independentFactor = null;
      if (forallExpr.Range == null && IsDefinitelyInhabitedBoundType(boundVar.Type)) {
        var conjuncts = new List<Expression>();
        QuantifierBounds.CollectConjuncts(logicalBody, conjuncts);
        var dependentConjuncts = new List<Expression>();
        var independentConjuncts = new List<Expression>();
        foreach (var conjunct in conjuncts) {
          if (ContainsBoundVar(conjunct, boundVar)) {
            dependentConjuncts.Add(conjunct);
          } else {
            independentConjuncts.Add(conjunct);
          }
        }

        if (independentConjuncts.Count > 0) {
          independentFactor = CombineConjuncts(independentConjuncts, forallExpr.Origin);
          if (dependentConjuncts.Count == 0) {
            replacement = SimplifyExpression(independentFactor, state.WithDepth(Math.Max(0, state.Depth - 1)));
            replacement.Type ??= Type.Bool;
            return true;
          }

          logicalBody = CombineConjuncts(dependentConjuncts, forallExpr.Origin);
        }
      }

      var supportValues = new HashSet<BigInteger>();
      if (!TryCollectFiniteSupportValues(logicalBody, boundVar, supportValues) || supportValues.Count == 0 || supportValues.Count > 32) {
        return false;
      }

      var valuesToCheck = new List<BigInteger>(supportValues);
      var outsideValue = BigInteger.Zero;
      while (supportValues.Contains(outsideValue)) {
        outsideValue++;
      }
      valuesToCheck.Add(outsideValue);

      var instantiatedConjuncts = new List<Expression>(valuesToCheck.Count);
      foreach (var value in valuesToCheck) {
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(forallExpr.Origin, value, boundVar.Type)
        };
        var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
        var instantiated = substituter.Substitute(logicalBody);
        var simplified = SimplifyExpression(instantiated, state.WithDepth(Math.Max(0, state.Depth - 1)));
        simplified.Type ??= Type.Bool;
        instantiatedConjuncts.Add(simplified);
      }

      replacement = CombineConjuncts(instantiatedConjuncts, forallExpr.Origin);
      if (independentFactor != null) {
        replacement = Expression.CreateAnd(independentFactor, replacement);
      }
      replacement = SimplifyExpression(replacement, state.WithDepth(Math.Max(0, state.Depth - 1)));
      replacement.Type ??= Type.Bool;
      return true;
    }

    private static bool TryCollectFiniteSupportValues(Expression expr, BoundVar boundVar, HashSet<BigInteger> supportValues) {
      if (expr == null) {
        return true;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (QuantifierBounds.IsBoundVar(expr, boundVar)) {
        return false;
      }

      if (expr is SeqSelectExpr { SelectOne: true, E0: not null, E1: null } selectExpr &&
          QuantifierBounds.IsBoundVar(selectExpr.E0, boundVar)) {
        return TryCollectIntKeysFromMapLiteral(selectExpr.Seq, supportValues);
      }

      if (expr is BinaryExpr binaryExpr) {
        if (!TryCollectFiniteSupportFromBinary(binaryExpr, boundVar, supportValues, out var shouldRecurse)) {
          return false;
        }

        if (!shouldRecurse) {
          return true;
        }
      }

      if (expr is FunctionCallExpr functionCallExpr) {
        foreach (var arg in functionCallExpr.Args) {
          if (ContainsBoundVar(arg, boundVar)) {
            return false;
          }
        }
      }

      foreach (var subExpression in expr.SubExpressions) {
        if (!TryCollectFiniteSupportValues(subExpression, boundVar, supportValues)) {
          return false;
        }
      }

      return true;
    }

    private static bool TryCollectFiniteSupportFromBinary(BinaryExpr binaryExpr, BoundVar boundVar,
      HashSet<BigInteger> supportValues, out bool shouldRecurse) {
      shouldRecurse = true;
      var resolvedOp = binaryExpr.ResolvedOp;

      var leftHasBoundVar = ContainsBoundVar(binaryExpr.E0, boundVar);
      var rightHasBoundVar = ContainsBoundVar(binaryExpr.E1, boundVar);

      if (resolvedOp is BinaryExpr.ResolvedOpcode.EqCommon or BinaryExpr.ResolvedOpcode.NeqCommon) {
        if (!leftHasBoundVar && !rightHasBoundVar) {
          return true;
        }

        if (TryCollectBoundVarComparisonValue(binaryExpr.E0, binaryExpr.E1, boundVar, supportValues)) {
          shouldRecurse = false;
          return true;
        }

        shouldRecurse = true;
        return true;
      }

      if (resolvedOp is BinaryExpr.ResolvedOpcode.InSet or BinaryExpr.ResolvedOpcode.InMultiSet or BinaryExpr.ResolvedOpcode.InMap) {
        if (!leftHasBoundVar && !rightHasBoundVar) {
          return true;
        }

        shouldRecurse = false;
        if (!QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar)) {
          return false;
        }

        return TryCollectIntValuesFromSetOrMapLiteral(binaryExpr.E1, supportValues);
      }

      if ((leftHasBoundVar || rightHasBoundVar) &&
          resolvedOp is BinaryExpr.ResolvedOpcode.Lt or BinaryExpr.ResolvedOpcode.Le or BinaryExpr.ResolvedOpcode.Gt or BinaryExpr.ResolvedOpcode.Ge) {
        return false;
      }

      return true;
    }

    private static bool TryCollectBoundVarComparisonValue(Expression left, Expression right, BoundVar boundVar,
      HashSet<BigInteger> supportValues) {
      if (QuantifierBounds.IsBoundVar(left, boundVar) && Expression.IsIntLiteral(right, out var rightLiteral)) {
        supportValues.Add(rightLiteral);
        return true;
      }

      if (QuantifierBounds.IsBoundVar(right, boundVar) && Expression.IsIntLiteral(left, out var leftLiteral)) {
        supportValues.Add(leftLiteral);
        return true;
      }

      return false;
    }

    private static bool TryCollectIntValuesFromSetOrMapLiteral(Expression expr, HashSet<BigInteger> supportValues) {
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is SetDisplayExpr setDisplayExpr) {
        foreach (var element in setDisplayExpr.Elements) {
          if (!Expression.IsIntLiteral(element, out var value)) {
            return false;
          }

          supportValues.Add(value);
        }

        return true;
      }

      if (expr is MultiSetDisplayExpr multiSetDisplayExpr) {
        foreach (var element in multiSetDisplayExpr.Elements) {
          if (!Expression.IsIntLiteral(element, out var value)) {
            return false;
          }

          supportValues.Add(value);
        }

        return true;
      }

      if (expr is MapDisplayExpr mapDisplayExpr) {
        foreach (var entry in mapDisplayExpr.Elements) {
          if (!Expression.IsIntLiteral(entry.A, out var key)) {
            return false;
          }

          supportValues.Add(key);
        }

        return true;
      }

      return false;
    }

    private static bool TryCollectIntKeysFromMapLiteral(Expression expr, HashSet<BigInteger> supportValues) {
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not MapDisplayExpr mapDisplayExpr) {
        return false;
      }

      foreach (var entry in mapDisplayExpr.Elements) {
        if (!Expression.IsIntLiteral(entry.A, out var key)) {
          return false;
        }

        supportValues.Add(key);
      }

      return true;
    }


    private static bool IsDefinitelyInhabitedBoundType(Type type) {
      var normalized = type?.NormalizeExpand();
      if (normalized == null) {
        return false;
      }

      if (normalized is IntType) {
        return true;
      }

      if (normalized.IsBoolType || normalized.IsCharType) {
        return true;
      }

      return normalized.AsSubsetType != null && normalized.AsSubsetType == Type.Int.AsSubsetType;
    }

    /// <summary>
    /// Recognizes a small arithmetic pattern inside <c>exists</c> and evaluates it to a boolean literal.
    /// This avoids expensive downstream reasoning for a few common "divisibility + lower bound" idioms.
    /// </summary>
    private bool TrySimplifyExistsArithmetic(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (existsExpr.BoundVars.Count != 1) {
        return false;
      }

      var boundVar = existsExpr.BoundVars[0];
      var subsetType = boundVar.Type.AsSubsetType;
      var isNat = subsetType == engine.systemModuleManager.NatDecl;
      var isInt = !isNat && boundVar.Type.NormalizeExpand() is IntType;
      if (!isNat && !isInt) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts);

      BigInteger? lowerBound = isNat ? BigInteger.Zero : null;
      Expression targetExpr = null;
      Expression divisorExpr = null;
      foreach (var conjunct in conjuncts) {
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct);
        if (Expression.IsBoolLiteral(normalized, out var boolValue)) {
          if (!boolValue) {
            replacement = Expression.CreateBoolLiteral(existsExpr.Origin, false);
            replacement.Type = Type.Bool;
            return true;
          }
          continue;
        }

        if (TryMatchLowerBound(normalized, boundVar, out var lower)) {
          lowerBound = lowerBound == null ? lower : BigInteger.Max(lowerBound.Value, lower);
          continue;
        }

        if (targetExpr == null && divisorExpr == null &&
            TryMatchLinearMultiplicationEquality(normalized, boundVar, out var targetCandidate, out var divisorCandidate)) {
          targetExpr = targetCandidate;
          divisorExpr = divisorCandidate;
          continue;
        }

        return false;
      }

      if (lowerBound != null && targetExpr == null && divisorExpr == null) {
        replacement = Expression.CreateBoolLiteral(existsExpr.Origin, true);
        replacement.Type = Type.Bool;
        return true;
      }

      if (lowerBound == null || targetExpr == null || divisorExpr == null) {
        return false;
      }

      if (!IsIntLike(targetExpr) || !IsIntLike(divisorExpr)) {
        return false;
      }

      var normalizedTarget = QuantifierBounds.NormalizeForPattern(targetExpr);
      var normalizedDivisor = QuantifierBounds.NormalizeForPattern(divisorExpr);
      QuantifierBounds.EnsureExpressionType(normalizedTarget, Type.Int);
      QuantifierBounds.EnsureExpressionType(normalizedDivisor, Type.Int);

      var simplifiedTarget = SimplifyExpression(normalizedTarget, state);
      var simplifiedDivisor = SimplifyExpression(normalizedDivisor, state);
      if (!Expression.IsIntLiteral(simplifiedTarget, out var targetLiteral) ||
          !Expression.IsIntLiteral(simplifiedDivisor, out var divisorLiteral)) {
        return false;
      }

      if (divisorLiteral < 0) {
        divisorLiteral = BigInteger.Negate(divisorLiteral);
        targetLiteral = BigInteger.Negate(targetLiteral);
      }

      var result = divisorLiteral == 0
        ? targetLiteral == 0
        : targetLiteral % divisorLiteral == 0 && targetLiteral / divisorLiteral >= lowerBound.Value;
      replacement = Expression.CreateBoolLiteral(existsExpr.Origin, result);
      replacement.Type = Type.Bool;
      return true;
    }

    private static bool TryMatchLowerBound(Expression expr, BoundVar boundVar, out BigInteger lowerBound) {
      lowerBound = default;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isGe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge || binaryExpr.Op == BinaryExpr.Opcode.Ge;
      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      if (!isGe && !isGt && !isLe && !isLt) {
        return false;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar) && Expression.IsIntLiteral(binaryExpr.E1, out var literalRight)) {
        lowerBound = isGt ? literalRight + 1 : literalRight;
        return isGe || isGt;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar) && Expression.IsIntLiteral(binaryExpr.E0, out var literalLeft)) {
        lowerBound = isLt ? literalLeft + 1 : literalLeft;
        return isLe || isLt;
      }

      return false;
    }

    private static bool TryMatchUpperBound(Expression expr, BoundVar boundVar, out BigInteger upperBound) {
      upperBound = default;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isGe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge || binaryExpr.Op == BinaryExpr.Opcode.Ge;
      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;
      var isLe = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Le || binaryExpr.Op == BinaryExpr.Opcode.Le;
      var isLt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Lt || binaryExpr.Op == BinaryExpr.Opcode.Lt;
      if (!isGe && !isGt && !isLe && !isLt) {
        return false;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar) && Expression.IsIntLiteral(binaryExpr.E1, out var literalRight)) {
        upperBound = isLt ? literalRight - 1 : literalRight;
        return isLe || isLt;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar) && Expression.IsIntLiteral(binaryExpr.E0, out var literalLeft)) {
        upperBound = isGt ? literalLeft - 1 : literalLeft;
        return isGe || isGt;
      }

      return false;
    }

    private static bool TryMatchLinearMultiplicationEquality(Expression expr, BoundVar boundVar,
      out Expression target, out Expression divisor) {
      target = null;
      divisor = null;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }
      var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
      if (!isEq) {
        return false;
      }

      if (TryExtractScaledBoundVar(binaryExpr.E0, boundVar, out var leftDivisor, out var leftOffset) &&
          !ContainsBoundVar(binaryExpr.E1, boundVar)) {
        target = QuantifierBounds.NormalizeForPattern(Expression.CreateSubtract(binaryExpr.E1, leftOffset));
        divisor = QuantifierBounds.NormalizeForPattern(leftDivisor);
        return IsIntLike(target) && IsIntLike(divisor);
      }

      if (TryExtractScaledBoundVar(binaryExpr.E1, boundVar, out var rightDivisor, out var rightOffset) &&
          !ContainsBoundVar(binaryExpr.E0, boundVar)) {
        target = QuantifierBounds.NormalizeForPattern(Expression.CreateSubtract(binaryExpr.E0, rightOffset));
        divisor = QuantifierBounds.NormalizeForPattern(rightDivisor);
        return IsIntLike(target) && IsIntLike(divisor);
      }

      return false;
    }

    private static bool TryExtractScaledBoundVar(Expression expr, BoundVar boundVar,
      out Expression divisor, out Expression offset) {
      divisor = null;
      offset = null;
      expr = QuantifierBounds.NormalizeForPattern(expr);

      if (TryExtractMulFactor(expr, boundVar, out divisor)) {
        offset = CreateIntLiteral(expr.Origin, BigInteger.Zero, Type.Int);
        return true;
      }

      if (expr is BinaryExpr binaryExpr) {
        var isAdd = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Add || binaryExpr.Op == BinaryExpr.Opcode.Add;
        if (!isAdd) {
          return false;
        }

        if (TryExtractMulFactor(binaryExpr.E0, boundVar, out divisor) && !ContainsBoundVar(binaryExpr.E1, boundVar)) {
          offset = binaryExpr.E1;
          return IsIntLike(offset);
        }

        if (TryExtractMulFactor(binaryExpr.E1, boundVar, out divisor) && !ContainsBoundVar(binaryExpr.E0, boundVar)) {
          offset = binaryExpr.E0;
          return IsIntLike(offset);
        }
      }

      return false;
    }

    private static bool TryExtractMulFactor(Expression expr, BoundVar boundVar, out Expression factor) {
      factor = null;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isMul = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Mul || binaryExpr.Op == BinaryExpr.Opcode.Mul;
      if (!isMul) {
        return false;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar) && !ContainsBoundVar(binaryExpr.E1, boundVar)) {
        factor = binaryExpr.E1;
        return true;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar) && !ContainsBoundVar(binaryExpr.E0, boundVar)) {
        factor = binaryExpr.E0;
        return true;
      }

      return false;
    }

    private static bool ContainsBoundVar(Expression expr, BoundVar boundVar) {
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (QuantifierBounds.IsBoundVar(expr, boundVar)) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {
        if (ContainsBoundVar(subExpression, boundVar)) {
          return true;
        }
      }

      return false;
    }

    private static bool IsIntLike(Expression expr) {
      return expr.Type != null && expr.Type.NormalizeExpand().IsNumericBased(Type.NumericPersuasion.Int);
    }

    private static Expression CreateResolvedIntBinary(
      IOrigin origin,
      BinaryExpr.Opcode op,
      BinaryExpr.ResolvedOpcode resolvedOp,
      Expression left,
      Expression right) {
      var binary = new BinaryExpr(origin, op, left, right) {
        ResolvedOp = resolvedOp,
        Type = Type.Int
      };
      return binary;
    }

    /// <summary>
    /// Recognizes a bounded <c>exists</c> over sequences/strings and tries to decide it by enumerating all
    /// candidates up to the configured unroll cap. If evaluation becomes unknown for a candidate, we stop
    /// early and keep the quantifier unchanged.
    /// </summary>
    private bool TrySimplifyExistsSequence(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      replacement = null;
      if (existsExpr.BoundVars.Count != 1) {
        return false;
      }

      var seqVar = existsExpr.BoundVars[0];
      var normalizedType = seqVar.Type.NormalizeExpand();
      var isString = normalizedType.IsStringType;
      var seqType = normalizedType.AsSeqType;
      if (!isString && seqType == null) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts);

      int? length = null;
      Expression lengthExpr = null;
      foreach (var conjunct in conjuncts) {
        if (engine.GetQuantifierBounds().TryGetSeqLengthConstraint(conjunct, seqVar, out var lengthValue)) {
          length = lengthValue;
          lengthExpr = conjunct;
          break;
        }
      }
      if (length == null) {
        return false;
      }

      List<Expression> elementDomain = null;
      Expression domainExpr = null;
      foreach (var conjunct in conjuncts) {
        if (conjunct is ForallExpr forallExpr &&
            engine.GetQuantifierBounds().TryGetElementDomainConstraint(forallExpr, seqVar, length.Value, out var domain)) {
          elementDomain = domain;
          domainExpr = conjunct;
          break;
        }
      }
      if (elementDomain == null || elementDomain.Count == 0) {
        return false;
      }

      if (lengthExpr != null) {
        conjuncts.Remove(lengthExpr);
      }
      if (domainExpr != null) {
        conjuncts.Remove(domainExpr);
      }

      var residual = CombineConjuncts(conjuncts, existsExpr.Origin);

      var cap = engine.GetPartialEvalUnrollCap();
      var domainSize = new BigInteger(elementDomain.Count);
      var product = BigInteger.One;
      for (var index = 0; index < length.Value; index++) {
        product *= domainSize;
        if (cap > 0 && product > cap) {
          return false;
        }
      }

      var elementType = isString ? Type.Char : seqType!.Arg;
      var evaluated = TryEvaluateExistsSequenceCandidates(
        existsExpr, seqVar, elementDomain, elementType, length.Value, isString, residual, state, out replacement);
      return evaluated;
    }

    private bool TryEvaluateExistsSequenceCandidates(
      ExistsExpr existsExpr,
      BoundVar seqVar,
      List<Expression> elementDomain,
      Type elementType,
      int length,
      bool isString,
      Expression residual,
      PartialEvalState state,
      out Expression replacement) {
      replacement = null;
      Expression localReplacement = null;
      var elements = new List<Expression>(length);
      var foundUnknown = false;

      bool EvaluateCandidate() {
        Expression literalExpr;
        if (isString) {
          var chars = new char[length];
          for (var index = 0; index < length; index++) {
            if (!TryGetCharLiteral(elements[index], out var value)) {
              return false;
            }
            chars[index] = value;
          }
          literalExpr = CreateStringLiteral(existsExpr.Origin, new string(chars), seqVar.Type, false);
        } else {
          var seqElements = elements.Select(element => element).ToList();
          literalExpr = CreateSeqDisplayLiteral(existsExpr.Origin, seqElements, seqVar.Type);
        }

        var substMap = new Dictionary<IVariable, Expression> { [seqVar] = literalExpr };
        var substituter = new Substituter(null, substMap, null, null, engine.systemModuleManager);
        var instantiated = substituter.Substitute(residual);
        var simplified = SimplifyExpression(instantiated, state);
        if (!Expression.IsBoolLiteral(simplified, out var result)) {
          foundUnknown = true;
          return false;
        }
        return result;
      }

      bool Enumerate(int position) {
        if (position == length) {
          if (EvaluateCandidate()) {
            localReplacement = Expression.CreateBoolLiteral(existsExpr.Origin, true);
            localReplacement.Type = Type.Bool;
            return true;
          }
          return false;
        }

        foreach (var element in elementDomain) {
          elements.Add(element);
          if (Enumerate(position + 1)) {
            return true;
          }
          elements.RemoveAt(elements.Count - 1);
          if (foundUnknown) {
            return false;
          }
        }

        return false;
      }

      if (Enumerate(0)) {
        replacement = localReplacement;
        return true;
      }
      if (foundUnknown) {
        return false;
      }

      replacement = Expression.CreateBoolLiteral(existsExpr.Origin, false);
      replacement.Type = Type.Bool;
      return true;
    }

    // ------------------- Expression rewriting: quantifier helpers -------------------

    private static Expression CombineConjuncts(List<Expression> conjuncts, IOrigin origin) {
      if (conjuncts == null || conjuncts.Count == 0) {
        var literal = Expression.CreateBoolLiteral(origin, true);
        literal.Type = Type.Bool;
        return literal;
      }

      var current = conjuncts[0];
      for (var index = 1; index < conjuncts.Count; index++) {
        current = Expression.CreateAnd(current, conjuncts[index]);
      }
      if (current.Type == null) {
        current.Type = Type.Bool;
      }
      return current;
    }

    private static Expression CombineDisjuncts(List<Expression> disjuncts, IOrigin origin) {
      if (disjuncts == null || disjuncts.Count == 0) {
        var literal = Expression.CreateBoolLiteral(origin, false);
        literal.Type = Type.Bool;
        return literal;
      }

      var current = disjuncts[0];
      for (var index = 1; index < disjuncts.Count; index++) {
        current = Expression.CreateOr(current, disjuncts[index]);
      }
      if (current.Type == null) {
        current.Type = Type.Bool;
      }
      return current;
    }

    // ------------------- Expression rewriting: comprehensions -------------------

    private bool SimplifySetComprehension(SetComprehension setComprehension, PartialEvalState state) {
      setComprehension.Range = SimplifyExpression(setComprehension.Range, state);
      setComprehension.Term = SimplifyExpression(setComprehension.Term, state);
      setComprehension.Bounds = SimplifyBounds(setComprehension.Bounds, state);
      if (TrySimplifyMapKeySetComprehension(setComprehension, out var keySetDisplay)) {
        SetReplacement(setComprehension, keySetDisplay);
        return false;
      }
      if (engine.TryMaterializeSetComprehension(setComprehension, out var setDisplay)) {
        SetReplacement(setComprehension, setDisplay);
      }
      return false;
    }

    private bool TrySimplifyMapKeySetComprehension(SetComprehension setComprehension, out SetDisplayExpr setDisplay) {
      setDisplay = null;
      if (setComprehension.BoundVars.Count != 1 || setComprehension.Range == null) {
        return false;
      }

      var boundVar = setComprehension.BoundVars[0];
      if (!QuantifierBounds.IsBoundVar(setComprehension.Term, boundVar)) {
        return false;
      }

      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(setComprehension.Range, conjuncts);

      MapDisplayExpr mapDisplay = null;
      foreach (var conjunct in conjuncts) {
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct);

        if (TryMatchBoundVarMapMembership(normalized, boundVar, out var membershipMap)) {
          if (mapDisplay != null && !MapDisplayLiteralsEqual(mapDisplay, membershipMap)) {
            return false;
          }
          mapDisplay = membershipMap;
          continue;
        }

        if (!TryMatchPositiveMapValueConstraint(normalized, boundVar, mapDisplay, out var valueMap)) {
          return false;
        }

        if (mapDisplay == null) {
          mapDisplay = valueMap;
        }
      }

      if (mapDisplay == null) {
        return false;
      }

      var keys = new List<Expression>();
      foreach (var entry in mapDisplay.Elements) {
        if (!Expression.IsIntLiteral(entry.B, out var multiplicity)) {
          return false;
        }

        if (multiplicity > 0) {
          keys.Add(entry.A);
        }
      }

      setDisplay = CreateSetDisplayLiteral(setComprehension.Origin, keys, setComprehension.Type);
      return true;
    }

    private static bool TryMatchBoundVarMapMembership(Expression expr, BoundVar boundVar, out MapDisplayExpr mapDisplay) {
      mapDisplay = null;
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isInMap = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InMap || binaryExpr.Op == BinaryExpr.Opcode.In;
      if (!isInMap || !QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar)) {
        return false;
      }

      if (!TryGetMapDisplayLiteral(binaryExpr.E1, out var mapLiteral) ||
          !AllMapKeysAreLiterals(mapLiteral) ||
          !AllElementsAreLiterals(mapLiteral)) {
        return false;
      }

      mapDisplay = mapLiteral;
      return true;
    }

    private static bool TryMatchPositiveMapValueConstraint(Expression expr, BoundVar boundVar, MapDisplayExpr expectedMap,
      out MapDisplayExpr mapDisplay) {
      mapDisplay = null;
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isGt = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Gt || binaryExpr.Op == BinaryExpr.Opcode.Gt;
      if (!isGt) {
        return false;
      }

      if (TryGetMapSelectOverBoundVar(binaryExpr.E0, boundVar, expectedMap, out mapDisplay) &&
          Expression.IsIntLiteral(binaryExpr.E1, out var rightLiteral) &&
          rightLiteral == 0) {
        return true;
      }

      if (TryGetMapSelectOverBoundVar(binaryExpr.E1, boundVar, expectedMap, out mapDisplay) &&
          Expression.IsIntLiteral(binaryExpr.E0, out var leftLiteral) &&
          leftLiteral == 0) {
        return true;
      }

      mapDisplay = null;
      return false;
    }

    private static bool TryGetMapSelectOverBoundVar(Expression expr, BoundVar boundVar, MapDisplayExpr expectedMap,
      out MapDisplayExpr mapDisplay) {
      mapDisplay = null;
      expr = QuantifierBounds.NormalizeForPattern(expr);
      if (expr is not SeqSelectExpr { SelectOne: true, E0: not null, E1: null } selectExpr) {
        return false;
      }

      if (!QuantifierBounds.IsBoundVar(selectExpr.E0, boundVar)) {
        return false;
      }

      if (!TryGetMapDisplayLiteral(selectExpr.Seq, out var mapLiteral) ||
          !AllMapKeysAreLiterals(mapLiteral) ||
          !AllElementsAreLiterals(mapLiteral)) {
        return false;
      }

      if (expectedMap != null && !MapDisplayLiteralsEqual(expectedMap, mapLiteral)) {
        return false;
      }

      mapDisplay = mapLiteral;
      return true;
    }

    private bool SimplifyMapComprehension(MapComprehension mapComprehension, PartialEvalState state) {
      mapComprehension.Range = SimplifyExpression(mapComprehension.Range, state);
      mapComprehension.Term = SimplifyExpression(mapComprehension.Term, state);
      if (mapComprehension.TermLeft != null) {
        mapComprehension.TermLeft = SimplifyExpression(mapComprehension.TermLeft, state);
      }
      mapComprehension.Bounds = SimplifyBounds(mapComprehension.Bounds, state);
      if (engine.TryMaterializeMapComprehension(mapComprehension, state, SimplifyExpression, out var mapDisplay)) {
        SetReplacement(mapComprehension, mapDisplay);
      }
      return false;
    }

    // ------------------- Expression rewriting: let and local statement expressions -------------------

    private bool SimplifyLetExpr(LetExpr letExpr, PartialEvalState state) {
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
            if (ConstValue.TryCreate(letExpr.RHSs[i], out var letConstValue)) {
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
    }

    // ------------------- Expression rewriting: collection literals -------------------

    private bool SimplifySeqDisplayExpr(SeqDisplayExpr seqDisplayExpr, PartialEvalState state) {
      for (var i = 0; i < seqDisplayExpr.Elements.Count; i++) {
        seqDisplayExpr.Elements[i] = SimplifyExpression(seqDisplayExpr.Elements[i], state);
      }
      return false;
    }

    private bool SimplifyStmtExpr(StmtExpr stmtExpr, PartialEvalState state) {
      EnterScope();
      try {
        Visit(stmtExpr.S, state);
        stmtExpr.E = SimplifyExpression(stmtExpr.E, state);
      }
      finally {
        ExitScope();
      }
      return false;
    }

    private bool SimplifyDatatypeValue(DatatypeValue datatypeValue, PartialEvalState state) {
      for (var i = 0; i < datatypeValue.Arguments.Count; i++) {
        var simplifiedArg = SimplifyExpression(datatypeValue.Arguments[i], state);
        datatypeValue.Arguments[i] = simplifiedArg;
        if (i < datatypeValue.Bindings.ArgumentBindings.Count) {
          datatypeValue.Bindings.ArgumentBindings[i].Actual = simplifiedArg;
        }
      }
      return false;
    }

    private bool SimplifySetDisplayExpr(SetDisplayExpr setDisplayExpr, PartialEvalState state) {
      for (var i = 0; i < setDisplayExpr.Elements.Count; i++) {
        setDisplayExpr.Elements[i] = SimplifyExpression(setDisplayExpr.Elements[i], state);
      }
      return false;
    }

    private bool SimplifyMultiSetDisplayExpr(MultiSetDisplayExpr multiSetDisplayExpr, PartialEvalState state) {
      for (var i = 0; i < multiSetDisplayExpr.Elements.Count; i++) {
        multiSetDisplayExpr.Elements[i] = SimplifyExpression(multiSetDisplayExpr.Elements[i], state);
      }
      return false;
    }

    // ------------------- Expression rewriting: sequence operations -------------------

    private bool SimplifySeqSelectExpr(SeqSelectExpr seqSelectExpr, PartialEvalState state) {
      Expression result;
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
    }

    private bool SimplifySeqUpdateExpr(SeqUpdateExpr seqUpdateExpr, PartialEvalState state) {
      seqUpdateExpr.Seq = SimplifyExpression(seqUpdateExpr.Seq, state);
      seqUpdateExpr.Index = SimplifyExpression(seqUpdateExpr.Index, state);
      seqUpdateExpr.Value = SimplifyExpression(seqUpdateExpr.Value, state);
      return false;
    }

    // ------------------- Expression rewriting: special-case intrinsics -------------------

    private static bool TrySimplifyArbitraryElement(FunctionCallExpr callExpr, out Expression simplified) {
      simplified = null;
      if (callExpr.Function == null || !string.Equals(callExpr.Function.Name, "ArbitraryElement", StringComparison.Ordinal)) {
        return false;
      }
      if (callExpr.Args.Count != 1) {
        return false;
      }
      if (!TryGetSetDisplayLiteral(callExpr.Args[0], out var setDisplay)) {
        return false;
      }
      if (!AllElementsAreLiterals(setDisplay.Elements)) {
        return false;
      }
      var distinct = new LiteralSet(setDisplay.Elements);
      if (distinct.Count != 1) {
        return false;
      }
      simplified = distinct.Elements[0];
      if (simplified.Type == null) {
        simplified.Type = callExpr.Type;
      }
      return true;
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

    // ------------------- Quantifier bound rewriting -------------------

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

    // ------------------- Constant value snapshot -------------------

    private readonly record struct ConstValue {
      private readonly Expression expr;

      private ConstValue(Expression expr) {
        this.expr = expr;
      }

      public static bool TryCreate(Expression expression, out ConstValue cached) {
        cached = default;
        if (expression == null) {
          return false;
        }
        if (!IsInlineableArgument(expression)) {
          return false;
        }
        cached = new ConstValue(expression);
        return true;
      }

      public Expression CreateExpression(Type type) {
        // Reuse the cached literal/lambda expression for speed; shared nodes are acceptable here.
        if (expr.Type == null) {
          expr.Type = type;
        }
        return expr;
      }
    }
  }
}
