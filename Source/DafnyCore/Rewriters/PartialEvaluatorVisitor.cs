using System;
using System.Collections.Generic;
using System.Linq;
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
    private readonly PartialEvaluatorEngine engine;
    private readonly Dictionary<Expression, Expression> replacements = new();
    private List<Dictionary<IVariable, ConstValue>> constScopes = [];

    public PartialEvaluatorVisitor(PartialEvaluatorEngine engine) {
      this.engine = engine;
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

    private void VisitBranchesWithIsolatedScopes(Statement thenBranch, Statement elseBranch, PartialEvalState state) {
      var incoming = CloneConstScopes();

      constScopes = CloneConstScopes();
      Visit(thenBranch, state);

      constScopes = incoming;
      if (elseBranch != null) {
        constScopes = CloneConstScopes();
        Visit(elseBranch, state);
      }

      constScopes = incoming;
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
        if (TryGetSetDisplayLiteral(unary.E, out var display)) {
          if (display.Elements.Count <= 1 || AllElementsAreLiterals(display.Elements)) {
            var distinct = DistinctLiteralElements(display.Elements);
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
      return false;
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

    private bool SimplifyQuantifierExpr(QuantifierExpr quantifierExpr, PartialEvalState state) {
      quantifierExpr.Range = quantifierExpr.Range == null ? null : SimplifyExpression(quantifierExpr.Range, state);
      quantifierExpr.Term = SimplifyExpression(quantifierExpr.Term, state);
      quantifierExpr.Bounds = SimplifyBounds(quantifierExpr.Bounds, state);
      if (engine.TryUnrollQuantifier(quantifierExpr, out var unrolled)) {
        SetReplacement(quantifierExpr, unrolled);
      }
      return false;
    }

    private bool SimplifySetComprehension(SetComprehension setComprehension, PartialEvalState state) {
      setComprehension.Range = SimplifyExpression(setComprehension.Range, state);
      setComprehension.Term = SimplifyExpression(setComprehension.Term, state);
      setComprehension.Bounds = SimplifyBounds(setComprehension.Bounds, state);
      if (engine.TryMaterializeSetComprehension(setComprehension, out var setDisplay)) {
        SetReplacement(setComprehension, setDisplay);
      }
      return false;
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
      var distinct = DistinctLiteralElements(setDisplay.Elements);
      if (distinct.Count != 1) {
        return false;
      }
      simplified = distinct[0];
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
        var cloner = new Cloner(cloneResolvedFields: true);
        var clone = cloner.CloneExpr(expr);
        if (clone.Type == null) {
          clone.Type = type;
        }
        return clone;
      }
    }
  }
}
