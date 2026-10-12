using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;

namespace Microsoft.Dafny;

internal sealed partial class PartialEvaluatorEngine {
  internal sealed class PartialEvalState {
    public int Depth { get; }
    public bool OldHeap { get; }
    public HashSet<Function> InlineStack { get; }
    public HashSet<string> InlineCallStack { get; }

    public PartialEvalState(int depth, HashSet<Function> inlineStack, HashSet<string> inlineCallStack, bool oldHeap = false) {
      Depth = depth;
      OldHeap = oldHeap;
      InlineStack = inlineStack;
      InlineCallStack = inlineCallStack;
    }

    public PartialEvalState WithOldHeap() => new(Depth, InlineStack, InlineCallStack, true);

    public PartialEvalState WithDepth(int depth) {
      return new PartialEvalState(depth, InlineStack, InlineCallStack, OldHeap);
    }
  }

  private sealed class PartialEvaluatorVisitor : TopDownVisitor<PartialEvalState> {
    private const string PartialPeelMarkerAttributeName = "_partial_peel";
    private readonly PartialEvaluatorEngine engine;
    private Action cancellationCheck => engine.cancellationCheck;
    private readonly Dictionary<(Expression, bool), Expression> replacements = new();
    private readonly Dictionary<IVariable, Expression> existentialWitnessValues = new();
    private readonly HashSet<SubsetTypeDecl> checkedSubsetMembershipStack = new();
    private ExistentialSupportFrame existentialSupportFrame;
    private bool currentOldHeap;
    private int checkedSubsetMembershipDepth;
    private int concreteLetMembershipDepth;
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
      engine.CheckForCancellation();
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

      // Membership construction adds identity casts around substituted datatype receivers.
      // Normalize only this temporary check; retain the original RHS and native binder types.
      if (concreteLetMembershipDepth > 0 && expr is ConversionExpr) {
        var normalized = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
        if (!ReferenceEquals(normalized, expr)) {
          return SimplifyExpression(normalized, state);
        }
      }

      var previousHeap = currentOldHeap;
      currentOldHeap = state.OldHeap;
      try {
        Visit(expr, state);
        var result = GetReplacement(expr);
        if (!ReferenceEquals(result, expr)) {
          AssertHasResolvedType(result);
        }
        return result;
      }
      finally {
        currentOldHeap = previousHeap;
      }
    }

    // ------------------- Replacement tracking -------------------

    private Expression GetReplacement(Expression expr) {
      return replacements.TryGetValue((expr, currentOldHeap), out var replacement) ? replacement : expr;
    }

    private void SetReplacement(Expression original, Expression replacement) {
      if (!ReferenceEquals(original, replacement)) {
        replacements[(original, currentOldHeap)] = replacement;
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
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
        if (constScopes[i].Remove(variable)) {
          return;
        }
      }
    }

    private void InvalidateConsts(IEnumerable<IVariable> variables) {
      foreach (var variable in variables) {
        cancellationCheck?.Invoke();
        InvalidateConst(variable);
      }
    }

    private void InvalidateAssignedLocals(Statement stmt) {
      foreach (var ide in stmt.GetAssignedLocals()) {
        cancellationCheck?.Invoke();
        if (ide?.Var != null) {
          InvalidateConst(ide.Var);
        }
      }
    }

    private List<Dictionary<IVariable, ConstValue>> CloneConstScopes(List<Dictionary<IVariable, ConstValue>> scopes) {
      var snapshot = new List<Dictionary<IVariable, ConstValue>>(scopes.Count);
      foreach (var scope in scopes) {
        cancellationCheck?.Invoke();
        snapshot.Add(new Dictionary<IVariable, ConstValue>(scope));
      }
      return snapshot;
    }

    private HashSet<IVariable> CollectAssignedLocalsDeep(Statement root) {
      var assigned = new HashSet<IVariable>();
      if (root == null) {
        return assigned;
      }

      var stack = new Stack<Statement>();
      stack.Push(root);
      while (stack.Count > 0) {
        cancellationCheck?.Invoke();
        var current = stack.Pop();
        foreach (var ide in current.GetAssignedLocals()) {
          cancellationCheck?.Invoke();
          if (ide?.Var != null) {
            assigned.Add(ide.Var);
          }
        }
        foreach (var child in current.SubStatements) {
          cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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
        if (!ConstValue.TryCreate(rhsExpr, out var constValue, cancellationCheck)) {
          continue;
        }

        SetConst(identifierExpr.Var, constValue);
      }
    }

    // ------------------- Statement rewriting -------------------

    protected override bool VisitOneStmt(Statement stmt, ref PartialEvalState state) {
      engine.CheckForCancellation();
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
        engine.CheckForCancellation();
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
        engine.CheckForCancellation();
        inv.E = SimplifyExpression(inv.E, state);
      }
      if (whileStmt.Decreases?.Expressions != null) {
        for (var i = 0; i < whileStmt.Decreases.Expressions.Count; i++) {
          cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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
        engine.CheckForCancellation();
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
        cancellationCheck?.Invoke();
        var exprToSimplify = hideRevealStmt.Exprs[i];
        if (exprToSimplify == null || !exprToSimplify.WasResolved()) {
          continue;
        }
        hideRevealStmt.Exprs[i] = SimplifyExpression(exprToSimplify, state);
      }
    }

    private void VisitSubStatements(Statement stmt, PartialEvalState state) {
      foreach (var sub in stmt.SubStatements) {
        engine.CheckForCancellation();
        Visit(sub, state);
      }
    }

    // ------------------- String and character literal helpers -------------------

    private IEnumerable<string> TokenizeStringLiteral(string value, bool isVerbatim) {
      if (!isVerbatim) {
        return Util.TokensWithEscapes(value, false);
      }

      var tokens = new List<string>();
      for (var i = 0; i < value.Length; i++) {
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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

    private string EscapeCharLiteral(int codePoint, bool unicodeChars) {
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
      if (engine.heapReduction != null && expr is StmtExpr or ApplyExpr) {
        engine.heapReduction.ResidualReasons.Add(expr is StmtExpr ? "proof_statement" : "higher_order_apply");
        return false;
      }
      switch (expr) {
        case ParensExpression parens:
          return SimplifyParensExpr(parens, state);
        case LiteralExpr:
          return false;
        case ConversionExpr conversionExpr:
          return SimplifyConversionExpr(conversionExpr, state);
        case IdentifierExpr identifierExpr:
          return SimplifyIdentifierExpr(identifierExpr);
        case UnaryOpExpr unary:
          return SimplifyUnaryExpr(unary, state);
        case BinaryExpr binary:
          return SimplifyBinaryExpr(binary, state);
        case ITEExpr ite:
          return SimplifyIteExpr(ite, state);
        case MatchExpr match when engine.UsesContractConcreteProfile:
          return SimplifyMatchExpr(match, state);
        case NestedMatchExpr { Flattened: not null } nestedMatch when engine.UsesContractConcreteProfile:
          if (engine.expressionExpansionBudget == null || engine.expressionExpansionBudget.TryReserve(nestedMatch.Flattened)) {
            SetReplacement(nestedMatch, SimplifyExpression(
              engine.CloneResolvedExpression(nestedMatch.Flattened), state));
          }
          return false;
        case FunctionCallExpr callExpr:
          return SimplifyFunctionCallExpr(callExpr, state);
        case ApplyExpr applyExpr:
          return SimplifyApplyExpr(applyExpr, state);
        case MemberSelectExpr memberSelectExpr:
          return SimplifyMemberSelectExpr(memberSelectExpr, state);
        case OldExpr oldExpr when engine.heapReduction != null:
          return SimplifyOldExpr(oldExpr, state);
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
        case MapDisplayExpr mapDisplayExpr:
          return SimplifyMapDisplayExpr(mapDisplayExpr, state);
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

    private bool SimplifyConversionExpr(ConversionExpr conversionExpr, PartialEvalState state) {
      if (!engine.UsesContractConcreteProfile) {
        return false;
      }

      var proofArtifacts = MarkProofArtifacts();
      var originalConversion = (ConversionExpr)engine.CloneResolvedExpression(conversionExpr);
      conversionExpr.E = SimplifyExpression(conversionExpr.E, state);
      if (TryEvaluateContractConcreteConversion(conversionExpr, out var convertedLiteral, cancellationCheck)) {
        SetReplacement(conversionExpr, convertedLiteral);
      } else if (TryEvaluateCheckedIntegerSubsetConversion(
                   conversionExpr, engine.proofCompositionMode ? originalConversion : null, state, out convertedLiteral)) {
        SetReplacement(conversionExpr, convertedLiteral);
      } else {
        // The entire failed conversion owns its operand's artifacts, not just membership work.
        RollbackProofArtifacts(proofArtifacts);
        SetReplacement(conversionExpr, originalConversion);
      }
      return false;
    }

    private bool TryEvaluateCheckedIntegerSubsetConversion(ConversionExpr conversionExpr,
      ConversionExpr originalConversion, PartialEvalState state, out LiteralExpr convertedLiteral) {
      convertedLiteral = null;
      if (originalConversion == null || engine.expressionExpansionBudget == null ||
          engine.quantifierExpansionBudget == null ||
          conversionExpr.Type == null || conversionExpr.ToType == null ||
          originalConversion.Type == null || originalConversion.ToType == null ||
          engine.HasFreeTypeParametersIncludingUnexpandedArguments(originalConversion.Type) ||
          engine.HasFreeTypeParametersIncludingUnexpandedArguments(originalConversion.ToType) ||
          !conversionExpr.Type.Equals(conversionExpr.ToType, keepConstraints: true) ||
          !engine.TryGetRevealedIntegerSubsetTarget(originalConversion.Type, out var targetSubset) ||
          !engine.TryGetRevealedIntegerSubsetTarget(originalConversion.ToType, out _)) {
        return false;
      }

      if (!IsClosedProofExpression(engine.options, originalConversion, cancellationCheck)) {
        return false;
      }
      var conversionToInt = new ConversionExpr(conversionExpr.Origin, conversionExpr.E, Type.Int) { Type = Type.Int };
      if (!TryEvaluateContractConcreteConversion(conversionToInt, out var intCarrier, cancellationCheck) ||
          !TryGetReducedIntLiteral(intCarrier, out var value, cancellationCheck)) {
        return false;
      }

      var proofArtifacts = MarkProofArtifacts();
      var membership = ConcreteCallSession.Membership(engine, intCarrier, conversionExpr.Type);
      if (!engine.expressionExpansionBudget.TryReserve(membership)) {
        return false;
      }
      if (!checkedSubsetMembershipStack.Add(targetSubset)) {
        return false;
      }
      Expression checkedMembership;
      checkedSubsetMembershipDepth++;
      try {
        checkedMembership = SimplifyExpression(
          engine.CloneResolvedExpression(membership), state);
      }
      finally {
        checkedSubsetMembershipDepth--;
        checkedSubsetMembershipStack.Remove(targetSubset);
      }
      if (!Expression.IsBoolLiteral(checkedMembership, out var isMember) || !isMember ||
          engine.ProofWitnesses.Count != proofArtifacts.Witnesses ||
          engine.ProofCompositionCandidates.Count != proofArtifacts.Candidates ||
          engine.ProofPrerequisites.Count != proofArtifacts.Prerequisites ||
          engine.ProofConcreteCalls.Count != proofArtifacts.ConcreteCalls) {
        RollbackProofArtifacts(proofArtifacts);
        return false;
      }

      var targetLiteral = CreateIntLiteral(conversionExpr.Origin, value, conversionExpr.Type);
      if (checkedSubsetMembershipDepth > 0) {
        convertedLiteral = targetLiteral;
        return true;
      }

      var nativeMembership = new TypeTestExpr(conversionExpr.Origin,
        engine.CloneResolvedExpression(intCarrier), originalConversion.ToType) { Type = Type.Bool };
      var equality = Expression.CreateEq(originalConversion, targetLiteral, Type.Int);
      if (!IsClosedProofExpression(engine.options, nativeMembership, cancellationCheck) ||
          !IsClosedProofExpression(engine.options, equality, cancellationCheck)) {
        RollbackProofArtifacts(proofArtifacts);
        return false;
      }
      if (engine.GetRemainingQuantifierExpansionLimit() == 0) {
        engine.RecordQuantifierExpansionExhaustion();
        RollbackProofArtifacts(proofArtifacts);
        return false;
      }
      if (!engine.expressionExpansionBudget.TryReserve(nativeMembership) ||
          !engine.expressionExpansionBudget.TryReserve(equality)) {
        RollbackProofArtifacts(proofArtifacts);
        return false;
      }

      engine.RecordQuantifierExpansion();
      engine.ProofPrerequisites.Add(nativeMembership);
      engine.ProofPrerequisites.Add(equality);
      convertedLiteral = targetLiteral;
      return true;
    }

    // ------------------- Expression rewriting: operators and conditionals -------------------

    private bool SimplifyUnaryExpr(UnaryOpExpr unary, PartialEvalState state) {
      var proofArtifacts = MarkProofArtifacts();
      unary.E = SimplifyExpression(unary.E, state);
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot) {
        // Composition proves positive predicate facts. Lifting them out of a
        // negation cannot establish that negated goal and can add unrelated WD.
        // A complete refutation may need its closed prerequisites and call==value certificates.
        // An enclosing discarded branch still rolls these back with its own mark.
        var retainsRefutation = Expression.IsBoolLiteral(unary.E, out var operandValue) && !operandValue;
        RollbackProofArtifacts(proofArtifacts, preservePrerequisites: retainsRefutation);
      }
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
          if (display.Elements.Count <= 1 || AllElementsAreLiterals(display.Elements, cancellationCheck)) {
            var distinct = new LiteralSet(display.Elements, cancellationCheck);
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
          if (display.Elements.Count <= 1 || AllMapKeysAreLiterals(display, cancellationCheck)) {
            var distinctKeys = new LiteralSet(display.Elements.Select(entry => entry.A), cancellationCheck);
            var result = CreateIntLiteral(unary.Origin, distinctKeys.Count, unary.Type);
            SetReplacement(unary, result);
            return false;
          }
        }
      }
      if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot &&
          TryGetReducedIntLiteral(unary.E, out var bitvectorValue, cancellationCheck) &&
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
      if (!QuantifierBounds.IsBoundVar(setComprehension.Term, boundVar, cancellationCheck)) {
        return false;
      }

      if (ContainsForeignBoundVar(setComprehension.Range, boundVar)) {
        return false;
      }

      var effectiveRange = QuantifierBounds.ConjoinWithImpliedTypeConstraints(setComprehension.BoundVars, setComprehension.Range, setComprehension.Origin, cancellationCheck);
      var hasFunctionCallInRange = ContainsAnyFunctionCall(effectiveRange);

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
        cancellationCheck?.Invoke();
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(setComprehension.Origin, value, boundVar.Type)
        };
        var substituter = engine.CreateSubstituter(null, substMap, null);
        var instantiatedRange = substituter.Substitute(effectiveRange);
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

    private bool ContainsRecursiveFunctionCall(Expression expr) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is FunctionCallExpr functionCallExpr && functionCallExpr.Function != null && functionCallExpr.Function.IsRecursive) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {

        cancellationCheck?.Invoke();
        if (ContainsRecursiveFunctionCall(subExpression)) {
          return true;
        }
      }

      return false;
    }

    private bool ContainsForeignBoundVar(Expression expr, BoundVar allowedBoundVar) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is IdentifierExpr identifierExpr &&
          identifierExpr.Var is BoundVar otherBoundVar &&
          otherBoundVar != allowedBoundVar) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {

        cancellationCheck?.Invoke();
        if (ContainsForeignBoundVar(subExpression, allowedBoundVar)) {
          return true;
        }
      }

      return false;
    }

    private bool ContainsAnyFunctionCall(Expression expr) {
      if (expr == null) {
        return false;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is FunctionCallExpr || expr is ApplyExpr) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {

        cancellationCheck?.Invoke();
        if (ContainsAnyFunctionCall(subExpression)) {
          return true;
        }
      }

      return false;
    }

    private bool TryGetFiniteIntBoundFromComprehension(
      SetComprehension setComprehension,
      out BigInteger lower,
      out BigInteger upper) {
      lower = default;
      upper = default;
      if (setComprehension.Bounds != null && setComprehension.Bounds.Count == 1 &&
          setComprehension.Bounds[0] is IntBoundedPool intPool &&
          intPool.LowerBound != null &&
          intPool.UpperBound != null) {
        var normalizedLower = QuantifierBounds.NormalizeForPattern(intPool.LowerBound, cancellationCheck);
        var normalizedUpper = QuantifierBounds.NormalizeForPattern(intPool.UpperBound, cancellationCheck);
        if (TryGetReducedIntLiteral(normalizedLower, out lower, cancellationCheck) &&
            TryGetReducedIntLiteral(normalizedUpper, out upper, cancellationCheck)) {
          return true;
        }
      }

      if (setComprehension.BoundVars.Count != 1 || setComprehension.Range == null) {
        return false;
      }

      var boundVar = setComprehension.BoundVars[0];
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(setComprehension.Range, conjuncts, cancellationCheck);

      BigInteger? lowerCandidate = null;
      BigInteger? upperCandidate = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
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
      var isAnd = binary.ResolvedOp == BinaryExpr.ResolvedOpcode.And;
      var isOr = binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Or;
      var isImplication = binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp;
      var isShortCircuit = isAnd || isOr || isImplication;
      var leftIsLiteral = Expression.IsBoolLiteral(binary.E0, out var leftValue);
      var leftDecides = leftIsLiteral &&
        (isAnd && !leftValue || isOr && leftValue || isImplication && !leftValue);
      // Ordinary reduction historically visits both operands and reports any
      // depth exhaustion incurred there. Only proof composition uses branch
      // liveness to avoid collecting obligations from an unreachable operand.
      if (!leftDecides || !engine.proofCompositionMode) {
        var proofArtifacts = MarkProofArtifacts();
        binary.E1 = SimplifyExpression(binary.E1, state);
        // A symbolic guard does not justify lifting a branch-local proof as an
        // unconditional native assertion. The simplification work stays charged.
        if (isShortCircuit && !leftIsLiteral) {
          RollbackProofArtifacts(proofArtifacts);
        }
      }
      var result = engine.SimplifyBinary(binary);
      if (ReferenceEquals(result, binary) && engine.UsesContractConcreteProfile &&
          binary.ResolvedOp == BinaryExpr.ResolvedOpcode.Concat &&
          TryGetConcreteSequenceElements(binary.E0, out var leftElements) &&
          TryGetConcreteSequenceElements(binary.E1, out var rightElements)) {
        var concatenated = CreateSeqDisplayLiteral(binary.Origin, leftElements.Concat(rightElements).ToList(), binary.Type);
        if (engine.expressionExpansionBudget == null || engine.expressionExpansionBudget.TryReserve(concatenated)) {
          result = concatenated;
        }
      }
      if (ReferenceEquals(result, binary) && engine.TrySimplifyContractConstructorEquality(binary, out var fields)) {
        result = SimplifyExpression(fields, state);
      }
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
      var proofArtifacts = MarkProofArtifacts();
      ite.Thn = SimplifyExpression(ite.Thn, state);
      RollbackProofArtifacts(proofArtifacts);
      ite.Els = SimplifyExpression(ite.Els, state);
      RollbackProofArtifacts(proofArtifacts);
      return false;
    }

    // The existing artifact lists stage support until the owning full body completes.
    private sealed class ExistentialSupportFrame {
      internal bool HasStagedSupport { get; set; }
    }

    private bool SupportBudgetsIntact => !engine.ExpressionNodeLimitExhausted &&
      !(engine.quantifierExpansionBudget?.IsExhausted ?? false) && !engine.InlineDepthExhausted;

    internal void RollbackIncompleteInline(ProofArtifactMark mark, Expression residual) {
      var preserveSupport = existentialSupportFrame != null &&
        residual.Type?.NormalizeExpand().IsBoolType == true && SupportBudgetsIntact &&
        HasClosedInlineSupport(mark);
      if (preserveSupport && (engine.ProofPrerequisites.Count > mark.Prerequisites ||
                             engine.ProofConcreteCalls.Count > mark.ConcreteCalls)) {
        existentialSupportFrame.HasStagedSupport = true;
      }
      // Raw witnesses and candidates never escape an incomplete inline.
      RollbackProofArtifacts(mark, preservePrerequisites: preserveSupport);
    }

    private bool HasClosedInlineSupport(ProofArtifactMark mark) {
      for (var index = mark.Prerequisites; index < engine.ProofPrerequisites.Count; index++) {
        if (!IsClosedProofExpression(engine.options, engine.ProofPrerequisites[index], cancellationCheck)) {
          return false;
        }
      }
      for (var index = mark.ConcreteCalls; index < engine.ProofConcreteCalls.Count; index++) {
        if (!IsClosedConcreteCallSupport(engine.ProofConcreteCalls[index])) {
          return false;
        }
      }
      return true;
    }

    private bool IsClosedConcreteCallSupport(ContractConcreteCallProof proof) {
      engine.CheckForCancellation();
      return IsClosedProofExpression(engine.options, proof.Equality, cancellationCheck) &&
        proof.Prerequisites.All(expression => IsClosedProofExpression(engine.options, expression, cancellationCheck)) &&
        proof.Witnesses.All(expression => IsClosedProofExpression(engine.options, expression, cancellationCheck)) &&
        proof.Dependencies.All(IsClosedConcreteCallSupport);
    }

    internal readonly record struct ProofArtifactMark(int Witnesses, int Candidates, int Prerequisites, int ConcreteCalls);

    internal ProofArtifactMark MarkProofArtifacts() =>
      new(engine.ProofWitnesses.Count, engine.ProofCompositionCandidates.Count, engine.ProofPrerequisites.Count,
        engine.ProofConcreteCalls.Count);

    // Discards proof artifacts collected after the mark; ordinary reduction keeps them.
    internal void RollbackProofArtifacts(ProofArtifactMark mark, bool preservePrerequisites = false) {
      if (!engine.proofCompositionMode) {
        return;
      }
      engine.ProofWitnesses.RemoveRange(mark.Witnesses, engine.ProofWitnesses.Count - mark.Witnesses);
      engine.ProofCompositionCandidates.RemoveRange(mark.Candidates,
        engine.ProofCompositionCandidates.Count - mark.Candidates);
      if (!preservePrerequisites) {
        engine.ProofConcreteCalls.RemoveRange(mark.ConcreteCalls, engine.ProofConcreteCalls.Count - mark.ConcreteCalls);
        engine.ProofPrerequisites.RemoveRange(mark.Prerequisites, engine.ProofPrerequisites.Count - mark.Prerequisites);
      }
    }

    private bool SimplifyMatchExpr(MatchExpr match, PartialEvalState state) {
      var source = SimplifyExpression(match.Source, state);
      match.UpdateSource(source);
      if (source is not DatatypeValue { Ctor: { } constructor } value) {
        return false;
      }
      var branch = match.Cases.SingleOrDefault(candidate => ReferenceEquals(candidate.Ctor, constructor));
      if (branch == null || branch.Arguments.Count != value.Arguments.Count) {
        return false;
      }
      var substitutions = new Dictionary<IVariable, Expression>();
      for (var index = 0; index < branch.Arguments.Count; index++) {
        cancellationCheck?.Invoke();
        substitutions.Add(branch.Arguments[index], value.Arguments[index]);
      }
      if (!engine.TryReserveQuantifierInstanceExpansion(branch.Body, substitutions)) {
        return false;
      }
      var substituter = engine.CreateSubstituter(null, substitutions, null);
      var body = substituter.Substitute(engine.CloneResolvedExpression(branch.Body));
      SetReplacement(match, SimplifyExpression(body, state));
      return false;
    }

    // ------------------- Expression rewriting: calls and selection -------------------

    private bool SimplifyFunctionCallExpr(FunctionCallExpr callExpr, PartialEvalState state) {
      callExpr.Receiver = SimplifyExpression(callExpr.Receiver, state);
      for (var i = 0; i < callExpr.Args.Count; i++) {
        cancellationCheck?.Invoke();
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
      var collectPredicateCandidate = engine.collectProofCompositionCandidates &&
        callExpr.Type?.NormalizeExpand().IsBoolType == true;
      if (engine.heapReduction == null && !engine.proofCompositionMode && !collectPredicateCandidate &&
          engine.HelperInterpreter.TryInterpret(callExpr, SimplifyExpression, state, out var interpreted)) {
        SetReplacement(callExpr, interpreted);
        return false;
      }
      if (engine.TryInlineCall(callExpr, state, this, out var inlined)) {
        SetReplacement(callExpr, inlined);
        return false;
      }
      return false;
    }

    private bool SimplifyApplyExpr(ApplyExpr applyExpr, PartialEvalState state) {
      applyExpr.Function = SimplifyExpression(applyExpr.Function, state);
      for (var i = 0; i < applyExpr.Args.Count; i++) {
        cancellationCheck?.Invoke();
        applyExpr.Args[i] = SimplifyExpression(applyExpr.Args[i], state);
      }

      if (applyExpr.Function is not LambdaExpr lambdaExpr) {
        return false;
      }

      if (lambdaExpr.Range != null || lambdaExpr.BoundVars.Count != applyExpr.Args.Count) {
        return false;
      }

      for (var i = 0; i < applyExpr.Args.Count; i++) {

        cancellationCheck?.Invoke();
        if (!IsInlineableArgument(applyExpr.Args[i], cancellationCheck)) {
          return false;
        }
      }

      var substMap = new Dictionary<IVariable, Expression>(lambdaExpr.BoundVars.Count);
      for (var i = 0; i < lambdaExpr.BoundVars.Count; i++) {
        cancellationCheck?.Invoke();
        substMap[lambdaExpr.BoundVars[i]] = applyExpr.Args[i];
      }

      var substituter = engine.CreateSubstituter(null, substMap, null);
      var substituted = substituter.Substitute(lambdaExpr.Body);
      var simplified = SimplifyExpression(substituted, state);
      SetReplacement(applyExpr, simplified);
      return false;
    }

    private bool SimplifyOldExpr(OldExpr oldExpr, PartialEvalState state) {
      if (oldExpr.AtLabel != null) {
        engine.heapReduction.ResidualReasons.Add("labeled_old");
        return false;
      }
      // Clone at the epoch boundary: the same substituted expression must never
      // acquire children rewritten under a different heap frame.
      var child = engine.CloneResolvedExpression(oldExpr.Expr);
      oldExpr.Expr = SimplifyExpression(child, state.WithOldHeap());
      if (ContractHeapReductionContext.IsHeapIndependent(oldExpr.Expr, cancellationCheck)) {
        SetReplacement(oldExpr, oldExpr.Expr);
      }
      return false;
    }

    private bool SimplifyMemberSelectExpr(MemberSelectExpr memberSelectExpr, PartialEvalState state) {
      if (engine.heapReduction != null && memberSelectExpr.AtLabel != null) {
        engine.heapReduction.ResidualReasons.Add("labeled_member");
        return false;
      }
      memberSelectExpr.Obj = SimplifyExpression(memberSelectExpr.Obj, state);
      if (engine.heapReduction != null && memberSelectExpr.Member is Field and not DatatypeDestructor and not DatatypeDiscriminator) {
        if (engine.heapReduction.Context.TryRead(memberSelectExpr, state.OldHeap, out var value)) {
          if (engine.expressionExpansionBudget != null && !engine.expressionExpansionBudget.TryReserve(value)) { return false; }
          if (state.OldHeap || !((Field)memberSelectExpr.Member).IsMutable) { engine.heapReduction.EntryReads++; } else { engine.heapReduction.CurrentReads++; }
          SetReplacement(memberSelectExpr, engine.CloneResolvedExpression(value));
          return false;
        }
        engine.heapReduction.ResidualReasons.Add("unknown_heap_cell");
      }
      if (engine.UsesContractConcreteProfile &&
          memberSelectExpr.Member is SpecialField { SpecialId: SpecialField.ID.Keys } &&
          memberSelectExpr.Obj is MapDisplayExpr mapDisplay &&
          TryNormalizeContractConcreteMapEntries(mapDisplay, out var entries, cancellationCheck)) {
        SetReplacement(memberSelectExpr, CreateSetDisplayLiteral(memberSelectExpr.Origin,
          entries.Select(entry => entry.A).ToList(), memberSelectExpr.Type));
        return false;
      }
      if (engine.UsesContractConcreteProfile &&
          memberSelectExpr.Obj is DatatypeValue { Ctor: { } ctor } datatype) {
        if (memberSelectExpr.Member is DatatypeDiscriminator discriminator) {
          SetReplacement(memberSelectExpr,
            Expression.CreateBoolLiteral(memberSelectExpr.Origin, ReferenceEquals(ctor.QueryField, discriminator)));
          return false;
        }
        if (memberSelectExpr.Member is DatatypeDestructor destructor) {
          var index = ctor.Destructors.FindIndex(candidate => ReferenceEquals(candidate, destructor));
          if (0 <= index && index < datatype.Arguments.Count) {
            SetReplacement(memberSelectExpr, datatype.Arguments[index]);
            return false;
          }
        }
      }
      if (TryGetTupleLiteral(memberSelectExpr.Obj, out var tuple) &&
          int.TryParse(memberSelectExpr.MemberName, out var tupleIndex) &&
          0 <= tupleIndex && tupleIndex < tuple.Arguments.Count &&
          IsLiteralLike(tuple.Arguments[tupleIndex], cancellationCheck)) {
        SetReplacement(memberSelectExpr, tuple.Arguments[tupleIndex]);
      }
      return false;
    }

    // ------------------- Expression rewriting: quantifiers -------------------

    private bool SimplifyQuantifierExpr(QuantifierExpr quantifierExpr, PartialEvalState state) =>
      SimplifyQuantifierExpr(quantifierExpr, state, out _);

    private bool SimplifyQuantifierExpr(QuantifierExpr quantifierExpr, PartialEvalState state,
      out bool completedFullBody) {
      engine.CheckForCancellation();
      var proofArtifacts = MarkProofArtifacts();
      var previousFrame = existentialSupportFrame;
      // Check the original binder and heap dependencies before its body is mutated.
      var frame = engine.proofCompositionMode && quantifierExpr is ExistsExpr &&
        IsClosedProofExpression(engine.options, quantifierExpr, cancellationCheck)
        ? new ExistentialSupportFrame() : null;
      existentialSupportFrame = frame;
      var retainStagedSupport = false;
      var completedNormally = false;
      completedFullBody = false;
      try {
        var result = SimplifyQuantifierExprCore(quantifierExpr, state, out completedFullBody);
        retainStagedSupport = completedFullBody && SupportBudgetsIntact;
        completedNormally = true;
        return result;
      }
      finally {
        existentialSupportFrame = previousFrame;
        if (quantifierExpr is ForallExpr || frame != null && !completedNormally ||
            frame is { HasStagedSupport: true } && !retainStagedSupport) {
          // Unstaged existential paths retain their existing behavior. New support
          // needs explicit full-body completion, never an early/vacuous Boolean.
          RollbackProofArtifacts(proofArtifacts);
        } else if (frame is { HasStagedSupport: true } && previousFrame != null) {
          // A completed child is still provisional until its enclosing owner completes.
          previousFrame.HasStagedSupport = true;
        }
      }
    }

    private bool SimplifyQuantifierExprCore(QuantifierExpr quantifierExpr, PartialEvalState state,
      out bool completedFullBody) {
      engine.CheckForCancellation();
      completedFullBody = false;
      if (engine.heapReduction != null &&
          !(engine.proofCompositionMode && IsHeapIndependentProofExpression(engine.options, quantifierExpr, cancellationCheck))) {
        // Rewriting a symbolic quantified body can require quantified definition
        // instantiations that the checked outer equivalence cannot establish.
        // Reduce concrete instances only; leave an unavailable domain's original
        // body, range and triggers together for native verification.
        if (engine.TryUnrollQuantifier(quantifierExpr,
              expression => SimplifyExpression(expression, state.WithDepth(Math.Max(0, state.Depth - 1))),
              out var heapUnrolled, emitOverflowResidual: engine.emitQuantifierOverflowResidual)) {
          SetReplacement(quantifierExpr, heapUnrolled);
        } else if (!engine.ExpressionNodeLimitExhausted && !(engine.quantifierExpansionBudget?.IsExhausted ?? false)) {
          engine.heapReduction.ResidualReasons.Add(quantifierExpr.SplitQuantifier != null
            ? "split_quantifier" : "unbounded_quantifier");
        }
        return false;
      }

      Expression witnessBody = null;
      if (engine.UsesContractConcreteProfile && quantifierExpr is ExistsExpr &&
          (engine.expressionExpansionBudget == null || engine.expressionExpansionBudget.TryReserve(quantifierExpr))) {
        witnessBody = engine.CloneResolvedExpression(
          QuantifierBounds.GetLogicalBodyWithImpliedTypeConstraints(quantifierExpr, cancellationCheck));
      }

      // The finite-sequence recognizer needs the original resolved domain constraint. Simplifying
      // a nested forall first can turn that constraint into individual index checks and erase the
      // finite element-domain shape used by the bounded enumerator.
      if (quantifierExpr is ExistsExpr sequenceExistsExpr &&
          TrySimplifyExistsSequence(sequenceExistsExpr, state, out var sequenceReplacement)) {
        SetReplacement(quantifierExpr, sequenceReplacement);
        return false;
      }

      quantifierExpr.Range = quantifierExpr.Range == null ? null : SimplifyExpression(quantifierExpr.Range, state);
      if (existentialSupportFrame != null && quantifierExpr.Range != null &&
          Expression.IsBoolLiteral(quantifierExpr.Range, out var liveRange) && !liveRange) {
        // The term was never needed; it cannot supply support for a vacuous result.
        SetReplacement(quantifierExpr, Expression.CreateBoolLiteral(quantifierExpr.Origin, false));
        return false;
      }
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
        if (engine.UsesContractConcreteProfile &&
            TrySimplifyExistsStructure(existsExpr, state, out var structuralReplacement, out completedFullBody)) {
          if (witnessBody != null && Expression.IsBoolLiteral(structuralReplacement, out var proved) && proved) {
            RecordConcreteExistentialWitness(existsExpr.BoundVars, witnessBody);
          }
          SetReplacement(quantifierExpr, structuralReplacement);
          return false;
        }
        if (TrySimplifyExistsByPointAssignments(existsExpr, state, out var pointReplacement)) {
          // Every binder is assigned; the residual retains all other original conjuncts and type constraints.
          completedFullBody = Expression.IsBoolLiteral(pointReplacement, out _);
          if (witnessBody != null && Expression.IsBoolLiteral(pointReplacement, out var proved) && proved) {
            RecordConcreteExistentialWitness(existsExpr.BoundVars, witnessBody);
          }
          SetReplacement(quantifierExpr, pointReplacement);
          return false;
        }
        if (engine.proofCompositionMode &&
            TrySimplifyExistsConstructorAlternatives(existsExpr, state, out var constructorReplacement)) {
          if (witnessBody != null && Expression.IsBoolLiteral(constructorReplacement, out var proved) && proved) {
            RecordConcreteExistentialWitness(existsExpr.BoundVars, witnessBody);
          }
          SetReplacement(quantifierExpr, constructorReplacement);
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
      }

      var inlineDepthForUnrolledInstances = Math.Max(0, state.Depth - 1);
      if ((!hasRecursiveLogicalBody || engine.UsesContractConcreteProfile) &&
          engine.TryUnrollQuantifier(
            quantifierExpr,
            expr => SimplifyExpression(expr, state.WithDepth(inlineDepthForUnrolledInstances)),
            out var unrolled,
            emitOverflowResidual: engine.emitQuantifierOverflowResidual)) {
        SetReplacement(quantifierExpr, unrolled);
      }
      return false;
    }

    private bool TryPeelLowerBoundedForall(ForallExpr forallExpr, PartialEvalState state, out Expression replacement) {
      engine.CheckForCancellation();
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

      var effectiveAntecedent = QuantifierBounds.ConjoinWithImpliedTypeConstraints(forallExpr.BoundVars, implication.E0, forallExpr.Origin, cancellationCheck);
      var effectiveBody = Expression.CreateImplies(effectiveAntecedent, implication.E1);
      effectiveBody.Type = Type.Bool;

      const int peelCount = 1;
      var simplifyState = state.WithDepth(Math.Max(0, state.Depth - 1));
      var instantiatedConjuncts = new List<Expression>(peelCount + 1);
      for (var offset = 0; offset < peelCount; offset++) {
        cancellationCheck?.Invoke();
        var value = inclusiveLowerBound + offset;
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(forallExpr.Origin, value, boundVar.Type)
        };
        var substituter = engine.CreateSubstituter(null, substMap, null);
        var instantiatedBody = substituter.Substitute(effectiveBody);
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

    // These rewrites expose exact finite product structure, rather than proposing witnesses.
    // Keeping all original conjuncts also retains subset constraints and conflicting equalities.
    private bool TrySimplifyExistsStructure(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement,
      out bool completedFullBody) {
      engine.CheckForCancellation();
      replacement = null;
      completedFullBody = false;
      var body = QuantifierBounds.GetLogicalBodyWithImpliedTypeConstraints(existsExpr, cancellationCheck);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(body, conjuncts, cancellationCheck);
      var usedNames = ContractReductionTraversal.LogicalNodes(body, cancellationCheck).OfType<IdentifierExpr>().Select(identifier => identifier.Name)
        .Concat(existsExpr.BoundVars.Select(variable => { cancellationCheck?.Invoke(); return variable.Name; })).ToHashSet();
      var nextName = 0;
      BoundVar FreshVariable(IOrigin origin, Type type) {
        string name;
        do { cancellationCheck?.Invoke(); name = "_contract_witness_" + nextName++; } while (!usedNames.Add(name));
        return new BoundVar(origin, name, type);
      }

      foreach (var variable in existsExpr.BoundVars) {

        cancellationCheck?.Invoke();
        foreach (var conjunct in conjuncts) {
          cancellationCheck?.Invoke();
          if (TryGetExistsPointAssignment(conjunct, new[] { variable }, out _, out var value)) {
            return TryReplaceExistentialVariable(existsExpr, body, variable, value, new List<BoundVar>(), state, out replacement, out completedFullBody);
          }
        }
      }

      if (TrySimplifyExistsConcatenation(existsExpr, body, conjuncts, state, out replacement)) {
        return true;
      }

      foreach (var variable in existsExpr.BoundVars) {

        cancellationCheck?.Invoke();
        var type = variable.Type.NormalizeExpand();
        if (type.AsSeqType is { } sequenceType) {
          foreach (var conjunct in conjuncts) {
            cancellationCheck?.Invoke();
            if (!engine.GetQuantifierBounds().TryGetSeqLengthConstraint(conjunct, variable, out var length)) {
              continue;
            }
            if (length > engine.GetRemainingQuantifierExpansionLimit()) {
              engine.RecordQuantifierExpansionExhaustion();
              return false;
            }
            var elements = new List<Expression>();
            var variables = new List<BoundVar>();
            for (var index = 0; index < length; index++) {
              cancellationCheck?.Invoke();
              var element = FreshVariable(variable.Origin, sequenceType.Arg);
              variables.Add(element);
              elements.Add(new IdentifierExpr(element.Origin, element.Name) { Var = element, Type = element.Type });
            }
            var value = CreateSeqDisplayLiteral(variable.Origin, elements, variable.Type);
            return TryReplaceExistentialVariable(existsExpr, body, variable, value, variables, state, out replacement, out completedFullBody);
          }
        }

        // A single inductive constructor is a product, including its field type constraints.
        // The instance/node budgets bound recursively nested products too.
        if (type.AsIndDatatype is { Ctors.Count: 1 } datatype && type is UserDefinedType userType) {
          var constructor = datatype.Ctors[0];
          var typeMap = TypeParameter.SubstitutionMap(datatype.TypeArgs, userType.TypeArgs);
          var variables = new List<BoundVar>();
          var arguments = new List<Expression>();
          foreach (var formal in constructor.Formals) {
            cancellationCheck?.Invoke();
            var field = FreshVariable(variable.Origin, formal.Type.Subst(typeMap));
            variables.Add(field);
            arguments.Add(new IdentifierExpr(field.Origin, field.Name) { Var = field, Type = field.Type });
          }
          var value = new DatatypeValue(variable.Origin, datatype.Name, constructor.Name, arguments) {
            Ctor = constructor,
            Type = variable.Type,
            InferredTypeArgs = userType.TypeArgs
          };
          return TryReplaceExistentialVariable(existsExpr, body, variable, value, variables, state, out replacement, out completedFullBody);
        }
      }

      // Enumerating the complete boolean type allows dependent sequence fields to become
      // point assignments. Other unbounded scalar types remain native solver residuals.
      var boolean = existsExpr.BoundVars.FirstOrDefault(variable => { cancellationCheck?.Invoke(); return variable.Type.NormalizeExpand().IsBoolType; });
      if (boolean != null) {
        if (engine.GetRemainingQuantifierExpansionLimit() < 2) {
          engine.RecordQuantifierExpansionExhaustion();
          return false;
        }
        var cases = new List<Expression>();
        var completedCases = true;
        foreach (var value in new[] { false, true }) {
          cancellationCheck?.Invoke();
          if (!TryReplaceExistentialVariable(existsExpr, body, boolean,
                Expression.CreateBoolLiteral(boolean.Origin, value), new List<BoundVar>(), state, out var branch,
                out var completedBranch)) {
            return false;
          }
          completedCases &= completedBranch;
          cases.Add(branch);
        }
        replacement = SimplifyExpression(CombineDisjuncts(cases, existsExpr.Origin), state);
        completedFullBody = completedCases && Expression.IsBoolLiteral(replacement, out _);
        return true;
      }
      return false;
    }

    // Every solution of concrete == left + right has one of these exact split positions.
    // Retain the whole original body: a matching fragment alone is never a witness.
    private bool TrySimplifyExistsConcatenation(ExistsExpr original, Expression body,
      List<Expression> conjuncts, PartialEvalState state, out Expression replacement) {
      engine.CheckForCancellation();
      replacement = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        if (QuantifierBounds.NormalizeForPattern(conjunct, cancellationCheck) is not BinaryExpr {
          ResolvedOp: BinaryExpr.ResolvedOpcode.SeqEq
        } equality) {
          continue;
        }
        foreach (var (sequence, concatenation) in new[] { (equality.E0, equality.E1), (equality.E1, equality.E0) }) {
          cancellationCheck?.Invoke();
          if (QuantifierBounds.NormalizeForPattern(concatenation, cancellationCheck) is not BinaryExpr {
            ResolvedOp: BinaryExpr.ResolvedOpcode.Concat
          } concat || !TryGetConcreteSequenceElements(sequence, out var elements)) {
            continue;
          }
          var replaceLeft = TryFindMatchingBoundVar(concat.E0, original.BoundVars, out var variable);
          if (!replaceLeft && !TryFindMatchingBoundVar(concat.E1, original.BoundVars, out variable)) {
            continue;
          }
          if ((ulong)elements.Count + 1 > engine.GetRemainingQuantifierExpansionLimit()) {
            engine.RecordQuantifierExpansionExhaustion();
            return false;
          }
          var proofArtifacts = MarkProofArtifacts();
          var savedWitnesses = new Dictionary<IVariable, Expression>(existentialWitnessValues);
          var branches = new List<Expression>();
          void RestoreBranch() {
            engine.ProofWitnesses.RemoveRange(proofArtifacts.Witnesses,
              engine.ProofWitnesses.Count - proofArtifacts.Witnesses);
            engine.ProofCompositionCandidates.RemoveRange(proofArtifacts.Candidates,
              engine.ProofCompositionCandidates.Count - proofArtifacts.Candidates);
            engine.ProofPrerequisites.RemoveRange(proofArtifacts.Prerequisites,
              engine.ProofPrerequisites.Count - proofArtifacts.Prerequisites);
            engine.ProofConcreteCalls.RemoveRange(proofArtifacts.ConcreteCalls,
              engine.ProofConcreteCalls.Count - proofArtifacts.ConcreteCalls);
            existentialWitnessValues.Clear();
            foreach (var pair in savedWitnesses) { existentialWitnessValues.Add(pair.Key, pair.Value); }
          }
          for (var split = 0; split <= elements.Count; split++) {
            cancellationCheck?.Invoke();
            RestoreBranch();
            // A fragment has the source element type until its target refinement is checked.
            var prefix = CreateSeqDisplayLiteral(sequence.Origin, elements.Take(split).ToList(), sequence.Type);
            var suffix = CreateSeqDisplayLiteral(sequence.Origin, elements.Skip(split).ToList(), sequence.Type);
            var complement = Expression.CreateEq(replaceLeft ? concat.E1 : concat.E0,
              replaceLeft ? suffix : prefix, sequence.Type.NormalizeExpand());
            var branchBody = Expression.CreateAnd(body, complement, allowSimplification: false);
            if (!TryReplaceExistentialVariable(original, branchBody, variable, replaceLeft ? prefix : suffix,
                  new List<BoundVar>(), state, out var branch, out _)) {
              RestoreBranch();
              return false;
            }
            if (Expression.IsBoolLiteral(branch, out var holds) && holds) {
              replacement = branch;
              return true;
            }
            branches.Add(branch);
          }
          RestoreBranch();
          var disjunction = CombineDisjuncts(branches, original.Origin);
          if (engine.expressionExpansionBudget != null && !engine.expressionExpansionBudget.TryReserve(disjunction)) {
            return false;
          }
          replacement = SimplifyExpression(disjunction, state);
          // A successful concrete witness needs no universal sequence lemma. Supply
          // negative proof support only after every exact split has been refuted.
          if (engine.proofCompositionMode && branches.All(branch => Expression.IsBoolLiteral(branch, out var holds) && !holds) &&
              QuantifierBounds.NormalizeForPattern(concat.E0, cancellationCheck) is IdentifierExpr left &&
              QuantifierBounds.NormalizeForPattern(concat.E1, cancellationCheck) is IdentifierExpr right &&
              ReferenceEquals(left.Var, variable) && ReferenceEquals(right.Var, variable) &&
              !TryRecordRepeatedConcatenationPrerequisite(sequence, variable, elements)) {
            replacement = null;
            return false;
          }
          return true;
        }
      }
      return false;
    }

    // These closed universal implications are valid in every branch and polarity; they are not witness assumptions.
    private bool TryRecordRepeatedConcatenationPrerequisite(Expression sequence, BoundVar variable,
      List<Expression> elements) {
      var origin = sequence.Origin;
      var bound = new BoundVar(origin, "_contract_concat", variable.Type);
      var value = Expression.CreateIdentExpr(bound);
      var length = new UnaryOpExpr(origin, UnaryOpExpr.Opcode.Cardinality, value) { Type = Type.Int };
      var sum = new BinaryExpr(origin, BinaryExpr.Opcode.Add, length, length) {
        Type = Type.Int,
        ResolvedOp = BinaryExpr.ResolvedOpcode.Add
      };
      Expression facts = Expression.CreateEq(sum, Expression.CreateIntLiteral(origin, elements.Count), Type.Int);
      if (elements.Count % 2 == 0) {
        var half = elements.Count / 2;
        facts = Expression.CreateAnd(facts,
          Expression.CreateEq(length, Expression.CreateIntLiteral(origin, half), Type.Int));
        for (var index = 0; index < half; index++) {
          cancellationCheck?.Invoke();
          var selected = new SeqSelectExpr(origin, true, value, Expression.CreateIntLiteral(origin, index), null) {
            Type = variable.Type.NormalizeExpand().AsSeqType.Arg
          };
          facts = Expression.CreateAnd(facts, Expression.CreateEq(selected, elements[index], selected.Type.NormalizeExpand()));
          facts = Expression.CreateAnd(facts, Expression.CreateEq(selected, elements[half + index], selected.Type.NormalizeExpand()));
        }
      }
      var concat = new BinaryExpr(origin, BinaryExpr.Opcode.Add, value, value) {
        Type = sequence.Type,
        ResolvedOp = BinaryExpr.ResolvedOpcode.Concat
      };
      var equality = Expression.CreateEq(sequence, concat, sequence.Type.NormalizeExpand());
      var implication = new ForallExpr(origin, [bound], null, Expression.CreateImplies(equality, facts)) {
        Type = Type.Bool,
        Bounds = [null]
      };
      if (!IsClosedProofExpression(engine.options, implication, cancellationCheck)) { return false; }
      if (engine.GetRemainingQuantifierExpansionLimit() == 0) {
        engine.RecordQuantifierExpansionExhaustion();
        return false;
      }
      if (engine.expressionExpansionBudget != null && !engine.expressionExpansionBudget.TryReserve(implication)) {
        return false;
      }
      engine.RecordQuantifierExpansion();
      engine.ProofPrerequisites.Add(engine.CloneResolvedExpression(implication));
      return true;
    }

    private bool TryGetConcreteSequenceElements(Expression expression, out List<Expression> elements) {
      expression = NormalizeContractConcreteExpression(expression, cancellationCheck);
      if (expression is SeqDisplayExpr sequence && IsContractConcreteValue(sequence, cancellationCheck)) {
        elements = sequence.Elements;
        return true;
      }
      if (engine.TryGetUnescapedStringCharacters(expression, out var characters)) {
        elements = characters.Select(character => (Expression)CreateCharLiteral(expression.Origin,
          EscapeCharLiteral(character, engine.options.Get(CommonOptionBag.UnicodeCharacters)), Type.Char)).ToList();
        return true;
      }
      elements = null;
      return false;
    }

    private bool TryReplaceExistentialVariable(ExistsExpr original, Expression body, BoundVar variable,
      Expression value, List<BoundVar> newVariables, PartialEvalState state, out Expression replacement,
      out bool completedFullBody) {
      engine.CheckForCancellation();
      replacement = null;
      completedFullBody = false;
      if (engine.GetRemainingQuantifierExpansionLimit() == 0) {
        engine.RecordQuantifierExpansionExhaustion();
        return false;
      }
      var substitutions = new Dictionary<IVariable, Expression> { [variable] = value };
      if (IsContractConcreteValue(value, cancellationCheck) && variable.Type.NormalizeExpand().AsSeqType != null) {
        // Resolver-implied constraints cover the outer subset only, not nested sequence elements.
        body = Expression.CreateAnd(ConcreteSequenceTypeConstraint(value, variable.Type), body,
          allowSimplification: false);
      }
      if (!engine.TryReserveQuantifierInstanceExpansion(body, substitutions)) {
        return false;
      }
      engine.RecordQuantifierExpansion();
      var substituter = engine.CreateSubstituter(null, substitutions, null);
      var substituted = substituter.Substitute(engine.CloneResolvedExpression(body));
      var remaining = original.BoundVars.Where(candidate => !ReferenceEquals(candidate, variable)).ToList();
      remaining.AddRange(newVariables);
      Expression rewritten = remaining.Count == 0 ? substituted : new ExistsExpr(original.Origin,
        remaining, null, substituted, null) {
        Type = Type.Bool,
        Bounds = ModuleResolver.DiscoverBestBounds_MultipleVars(remaining, substituted, true)
      };
      if (engine.proofCompositionMode && rewritten is ExistsExpr remainingExists) {
        // Preserve completion provenance through exact structural substitution: an
        // empty remaining domain must not promote support staged before substitution.
        SimplifyQuantifierExpr(remainingExists, state, out completedFullBody);
        replacement = GetReplacement(remainingExists);
      } else {
        replacement = SimplifyExpression(rewritten, state);
        completedFullBody = remaining.Count == 0 && Expression.IsBoolLiteral(replacement, out _);
      }
      if (Expression.IsBoolLiteral(replacement, out var holds) && holds) {
        var witnessSubstituter = engine.CreateSubstituter(null, existentialWitnessValues, null);
        existentialWitnessValues[variable] = SimplifyExpression(
          witnessSubstituter.Substitute(engine.CloneResolvedExpression(value)), state.WithDepth(0));
      }
      return true;
    }

    private Expression ConcreteSequenceTypeConstraint(Expression value, Type expectedType) {
      engine.CheckForCancellation();
      var constraint = ModuleResolver.GetImpliedTypeConstraint(value, expectedType);
      if (expectedType.NormalizeExpand().AsSeqType is { } sequenceType &&
          TryGetConcreteSequenceElements(value, out var elements)) {
        foreach (var element in elements) {
          engine.CheckForCancellation();
          constraint = Expression.CreateAnd(constraint, ConcreteSequenceTypeConstraint(element, sequenceType.Arg));
        }
      } else if (expectedType.NormalizeExpand().TypeArgs.Count > 0) {
        // Unsupported nested containers retain a native membership test rather than acquiring a narrower type.
        constraint = Expression.CreateAnd(constraint,
          new TypeTestExpr(value.Origin, value, expectedType) { Type = Type.Bool });
      }
      return constraint;
    }

    private void RecordConcreteExistentialWitness(List<BoundVar> variables, Expression body) {
      engine.CheckForCancellation();
      if (!variables.All(variable => existentialWitnessValues.TryGetValue(variable, out var value) &&
                                     IsContractConcreteValue(value, cancellationCheck))) {
        return;
      }
      var substituter = engine.CreateSubstituter(null, existentialWitnessValues, null);
      var instance = substituter.Substitute(body);
      // Only escaping binder variables prevent lifting. Quantifiers inside the witness
      // bind their own variables and remain part of its independently checked assertion.
      if (!IsClosedProofExpression(engine.options, instance, cancellationCheck)) {
        return;
      }
      if (engine.expressionExpansionBudget == null || engine.expressionExpansionBudget.TryReserve(instance)) {
        engine.ProofWitnesses.Add(instance);
      }
    }

    // A datatype has finitely many constructor alternatives, but its fields keep their original domains.
    private bool TrySimplifyExistsConstructorAlternatives(ExistsExpr original, PartialEvalState state,
      out Expression replacement) {
      engine.CheckForCancellation();
      replacement = null;
      var variable = original.BoundVars.FirstOrDefault(bound => {
        cancellationCheck?.Invoke();
        return bound.Type.NormalizeExpand() is
          UserDefinedType { ResolvedClass: IndDatatypeDecl { Ctors.Count: > 1 } };
      });
      if (variable == null) { return false; }
      var type = (UserDefinedType)variable.Type.NormalizeExpand();
      var datatype = (IndDatatypeDecl)type.ResolvedClass;
      if (!datatype.IsRevealedInScope(engine.effectiveScope)) { return false; }
      if (datatype.Ctors.Count > engine.GetRemainingQuantifierExpansionLimit()) {
        engine.RecordQuantifierExpansionExhaustion();
        return false;
      }
      var body = QuantifierBounds.GetLogicalBodyWithImpliedTypeConstraints(original, cancellationCheck);
      var names = ContractReductionTraversal.LogicalNodes(body, cancellationCheck).OfType<IdentifierExpr>().Select(identifier => identifier.Name)
        .Concat(original.BoundVars.Select(bound => { cancellationCheck?.Invoke(); return bound.Name; })).ToHashSet();
      var nextName = 0;
      var mark = MarkProofArtifacts();
      var savedWitnesses = new Dictionary<IVariable, Expression>(existentialWitnessValues);
      var branches = new List<Expression>();
      void RestoreBranch() {
        engine.CheckForCancellation();
        RollbackProofArtifacts(mark);
        existentialWitnessValues.Clear();
        foreach (var pair in savedWitnesses) {
          engine.CheckForCancellation();
          existentialWitnessValues.Add(pair.Key, pair.Value);
        }
      }
      foreach (var constructor in datatype.Ctors) {
        engine.CheckForCancellation();
        RestoreBranch();
        var typeMap = TypeParameter.SubstitutionMap(datatype.TypeArgs, type.TypeArgs);
        var fields = new List<BoundVar>();
        foreach (var formal in constructor.Formals) {
          engine.CheckForCancellation();
          string name;
          do { cancellationCheck?.Invoke(); name = "_contract_case" + nextName++; } while (!names.Add(name));
          fields.Add(new BoundVar(variable.Origin, name, formal.Type.Subst(typeMap)));
        }
        var value = new DatatypeValue(variable.Origin, datatype.Name, constructor.Name,
          fields.Select(field => { cancellationCheck?.Invoke(); return (Expression)Expression.CreateIdentExpr(field); }).ToList()) {
          Ctor = constructor,
          Type = type,
          InferredTypeArgs = type.TypeArgs
        };
        if (!TryReplaceExistentialVariable(original, body, variable, value, fields, state, out var branch, out _)) {
          RestoreBranch();
          return false;
        }
        if (Expression.IsBoolLiteral(branch, out var holds) && holds) {
          replacement = branch;
          return true;
        }
        branches.Add(branch);
      }
      RestoreBranch();
      var disjunction = CombineDisjuncts(branches, original.Origin);
      if (engine.expressionExpansionBudget != null && !engine.expressionExpansionBudget.TryReserve(disjunction)) { return false; }
      replacement = disjunction;
      return true;
    }

    private bool TrySimplifyExistsByPointAssignments(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      engine.CheckForCancellation();
      replacement = null;
      if (existsExpr.BoundVars.Count == 0) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      combined = QuantifierBounds.ConjoinWithImpliedTypeConstraints(existsExpr.BoundVars, combined, existsExpr.Origin, cancellationCheck);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts, cancellationCheck);

      var assignments = new Dictionary<BoundVar, Expression>();
      var consumedConjuncts = new HashSet<Expression>();
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
        if (!consumedConjuncts.Contains(conjunct)) {
          residualConjuncts.Add(conjunct);
        }
      }

      var residual = CombineConjuncts(residualConjuncts, existsExpr.Origin);
      var substMap = new Dictionary<IVariable, Expression>(assignments.Count);
      foreach (var assignment in assignments) {
        cancellationCheck?.Invoke();
        substMap[assignment.Key] = assignment.Value;
      }

      var substituter = engine.CreateSubstituter(null, substMap, null);
      var substituted = substituter.Substitute(residual);
      replacement = SimplifyExpression(substituted, state);
      replacement.Type ??= Type.Bool;
      if (engine.proofCompositionMode && Expression.IsBoolLiteral(replacement, out var holds) && holds) {
        foreach (var assignment in assignments) {
          cancellationCheck?.Invoke();
          existentialWitnessValues[assignment.Key] = SimplifyExpression(
            engine.CloneResolvedExpression(assignment.Value), state);
        }
      }
      return true;
    }

    private bool TrySimplifyExistsByDisjunctivePointAssignments(ExistsExpr existsExpr, PartialEvalState state, out Expression replacement) {
      engine.CheckForCancellation();
      replacement = null;
      if (existsExpr.BoundVars.Count == 0) {
        return false;
      }

      var combined = existsExpr.Range == null
        ? existsExpr.Term
        : Expression.CreateAnd(existsExpr.Range, existsExpr.Term);
      combined = QuantifierBounds.ConjoinWithImpliedTypeConstraints(existsExpr.BoundVars, combined, existsExpr.Origin, cancellationCheck);
      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(combined, conjuncts, cancellationCheck);

      Expression disjunctiveChoices = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct, cancellationCheck);
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
      QuantifierBounds.CollectDisjuncts(disjunctiveChoices, branchExpressions, cancellationCheck);
      if (branchExpressions.Count == 0 || branchExpressions.Count > 16) {
        return false;
      }

      var nonChoiceConjuncts = new List<Expression>();
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        if (!ReferenceEquals(conjunct, disjunctiveChoices)) {
          nonChoiceConjuncts.Add(conjunct);
        }
      }

      var rewrittenDisjuncts = new List<Expression>();
      foreach (var branch in branchExpressions) {
        cancellationCheck?.Invoke();
        var branchConjuncts = new List<Expression>();
        QuantifierBounds.CollectConjuncts(branch, branchConjuncts, cancellationCheck);
        var branchAssignments = new Dictionary<BoundVar, Expression>();
        var consumedInBranch = new HashSet<Expression>();

        foreach (var branchConjunct in branchConjuncts) {

          cancellationCheck?.Invoke();
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
          cancellationCheck?.Invoke();
          if (!consumedInBranch.Contains(branchConjunct)) {
            branchResidualConjuncts.Add(branchConjunct);
          }
        }

        var branchResidual = CombineConjuncts(branchResidualConjuncts, existsExpr.Origin);
        var substMap = new Dictionary<IVariable, Expression>(branchAssignments.Count);
        foreach (var assignment in branchAssignments) {
          cancellationCheck?.Invoke();
          substMap[assignment.Key] = assignment.Value;
        }

        var substituter = engine.CreateSubstituter(null, substMap, null);
        var branchSubstituted = substituter.Substitute(branchResidual);
        var branchSimplified = SimplifyExpression(branchSubstituted, state);
        rewrittenDisjuncts.Add(branchSimplified);
      }

      var rewritten = CombineDisjuncts(rewrittenDisjuncts, existsExpr.Origin);
      replacement = SimplifyExpression(rewritten, state);
      replacement.Type ??= Type.Bool;
      return true;
    }

    private bool TryGetExistsPointAssignment(Expression expr, IReadOnlyList<BoundVar> boundVars,
      out BoundVar boundVar, out Expression assignedValue) {
      boundVar = null;
      assignedValue = null;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
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

    private bool TryFindMatchingBoundVar(Expression expr, IReadOnlyList<BoundVar> boundVars, out BoundVar boundVar) {
      foreach (var candidate in boundVars) {
        cancellationCheck?.Invoke();
        if (QuantifierBounds.IsBoundVar(expr, candidate, cancellationCheck)) {
          boundVar = candidate;
          return true;
        }
      }

      boundVar = null;
      return false;
    }

    private bool ContainsAnyBoundVar(Expression expr, IReadOnlyList<BoundVar> boundVars) {
      foreach (var boundVar in boundVars) {
        cancellationCheck?.Invoke();
        if (ContainsBoundVar(expr, boundVar)) {
          return true;
        }
      }

      return false;
    }


    private bool TrySimplifyForallByFiniteSupport(ForallExpr forallExpr, PartialEvalState state, out Expression replacement) {
      engine.CheckForCancellation();
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

      var logicalBody = QuantifierBounds.GetLogicalBodyWithImpliedTypeConstraints(forallExpr, cancellationCheck);
      if (logicalBody == null) {
        return false;
      }

      if (!ContainsBoundVar(logicalBody, boundVar)) {
        return false;
      }

      Expression independentFactor = null;
      if (forallExpr.Range == null && IsDefinitelyInhabitedBoundType(boundVar.Type)) {
        var conjuncts = new List<Expression>();
        QuantifierBounds.CollectConjuncts(logicalBody, conjuncts, cancellationCheck);
        var dependentConjuncts = new List<Expression>();
        var independentConjuncts = new List<Expression>();
        foreach (var conjunct in conjuncts) {
          cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
        outsideValue++;
      }
      valuesToCheck.Add(outsideValue);

      var instantiatedConjuncts = new List<Expression>(valuesToCheck.Count);
      foreach (var value in valuesToCheck) {
        cancellationCheck?.Invoke();
        var substMap = new Dictionary<IVariable, Expression>(1) {
          [boundVar] = CreateIntLiteral(forallExpr.Origin, value, boundVar.Type)
        };
        var substituter = engine.CreateSubstituter(null, substMap, null);
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

    private bool TryCollectFiniteSupportValues(Expression expr, BoundVar boundVar, HashSet<BigInteger> supportValues) {
      if (expr == null) {
        return true;
      }

      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (QuantifierBounds.IsBoundVar(expr, boundVar, cancellationCheck)) {
        return false;
      }

      if (expr is SeqSelectExpr { SelectOne: true, E0: not null, E1: null } selectExpr &&
          QuantifierBounds.IsBoundVar(selectExpr.E0, boundVar, cancellationCheck)) {
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
          cancellationCheck?.Invoke();
          if (ContainsBoundVar(arg, boundVar)) {
            return false;
          }
        }
      }

      foreach (var subExpression in expr.SubExpressions) {

        cancellationCheck?.Invoke();
        if (!TryCollectFiniteSupportValues(subExpression, boundVar, supportValues)) {
          return false;
        }
      }

      return true;
    }

    private bool TryCollectFiniteSupportFromBinary(BinaryExpr binaryExpr, BoundVar boundVar,
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
        if (!QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar, cancellationCheck)) {
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

    private bool TryCollectBoundVarComparisonValue(Expression left, Expression right, BoundVar boundVar,
      HashSet<BigInteger> supportValues) {
      if (QuantifierBounds.IsBoundVar(left, boundVar, cancellationCheck) && TryGetReducedIntLiteral(right, out var rightLiteral, cancellationCheck)) {
        supportValues.Add(rightLiteral);
        return true;
      }

      if (QuantifierBounds.IsBoundVar(right, boundVar, cancellationCheck) && TryGetReducedIntLiteral(left, out var leftLiteral, cancellationCheck)) {
        supportValues.Add(leftLiteral);
        return true;
      }

      return false;
    }

    private bool TryCollectIntValuesFromSetOrMapLiteral(Expression expr, HashSet<BigInteger> supportValues) {
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is SetDisplayExpr setDisplayExpr) {
        foreach (var element in setDisplayExpr.Elements) {
          cancellationCheck?.Invoke();
          if (!TryGetReducedIntLiteral(element, out var value, cancellationCheck)) {
            return false;
          }

          supportValues.Add(value);
        }

        return true;
      }

      if (expr is MultiSetDisplayExpr multiSetDisplayExpr) {
        foreach (var element in multiSetDisplayExpr.Elements) {
          cancellationCheck?.Invoke();
          if (!TryGetReducedIntLiteral(element, out var value, cancellationCheck)) {
            return false;
          }

          supportValues.Add(value);
        }

        return true;
      }

      if (expr is MapDisplayExpr mapDisplayExpr) {
        foreach (var entry in mapDisplayExpr.Elements) {
          cancellationCheck?.Invoke();
          if (!TryGetReducedIntLiteral(entry.A, out var key, cancellationCheck)) {
            return false;
          }

          supportValues.Add(key);
        }

        return true;
      }

      return false;
    }

    private bool TryCollectIntKeysFromMapLiteral(Expression expr, HashSet<BigInteger> supportValues) {
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is not MapDisplayExpr mapDisplayExpr) {
        return false;
      }

      foreach (var entry in mapDisplayExpr.Elements) {

        cancellationCheck?.Invoke();
        if (!TryGetReducedIntLiteral(entry.A, out var key, cancellationCheck)) {
          return false;
        }

        supportValues.Add(key);
      }

      return true;
    }


    private bool IsDefinitelyInhabitedBoundType(Type type) {
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
      engine.CheckForCancellation();
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
      QuantifierBounds.CollectConjuncts(combined, conjuncts, cancellationCheck);

      BigInteger? lowerBound = isNat ? BigInteger.Zero : null;
      Expression targetExpr = null;
      Expression divisorExpr = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct, cancellationCheck);
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

      var normalizedTarget = QuantifierBounds.NormalizeForPattern(targetExpr, cancellationCheck);
      var normalizedDivisor = QuantifierBounds.NormalizeForPattern(divisorExpr, cancellationCheck);
      QuantifierBounds.EnsureExpressionType(normalizedTarget, Type.Int);
      QuantifierBounds.EnsureExpressionType(normalizedDivisor, Type.Int);

      var simplifiedTarget = SimplifyExpression(normalizedTarget, state);
      var simplifiedDivisor = SimplifyExpression(normalizedDivisor, state);
      if (!TryGetReducedIntLiteral(simplifiedTarget, out var targetLiteral, cancellationCheck) ||
          !TryGetReducedIntLiteral(simplifiedDivisor, out var divisorLiteral, cancellationCheck)) {
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

    private bool TryMatchLowerBound(Expression expr, BoundVar boundVar, out BigInteger lowerBound) {
      lowerBound = default;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
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

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar, cancellationCheck) && TryGetReducedIntLiteral(binaryExpr.E1, out var literalRight, cancellationCheck)) {
        lowerBound = isGt ? literalRight + 1 : literalRight;
        return isGe || isGt;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar, cancellationCheck) && TryGetReducedIntLiteral(binaryExpr.E0, out var literalLeft, cancellationCheck)) {
        lowerBound = isLt ? literalLeft + 1 : literalLeft;
        return isLe || isLt;
      }

      return false;
    }

    private bool TryMatchUpperBound(Expression expr, BoundVar boundVar, out BigInteger upperBound) {
      upperBound = default;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
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

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar, cancellationCheck) && TryGetReducedIntLiteral(binaryExpr.E1, out var literalRight, cancellationCheck)) {
        upperBound = isLt ? literalRight - 1 : literalRight;
        return isLe || isLt;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar, cancellationCheck) && TryGetReducedIntLiteral(binaryExpr.E0, out var literalLeft, cancellationCheck)) {
        upperBound = isGt ? literalLeft - 1 : literalLeft;
        return isGe || isGt;
      }

      return false;
    }

    private bool TryMatchLinearMultiplicationEquality(Expression expr, BoundVar boundVar,
      out Expression target, out Expression divisor) {
      target = null;
      divisor = null;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }
      var isEq = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || binaryExpr.Op == BinaryExpr.Opcode.Eq;
      if (!isEq) {
        return false;
      }

      if (TryExtractScaledBoundVar(binaryExpr.E0, boundVar, out var leftDivisor, out var leftOffset) &&
          !ContainsBoundVar(binaryExpr.E1, boundVar)) {
        target = QuantifierBounds.NormalizeForPattern(Expression.CreateSubtract(binaryExpr.E1, leftOffset), cancellationCheck);
        divisor = QuantifierBounds.NormalizeForPattern(leftDivisor, cancellationCheck);
        return IsIntLike(target) && IsIntLike(divisor);
      }

      if (TryExtractScaledBoundVar(binaryExpr.E1, boundVar, out var rightDivisor, out var rightOffset) &&
          !ContainsBoundVar(binaryExpr.E0, boundVar)) {
        target = QuantifierBounds.NormalizeForPattern(Expression.CreateSubtract(binaryExpr.E0, rightOffset), cancellationCheck);
        divisor = QuantifierBounds.NormalizeForPattern(rightDivisor, cancellationCheck);
        return IsIntLike(target) && IsIntLike(divisor);
      }

      return false;
    }

    private bool TryExtractScaledBoundVar(Expression expr, BoundVar boundVar,
      out Expression divisor, out Expression offset) {
      divisor = null;
      offset = null;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);

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

    private bool TryExtractMulFactor(Expression expr, BoundVar boundVar, out Expression factor) {
      factor = null;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isMul = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.Mul || binaryExpr.Op == BinaryExpr.Opcode.Mul;
      if (!isMul) {
        return false;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar, cancellationCheck) && !ContainsBoundVar(binaryExpr.E1, boundVar)) {
        factor = binaryExpr.E1;
        return true;
      }

      if (QuantifierBounds.IsBoundVar(binaryExpr.E1, boundVar, cancellationCheck) && !ContainsBoundVar(binaryExpr.E0, boundVar)) {
        factor = binaryExpr.E0;
        return true;
      }

      return false;
    }

    private bool ContainsBoundVar(Expression expr, BoundVar boundVar) {
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (QuantifierBounds.IsBoundVar(expr, boundVar, cancellationCheck)) {
        return true;
      }

      foreach (var subExpression in expr.SubExpressions) {

        cancellationCheck?.Invoke();
        if (ContainsBoundVar(subExpression, boundVar)) {
          return true;
        }
      }

      return false;
    }

    private bool IsIntLike(Expression expr) {
      return expr.Type != null && expr.Type.NormalizeExpand().IsNumericBased(Type.NumericPersuasion.Int);
    }

    private Expression CreateResolvedIntBinary(
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
      engine.CheckForCancellation();
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
      QuantifierBounds.CollectConjuncts(combined, conjuncts, cancellationCheck);

      int? length = null;
      Expression lengthExpr = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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

      var cap = engine.GetRemainingQuantifierExpansionLimit();
      var domainSize = new BigInteger(elementDomain.Count);
      var product = BigInteger.One;
      for (var index = 0; index < length.Value; index++) {
        engine.CheckForCancellation();
        product *= domainSize;
        if (engine.HasQuantifierExpansionLimit() && product > cap) {
          engine.RecordQuantifierExpansionExhaustion();
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
      engine.CheckForCancellation();
      replacement = null;
      Expression localReplacement = null;
      var elements = new List<Expression>(length);
      var foundUnknown = false;

      bool EvaluateCandidate() {
        engine.CheckForCancellation();
        engine.RecordQuantifierExpansion();
        Expression literalExpr;
        if (isString) {
          var chars = new char[length];
          for (var index = 0; index < length; index++) {
            engine.CheckForCancellation();
            if (!TryGetCharLiteral(elements[index], out var value, cancellationCheck)) {
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
        var substituter = engine.CreateSubstituter(null, substMap, null);
        var instantiated = substituter.Substitute(residual);
        var simplified = SimplifyExpression(instantiated, state);
        if (!Expression.IsBoolLiteral(simplified, out var result)) {
          foundUnknown = true;
          return false;
        }
        return result;
      }

      bool Enumerate(int position) {
        engine.CheckForCancellation();
        if (position == length) {
          if (EvaluateCandidate()) {
            localReplacement = Expression.CreateBoolLiteral(existsExpr.Origin, true);
            localReplacement.Type = Type.Bool;
            return true;
          }
          return false;
        }

        foreach (var element in elementDomain) {
          engine.CheckForCancellation();
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

    private Expression CombineConjuncts(List<Expression> conjuncts, IOrigin origin) {
      if (conjuncts == null || conjuncts.Count == 0) {
        var literal = Expression.CreateBoolLiteral(origin, true);
        literal.Type = Type.Bool;
        return literal;
      }

      var current = conjuncts[0];
      for (var index = 1; index < conjuncts.Count; index++) {
        cancellationCheck?.Invoke();
        current = Expression.CreateAnd(current, conjuncts[index]);
      }
      if (current.Type == null) {
        current.Type = Type.Bool;
      }
      return current;
    }

    private Expression CombineDisjuncts(List<Expression> disjuncts, IOrigin origin) {
      if (disjuncts == null || disjuncts.Count == 0) {
        var literal = Expression.CreateBoolLiteral(origin, false);
        literal.Type = Type.Bool;
        return literal;
      }

      var current = disjuncts[0];
      for (var index = 1; index < disjuncts.Count; index++) {
        cancellationCheck?.Invoke();
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
      if (TrySimplifyMapKeySetComprehension(setComprehension, state, out var keySetDisplay)) {
        SetReplacement(setComprehension, keySetDisplay);
        return false;
      }
      if (engine.TryMaterializeSetComprehension(setComprehension, out var setDisplay)) {
        SetReplacement(setComprehension, setDisplay);
      }
      return false;
    }

    private bool IsInImpliedTypeDomain(BoundVar boundVar, Expression value, PartialEvalState state) {
      var typeConstraint = QuantifierBounds.GetImpliedTypeConstraint(boundVar, cancellationCheck);
      var substMap = new Dictionary<IVariable, Expression>(1) {
        [boundVar] = value
      };
      var substituter = engine.CreateSubstituter(null, substMap, null);
      var instantiatedConstraint = substituter.Substitute(typeConstraint);
      var simplifiedConstraint = SimplifyExpression(instantiatedConstraint, state.WithDepth(Math.Max(0, state.Depth - 1)));
      return Expression.IsBoolLiteral(simplifiedConstraint, out var isInDomain) && isInDomain;
    }

    private bool TrySimplifyMapKeySetComprehension(SetComprehension setComprehension, PartialEvalState state, out SetDisplayExpr setDisplay) {
      setDisplay = null;
      if (setComprehension.BoundVars.Count != 1 || setComprehension.Range == null) {
        return false;
      }

      var boundVar = setComprehension.BoundVars[0];
      if (!QuantifierBounds.IsBoundVar(setComprehension.Term, boundVar, cancellationCheck)) {
        return false;
      }

      var conjuncts = new List<Expression>();
      QuantifierBounds.CollectConjuncts(setComprehension.Range, conjuncts, cancellationCheck);

      MapDisplayExpr mapDisplay = null;
      foreach (var conjunct in conjuncts) {
        cancellationCheck?.Invoke();
        var normalized = QuantifierBounds.NormalizeForPattern(conjunct, cancellationCheck);

        if (TryMatchBoundVarMapMembership(normalized, boundVar, out var membershipMap)) {
          if (mapDisplay != null && !MapDisplayLiteralsEqual(mapDisplay, membershipMap, cancellationCheck)) {
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

      if (!TryNormalizeLiteralMapEntries(mapDisplay, out var normalizedEntries, cancellationCheck)) {
        return false;
      }

      var keys = new List<Expression>();
      foreach (var entry in normalizedEntries) {
        cancellationCheck?.Invoke();
        if (!TryGetReducedIntLiteral(entry.B, out var multiplicity, cancellationCheck)) {
          return false;
        }

        if (multiplicity > 0 && IsInImpliedTypeDomain(boundVar, entry.A, state)) {
          keys.Add(entry.A);
        }
      }

      setDisplay = CreateSetDisplayLiteral(setComprehension.Origin, keys, setComprehension.Type);
      return true;
    }

    private bool TryMatchBoundVarMapMembership(Expression expr, BoundVar boundVar, out MapDisplayExpr mapDisplay) {
      mapDisplay = null;
      if (expr is not BinaryExpr binaryExpr) {
        return false;
      }

      var isInMap = binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InMap || binaryExpr.Op == BinaryExpr.Opcode.In;
      if (!isInMap || !QuantifierBounds.IsBoundVar(binaryExpr.E0, boundVar, cancellationCheck)) {
        return false;
      }

      if (!TryGetMapDisplayLiteral(binaryExpr.E1, out var mapLiteral) ||
          !AllMapKeysAreLiterals(mapLiteral, cancellationCheck) ||
          !AllElementsAreLiterals(mapLiteral, cancellationCheck)) {
        return false;
      }

      mapDisplay = mapLiteral;
      return true;
    }

    private bool TryMatchPositiveMapValueConstraint(Expression expr, BoundVar boundVar, MapDisplayExpr expectedMap,
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
          TryGetReducedIntLiteral(binaryExpr.E1, out var rightLiteral, cancellationCheck) &&
          rightLiteral == 0) {
        return true;
      }

      if (TryGetMapSelectOverBoundVar(binaryExpr.E1, boundVar, expectedMap, out mapDisplay) &&
          TryGetReducedIntLiteral(binaryExpr.E0, out var leftLiteral, cancellationCheck) &&
          leftLiteral == 0) {
        return true;
      }

      mapDisplay = null;
      return false;
    }

    private bool TryGetMapSelectOverBoundVar(Expression expr, BoundVar boundVar, MapDisplayExpr expectedMap,
      out MapDisplayExpr mapDisplay) {
      mapDisplay = null;
      expr = QuantifierBounds.NormalizeForPattern(expr, cancellationCheck);
      if (expr is not SeqSelectExpr { SelectOne: true, E0: not null, E1: null } selectExpr) {
        return false;
      }

      if (!QuantifierBounds.IsBoundVar(selectExpr.E0, boundVar, cancellationCheck)) {
        return false;
      }

      if (!TryGetMapDisplayLiteral(selectExpr.Seq, out var mapLiteral) ||
          !AllMapKeysAreLiterals(mapLiteral, cancellationCheck) ||
          !AllElementsAreLiterals(mapLiteral, cancellationCheck)) {
        return false;
      }

      if (expectedMap != null && !MapDisplayLiteralsEqual(expectedMap, mapLiteral, cancellationCheck)) {
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
        cancellationCheck?.Invoke();
        letExpr.RHSs[i] = SimplifyExpression(letExpr.RHSs[i], state);
      }
      if (letExpr.Exact) {
        EnterScope();
        try {
          var allLiteral = true;
          for (var i = 0; i < letExpr.LHSs.Count; i++) {
            cancellationCheck?.Invoke();
            var boundVar = letExpr.LHSs[i].Var;
            if (boundVar == null) {
              allLiteral = false;
              continue;
            }
            if (ConstValue.TryCreate(letExpr.RHSs[i], out var letConstValue, cancellationCheck) ||
                TryCreateConcreteLetConst(letExpr.RHSs[i], boundVar.Type, state, out letConstValue)) {
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

    private bool TryCreateConcreteLetConst(Expression value, Type expectedType, PartialEvalState state,
      out ConstValue constant) {
      constant = default;
      if (!engine.proofCompositionMode || !engine.UsesContractConcreteProfile ||
          engine.expressionExpansionBudget == null || engine.quantifierExpansionBudget == null ||
          !SupportBudgetsIntact || value.Type == null || expectedType == null ||
          !IsConcreteLetTypeRevealed(value.Type, new HashSet<TopLevelDecl>()) ||
          !IsConcreteLetTypeRevealed(expectedType, new HashSet<TopLevelDecl>()) ||
          !value.Type.NormalizeExpand().Equals(expectedType.NormalizeExpand(), keepConstraints: true) ||
          !ConstValue.TryCreate(value, out var candidate, cancellationCheck, allowContractConcrete: true)) {
        return false;
      }

      // RHS simplification precedes this mark: its live support must survive a failed admission.
      var mark = MarkProofArtifacts();
      var previousSupportFrame = existentialSupportFrame;
      concreteLetMembershipDepth++;
      existentialSupportFrame = null;
      try {
        var membership = ConcreteCallSession.Membership(engine, value, expectedType);
        if (!engine.expressionExpansionBudget.TryReserve(membership)) {
          return false;
        }
        var checkedMembership = SimplifyExpression(engine.CloneResolvedExpression(membership), state);
        if (!Expression.IsBoolLiteral(checkedMembership, out var valid) || !valid ||
            !SupportBudgetsIntact || MarkProofArtifacts() != mark) {
          return false;
        }
        constant = candidate;
        return true;
      }
      finally {
        existentialSupportFrame = previousSupportFrame;
        concreteLetMembershipDepth--;
        RollbackProofArtifacts(mark);
      }
    }

    private bool IsConcreteLetTypeRevealed(Type type, HashSet<TopLevelDecl> visited) {
      engine.CheckForCancellation();
      type = type.Normalize();
      if (type is TypeProxy || engine.HasFreeTypeParametersIncludingUnexpandedArguments(type) ||
          !type.TypeArgs.All(argument => IsConcreteLetTypeRevealed(argument, visited))) {
        return false;
      }
      if (type is not UserDefinedType userType) {
        return true;
      }
      if (userType.ResolvedClass is not { } declaration ||
          declaration is InternalTypeSynonymDecl or NewtypeDecl ||
          !declaration.IsRevealedInScope(engine.effectiveScope)) {
        return false;
      }
      if (!visited.Add(declaration)) {
        return true;
      }
      if (declaration is TypeSynonymDecl synonym) {
        return IsConcreteLetTypeRevealed(synonym.RhsWithArgumentIgnoringScope(userType.TypeArgs), visited);
      }
      if (declaration is not IndDatatypeDecl datatype) {
        return false;
      }
      var typeMap = TypeParameter.SubstitutionMap(datatype.TypeArgs, userType.TypeArgs);
      foreach (var constructor in datatype.Ctors) {
        engine.CheckForCancellation();
        foreach (var formal in constructor.Formals) {
          engine.CheckForCancellation();
          if (!IsConcreteLetTypeRevealed(formal.Type.Subst(typeMap), visited)) {
            return false;
          }
        }
      }
      return true;
    }

    // ------------------- Expression rewriting: collection literals -------------------

    private bool SimplifySeqDisplayExpr(SeqDisplayExpr seqDisplayExpr, PartialEvalState state) {
      for (var i = 0; i < seqDisplayExpr.Elements.Count; i++) {
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
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
        cancellationCheck?.Invoke();
        setDisplayExpr.Elements[i] = SimplifyExpression(setDisplayExpr.Elements[i], state);
      }
      return false;
    }

    private bool SimplifyMultiSetDisplayExpr(MultiSetDisplayExpr multiSetDisplayExpr, PartialEvalState state) {
      for (var i = 0; i < multiSetDisplayExpr.Elements.Count; i++) {
        cancellationCheck?.Invoke();
        multiSetDisplayExpr.Elements[i] = SimplifyExpression(multiSetDisplayExpr.Elements[i], state);
      }
      return false;
    }

    private bool SimplifyMapDisplayExpr(MapDisplayExpr mapDisplayExpr, PartialEvalState state) {
      if (!engine.UsesContractConcreteProfile) {
        return false;
      }
      foreach (var entry in mapDisplayExpr.Elements) {
        cancellationCheck?.Invoke();
        entry.A = SimplifyExpression(entry.A, state);
        entry.B = SimplifyExpression(entry.B, state);
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
        if (engine.UsesContractConcreteProfile &&
            seqSelectExpr.Seq is MapDisplayExpr mapDisplay &&
            seqSelectExpr.E0 != null && IsContractConcreteValue(seqSelectExpr.E0, cancellationCheck) &&
            TryNormalizeContractConcreteMapEntries(mapDisplay, out var entries, cancellationCheck)) {
          var entry = entries.LastOrDefault(candidate =>
            AreContractConcreteExpressionsEqual(candidate.A, seqSelectExpr.E0, cancellationCheck));
          if (entry != null) {
            SetReplacement(seqSelectExpr, entry.B);
            return false;
          }
        }
        if (TryGetStringLiteral(seqSelectExpr.Seq, out var strValue, out var strVerbatim) &&
            seqSelectExpr.E0 != null &&
            TryGetIntLiteralValue(seqSelectExpr.E0, out var index, cancellationCheck) &&
            TryGetUnescapedCharLiteral(strValue, strVerbatim, index, out var escapedChar)) {
          result = CreateCharLiteral(seqSelectExpr.Origin, escapedChar, seqSelectExpr.Type);
          SetReplacement(seqSelectExpr, result);
          return false;
        }
        if (TryGetSeqDisplayLiteral(seqSelectExpr.Seq, out var display) &&
            (AllElementsAreLiterals(display, cancellationCheck) || engine.UsesContractConcreteProfile) &&
            seqSelectExpr.E0 != null &&
            TryGetIntLiteralValue(seqSelectExpr.E0, out index, cancellationCheck) &&
            0 <= index && index < display.Elements.Count &&
            (IsLiteralLike(display.Elements[index], cancellationCheck) || engine.UsesContractConcreteProfile)) {
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
          (AllElementsAreLiterals(sourceSeq, cancellationCheck) ||
           engine.UsesContractConcreteProfile && sourceSeq.Elements.All(value => IsContractConcreteValue(value, cancellationCheck))) &&
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

    private bool TrySimplifyArbitraryElement(FunctionCallExpr callExpr, out Expression simplified) {
      simplified = null;
      // This rewrite stays disabled until we can compare the exact builtin declaration identity.
      return false;
    }

    private bool TryGetSliceBounds(SeqSelectExpr expr, int length, out int start, out int end) {
      start = 0;
      end = length;
      if (expr.E0 != null && !TryGetIntLiteralValue(expr.E0, out start, cancellationCheck)) {
        return false;
      }
      if (expr.E1 != null && !TryGetIntLiteralValue(expr.E1, out end, cancellationCheck)) {
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
        cancellationCheck?.Invoke();
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

      public static bool TryCreate(Expression expression, out ConstValue cached, Action cancellationCheck = null,
        bool allowContractConcrete = false) {
        cached = default;
        if (expression == null) {
          return false;
        }
        if (!IsInlineableArgument(expression, cancellationCheck) &&
            !(allowContractConcrete && IsContractConcreteValue(expression, cancellationCheck))) {
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
