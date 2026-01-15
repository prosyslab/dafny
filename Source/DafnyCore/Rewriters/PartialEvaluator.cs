// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.Dafny;

public class PartialEvaluator : IRewriter {
  private readonly Program program;

  public PartialEvaluator(Program program, ErrorReporter reporter) : base(reporter) {
    Contract.Requires(program != null);
    this.program = program;
  }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    var entryName = Reporter.Options.Get(CommonOptionBag.PartialEvalEntry);
    if (string.IsNullOrEmpty(entryName)) {
      return;
    }

    var inlineDepth = Reporter.Options.Get(CommonOptionBag.PartialEvalInlineDepth);
    var entryTargets = new List<ICallable>();
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      if (decl is Declaration declaration && declaration.Name == entryName) {
        entryTargets.Add(decl);
      }
    }

    if (entryTargets.Count == 0) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Partial evaluation entry '{entryName}' was not found in module '{moduleDefinition.Name}'.");
      return;
    }

    if (entryTargets.Count > 1) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Multiple callables named '{entryName}' found; partial evaluation will run on all matches.");
    }

    var evaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth);
    foreach (var target in entryTargets) {
      evaluator.PartialEvalEntry(target);
    }
  }
}

internal sealed class PartialEvaluatorEngine {
  private readonly DafnyOptions options;
  private readonly ModuleDefinition module;
  private readonly SystemModuleManager systemModuleManager;
  private readonly uint inlineDepth;

  public PartialEvaluatorEngine(DafnyOptions options, ModuleDefinition module, SystemModuleManager systemModuleManager, uint inlineDepth) {
    this.options = options;
    this.module = module;
    this.systemModuleManager = systemModuleManager;
    this.inlineDepth = inlineDepth;
  }

  public void PartialEvalEntry(ICallable callable) {
    switch (callable) {
      case Function function when function.Body != null:
        function.Body = SimplifyExpr(function.Body, (int)inlineDepth, new HashSet<Function>());
        break;
      case MethodOrConstructor method when method.Body != null:
        SimplifyStmt(method.Body, (int)inlineDepth, new HashSet<Function>());
        break;
    }
  }

  private void SimplifyStmt(Statement stmt, int depth, HashSet<Function> inlineStack) {
    switch (stmt) {
      case BlockStmt block:
        foreach (var s in block.Body) {
          SimplifyStmt(s, depth, inlineStack);
        }
        break;
      case IfStmt ifStmt:
        ifStmt.Guard = SimplifyExpr(ifStmt.Guard, depth, inlineStack);
        SimplifyStmt(ifStmt.Thn, depth, inlineStack);
        if (ifStmt.Els != null) {
          SimplifyStmt(ifStmt.Els, depth, inlineStack);
        }
        break;
      case WhileStmt whileStmt:
        whileStmt.Guard = SimplifyExpr(whileStmt.Guard, depth, inlineStack);
        foreach (var inv in whileStmt.Invariants) {
          inv.E = SimplifyExpr(inv.E, depth, inlineStack);
        }
        if (whileStmt.Decreases?.Expressions != null) {
          for (var i = 0; i < whileStmt.Decreases.Expressions.Count; i++) {
            whileStmt.Decreases.Expressions[i] =
              SimplifyExpr(whileStmt.Decreases.Expressions[i], depth, inlineStack);
          }
        }
        SimplifyStmt(whileStmt.Body, depth, inlineStack);
        break;
      case AssertStmt assertStmt:
        assertStmt.Expr = SimplifyExpr(assertStmt.Expr, depth, inlineStack);
        break;
      case AssumeStmt assumeStmt:
        assumeStmt.Expr = SimplifyExpr(assumeStmt.Expr, depth, inlineStack);
        break;
      case ExpectStmt expectStmt:
        expectStmt.Expr = SimplifyExpr(expectStmt.Expr, depth, inlineStack);
        if (expectStmt.Message != null) {
          expectStmt.Message = SimplifyExpr(expectStmt.Message, depth, inlineStack);
        }
        break;
      case SingleAssignStmt assignStmt:
        if (assignStmt.Rhs is ExprRhs exprRhs) {
          exprRhs.Expr = SimplifyExpr(exprRhs.Expr, depth, inlineStack);
        }
        break;
      case CallStmt callStmt:
        callStmt.MethodSelect.Obj = SimplifyExpr(callStmt.MethodSelect.Obj, depth, inlineStack);
        for (var i = 0; i < callStmt.Args.Count; i++) {
          callStmt.Args[i] = SimplifyExpr(callStmt.Args[i], depth, inlineStack);
        }
        break;
      case ReturnStmt returnStmt:
        if (returnStmt.Rhss != null) {
          foreach (var rhs in returnStmt.Rhss) {
            if (rhs is ExprRhs returnExprRhs) {
              returnExprRhs.Expr = SimplifyExpr(returnExprRhs.Expr, depth, inlineStack);
            }
          }
        }
        break;
      case HideRevealStmt hideRevealStmt:
        if (hideRevealStmt.Exprs != null) {
          for (var i = 0; i < hideRevealStmt.Exprs.Count; i++) {
            var exprToSimplify = hideRevealStmt.Exprs[i];
            if (exprToSimplify == null || !exprToSimplify.WasResolved()) {
              continue;
            }
            hideRevealStmt.Exprs[i] = SimplifyExpr(exprToSimplify, depth, inlineStack);
          }
        }
        break;
      default:
        foreach (var sub in stmt.SubStatements) {
          SimplifyStmt(sub, depth, inlineStack);
        }
        break;
    }
  }

  private Expression SimplifyExpr(Expression expr, int depth, HashSet<Function> inlineStack) {
    if (expr == null) {
      return null;
    }

    if (expr.Resolved != null && expr.Resolved != expr) {
      expr = expr.Resolved;
    }

    switch (expr) {
      case ParensExpression parens:
        return SimplifyExpr(parens.E, depth, inlineStack);
      case LiteralExpr:
        return expr;
      case UnaryOpExpr unary:
        unary.E = SimplifyExpr(unary.E, depth, inlineStack);
        if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot &&
            Expression.IsBoolLiteral(unary.E, out var boolValue)) {
          return Expression.CreateBoolLiteral(unary.Origin, !boolValue);
        }
        return unary;
      case BinaryExpr binary:
        binary.E0 = SimplifyExpr(binary.E0, depth, inlineStack);
        binary.E1 = SimplifyExpr(binary.E1, depth, inlineStack);
        return SimplifyBinary(binary);
      case ITEExpr ite:
        ite.Test = SimplifyExpr(ite.Test, depth, inlineStack);
        if (Expression.IsBoolLiteral(ite.Test, out var cond)) {
          return SimplifyExpr(cond ? ite.Thn : ite.Els, depth, inlineStack);
        }
        ite.Thn = SimplifyExpr(ite.Thn, depth, inlineStack);
        ite.Els = SimplifyExpr(ite.Els, depth, inlineStack);
        return ite;
      case FunctionCallExpr callExpr:
        callExpr.Receiver = SimplifyExpr(callExpr.Receiver, depth, inlineStack);
        for (var i = 0; i < callExpr.Args.Count; i++) {
          callExpr.Args[i] = SimplifyExpr(callExpr.Args[i], depth, inlineStack);
        }
        if (depth > 0 && TryInlineCall(callExpr, depth, inlineStack, out var inlined)) {
          return inlined;
        }
        return callExpr;
      case QuantifierExpr quantifierExpr:
        quantifierExpr.Range = quantifierExpr.Range == null
          ? null
          : SimplifyExpr(quantifierExpr.Range, depth, inlineStack);
        quantifierExpr.Term = SimplifyExpr(quantifierExpr.Term, depth, inlineStack);
        quantifierExpr.Bounds = SimplifyBounds(quantifierExpr.Bounds, depth, inlineStack);
        return quantifierExpr;
      case LetExpr letExpr:
        for (var i = 0; i < letExpr.RHSs.Count; i++) {
          letExpr.RHSs[i] = SimplifyExpr(letExpr.RHSs[i], depth, inlineStack);
        }
        letExpr.Body = SimplifyExpr(letExpr.Body, depth, inlineStack);
        return letExpr;
      default:
        return expr;
    }
  }

  private List<BoundedPool> SimplifyBounds(List<BoundedPool> bounds, int depth, HashSet<Function> inlineStack) {
    if (bounds == null) {
      return null;
    }
    var changed = false;
    var newBounds = new List<BoundedPool>(bounds.Count);
    foreach (var bound in bounds) {
      var simplified = SimplifyBoundedPool(bound, depth, inlineStack);
      if (!ReferenceEquals(simplified, bound)) {
        changed = true;
      }
      newBounds.Add(simplified);
    }
    return changed ? newBounds : bounds;
  }

  private BoundedPool SimplifyBoundedPool(BoundedPool bound, int depth, HashSet<Function> inlineStack) {
    switch (bound) {
      case IntBoundedPool intPool: {
        var lower = intPool.LowerBound == null ? null : SimplifyExpr(intPool.LowerBound, depth, inlineStack);
        var upper = intPool.UpperBound == null ? null : SimplifyExpr(intPool.UpperBound, depth, inlineStack);
        if (lower != intPool.LowerBound || upper != intPool.UpperBound) {
          return new IntBoundedPool(lower, upper);
        }
        return bound;
      }
      case SetBoundedPool setPool: {
        var set = SimplifyExpr(setPool.Set, depth, inlineStack);
        return set != setPool.Set
          ? new SetBoundedPool(set, setPool.BoundVariableType, setPool.CollectionElementType, setPool.IsFiniteCollection)
          : bound;
      }
      case SubSetBoundedPool subSet: {
        var upper = SimplifyExpr(subSet.UpperBound, depth, inlineStack);
        return upper != subSet.UpperBound
          ? new SubSetBoundedPool(upper, subSet.IsFiniteCollection)
          : bound;
      }
      case SuperSetBoundedPool superSet: {
        var lower = SimplifyExpr(superSet.LowerBound, depth, inlineStack);
        return lower != superSet.LowerBound
          ? new SuperSetBoundedPool(lower)
          : bound;
      }
      case SeqBoundedPool seqPool: {
        var seq = SimplifyExpr(seqPool.Seq, depth, inlineStack);
        return seq != seqPool.Seq
          ? new SeqBoundedPool(seq, seqPool.BoundVariableType, seqPool.CollectionElementType)
          : bound;
      }
      case MapBoundedPool mapPool: {
        var map = SimplifyExpr(mapPool.Map, depth, inlineStack);
        return map != mapPool.Map
          ? new MapBoundedPool(map, mapPool.BoundVariableType, mapPool.CollectionElementType, mapPool.IsFiniteCollection)
          : bound;
      }
      case MultiSetBoundedPool multiSetPool: {
        var multiset = SimplifyExpr(multiSetPool.MultiSet, depth, inlineStack);
        return multiset != multiSetPool.MultiSet
          ? new MultiSetBoundedPool(multiset, multiSetPool.BoundVariableType, multiSetPool.CollectionElementType)
          : bound;
      }
      default:
        return bound;
    }
  }

  private Expression SimplifyBinary(BinaryExpr binary) {
    switch (binary.ResolvedOp) {
      case BinaryExpr.ResolvedOpcode.And:
        if (Expression.IsBoolLiteral(binary.E0, out var lAnd)) {
          return lAnd ? binary.E1 : Expression.CreateBoolLiteral(binary.Origin, false);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rAnd)) {
          return rAnd ? binary.E0 : Expression.CreateBoolLiteral(binary.Origin, false);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Or:
        if (Expression.IsBoolLiteral(binary.E0, out var lOr)) {
          return lOr ? Expression.CreateBoolLiteral(binary.Origin, true) : binary.E1;
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rOr)) {
          return rOr ? Expression.CreateBoolLiteral(binary.Origin, true) : binary.E0;
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Imp:
        if (Expression.IsBoolLiteral(binary.E0, out var lImp)) {
          return lImp ? binary.E1 : Expression.CreateBoolLiteral(binary.Origin, true);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rImp)) {
          return rImp ? Expression.CreateBoolLiteral(binary.Origin, true) : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Iff:
        if (Expression.IsBoolLiteral(binary.E0, out var lIff)) {
          return lIff ? binary.E1 : Expression.CreateNot(binary.Origin, binary.E1);
        }
        if (Expression.IsBoolLiteral(binary.E1, out var rIff)) {
          return rIff ? binary.E0 : Expression.CreateNot(binary.Origin, binary.E0);
        }
        return binary;
      case BinaryExpr.ResolvedOpcode.Add:
        return SimplifyIntBinary(binary, (a, b) => a + b, 0, BinaryExpr.ResolvedOpcode.Add);
      case BinaryExpr.ResolvedOpcode.Sub:
        return SimplifyIntBinary(binary, (a, b) => a - b, 0, BinaryExpr.ResolvedOpcode.Sub);
      case BinaryExpr.ResolvedOpcode.Mul:
        return SimplifyIntBinary(binary, (a, b) => a * b, 1, BinaryExpr.ResolvedOpcode.Mul);
      case BinaryExpr.ResolvedOpcode.Div:
        return SimplifyIntBinary(binary, (a, b) => b == 0 ? null : a / b);
      case BinaryExpr.ResolvedOpcode.Mod:
        return SimplifyIntBinary(binary, (a, b) => b == 0 ? null : a % b);
      case BinaryExpr.ResolvedOpcode.Lt:
        return SimplifyIntComparison(binary, (a, b) => a < b);
      case BinaryExpr.ResolvedOpcode.Le:
        return SimplifyIntComparison(binary, (a, b) => a <= b);
      case BinaryExpr.ResolvedOpcode.Gt:
        return SimplifyIntComparison(binary, (a, b) => a > b);
      case BinaryExpr.ResolvedOpcode.Ge:
        return SimplifyIntComparison(binary, (a, b) => a >= b);
      case BinaryExpr.ResolvedOpcode.EqCommon:
        return SimplifyEquality(binary, true);
      case BinaryExpr.ResolvedOpcode.NeqCommon:
        return SimplifyEquality(binary, false);
      default:
        return binary;
    }
  }

  private Expression SimplifyIntBinary(BinaryExpr binary, System.Func<BigInteger, BigInteger, BigInteger> op, int identity, BinaryExpr.ResolvedOpcode opcode) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      return CreateIntLiteral(binary.Origin, op(left, right));
    }

    if (Expression.IsIntLiteral(binary.E0, out left) && left == identity && opcode == BinaryExpr.ResolvedOpcode.Add) {
      return binary.E1;
    }

    if (Expression.IsIntLiteral(binary.E1, out right) && right == identity && opcode is BinaryExpr.ResolvedOpcode.Add or BinaryExpr.ResolvedOpcode.Sub) {
      return binary.E0;
    }

    if (opcode == BinaryExpr.ResolvedOpcode.Mul) {
      if (Expression.IsIntLiteral(binary.E0, out left)) {
        if (left == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (left == 1) {
          return binary.E1;
        }
      }
      if (Expression.IsIntLiteral(binary.E1, out right)) {
        if (right == 0) {
          return CreateIntLiteral(binary.Origin, BigInteger.Zero);
        }
        if (right == 1) {
          return binary.E0;
        }
      }
    }

    return binary;
  }

  private Expression SimplifyIntBinary(BinaryExpr binary, System.Func<BigInteger, BigInteger, BigInteger?> op) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      var result = op(left, right);
      if (result != null) {
        return CreateIntLiteral(binary.Origin, result.Value);
      }
    }
    return binary;
  }

  private Expression SimplifyIntComparison(BinaryExpr binary, System.Func<BigInteger, BigInteger, bool> op) {
    if (Expression.IsIntLiteral(binary.E0, out var left) && Expression.IsIntLiteral(binary.E1, out var right)) {
      return Expression.CreateBoolLiteral(binary.Origin, op(left, right));
    }
    return binary;
  }

  private Expression SimplifyEquality(BinaryExpr binary, bool isEq) {
    if (Expression.IsBoolLiteral(binary.E0, out var leftBool) && Expression.IsBoolLiteral(binary.E1, out var rightBool)) {
      return Expression.CreateBoolLiteral(binary.Origin, isEq ? leftBool == rightBool : leftBool != rightBool);
    }
    if (Expression.IsIntLiteral(binary.E0, out var leftInt) && Expression.IsIntLiteral(binary.E1, out var rightInt)) {
      return Expression.CreateBoolLiteral(binary.Origin, isEq ? leftInt == rightInt : leftInt != rightInt);
    }
    return binary;
  }

  private bool TryInlineCall(FunctionCallExpr callExpr, int depth, HashSet<Function> inlineStack, out Expression inlined) {
    inlined = null;
    var function = callExpr.Function;
    if (function == null || function.Body == null || depth <= 0) {
      return false;
    }

    if (BoogieGenerator.IsOpaque(function, options) || !function.IsRevealedInScope(module.VisibilityScope)) {
      return false;
    }

    if (function.Reads.Expressions != null && function.Reads.Expressions.Count > 0) {
      return false;
    }

    for (var i = 0; i < callExpr.Args.Count; i++) {
      var simplifiedArg = SimplifyExpr(callExpr.Args[i], 0, inlineStack);
      if (simplifiedArg is not LiteralExpr) {
        return false;
      }
      callExpr.Args[i] = simplifiedArg;
    }

    if (!inlineStack.Add(function)) {
      return false;
    }

    var substMap = new Dictionary<IVariable, Expression>(function.Ins.Count);
    for (var i = 0; i < function.Ins.Count; i++) {
      substMap[function.Ins[i]] = callExpr.Args[i];
    }

    Expression receiverReplacement = function.IsStatic ? null : callExpr.Receiver;
    var typeMap = callExpr.GetTypeArgumentSubstitutions();
    var substituter = new Substituter(receiverReplacement, substMap, typeMap, null, systemModuleManager);
    var body = substituter.Substitute(function.Body);
    inlined = SimplifyExpr(body, depth - 1, inlineStack);
    inlineStack.Remove(function);
    return true;
  }

  private static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value) {
    return new LiteralExpr(origin, value) { Type = Type.Int };
  }
}
