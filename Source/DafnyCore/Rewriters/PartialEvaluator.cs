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
    var state = new PartialEvalState((int)inlineDepth, new HashSet<Function>());
    var visitor = new PartialEvaluatorVisitor(this);
    switch (callable) {
      case Function function when function.Body != null:
        function.Body = visitor.SimplifyExpression(function.Body, state);
        break;
      case MethodOrConstructor method when method.Body != null:
        visitor.Visit(method.Body, state);
        break;
    }
  }

  private static void AssertHasResolvedType(Expression expr) {
    if (expr == null) {
      return;
    }
    Contract.Assert(expr.Type != null, "PartialEvaluator produced an expression with null Type");
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

  private bool TryInlineCall(FunctionCallExpr callExpr, PartialEvalState state, PartialEvaluatorVisitor visitor, out Expression inlined) {
    inlined = null;
    var function = callExpr.Function;
    if (function == null || function.Body == null || state.Depth <= 0) {
      return false;
    }

    if (BoogieGenerator.IsOpaque(function, options) || !function.IsRevealedInScope(module.VisibilityScope)) {
      return false;
    }

    if (function.Reads.Expressions != null && function.Reads.Expressions.Count > 0) {
      return false;
    }

    for (var i = 0; i < callExpr.Args.Count; i++) {
      var simplifiedArg = visitor.SimplifyExpression(callExpr.Args[i], state.WithDepth(0));
      if (simplifiedArg is not LiteralExpr) {
        return false;
      }
      callExpr.Args[i] = simplifiedArg;
    }

    if (!state.InlineStack.Add(function)) {
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
    inlined = visitor.SimplifyExpression(body, state.WithDepth(state.Depth - 1));
    state.InlineStack.Remove(function);
    return true;
  }

  private static LiteralExpr CreateIntLiteral(IOrigin origin, BigInteger value) {
    return new LiteralExpr(origin, value) { Type = Type.Int };
  }

  private sealed class PartialEvalState {
    public int Depth { get; }
    public HashSet<Function> InlineStack { get; }

    public PartialEvalState(int depth, HashSet<Function> inlineStack) {
      Depth = depth;
      InlineStack = inlineStack;
    }

    public PartialEvalState WithDepth(int depth) {
      return new PartialEvalState(depth, InlineStack);
    }
  }

  private sealed class PartialEvaluatorVisitor : TopDownVisitor<PartialEvalState> {
    private readonly PartialEvaluatorEngine engine;
    private readonly Dictionary<Expression, Expression> replacements = new();

    public PartialEvaluatorVisitor(PartialEvaluatorEngine engine) {
      this.engine = engine;
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

    protected override bool VisitOneStmt(Statement stmt, ref PartialEvalState state) {
      switch (stmt) {
        case BlockStmt block:
          foreach (var s in block.Body) {
            Visit(s, state);
          }
          break;
        case IfStmt ifStmt:
          ifStmt.Guard = SimplifyExpression(ifStmt.Guard, state);
          Visit(ifStmt.Thn, state);
          if (ifStmt.Els != null) {
            Visit(ifStmt.Els, state);
          }
          break;
        case WhileStmt whileStmt:
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
          if (assignStmt.Rhs is ExprRhs exprRhs) {
            exprRhs.Expr = SimplifyExpression(exprRhs.Expr, state);
          }
          break;
        case CallStmt callStmt:
          callStmt.MethodSelect.Obj = SimplifyExpression(callStmt.MethodSelect.Obj, state);
          for (var i = 0; i < callStmt.Args.Count; i++) {
            callStmt.Args[i] = SimplifyExpression(callStmt.Args[i], state);
          }
          break;
        case ReturnStmt returnStmt:
          if (returnStmt.Rhss != null) {
            foreach (var rhs in returnStmt.Rhss) {
              if (rhs is ExprRhs returnExprRhs) {
                returnExprRhs.Expr = SimplifyExpression(returnExprRhs.Expr, state);
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
              hideRevealStmt.Exprs[i] = SimplifyExpression(exprToSimplify, state);
            }
          }
          break;
        default:
          foreach (var sub in stmt.SubStatements) {
            Visit(sub, state);
          }
          break;
      }
      return false;
    }

    protected override bool VisitOneExpr(Expression expr, ref PartialEvalState state) {
      Expression result;
      switch (expr) {
        case ParensExpression parens:
          result = SimplifyExpression(parens.E, state);
          SetReplacement(parens, result);
          return false;
        case LiteralExpr:
          return false;
        case UnaryOpExpr unary:
          unary.E = SimplifyExpression(unary.E, state);
          if (unary.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BoolNot &&
              Expression.IsBoolLiteral(unary.E, out var boolValue)) {
            result = Expression.CreateBoolLiteral(unary.Origin, !boolValue);
            SetReplacement(unary, result);
            return false;
          }
          return false;
        case BinaryExpr binary:
          binary.E0 = SimplifyExpression(binary.E0, state);
          binary.E1 = SimplifyExpression(binary.E1, state);
          result = engine.SimplifyBinary(binary);
          SetReplacement(binary, result);
          return false;
        case ITEExpr ite:
          ite.Test = SimplifyExpression(ite.Test, state);
          if (Expression.IsBoolLiteral(ite.Test, out var cond)) {
            result = SimplifyExpression(cond ? ite.Thn : ite.Els, state);
            SetReplacement(ite, result);
            return false;
          }
          ite.Thn = SimplifyExpression(ite.Thn, state);
          ite.Els = SimplifyExpression(ite.Els, state);
          return false;
        case FunctionCallExpr callExpr:
          callExpr.Receiver = SimplifyExpression(callExpr.Receiver, state);
          for (var i = 0; i < callExpr.Args.Count; i++) {
            callExpr.Args[i] = SimplifyExpression(callExpr.Args[i], state);
          }
          if (state.Depth > 0 && engine.TryInlineCall(callExpr, state, this, out var inlined)) {
            SetReplacement(callExpr, inlined);
            return false;
          }
          return false;
        case QuantifierExpr quantifierExpr:
          quantifierExpr.Range = quantifierExpr.Range == null
            ? null
            : SimplifyExpression(quantifierExpr.Range, state);
          quantifierExpr.Term = SimplifyExpression(quantifierExpr.Term, state);
          quantifierExpr.Bounds = SimplifyBounds(quantifierExpr.Bounds, state);
          return false;
        case LetExpr letExpr:
          for (var i = 0; i < letExpr.RHSs.Count; i++) {
            letExpr.RHSs[i] = SimplifyExpression(letExpr.RHSs[i], state);
          }
          letExpr.Body = SimplifyExpression(letExpr.Body, state);
          return false;
        default:
          return false;
      }
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
  }
}
