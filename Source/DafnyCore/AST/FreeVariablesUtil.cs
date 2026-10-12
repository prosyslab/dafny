using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public static class FreeVariablesUtil {
    /// <summary>
    /// Returns true iff
    ///   (if 'v' is non-null) 'v' occurs as a free variable in 'expr' or
    ///   (if 'lookForReceiver' is true) 'this' occurs in 'expr'.
    /// </summary>
    public static bool ContainsFreeVariable(Expression expr, bool lookForReceiver, IVariable v) =>
      ContainsFreeVariable(expr, lookForReceiver, v, null);

    /// <summary>Checks free-variable occurrence while observing the supplied traversal boundary.</summary>
    public static bool ContainsFreeVariable(Expression expr, bool lookForReceiver, IVariable v, Action cancellationCheck) {
      cancellationCheck?.Invoke();
      Contract.Requires(expr != null);
      Contract.Requires(lookForReceiver || v != null);

      if (expr is ThisExpr) {
        return lookForReceiver;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return e.Var == v;
      } else {
        return Contract.Exists(expr.SubExpressions, ee => ContainsFreeVariable(ee, lookForReceiver, v, cancellationCheck));
      }
    }

    public static ISet<IVariable> ComputeFreeVariables(DafnyOptions options, Expression expr) {
      Contract.Requires(expr != null);
      ISet<IVariable> fvs = new HashSet<IVariable>();
      ComputeFreeVariables(options, expr, fvs);
      return fvs;
    }
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr, ISet<IVariable> fvs) =>
      ComputeFreeVariables(options, expr, fvs, null);

    /// <summary>Adds free variables while observing the supplied traversal boundary.</summary>
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr, ISet<IVariable> fvs, Action cancellationCheck) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare0 = false, dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(options, expr, fvs, ref dontCare0, ref dontCare1, dontCareHeapAt, ref dontCareT, false, cancellationCheck);
    }
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr, ISet<IVariable> fvs, ref bool usesHeap, bool includeStatements = false) =>
      ComputeFreeVariables(options, expr, fvs, ref usesHeap, includeStatements, null);

    /// <summary>Collects free variables and heap use with cancellation during recursive traversal.</summary>
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr, ISet<IVariable> fvs,
      ref bool usesHeap, bool includeStatements, Action cancellationCheck) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(options, expr, fvs, ref usesHeap, ref dontCare1, dontCareHeapAt, ref dontCareT, includeStatements, cancellationCheck);
    }
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr,
      ISet<IVariable> fvs,
      ref bool usesHeap, ref bool usesOldHeap, ISet<Label> freeHeapAtVariables, ref Type usesThis,
      bool includeStatements) =>
      ComputeFreeVariables(options, expr, fvs, ref usesHeap, ref usesOldHeap, freeHeapAtVariables,
        ref usesThis, includeStatements, null);

    /// <summary>Tracks free variables, receivers and heap epochs while checking recursive expressions and statements.</summary>
    public static void ComputeFreeVariables(DafnyOptions options, Expression expr, ISet<IVariable> fvs,
      ref bool usesHeap, ref bool usesOldHeap, ISet<Label> freeHeapAtVariables, ref Type usesThis,
      bool includeStatements, Action cancellationCheck) {
      cancellationCheck?.Invoke();
      Contract.Requires(expr != null);

      if (expr is ThisExpr) {
        Contract.Assert(expr.Type != null);
        usesThis = expr.Type;
        return;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        fvs.Add(e.Var);
        return;
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is not Field { IsMutable: false }) {
          usesHeap = true;
        }
        if (e.AtLabel != null) {
          freeHeapAtVariables.Add(e.AtLabel);
        }
      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is MultiSelectExpr) {
        usesHeap = true;
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function == null || e.Function.ReadsHeap) {
          usesHeap = true;
        }
        if (e.AtLabel != null) {
          freeHeapAtVariables.Add(e.AtLabel);
        }
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        // Note, we don't have to look out for const fields here, because const fields
        // are not allowed in unchanged expressions.
        usesHeap = true;
        if (e.AtLabel == null) {
          usesOldHeap = true;
        } else {
          freeHeapAtVariables.Add(e.AtLabel);
        }
      } else if (expr is ApplyExpr) {
        usesHeap = true; // because the translation of an ApplyExpr always throws in the heap variable
      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Fresh) {
          var f = (FreshExpr)e;
          if (f.AtLabel == null) {
            usesOldHeap = true;
          } else {
            freeHeapAtVariables.Add(f.AtLabel);
          }
        } else if (e.Op == UnaryOpExpr.Opcode.Allocated) {
          usesHeap = true;
        }
      }

      // visit subexpressions
      bool uHeap = false, uOldHeap = false;
      Type uThis = null;
      if (expr is StmtExpr stmtExpr && includeStatements) {
        foreach (var subExpression in StatementExpressions(stmtExpr.S, cancellationCheck)) {
          ComputeFreeVariables(options, subExpression, fvs, ref uHeap, ref uOldHeap, freeHeapAtVariables, ref uThis, includeStatements, cancellationCheck);
        }
      }
      foreach (var subExpression in expr.SubExpressions) {
        ComputeFreeVariables(options, subExpression, fvs, ref uHeap, ref uOldHeap, freeHeapAtVariables, ref uThis, includeStatements, cancellationCheck);
      }
      Contract.Assert(usesThis == null || uThis == null || usesThis.Equals(uThis));
      usesThis = usesThis ?? uThis;
      var asOldExpr = expr as OldExpr;
      if (asOldExpr != null && asOldExpr.AtLabel == null) {
        usesOldHeap |= uHeap | uOldHeap;
      } else if (asOldExpr != null) {
        if (uHeap) {  // if not, then there was no real point in using an "old" expression
          freeHeapAtVariables.Add(asOldExpr.AtLabel);
        }
        usesOldHeap |= uOldHeap;
      } else {
        usesHeap |= uHeap;
        usesOldHeap |= uOldHeap;
      }

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var pattern in e.LHSs) {
          RemovePatternVariables(pattern, fvs, cancellationCheck);
        }
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var v in e.BoundVars) {
          cancellationCheck?.Invoke();
          fvs.Remove(v);
        }
      } else if (expr is MatchExpr me) {
        foreach (var matchCase in me.Cases) {
          cancellationCheck?.Invoke();
          foreach (var variable in matchCase.Arguments) {
            cancellationCheck?.Invoke();
            fvs.Remove(variable);
          }
        }
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        foreach (var matchCase in nestedMatchExpr.Cases) {
          cancellationCheck?.Invoke();
          var pending = new Stack<INode>();
          pending.Push(matchCase.Pat);
          while (pending.TryPop(out var pattern)) {
            cancellationCheck?.Invoke();
            if (pattern is IdPattern { Arguments: null } identifier) {
              fvs.Remove(identifier.BoundVar);
            }
            foreach (var child in pattern.Children) {
              cancellationCheck?.Invoke();
              pending.Push(child);
            }
          }
        }
      }
    }

    private static void RemovePatternVariables(CasePattern<BoundVar> pattern, ISet<IVariable> freeVariables,
      Action cancellationCheck) {
      cancellationCheck?.Invoke();
      if (pattern.Var != null) {
        freeVariables.Remove(pattern.Var);
      } else if (pattern.Arguments != null) {
        foreach (var argument in pattern.Arguments) {
          RemovePatternVariables(argument, freeVariables, cancellationCheck);
        }
      }
    }

    private static IEnumerable<Expression> StatementExpressions(Statement statement, Action cancellationCheck) {
      cancellationCheck?.Invoke();
      foreach (var expression in statement.SubExpressions) {
        cancellationCheck?.Invoke();
        yield return expression;
      }
      foreach (var child in statement.SubStatements) {
        cancellationCheck?.Invoke();
        foreach (var expression in StatementExpressions(child, cancellationCheck)) {
          yield return expression;
        }
      }
    }
  }
}