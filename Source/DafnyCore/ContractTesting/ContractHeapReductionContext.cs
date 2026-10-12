#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>A typed, resolved cell value established at one diagnostic heap epoch.</summary>
public sealed record ContractHeapReductionFact(IVariable Reference, Field Field, Expression Value);

/// <summary>Immutable known heap cells and explicitly revealed definitions for one reduction.</summary>
public sealed class ContractHeapReductionContext {
  private readonly Dictionary<(IVariable, Field), Expression> entry;
  private readonly Dictionary<(IVariable, Field), Expression> current;
  private readonly HashSet<Function> revealed;

  /// <summary>Copies resolved facts and reveal identities for an isolated reduction.</summary>
  public ContractHeapReductionContext(IEnumerable<ContractHeapReductionFact> entry,
    IEnumerable<ContractHeapReductionFact> current, IEnumerable<Function>? revealed = null,
    Action? cancellationCheck = null) {
    this.entry = Copy(entry, cancellationCheck);
    this.current = Copy(current, cancellationCheck);
    this.revealed = [];
    foreach (var function in revealed ?? []) {
      cancellationCheck?.Invoke();
      this.revealed.Add(function);
    }
    cancellationCheck?.Invoke();
  }

  internal bool IsRevealed(Function function) => revealed.Contains(function);

  internal bool TryRead(MemberSelectExpr expression, bool oldHeap, out Expression value) {
    value = null!;
    return expression.Obj.Resolved is IdentifierExpr { Var: { } reference } &&
      expression.Member is Field field &&
      (oldHeap || !field.IsMutable ? entry : current).TryGetValue((reference, field), out value!);
  }

  // A formal denotes its already evaluated argument even beneath old. Residual
  // heap expressions cannot be substituted there without a separate value binder.
  /// <summary>Checks whether substitution beneath old preserves an already evaluated value.</summary>
  public static bool IsHeapIndependent(Expression expression) => IsHeapIndependent(expression, null);

  /// <summary>Checks each recursively visited value against the caller's query boundary.</summary>
  public static bool IsHeapIndependent(Expression expression, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    expression = expression.Resolved;
    return expression switch {
      LiteralExpr or IdentifierExpr or StaticReceiverExpr => true,
      MemberSelectExpr member when member.AtLabel == null && member.Member is DatatypeDestructor or DatatypeDiscriminator => IsHeapIndependent(member.Obj, cancellationCheck),
      FunctionCallExpr call => !call.Function.ReadsHeap && call.AtLabel == null &&
        IsHeapIndependent(call.Receiver, cancellationCheck) &&
        call.Args.All(argument => IsHeapIndependent(argument, cancellationCheck)),
      BinaryExpr or UnaryOpExpr or ConversionExpr or ITEExpr or DatatypeValue or DisplayExpression or MapDisplayExpr =>
        expression.SubExpressions.All(child => IsHeapIndependent(child, cancellationCheck)),
      SeqSelectExpr select => !select.Seq.Type.IsArrayType && expression.SubExpressions.All(child => IsHeapIndependent(child, cancellationCheck)),
      OldExpr old when old.AtLabel == null => IsHeapIndependent(old.Expr, cancellationCheck),
      _ => false
    };
  }

  private static Dictionary<(IVariable, Field), Expression> Copy(IEnumerable<ContractHeapReductionFact> facts,
    Action? cancellationCheck) {
    ArgumentNullException.ThrowIfNull(facts);
    var result = new Dictionary<(IVariable, Field), Expression>();
    foreach (var fact in facts) {
      cancellationCheck?.Invoke();
      if (!fact.Reference.Type.IsRefType || !fact.Value.WasResolved() || fact.Value.Type == null ||
          !IsHeapIndependent(fact.Value, cancellationCheck)) {
        throw new ArgumentException("Heap reduction facts require resolved heap-independent values and reference identities.");
      }
      result.Add((fact.Reference, fact.Field), new ContractReductionCloner(cancellationCheck).CloneExpr(fact.Value));
    }
    return result;
  }
}

/// <summary>Observed state projection work, without asserting a logical verdict.</summary>
public sealed record ContractHeapReductionStatistics(int EntryReads, int CurrentReads, int StatefulInlines,
  IReadOnlyList<string> ResidualReasons);

internal sealed class ContractHeapReductionSession(ContractHeapReductionContext context) {
  internal ContractHeapReductionContext Context { get; } = context;
  internal int EntryReads;
  internal int CurrentReads;
  internal int StatefulInlines;
  internal HashSet<string> ResidualReasons { get; } = [];
  internal ContractHeapReductionStatistics Statistics => new(EntryReads, CurrentReads, StatefulInlines,
    ResidualReasons.OrderBy(reason => reason, StringComparer.Ordinal).ToList().AsReadOnly());
}
