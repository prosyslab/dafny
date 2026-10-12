#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Projects known states in a straight-line query and adds only a checked equivalence.</summary>
public static class ContractQueryHeapReduction {
  public const string EquivalenceMarker = "contract_reduction_equivalence";

  /// <summary>Retains all original statements and target metadata; unsupported query shapes are unchanged.</summary>
  public static bool TryApply(Program program, Method method, TextWriter log, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    if (method.Body is not { Body.Count: > 0 } body || body.Body[^1] is not AssertStmt target) { return false; }
    var originals = body.Body.ToArray();
    var originalExpression = target.Expr;
    var originalOrigin = target.Origin;
    var originalAttributes = target.Attributes;
    var budget = new ContractReductionBudget();
    var requires = method.Req.SelectMany(clause => Conjuncts(clause.E, cancellationCheck)).ToList();
    var inputNodes = requires.Concat([target.Expr]).SelectMany(expression => Nodes(expression, cancellationCheck))
      .Take((int)budget.ExpressionNodeLimit + 1).Count();
    if (inputNodes > budget.ExpressionNodeLimit) { log.WriteLine("Heap reduction residual: context_node_limit."); return false; }
    var aliases = method.Ins.Where(variable => variable.Type.IsRefType).ToDictionary(variable => (IVariable)variable, variable => (IVariable)variable);
    IVariable Root(IVariable variable) {
      while (aliases.TryGetValue(variable, out var next) && next != variable) {
        cancellationCheck?.Invoke();
        variable = next;
      }
      return variable;
    }
    foreach (var clause in requires) {
      cancellationCheck?.Invoke();
      if (clause.Resolved is BinaryExpr { Op: BinaryExpr.Opcode.Eq } equality &&
          equality.E0.Resolved is IdentifierExpr left && equality.E1.Resolved is IdentifierExpr right &&
          aliases.ContainsKey(left.Var) && aliases.ContainsKey(right.Var)) {
        aliases[Root(left.Var)] = Root(right.Var);
      }
    }
    var substitutions = aliases.ToDictionary(pair => pair.Key, pair => (Expression)Id(Root(pair.Key), target.Origin));
    foreach (var clause in requires) {
      cancellationCheck?.Invoke();
      if (clause.Resolved is BinaryExpr { Op: BinaryExpr.Opcode.Eq } equality &&
          equality.E0.Resolved is IdentifierExpr identifier && !identifier.Type.IsRefType &&
          IsValue(equality.E1, cancellationCheck)) {
        if (!substitutions.TryAdd(identifier.Var, equality.E1)) { return false; }
      }
    }
    Expression Normalize(Expression expression) => new ContractReductionSubstituter(null, substitutions,
      new Dictionary<TypeParameter, Type>(), null, program.SystemModuleManager, cancellationCheck)
      .Substitute(expression).Resolved;
    var distinct = new HashSet<(IVariable, IVariable)>();
    foreach (var clause in requires) {
      cancellationCheck?.Invoke();
      if (Normalize(clause) is BinaryExpr { Op: BinaryExpr.Opcode.Neq } inequality &&
          inequality.E0.Resolved is IdentifierExpr left && inequality.E1.Resolved is IdentifierExpr right) {
        distinct.Add((Root(left.Var), Root(right.Var)));
        distinct.Add((Root(right.Var), Root(left.Var)));
      }
    }
    var entry = new Dictionary<(IVariable, Field), Expression>();
    foreach (var clause in requires) {
      cancellationCheck?.Invoke();
      if (Normalize(clause) is BinaryExpr { Op: BinaryExpr.Opcode.Eq } equality &&
          equality.E0.Resolved is MemberSelectExpr { Obj.Resolved: IdentifierExpr reference, Member: Field field } &&
          reference.Type.IsRefType && ContractHeapReductionContext.IsHeapIndependent(equality.E1, cancellationCheck)) {
        var key = (Root(reference.Var), field);
        // Each retained fact is itself an original requires; later duplicate
        // requirements remain native premises and need no host equality decision.
        entry.TryAdd(key, equality.E1);
      }
    }
    var current = new Dictionary<(IVariable, Field), Expression>(entry);
    var revealed = new HashSet<Function>();
    var invalidations = 0;
    foreach (var statement in originals.Take(originals.Length - 1)) {
      cancellationCheck?.Invoke();
      if (statement is HideRevealStmt { Wildcard: false, LabeledAsserts.Count: 0 } reveal) {
        foreach (var function in reveal.OffsetMembers.OfType<Function>()) {
          cancellationCheck?.Invoke();
          if (reveal.Kind == "reveal") { revealed.Add(function); } else { revealed.Remove(function); }
        }
        // Constants and hide directives alter the proof context as well. Leave
        // these unmodeled cases to the complete original native translation.
        if (reveal.Kind != "reveal" || reveal.OffsetMembers.Any(member => member is not Function)) { return false; }
        continue;
      }
      IEnumerable<Statement> assignments = statement is AssignStatement { ResolvedStatements: { } resolved } ? resolved : [statement];
      foreach (var assignment in assignments) {
        cancellationCheck?.Invoke();
        if (assignment is not SingleAssignStmt { Rhs: ExprRhs rhs } write ||
            Normalize(write.Lhs) is not MemberSelectExpr { Obj.Resolved: IdentifierExpr receiver, Member: Field { IsMutable: true } field } ||
            !receiver.Type.IsRefType) {
          log.WriteLine("Heap reduction residual: unsupported_statement."); return false;
        }
        var identity = Root(receiver.Var);
        // A different source variable may denote the same object. Preserve only
        // cells whose receiver is proved distinct, or whose field is different.
        foreach (var key in current.Keys.Where(key => key.Item2 == field && !distinct.Contains((identity, key.Item1))).ToList()) {
          cancellationCheck?.Invoke();
          current.Remove(key); invalidations++;
        }
        var value = Normalize(rhs.Expr);
        if (ContractHeapReductionContext.IsHeapIndependent(value, cancellationCheck)) { current[(identity, field)] = value; }
      }
    }
    if (entry.Count == 0 && !Nodes(target.Expr, cancellationCheck).OfType<FunctionCallExpr>()
          .Any(call => call.Function.ReadsHeap)) { return false; }
    var context = new ContractHeapReductionContext(Facts(entry), Facts(current), revealed, cancellationCheck);
    var owner = method.EnclosingClass.EnclosingModuleDefinition;
    var reducer = new ContractExpressionReducer(program.Options, owner, program.SystemModuleManager,
      program.ModuleSigs[owner].VisibilityScope);
    var reduction = reducer.ReduceWithHeapForNativeProofComposition(target.Expr, context, substitutions, budget,
      cancellationCheck);
    var stats = reduction.HeapReduction;
    log.WriteLine("Heap reduction: decision=" + reduction.Decision + ", residual=" + reduction.ResidualKind +
      ", entryReads=" + (stats?.EntryReads ?? 0) + ", currentReads=" + (stats?.CurrentReads ?? 0) +
      ", statefulInlines=" + (stats?.StatefulInlines ?? 0) + ", aliasInvalidations=" + invalidations +
      ", quantifierInstances=" + reduction.QuantifierInstancesUsed + "/" + reduction.QuantifierInstanceLimit +
      ", inlineDepth=" + reduction.InlineDepthLimit + ", nodes=" + reduction.ReducedExpressionNodeCount +
      ", expansionNodes=" + reduction.ExpressionExpansionNodeCount + ", exhaustion=" + string.Join(",", reduction.ExhaustionReasons) +
      ", unsupported=" + string.Join(",", stats?.ResidualReasons ?? []));
    log.WriteLine("Heap reduction residual expression: " +
      ContractReductionTraversal.PrintExpression(program.Options, reduction.ReducedExpression, cancellationCheck));
    var added = new List<Statement>();
    foreach (var obligation in reduction.ProofObligations) {
      cancellationCheck?.Invoke();
      var markerName = obligation.Kind switch {
        ContractReductionProofKind.Witness => "contract_reduction_witness",
        ContractReductionProofKind.Prerequisite => "contract_reduction_prerequisite",
        ContractReductionProofKind.Predicate => "contract_reduction_predicate",
        _ => throw new ArgumentOutOfRangeException()
      };
      var proofMarker = new StringLiteralExpr(target.Origin, markerName, false) { Type = new SeqType(Type.Char) };
      added.Add(new AssertStmt(target.Origin, obligation.Expression, null, new Attributes("error", [proofMarker], null)));
    }
    var equivalence = new BinaryExpr(target.Origin, BinaryExpr.Opcode.Iff,
      new ContractReductionCloner(cancellationCheck).CloneExpr(target.Expr), reduction.ReducedExpression) {
      ResolvedOp = BinaryExpr.ResolvedOpcode.Iff,
      Type = Type.Bool
    };
    var marker = new StringLiteralExpr(target.Origin, EquivalenceMarker, false) { Type = new SeqType(Type.Char) };
    var step = new AssertStmt(target.Origin, equivalence, null, new Attributes("error", [marker], null));
    added.Add(step);
    cancellationCheck?.Invoke();
    body.Body.InsertRange(body.Body.Count - 1, added);
    if (!originals.SequenceEqual(body.Body.Where(statement => !added.Contains(statement))) ||
        !ReferenceEquals(target.Expr, originalExpression) || !ReferenceEquals(target.Origin, originalOrigin) ||
        !ReferenceEquals(target.Attributes, originalAttributes)) {
      throw new InvalidOperationException("Heap reduction modified an original query statement.");
    }
    log.WriteLine("Heap reduction inventory: originalCommands=" + originals.Length +
      ", retainedCommands=" + originals.Length + ", originalTargetAssertions=1, retainedTargetAssertions=1, addedCheckedEquivalences=1" +
      ", addedCheckedProofSteps=" + reduction.ProofObligations.Count + ".");
    return true;
  }

  private static IEnumerable<ContractHeapReductionFact> Facts(Dictionary<(IVariable, Field), Expression> cells) =>
    cells.Select(pair => new ContractHeapReductionFact(pair.Key.Item1, pair.Key.Item2, pair.Value));

  private static IdentifierExpr Id(IVariable variable, IOrigin origin) => new(origin, variable.Name) { Var = variable, Type = variable.Type };

  private static IEnumerable<Expression> Conjuncts(Expression expression, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    if (expression.Resolved is BinaryExpr { Op: BinaryExpr.Opcode.And } conjunction) {
      foreach (var child in Conjuncts(conjunction.E0, cancellationCheck)
                 .Concat(Conjuncts(conjunction.E1, cancellationCheck))) {
        cancellationCheck?.Invoke();
        yield return child;
      }
    } else { yield return expression; }
  }

  private static IEnumerable<Expression> Nodes(Expression expression, Action? cancellationCheck) {
    var pending = new Stack<Expression>();
    pending.Push(expression);
    while (pending.Count > 0) {
      cancellationCheck?.Invoke();
      var next = pending.Pop();
      yield return next;
      foreach (var child in next.SubExpressions) { pending.Push(child); }
    }
  }

  private static bool IsValue(Expression expression, Action? cancellationCheck) {
    cancellationCheck?.Invoke();
    return expression.Resolved switch {
      LiteralExpr => true,
      DatatypeValue or DisplayExpression or MapDisplayExpr or ConversionExpr =>
        expression.Resolved.SubExpressions.All(child => IsValue(child, cancellationCheck)),
      _ => false
    };
  }
}
