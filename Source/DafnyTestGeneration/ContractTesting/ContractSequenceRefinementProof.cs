#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Function = Microsoft.Boogie.Function;
using Program = Microsoft.Boogie.Program;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Identifies an unchanged original native assertion in a selected implementation.</summary>
public sealed record ContractNativeAssertion(string Id, string Source, int Line, int Column, string PredicateHash);

/// <summary>Records native command preservation and checked proof steps, not solver VC counts.</summary>
public sealed record ContractSequenceImplementationInventory(string Implementation,
  int OriginalCommands, int RetainedCommands, IReadOnlyList<ContractNativeAssertion> OriginalAssertions,
  int RetainedAssertions, IReadOnlyList<string> AddedAssertionIds, int UnsupportedAssertions, int ExhaustedAssertions);

/// <summary>Describes the bounded addition of checked sequence-membership assertions to original native code.</summary>
public sealed record ContractSequenceRefinementResult(bool Preserved,
  IReadOnlyList<ContractSequenceImplementationInventory> Implementations, string? Failure = null);

/// <summary>Adds checked memberships for original sequence subterms without replacing any original command.</summary>
public static class ContractSequenceRefinementProof {
  private static readonly string[] PreludeNames = ["$Is", "$IsBox", "TSeq", "Seq#Empty", "Seq#Build", "Seq#Append", "Lit"];

  /// <summary>Inserts only native assertions and inventories every retained original command and assertion.</summary>
  public static ContractSequenceRefinementResult Apply(Program program, IReadOnlyList<Implementation> implementations,
    CancellationToken cancellationToken, long? deadlineTimestamp = null) {
    CheckDeadline();
    var prelude = Prelude(program);
    var inventory = new List<ContractSequenceImplementationInventory>();
    var remaining = (int)ContractReductionBudget.DefaultExpressionNodeLimit;
    foreach (var implementation in implementations) {
      CheckDeadline();
      var originalBlocks = implementation.Blocks.ToList();
      var original = originalBlocks.Select(block => new BlockSnapshot(block, block.Cmds.ToList(), block.TransferCmd)).ToList();
      var assertions = new List<ContractNativeAssertion>();
      var assertionStates = new List<(AssertCmd Command, Expr Predicate, TokenSnapshot Token,
        IReadOnlyList<AttributeSnapshot> Attributes, string Hash)>();
      var additions = new List<string>();
      var unsupported = 0;
      var exhausted = 0;
      var inserted = new HashSet<Cmd>(ReferenceEqualityComparer.Instance);
      foreach (var (block, commands, _) in original) {
        var rewritten = new List<Cmd>();
        for (var index = 0; index < commands.Count; index++) {
          CheckDeadline();
          var command = commands[index];
          if (command is AssertCmd assertion) {
            var id = implementation.Name + "/" + originalBlocks.IndexOf(block) + "/" + index;
            var hash = ContractHarnessBuilder.Hash(assertion.Expr.ToString());
            assertions.Add(new(id, assertion.tok.filename ?? "", assertion.tok.line, assertion.tok.col, hash));
            assertionStates.Add((assertion, assertion.Expr, TokenSnapshot.Capture(assertion.tok),
              AttributeSnapshots(assertion.Attributes), hash));
            if (prelude != null && Membership(assertion.Expr, prelude) is { } membership) {
              var steps = PrepareSteps(membership, prelude, ref remaining, CheckDeadline, out var status);
              if (status == Preparation.Unsupported) { unsupported++; }
              if (status == Preparation.Exhausted) { exhausted++; }
              for (var step = 0; step < steps.Count; step++) {
                // A plain AssertCmd cannot introduce an assumed fact without also requiring its proof.
                var added = new AssertCmd(assertion.tok, steps[step]);
                rewritten.Add(added);
                inserted.Add(added);
                additions.Add(id + "/sequence-step-" + step);
              }
            }
          }
          rewritten.Add(command);
        }
        block.Cmds = rewritten;
      }

      CheckDeadline();
      var keptBlocks = originalBlocks.SequenceEqual(implementation.Blocks, ReferenceEqualityComparer.Instance);
      var retainedCommands = 0;
      foreach (var (block, commands, transfer) in original) {
        var kept = block.Cmds.Where(command => !inserted.Contains(command)).ToList();
        if (!commands.SequenceEqual(kept, ReferenceEqualityComparer.Instance) || !ReferenceEquals(transfer, block.TransferCmd)) {
          return new(false, inventory, "Original native command order or transfer changed in " + implementation.Name);
        }
        retainedCommands += kept.Count;
      }
      var retainedAssertions = assertionStates.Count(state =>
        ReferenceEquals(state.Command.Expr, state.Predicate) && state.Token.Retained(state.Command.tok) &&
        AttributesRetained(state.Command.Attributes, state.Attributes) &&
        ContractHarnessBuilder.Hash(state.Command.Expr.ToString()) == state.Hash);
      var afterAssertions = implementation.Blocks.SelectMany(block => block.Cmds).OfType<AssertCmd>().Count();
      if (!keptBlocks || retainedAssertions != assertions.Count || afterAssertions != assertions.Count + additions.Count) {
        return new(false, inventory, "Original native assertion coverage changed in " + implementation.Name);
      }
      inventory.Add(new(implementation.Name, original.Sum(block => block.Commands.Count), retainedCommands,
        assertions, retainedAssertions, additions, unsupported, exhausted));
    }
    CheckDeadline();
    return new(true, inventory);

    void CheckDeadline() => ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
  }

  private sealed record BlockSnapshot(Block Block, List<Cmd> Commands, TransferCmd Transfer);
  private sealed record TokenSnapshot(Microsoft.Boogie.IToken Token, string? Source, int Line, int Column) {
    public static TokenSnapshot Capture(Microsoft.Boogie.IToken token) => new(token, token.filename, token.line, token.col);
    public bool Retained(Microsoft.Boogie.IToken token) => ReferenceEquals(Token, token) &&
      Source == token.filename && Line == token.line && Column == token.col;
  }
  private sealed record AttributeSnapshot(QKeyValue Attribute, TokenSnapshot Token, string Key,
    object[] Parameters, string?[] Contents);
  private enum Preparation { Complete, Unsupported, Exhausted }

  private static IReadOnlyList<AttributeSnapshot> AttributeSnapshots(QKeyValue? attributes) {
    var result = new List<AttributeSnapshot>();
    for (var attribute = attributes; attribute != null; attribute = attribute.Next) {
      result.Add(new(attribute, TokenSnapshot.Capture(attribute.tok), attribute.Key,
        attribute.Params.ToArray(), attribute.Params.Select(parameter => parameter?.ToString()).ToArray()));
    }
    return result;
  }

  private static bool AttributesRetained(QKeyValue? attributes, IReadOnlyList<AttributeSnapshot> snapshots) {
    foreach (var snapshot in snapshots) {
      if (!ReferenceEquals(attributes, snapshot.Attribute) || attributes == null ||
          !snapshot.Token.Retained(attributes.tok) || attributes.Key != snapshot.Key ||
          !attributes.Params.SequenceEqual(snapshot.Parameters, ReferenceEqualityComparer.Instance) ||
          !attributes.Params.Select(parameter => parameter?.ToString()).SequenceEqual(snapshot.Contents)) {
        return false;
      }
      attributes = attributes.Next;
    }
    return attributes == null;
  }

  private static Dictionary<string, Function>? Prelude(Program program) {
    var functions = program.TopLevelDeclarations.OfType<Function>().GroupBy(function => function.Name)
      .ToDictionary(group => group.Key, group => group.ToList(), StringComparer.Ordinal);
    var result = new Dictionary<string, Function>(StringComparer.Ordinal);
    foreach (var name in PreludeNames) {
      if (!functions.TryGetValue(name, out var matches) || matches.Count != 1 || !matches[0].AlwaysRevealed) { return null; }
      result.Add(name, matches[0]);
    }
    return result;
  }

  private static bool Calls(Expr expression, string name, IReadOnlyDictionary<string, Function> prelude) =>
    expression is NAryExpr { Fun: FunctionCall call } &&
    (call.Func != null ? ReferenceEquals(call.Func, prelude[name]) : call.FunctionName == prelude[name].Name);

  private static NAryExpr? Membership(Expr expression, IReadOnlyDictionary<string, Function> prelude) {
    // Native literal/coercion wrappers are inspected, never stripped from the original assertion.
    var remaining = ContractReductionBudget.DefaultExpressionNodeLimit;
    while (expression is NAryExpr { Args.Count: 1 } wrapper &&
           (wrapper.Fun is TypeCoercion || Calls(wrapper, "Lit", prelude))) {
      if (remaining-- == 0) { return null; }
      expression = wrapper.Args[0];
    }
    return Calls(expression, "$Is", prelude) && expression is NAryExpr { Args.Count: 2 } membership &&
      Calls(membership.Args[1], "TSeq", prelude) && membership.Args[1] is NAryExpr { Args.Count: 1 }
      ? membership : null;
  }

  private static IReadOnlyList<Expr> PrepareSteps(NAryExpr membership, IReadOnlyDictionary<string, Function> prelude,
    ref int remaining, System.Action checkDeadline, out Preparation status) {
    var steps = new List<Expr>();
    var target = membership.Args[1];
    var elementType = ((NAryExpr)target).Args[0];
    var pending = new Stack<(Expr Term, bool Expanded)>();
    var finished = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
    pending.Push((membership.Args[0], false));
    while (pending.TryPop(out var item)) {
      checkDeadline();
      if (!TryReserve(ref remaining)) { status = Preparation.Exhausted; return []; }
      if (finished.Contains(item.Term)) { continue; }
      if (item.Term is not NAryExpr term) { status = Preparation.Unsupported; return []; }
      var wrapper = term.Args.Count == 1 && (term.Fun is TypeCoercion || Calls(term, "Lit", prelude));
      var empty = Calls(term, "Seq#Empty", prelude) && term.Args.Count == 0;
      var build = Calls(term, "Seq#Build", prelude) && term.Args.Count == 2;
      var append = Calls(term, "Seq#Append", prelude) && term.Args.Count == 2;
      if (!wrapper && !empty && !build && !append) { status = Preparation.Unsupported; return []; }
      if (!item.Expanded) {
        pending.Push((term, true));
        if (append) { pending.Push((term.Args[1], false)); }
        if (wrapper || build || append) { pending.Push((term.Args[0], false)); }
        continue;
      }
      if (build) {
        if (!TryReserve(ref remaining)) { status = Preparation.Exhausted; return []; }
        steps.Add(Call(prelude["$IsBox"], term.Args[1], elementType));
      }
      if (!TryReserve(ref remaining)) { status = Preparation.Exhausted; return []; }
      steps.Add(Call(prelude["$Is"], term, target));
      finished.Add(term);
    }
    status = Preparation.Complete;
    return steps;
  }

  // Every visited term and emitted step consumes one unit of the shared node budget.
  private static bool TryReserve(ref int remaining) {
    if (remaining <= 0) { return false; }
    remaining--;
    return true;
  }

  private static Expr Call(Function function, params Expr[] arguments) =>
    new NAryExpr(arguments[0].tok, new FunctionCall(function), arguments.ToList()) { Type = Type.Bool };
}
