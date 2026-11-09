#nullable enable
using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text.Json;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public static partial class DefinitionAnalysis {
  /// <summary>Lift a translation's lambdas once, as one-shot verification does; see <see cref="ModularProofKeys"/>.</summary>
  public static void LiftLambdasOnce(DafnyOptions options, Bpl.Program program) =>
    ModularProofKeys.LiftLambdas(options, program);

  /// <summary>
  /// Orders a translation the engine will verify for the stable seed (see <see cref="ModularProofKeys.OrderBySeed"/>);
  /// does nothing without <see cref="DafnyOptions.StableRandomSeed"/>. Call it before the engine prepares tasks.
  /// </summary>
  public static void ApplyStableSeededOrder(DafnyOptions options, Bpl.Program program) {
    if (options.StableRandomSeed is { } seed) {
      ModularProofKeys.OrderBySeed(options, program, seed);
    }
  }

  /// <summary>
  /// Per-implementation proof-input keys over the lambda-lifted Boogie program that the session hands to the
  /// engine. A key covers the implementation, its own procedure, every called procedure and an ordered
  /// superset of every split's pruned solver declarations (<see cref="Bpl.Pruner.GetLiveDeclarations"/>).
  /// </summary>
  /// <remarks>
  /// Superset argument (Boogie 3.5.5). A split's solver declarations are <c>Pruner.GetLiveDeclarations</c> of
  /// its blocks: every type, global and synonym, plus the constants, functions and axioms reachable over the
  /// declaration graph from the blocks and the <c>{:keep}</c> roots, except that the axioms marked CanHide of a
  /// function hidden at every assertion are cut. Reachability is monotone in its roots and in the revealed set.
  /// The roots used here contain every command of the implementation, the expressions that preparation adds
  /// (own and called contracts, where clauses of formals, locals and globals), and a leading assertion under
  /// the initial all-revealed state, so no CanHide edge is cut. Equal content of that superset, as a multiset,
  /// then determines every split's declaration set, because the sub-graph reachable from any subset of the roots,
  /// and its edges, are functions of the content of the reachable declarations.
  ///
  /// The key is order-insensitive (live and callee lists enter as sorted multisets). Under a stable seed
  /// (<see cref="DafnyOptions.StableRandomSeed"/>, a non-zero <c>/randomSeed</c> in <c>--boogie</c>) the engine
  /// receives the solver declarations in an order that depends only on their own content and the seed
  /// (<see cref="OrderBySeed"/>), so an equal key, seed, options and toolchain give every split byte-identical SMT
  /// text. Without a seed, Boogie orders by <c>ContentHash</c>, which ignores names, and breaks its ties in program
  /// order; an equal key then means a logically identical formula set whose SMT text, and solver time, can differ.
  /// Boogie's own seeded randomization (an implementation's <c>{:random_seed}</c>, <c>/randomizeVcIterations</c>)
  /// shuffles the whole pruned list and is never keyed. Names from translation-wide counters other than lifted
  /// lambdas (Dafny's <c>$let#N</c>) are part of the key, so renumbering them misses.
  ///
  /// The dependency graph is computed on the program the engine will verify. Boogie's axiom visitor
  /// rewrites <see cref="Bpl.Expr.pos"/> of the expressions it visits using their previous values, so a second
  /// graph computation over the same objects can differ from the first. Only quantifier positions are read
  /// back (<c>AxiomVisitor</c>), so they are restored afterwards and the engine's own computation matches a
  /// one-shot run.
  /// </remarks>
  internal static class ModularProofKeys {
    // 3: the stable seeded order makes an equal key predict identical seeded SMT; Boogie-seeded implementations
    // are unsupported.
    internal const int SchemaVersion = 3;

    /// <summary>One implementation's solver-input content, or the reason it has none.</summary>
    internal sealed record ImplementationKey(Bpl.Implementation Implementation, string? Content, string? Unsupported,
      IReadOnlyList<Bpl.Declaration> Closure, IReadOnlyList<Bpl.Declaration> Live);

    internal sealed class ProgramKeys {
      public string? Unsupported { get; init; }
      public IReadOnlyDictionary<Bpl.Implementation, ImplementationKey> Implementations { get; init; } =
        new Dictionary<Bpl.Implementation, ImplementationKey>();
      public int LambdaFunctions { get; init; }
    }

    private sealed class LiftedLambdas(IReadOnlyList<Bpl.Function> functions) {
      public IReadOnlyList<Bpl.Function> Functions { get; } = functions;
    }

    private static readonly ConditionalWeakTable<Bpl.Program, LiftedLambdas> Lifted = new();
    private static readonly ConditionalWeakTable<Bpl.Program, ProgramKeys> Computed = new();
    private static readonly ConditionalWeakTable<Bpl.Program, string> Ordered = new();

    internal static bool IsLifted(Bpl.Program program) => Lifted.TryGetValue(program, out _);

    /// <summary>The keys already computed for this program object, if any.</summary>
    internal static ProgramKeys? Existing(Bpl.Program program) => Computed.TryGetValue(program, out var keys) ? keys : null;

    /// <summary>
    /// Lifts lambdas once per program the way the one-shot CLI (VerifySnapshots 0) does. Later calls do nothing,
    /// so the session's pre-engine lift and the key computation share one lifted program. With snapshots on, the
    /// lifted functions get the constant checksum Boogie would have given them.
    /// </summary>
    internal static void LiftLambdas(DafnyOptions options, Bpl.Program program) {
      lock (program) {
        if (Lifted.TryGetValue(program, out _)) {
          return;
        }
        var lifting = new DafnyOptions(options, useNullWriters: true) { VerifySnapshots = 0 };
        // The engine would reject an ill-formed program before verification. Lifting runs first and prints to a
        // null writer, so reject here with the engine's message instead of handing on an already lifted program.
        var resolutionErrors = program.Resolve(lifting);
        if (resolutionErrors != 0) {
          throw new ArgumentException($"Boogie program had {resolutionErrors} resolution errors: ");
        }
        var typeErrors = program.Typecheck(lifting);
        if (typeErrors != 0) {
          throw new ArgumentException($"Boogie program had {typeErrors} type errors: ");
        }
        Bpl.LambdaHelper.Desugar(lifting, program, out var axioms, out var functions);
        foreach (var function in functions) {
          if (options.VerifySnapshots > 0 && function.Checksum == null) {
            function.AddAttribute("checksum", "lambda expression");
          }
          program.AddTopLevelDeclaration(function);
        }
        foreach (var axiom in axioms) {
          program.AddTopLevelDeclaration(axiom);
        }
        Lifted.Add(program, new LiftedLambdas(functions.ToList()));
      }
    }

    /// <summary>Lifts the program if needed and computes its implementation keys once.</summary>
    internal static ProgramKeys Compute(DafnyOptions options, Bpl.Program program) {
      lock (program) {
        if (Computed.TryGetValue(program, out var existing)) {
          return existing;
        }
        ProgramKeys result;
        if (!options.ExpandLambdas) {
          result = new ProgramKeys { Unsupported = "lambda expansion is disabled" };
        } else {
          try {
            LiftLambdas(options, program);
            result = ComputeLifted(options, program);
          } catch (ArgumentException exception) {
            // The engine reports the same ill-formed program again when it prepares tasks.
            result = new ProgramKeys { Unsupported = exception.Message };
          }
        }
        Computed.AddOrUpdate(program, result);
        return result;
      }
    }

    /// <summary>The final per-implementation key, binding toolchain and effective options.</summary>
    internal static string Key(string toolchain, string optionsHash, string content) =>
      ProofHash(JsonSerializer.Serialize(new { Schema = SchemaVersion, toolchain, optionsHash, content }));

    /// <summary>
    /// Puts the declarations that Boogie hands to the solver in list order (<c>Checker.Setup</c>: type
    /// constructors, constants, functions, axioms) into an order that depends only on their own content and the
    /// seed: ascending SHA-256 of the seed and the key, then the key. The key is the declaration's kind and
    /// position-free hash (lifted lambdas named by content, see <see cref="DeclarationHasher"/>), here also blind to
    /// the names of bound variables, let-bound names, function formals and type parameters: Boogie's lambda lifter
    /// shares one function between alpha-equivalent lambdas and keeps the bound names of the first one it meets,
    /// which can be another declaration's, while Dafny's normalized solver names never show them. An equal modular
    /// key (exact text) therefore implies equal order keys. The declarations are written back into their own slots
    /// of <c>TopLevelDeclarations</c>, which Boogie filters into every split's pruned list without reordering at
    /// seed 0 with <c>NormalizeDeclarationOrder</c> off. A split's solver order is then a function of its live set
    /// and the seed: adding, removing or moving an unrelated declaration does not change it. Ties keep program order;
    /// tied declarations differ at most in those local names, so they give the same solver text, except content-equal
    /// lifted lambdas, which also make the program's keys unsupported.
    ///
    /// Every other declaration keeps its place: procedures and implementations, type synonyms and global variables
    /// (their order is the order of the where-clause assumptions in every VC, not solver-list order). So does the
    /// leading run up to the last declaration where a program-order visit first meets a basic type:
    /// <c>Checker.Target</c> numbers the basic types (type tags 0-2) in that order over the whole program, and moving
    /// another declaration to the front could renumber them with unrelated edits. For Dafny that run is the start of
    /// the prelude.
    ///
    /// Lambdas are lifted first, as the session does, so the engine adds no declaration afterwards. An implementation
    /// with its own <c>{:random_seed N}</c> keeps Boogie's seeded shuffle and namer; it gets <c>{:smt_option}</c>
    /// entries for N, which Boogie sends after the global stable seed options, so that Z3 also keeps N.
    /// </summary>
    internal static void OrderBySeed(DafnyOptions options, Bpl.Program program, int seed) {
      lock (program) {
        var seedText = seed.ToString(CultureInfo.InvariantCulture);
        if (Ordered.TryGetValue(program, out var done) && done == seedText) {
          return;
        }
        if (options.ExpandLambdas) {
          try {
            LiftLambdas(options, program);
          } catch (ArgumentException) {
            // The engine reports the ill-formed program when it prepares tasks.
            return;
          }
        }
        var declarations = program.TopLevelDeclarations.ToList();
        var slots = Enumerable.Range(0, declarations.Count).Skip(BasicTypePrefix(declarations))
          .Where(index => declarations[index] is Bpl.TypeCtorDecl or Bpl.Constant or Bpl.Function or Bpl.Axiom).ToList();
        var hasher = new DeclarationHasher(options,
          Lifted.TryGetValue(program, out var lifted) ? lifted.Functions : Array.Empty<Bpl.Function>(),
          program.TopLevelDeclarations.OfType<Bpl.NamedDeclaration>()
            .Select(declaration => Bpl.TokenTextWriter.SanitizeIdentifier(declaration.Name)).ToHashSet(StringComparer.Ordinal));
        var ordered = slots.Select(index => {
          var key = declarations[index].GetType().Name + ":" + hasher.Hash(declarations[index]);
          return (Declaration: declarations[index], Key: key, Order: ProofHash(seedText + "\0" + key));
        }).OrderBy(entry => entry.Order, StringComparer.Ordinal).ThenBy(entry => entry.Key, StringComparer.Ordinal)
          .Select(entry => entry.Declaration).ToList();
        for (var index = 0; index < slots.Count; index++) {
          declarations[slots[index]] = ordered[index];
        }
        program.TopLevelDeclarations = declarations;
        foreach (var implementation in program.Implementations) {
          if (implementation.RandomSeed is { } own) {
            foreach (var name in new[] { "smt.random_seed", "sat.random_seed" }) {
              if (!implementation.GetExtraSMTOptions().ContainsKey(name)) {
                // One attribute per option: AddAttribute would append to an existing smt_option.
                implementation.Attributes = new Bpl.QKeyValue(implementation.tok, "smt_option",
                  new List<object> { name, own.ToString(CultureInfo.InvariantCulture) }, implementation.Attributes);
              }
            }
          }
        }
        Ordered.AddOrUpdate(program, seedText);
      }
    }

    /// <summary>
    /// One past the last declaration at which a program-order visit, as <c>Checker.Target</c>'s
    /// <see cref="Bpl.BasicTypeVisitor"/> makes it (other implementations excluded), first meets a basic type.
    /// </summary>
    private static int BasicTypePrefix(IReadOnlyList<Bpl.Declaration> declarations) {
      var seen = new HashSet<Bpl.Type>();
      var end = 0;
      for (var index = 0; index < declarations.Count; index++) {
        if (declarations[index] is Bpl.Implementation) {
          continue;
        }
        foreach (var type in new Bpl.BasicTypeVisitor(declarations[index], _ => true).GetBasicTypes()) {
          if (seen.Add(type)) {
            end = index + 1;
          }
        }
      }
      return end;
    }

    private static ProgramKeys ComputeLifted(DafnyOptions options, Bpl.Program program) {
      var lambdas = Lifted.TryGetValue(program, out var lifted) ? lifted.Functions : Array.Empty<Bpl.Function>();
      var hasher = new DeclarationHasher(options, lambdas);
      if (hasher.Unsupported != null) {
        return new ProgramKeys { Unsupported = hasher.Unsupported, LambdaFunctions = lambdas.Count };
      }
      var procedures = program.TopLevelDeclarations.OfType<Bpl.Procedure>()
        .GroupBy(procedure => procedure.Name, StringComparer.Ordinal)
        .ToDictionary(group => group.Key, group => group.ToList(), StringComparer.Ordinal);
      var inlined = program.TopLevelDeclarations.OfType<Bpl.Implementation>()
        .Where(implementation => HasInlineAttribute(implementation.Attributes))
        .Select(implementation => implementation.Name)
        .Concat(procedures.Values.SelectMany(group => group).Where(procedure => HasInlineAttribute(procedure.Attributes))
          .Select(procedure => procedure.Name))
        .ToHashSet(StringComparer.Ordinal);
      var globalWheres = program.TopLevelDeclarations.OfType<Bpl.GlobalVariable>()
        .Select(variable => variable.TypedIdent.WhereExpr).Where(where => where != null).ToList();

      var quantifiers = new QuantifierPositions();
      foreach (var axiom in program.TopLevelDeclarations.OfType<Bpl.Axiom>()) {
        quantifiers.Visit(axiom);
      }
      var previous = program.DeclarationDependencies;
      var keys = new Dictionary<Bpl.Implementation, ImplementationKey>();
      try {
        program.DeclarationDependencies = Bpl.Pruner.ComputeDeclarationDependencies(options, program);
        foreach (var implementation in program.TopLevelDeclarations.OfType<Bpl.Implementation>()) {
          keys[implementation] = ImplementationContent(options, program, implementation, procedures, inlined,
            globalWheres, hasher);
        }
      }
      finally {
        program.DeclarationDependencies = previous;
        quantifiers.Restore();
      }
      return new ProgramKeys { Implementations = keys, LambdaFunctions = lambdas.Count };
    }

    private static ImplementationKey ImplementationContent(DafnyOptions options, Bpl.Program program,
      Bpl.Implementation implementation, IReadOnlyDictionary<string, List<Bpl.Procedure>> procedures,
      IReadOnlySet<string> inlined, IReadOnlyList<Bpl.Expr> globalWheres, DeclarationHasher hasher) {
      ImplementationKey Unsupported(string reason) =>
        new(implementation, null, reason, Array.Empty<Bpl.Declaration>(), Array.Empty<Bpl.Declaration>());
      Bpl.Procedure? Lookup(string name) =>
        procedures.TryGetValue(name, out var matches) && matches.Count == 1 ? matches[0] : null;

      var own = Lookup(implementation.Name);
      if (own == null || implementation.Proc != null && !ReferenceEquals(implementation.Proc, own)) {
        return Unsupported("the implementation's procedure is missing or ambiguous");
      }
      if (implementation.RandomSeed != null) {
        // Boogie shuffles the whole pruned list for this implementation (see the remarks).
        return Unsupported("the implementation sets its own Boogie random seed");
      }
      var callees = new SortedDictionary<string, Bpl.Procedure>(StringComparer.Ordinal);
      string? calleeFailure = null;
      void AddCallee(Bpl.Procedure? resolved, string name) {
        var procedure = Lookup(name);
        if (procedure == null || resolved != null && !ReferenceEquals(resolved, procedure)) {
          calleeFailure ??= "a called procedure is missing or ambiguous: " + name;
        } else if (inlined.Contains(name)) {
          // Boogie inlines the callee body into this implementation before verification.
          calleeFailure ??= "a called procedure is inlined: " + name;
        } else {
          callees[name] = procedure;
        }
      }
      var roots = new List<Bpl.Cmd> { new Bpl.AssertCmd(Bpl.Token.NoToken, Bpl.Expr.True) };
      void VisitCommands(IEnumerable<Bpl.Cmd> commands) {
        foreach (var command in commands) {
          switch (command) {
            case Bpl.CallCmd call:
              AddCallee(call.Proc, call.callee);
              break;
            case Bpl.ParCallCmd parallel:
              foreach (var call in parallel.CallCmds) {
                AddCallee(call.Proc, call.callee);
              }
              break;
            case Bpl.StateCmd state:
              VisitCommands(state.Cmds);
              break;
            case Bpl.SugaredCmd other:
              // Other desugared commands are not produced by Dafny; their desugaring is not covered here.
              calleeFailure ??= "an unsupported command: " + other.GetType().Name;
              break;
          }
        }
      }
      foreach (var block in implementation.Blocks) {
        VisitCommands(block.Cmds);
        // Push and pop only scope hide/reveal states, which the leading assertion already makes all-revealed.
        // Flattened blocks could pop an empty scope stack, so they are left out.
        roots.AddRange(block.Cmds.Where(command => command is not Bpl.ChangeScope));
        if (block.TransferCmd is Bpl.ReturnExprCmd returnExpression) {
          roots.Add(new Bpl.AssumeCmd(Bpl.Token.NoToken, returnExpression.Expr));
        }
      }
      if (calleeFailure != null) {
        return Unsupported(calleeFailure);
      }
      void Assume(Bpl.Expr? expression) {
        if (expression != null) {
          roots.Add(new Bpl.AssumeCmd(Bpl.Token.NoToken, expression));
        }
      }
      void AssumeContract(Bpl.Procedure procedure) {
        foreach (var requires in procedure.Requires) {
          Assume(requires.Condition);
        }
        foreach (var ensures in procedure.Ensures) {
          Assume(ensures.Condition);
        }
        foreach (var formal in procedure.InParams.Concat(procedure.OutParams)) {
          Assume(formal.TypedIdent.WhereExpr);
        }
      }
      AssumeContract(own);
      foreach (var callee in callees.Values) {
        AssumeContract(callee);
      }
      foreach (var variable in implementation.InParams.Concat(implementation.OutParams).Concat(implementation.LocVars)) {
        Assume(variable.TypedIdent.WhereExpr);
      }
      foreach (var where in globalWheres) {
        Assume(where);
      }
      // A fresh block list: the analysis recomputes predecessors of the blocks it is given, and the
      // implementation's own blocks must stay untouched for the engine.
      var synthetic = new Bpl.Block(Bpl.Token.NoToken, "proof-input-roots", roots, new Bpl.ReturnCmd(Bpl.Token.NoToken));
      var live = Bpl.Pruner.GetLiveDeclarations(options, program, new List<Bpl.Block> { synthetic }).LiveDeclarations
        .Where(IsSolverInput).ToList();
      // Sorted multisets: program order is not solver input identity (see the remarks).
      static IReadOnlyList<string> Sorted(IEnumerable<string> items) => items.OrderBy(item => item, StringComparer.Ordinal).ToList();
      var content = ProofHash(JsonSerializer.Serialize(new {
        Schema = SchemaVersion,
        Implementation = hasher.Hash(implementation),
        Procedure = hasher.Hash(own),
        Callees = Sorted(callees.Values.Select(callee => hasher.Hash(callee))),
        Live = Sorted(live.Select(declaration => declaration.GetType().Name + ":" + hasher.Hash(declaration)))
      }));
      var closure = new List<Bpl.Declaration> { implementation, own };
      closure.AddRange(callees.Values.Where(callee => !ReferenceEquals(callee, own)));
      closure.AddRange(live);
      return new ImplementationKey(implementation, content, null, closure, live);
    }

    /// <summary>
    /// Kinds that reach the solver through <c>Checker.Setup</c> (types, constants, functions, axioms, globals),
    /// plus type synonyms, which are never pruned and can name a type in printed text.
    /// </summary>
    internal static bool IsSolverInput(Bpl.Declaration declaration) =>
      declaration is Bpl.TypeCtorDecl or Bpl.TypeSynonymDecl or Bpl.Constant or Bpl.Function or Bpl.Axiom or
        Bpl.GlobalVariable;

    /// <summary>Records quantifier positions before the dependency graph is computed and restores them.</summary>
    private sealed class QuantifierPositions : Bpl.ReadOnlyVisitor {
      private readonly Dictionary<Bpl.QuantifierExpr, Bpl.Expr.Position> positions = new(ReferenceEqualityComparer.Instance);

      public override Bpl.Expr VisitExpr(Bpl.Expr node) {
        if (node is Bpl.QuantifierExpr quantifier) {
          positions.TryAdd(quantifier, quantifier.pos);
        }
        return base.VisitExpr(node);
      }

      public void Restore() {
        foreach (var (quantifier, position) in positions) {
          quantifier.pos = position;
        }
      }
    }

    /// <summary>
    /// Memoized position-free declaration hashes for one program. Lifted lambda functions are named by a counter
    /// that changes with unrelated edits, so every reference to one is replaced by a name derived from its
    /// content (the function with its defining axiom, its own name masked, nested lambdas named the same way).
    /// Two lambdas with equal content would get one name; the program is then unsupported.
    ///
    /// With <c>globalNames</c> (the stable seeded order), local names are also replaced, by their first occurrence:
    /// the variables bound by quantifiers, lambdas and lets, a function's formals and type parameters. A local name
    /// that is also the name of a global declaration is kept, so a global is never taken for a local.
    /// </summary>
    private sealed class DeclarationHasher {
      private readonly DafnyOptions printOptions;
      private readonly IReadOnlySet<string>? globalNames;
      private readonly Dictionary<string, Bpl.Function> lambdas = new(StringComparer.Ordinal);
      private readonly Dictionary<string, string> canonical = new(StringComparer.Ordinal);
      private readonly HashSet<string> naming = new(StringComparer.Ordinal);
      private readonly Dictionary<Bpl.Declaration, string> hashes = new(ReferenceEqualityComparer.Instance);
      public string? Unsupported { get; private set; }

      public DeclarationHasher(DafnyOptions options, IReadOnlyList<Bpl.Function> lambdaFunctions,
        IReadOnlySet<string>? globalNames = null) {
        printOptions = ProofPrintOptions(options);
        this.globalNames = globalNames;
        foreach (var function in lambdaFunctions) {
          if (!lambdas.TryAdd(Bpl.TokenTextWriter.SanitizeIdentifier(function.Name), function)) {
            Unsupported = "two lifted lambda functions have one name";
            return;
          }
        }
        foreach (var name in lambdas.Keys.ToList()) {
          Name(name);
        }
        if (Unsupported == null && canonical.Values.Distinct(StringComparer.Ordinal).Count() != canonical.Count) {
          Unsupported = "two lifted lambda functions have equal content";
        }
      }

      private string Name(string lambda) {
        if (canonical.TryGetValue(lambda, out var known)) {
          return known;
        }
        if (!naming.Add(lambda)) {
          Unsupported ??= "lifted lambda functions refer to each other cyclically";
          return "lambda@cycle";
        }
        var function = lambdas[lambda];
        var name = "lambda@" + Print(function, token =>
          token == lambda ? "lambda@self" : lambdas.ContainsKey(token) ? Name(token) : token);
        naming.Remove(lambda);
        canonical[lambda] = name;
        return name;
      }

      public string Hash(Bpl.Declaration declaration) {
        if (!hashes.TryGetValue(declaration, out var hash)) {
          hash = Print(declaration, token => canonical.TryGetValue(token, out var name) ? name : token);
          hashes[declaration] = hash;
        }
        return hash;
      }

      private string Print(Bpl.Declaration declaration, Func<string, string> rename) {
        if (globalNames == null) {
          return ProofDeclarationHash(printOptions, declaration, rename);
        }
        var locals = LocalNames.Of(declaration);
        locals.RemoveWhere(globalNames.Contains);
        var renamed = new Dictionary<string, string>(StringComparer.Ordinal);
        return ProofDeclarationHash(printOptions, declaration, token => {
          if (!locals.Contains(token)) {
            return rename(token);
          }
          if (!renamed.TryGetValue(token, out var name)) {
            name = "local@" + renamed.Count;
            renamed[token] = name;
          }
          return name;
        });
      }
    }

    /// <summary>The printed local names of a declaration (see <see cref="DeclarationHasher"/>).</summary>
    private sealed class LocalNames : Bpl.ReadOnlyVisitor {
      private readonly HashSet<string> names = new(StringComparer.Ordinal);

      public static HashSet<string> Of(Bpl.Declaration declaration) {
        var collector = new LocalNames();
        collector.Visit(declaration);
        if (declaration is Bpl.Function function) {
          foreach (var formal in function.InParams.Concat(function.OutParams)) {
            collector.Add(formal.Name);
          }
          foreach (var parameter in function.TypeParameters) {
            collector.Add(parameter.Name);
          }
        }
        // Printed in the uses clause of a function or constant.
        var definitions = declaration switch {
          Bpl.Function withAxioms => withAxioms.DefinitionAxioms,
          Bpl.Constant constant => constant.DefinitionAxioms,
          _ => Enumerable.Empty<Bpl.Axiom>()
        };
        foreach (var axiom in definitions) {
          collector.Visit(axiom);
        }
        return collector.names;
      }

      private void Add(string? name) {
        if (!string.IsNullOrEmpty(name)) {
          names.Add(Bpl.TokenTextWriter.SanitizeIdentifier(name));
        }
      }

      public override Bpl.Absy Visit(Bpl.Absy node) {
        switch (node) {
          case Bpl.BinderExpr binder:
            binder.Dummies.ForEach(variable => Add(variable.Name));
            binder.TypeParameters.ForEach(parameter => Add(parameter.Name));
            break;
          case Bpl.LetExpr let:
            let.Dummies.ForEach(variable => Add(variable.Name));
            break;
        }
        return base.Visit(node);
      }
    }
  }
}
