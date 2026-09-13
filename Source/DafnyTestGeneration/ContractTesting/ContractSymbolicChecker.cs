using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Microsoft.Dafny.Auditor;
using BoogiePipelineOutcome = Microsoft.Boogie.PipelineOutcome;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Checks original Dafny implementations and contracts without compiling or executing them.</summary>
public static class ContractSymbolicChecker {
  private sealed record VerificationRun(ContractSymbolicStatus Status, string Diagnostics);

  public static async Task<ContractSymbolicResult> CheckAsync(ContractSymbolicRequest request,
    DafnyOptions baseOptions, CancellationToken cancellationToken) {
    Validate(request);

    var discoveryReporter = Reporter(baseOptions);
    var discovery = await ContractSourceSnapshot.ParseAsync(discoveryReporter, request.Sources, cancellationToken);
    if (discoveryReporter.ErrorCount != 0) {
      return Failure(ContractSymbolicStatus.InvalidInput, "The source snapshot did not parse and resolve.",
        discoveryReporter.AllMessages.Select(message => message.Message), sourceSnapshots: SourceEvidence(request.Sources));
    }

    var entry = Select(discovery, request.Entry.Symbol);
    if (entry is not Method) {
      throw new ArgumentException("Symbolic entry checking currently requires a method entry; reachable functions are verified.");
    }
    if (IsExtern(entry)) {
      throw new ArgumentException("The selected symbolic entry must have an internal implementation.");
    }
    if (Body(entry) == null) {
      throw new ArgumentException("The selected symbolic entry has no implementation body.");
    }
    if (entry.HasVerifyFalseAttribute) {
      throw new ArgumentException("The selected symbolic entry cannot carry {:verify false}.");
    }

    var reachable = Reachable(discovery, entry, request.Entry.Scope);
    var externs = reachable.Where(IsExtern).ToHashSet();
    var checkedCallables = reachable.Where(callable => !IsExtern(callable) && Body(callable) != null &&
      !callable.HasVerifyFalseAttribute).ToHashSet();
    var checkedSymbols = checkedCallables.Select(Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToList();
    var externSymbols = externs.Select(Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToList();
    var dependencies = TrustDependencies(reachable);
    var location = Location(request.Sources, entry);
    var sourceSnapshots = SourceEvidence(request.Sources);

    var premiseReporter = Reporter(baseOptions);
    var premiseProgram = await ContractSourceSnapshot.ParseAsync(premiseReporter, request.Sources, cancellationToken);
    if (premiseReporter.ErrorCount != 0) {
      return Failure(ContractSymbolicStatus.InvalidInput, "The source snapshot did not parse and resolve.",
        premiseReporter.AllMessages.Select(message => message.Message), location, checkedSymbols, externSymbols, dependencies,
        sourceSnapshots);
    }
    var premiseEntry = Select(premiseProgram, request.Entry.Symbol);
    PreparePremiseProgram(premiseProgram, (Method)premiseEntry);
    var premise = await VerifyAsync(premiseProgram, premiseReporter, cancellationToken);
    if (premise.Status == ContractSymbolicStatus.Verified) {
      return new ContractSymbolicResult(ContractJson.SchemaVersion, ContractSymbolicStatus.InconsistentPremise,
        "The selected entry precondition is inconsistent; implementation verification would be vacuous.", location,
        checkedSymbols, externSymbols, dependencies,
        [new ContractSymbolicObligation(ContractSymbolicObligationKind.PremiseConsistency,
          ContractSymbolicStatus.InconsistentPremise, "No state satisfies the selected entry requires clauses.")],
        Diagnostics(premise.Diagnostics), sourceSnapshots);
    }
    if (premise.Status != ContractSymbolicStatus.ObligationFailed) {
      return new ContractSymbolicResult(ContractJson.SchemaVersion, premise.Status,
        "The selected entry premise consistency query did not complete.", location, checkedSymbols, externSymbols,
        dependencies, [new ContractSymbolicObligation(ContractSymbolicObligationKind.PremiseConsistency,
          premise.Status, "Could not decide whether the entry premise is consistent.")], Diagnostics(premise.Diagnostics),
        sourceSnapshots);
    }

    var reporter = Reporter(baseOptions);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, cancellationToken);
    if (reporter.ErrorCount != 0) {
      return Failure(ContractSymbolicStatus.InvalidInput, "The source snapshot did not parse and resolve.",
        reporter.AllMessages.Select(message => message.Message), location, checkedSymbols, externSymbols, dependencies,
        sourceSnapshots);
    }
    var verificationEntry = Select(program, request.Entry.Symbol);
    var verificationReachable = Reachable(program, verificationEntry, request.Entry.Scope);
    PrepareVerificationProgram(program, verificationReachable);
    var verification = await VerifyAsync(program, reporter, cancellationToken);
    var reason = verification.Status switch {
      ContractSymbolicStatus.Verified => "The selected modular implementation scope verified.",
      ContractSymbolicStatus.ObligationFailed => "One or more Dafny proof obligations failed; this is not a runtime counterexample.",
      ContractSymbolicStatus.Unknown => "The solver returned an inconclusive or resource-exhausted result.",
      ContractSymbolicStatus.Timeout => "Symbolic verification exceeded its solver deadline.",
      _ => "Symbolic verification failed before producing a proof result."
    };
    return new ContractSymbolicResult(ContractJson.SchemaVersion, verification.Status, reason, location,
      checkedSymbols, externSymbols, dependencies,
      [new ContractSymbolicObligation(ContractSymbolicObligationKind.PremiseConsistency,
          ContractSymbolicStatus.Verified, "At least one state satisfies the selected entry requires clauses."),
        new ContractSymbolicObligation(ContractSymbolicObligationKind.Implementation, verification.Status,
          "Original bodies, postconditions, frames, assertions, termination, and call preconditions in the selected scope.")],
      Diagnostics(verification.Diagnostics), sourceSnapshots);
  }

  private static void Validate(ContractSymbolicRequest request) {
    if (request.SchemaVersion != ContractJson.SchemaVersion || request.Sources == null || request.Sources.Count == 0 ||
        request.TimeoutMilliseconds <= 0 ||
        request.Entry == null || string.IsNullOrWhiteSpace(request.Entry.Symbol)) {
      throw new ArgumentException(
        "Symbolic checking requires schema version 1, source snapshots, an entry symbol, and a positive deadline.");
    }
    if (request.Dependencies is { Count: > 0 }) {
      throw new ArgumentException("Symbolic source snapshots are closed; filesystem dependencies are not accepted.");
    }
  }

  private static BatchErrorReporter Reporter(DafnyOptions baseOptions) {
    var options = new DafnyOptions(baseOptions, useNullWriters: true) {
      Compile = false,
      RunningBoogieFromCommandLine = true,
      DisallowIncludes = false,
      ProcsToCheck = ["*"]
    };
    options.Printer = new DafnyConsolePrinter(options);
    return new BatchErrorReporter(options);
  }

  private static MethodOrFunction Select(Microsoft.Dafny.Program program, string symbol) {
    var matches = AllCallables(program)
      .Where(callable => callable.FullDafnyName == symbol || callable.FullName == symbol).ToList();
    if (matches.Count != 1) {
      throw new ArgumentException($"Expected one resolved callable named '{symbol}', found {matches.Count}.");
    }
    return matches[0];
  }

  private static HashSet<MethodOrFunction> Reachable(Microsoft.Dafny.Program program, MethodOrFunction entry,
    ContractSymbolicScope scope) {
    var result = new HashSet<MethodOrFunction>();
    var pending = new Queue<MethodOrFunction>();
    var allCallables = AllCallables(program).ToList();
    pending.Enqueue(entry);
    while (pending.TryDequeue(out var callable)) {
      if (!result.Add(callable) || scope == ContractSymbolicScope.EntryImplementation) {
        continue;
      }
      var nodes = ReachabilityNodes(callable);
      foreach (var callee in nodes.Select(node => node switch {
        FunctionCallExpr call => (MethodOrFunction?)call.Function,
        CallStmt call => call.Method,
        _ => null
      }).Where(callee => callee != null)) {
        pending.Enqueue(callee!);
        foreach (var implementation in allCallables.Where(candidate => candidate.Overrides(callee!))) {
          pending.Enqueue(implementation);
        }
      }
    }
    return result;
  }

  private static IEnumerable<INode> ReachabilityNodes(MethodOrFunction callable) {
    if (!IsExtern(callable)) {
      return callable.Descendants().Prepend((INode)callable);
    }
    IEnumerable<INode> contractRoots = callable.Req.Cast<INode>()
      .Concat(callable.Ens)
      .Concat(callable.Reads.Expressions ?? []);
    if (callable is Method method) {
      contractRoots = contractRoots.Concat(method.Mod.Expressions ?? []);
    }
    return contractRoots.SelectMany(root => root.Descendants().Prepend(root));
  }

  private static void PrepareVerificationProgram(Microsoft.Dafny.Program program,
    HashSet<MethodOrFunction> reachable) {
    foreach (var callable in AllCallables(program)) {
      if (IsExtern(callable)) {
        RemoveBody(callable);
      } else if (!reachable.Contains(callable)) {
        RemoveBody(callable);
      }
    }
  }

  private static void PreparePremiseProgram(Microsoft.Dafny.Program program, Method entry) {
    foreach (var callable in AllCallables(program)) {
      if (callable != entry) {
        RemoveBody(callable);
      }
    }
    var falseExpression = Expression.CreateBoolLiteral(entry.Origin, false);
    entry.Ens.Clear();
    entry.Mod.Expressions?.Clear();
    entry.SetBody(new BlockStmt(entry.Origin, [new AssertStmt(entry.Origin, falseExpression, null, null)]));
  }

  private static async Task<VerificationRun> VerifyAsync(Microsoft.Dafny.Program program, BatchErrorReporter reporter,
    CancellationToken cancellationToken) {
    var log = new StringWriter();
    var options = program.Options;
    options.ProcessSolverOptions(reporter, Microsoft.Dafny.Token.NoToken);
    if (reporter.ErrorCount != 0) {
      return new VerificationRun(ContractSymbolicStatus.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    using var engine = Microsoft.Boogie.ExecutionEngine.CreateWithoutSharedCache(options);
    var verified = 0;
    var errors = 0;
    foreach (var (module, boogieProgram) in BoogieGenerator.Translate(program, reporter)) {
      cancellationToken.ThrowIfCancellationRequested();
      var (outcome, stats) = await DafnyMain.BoogieOnce(reporter, options, log, engine,
        "contract-symbolic", module, boogieProgram, null);
      if (stats.TimeoutCount > 0) {
        return new VerificationRun(ContractSymbolicStatus.Timeout, log.ToString());
      }
      if (stats.InconclusiveCount + stats.OutOfResourceCount + stats.OutOfMemoryCount > 0) {
        return new VerificationRun(ContractSymbolicStatus.Unknown, log.ToString());
      }
      if (stats.SolverExceptionCount > 0 || outcome is not (BoogiePipelineOutcome.Done or BoogiePipelineOutcome.VerificationCompleted)) {
        return new VerificationRun(ContractSymbolicStatus.Error, log.ToString());
      }
      verified += stats.VerifiedCount;
      errors += stats.ErrorCount;
    }
    if (errors > 0) {
      return new VerificationRun(ContractSymbolicStatus.ObligationFailed, log.ToString());
    }
    return verified > 0
      ? new VerificationRun(ContractSymbolicStatus.Verified, log.ToString())
      : new VerificationRun(ContractSymbolicStatus.Error, "No implementation verification obligations were produced.");
  }

  private static IReadOnlyList<ContractSymbolicDependency> TrustDependencies(
    IEnumerable<MethodOrFunction> callables) {
    var result = new List<ContractSymbolicDependency>();
    foreach (var callable in callables) {
      var symbol = Symbol(callable);
      if (IsExtern(callable)) {
        result.Add(new ContractSymbolicDependency(symbol, "extern_contract",
          "The external implementation was not checked; callers use its original contract and frame."));
      }
      if (callable.HasAxiomAttribute) {
        result.Add(new ContractSymbolicDependency(symbol, "axiom", "The declaration carries {:axiom}."));
      }
      if (callable.HasVerifyFalseAttribute) {
        result.Add(new ContractSymbolicDependency(symbol, "verify_false", "The declaration carries {:verify false}."));
      }
      if (!IsExtern(callable) && Body(callable) == null) {
        result.Add(new ContractSymbolicDependency(symbol, "bodyless_contract",
          "The declaration has no implementation and is used through its contract."));
      }
      foreach (var assumption in callable.Assumptions(callable)) {
        var kind = TrustKind(assumption.desc);
        if (kind != null) {
          result.Add(new ContractSymbolicDependency(symbol, kind, assumption.desc.Issue));
        }
      }
    }
    return result.Distinct().OrderBy(item => item.Symbol, StringComparer.Ordinal)
      .ThenBy(item => item.Kind, StringComparer.Ordinal).ToList();
  }

  private static string? TrustKind(AssumptionDescription description) {
    if (description == AssumptionDescription.MayNotTerminate) {
      return "nontermination";
    }
    if (description == AssumptionDescription.ForallWithoutBody) {
      return "forall_without_body";
    }
    if (description == AssumptionDescription.LoopWithoutBody) {
      return "loop_without_body";
    }
    if (description == AssumptionDescription.AssertOnly) {
      return "assert_only";
    }
    if (description == AssumptionDescription.MemberOnly) {
      return "verify_only";
    }
    if (description.Issue.Contains("[assume", StringComparison.Ordinal)) {
      return "assume";
    }
    if (description.Issue.Contains("assume_concurrent", StringComparison.Ordinal)) {
      return "assume_concurrent";
    }
    return null;
  }

  private static ContractSourceLocation Location(IReadOnlyList<ContractSource> sources, MethodOrFunction callable) {
    var source = ContractSourceSnapshot.Find(sources, callable.Origin.Uri);
    return new ContractSourceLocation(source.Path, callable.Origin.line, callable.Origin.col,
      Symbol(callable), source.Sha256);
  }

  private static IReadOnlyList<ContractDependency> SourceEvidence(IReadOnlyList<ContractSource> sources) =>
    sources.Select(source => new ContractDependency(source.Path, source.Sha256))
      .OrderBy(source => source.Path, StringComparer.Ordinal).ToList();

  private static IEnumerable<MethodOrFunction> AllCallables(Microsoft.Dafny.Program program) =>
    program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
      .SelectMany(declaration => declaration.Members).OfType<MethodOrFunction>();

  private static INode? Body(MethodOrFunction callable) => callable switch {
    Method method => method.Body,
    Microsoft.Dafny.Function function => (INode?)function.ByMethodBody ?? function.Body,
    _ => null
  };

  private static bool IsExtern(MethodOrFunction callable) =>
    Attributes.Contains(callable.Attributes, "extern");

  private static string Symbol(MethodOrFunction callable) => callable.FullDafnyName;

  private static void RemoveBody(MethodOrFunction callable) {
    if (callable is Method method) {
      method.SetBody(null!);
    } else if (callable is Microsoft.Dafny.Function function) {
      function.Body = null;
      function.ByMethodBody = null;
      if (function.ByMethodDecl != null) {
        function.ByMethodDecl.SetBody(null!);
      }
    }
  }

  private static IReadOnlyList<string> Diagnostics(string diagnostics) => diagnostics.Split('\n')
    .Select(line => line.TrimEnd('\r')).Where(line => !string.IsNullOrWhiteSpace(line)).ToList();

  private static ContractSymbolicResult Failure(ContractSymbolicStatus status, string reason,
    IEnumerable<string> diagnostics, ContractSourceLocation? entry = null,
    IReadOnlyList<string>? checkedSymbols = null, IReadOnlyList<string>? externSymbols = null,
    IReadOnlyList<ContractSymbolicDependency>? dependencies = null,
    IReadOnlyList<ContractDependency>? sourceSnapshots = null) =>
    new(ContractJson.SchemaVersion, status, reason, entry, checkedSymbols ?? [], externSymbols ?? [],
      dependencies ?? [], [], diagnostics.ToList(), sourceSnapshots ?? []);
}
