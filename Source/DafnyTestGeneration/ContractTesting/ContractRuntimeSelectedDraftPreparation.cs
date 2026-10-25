#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

internal sealed record ContractRuntimeSelectedDraftSources(ContractRuntimePreparedSources Preparation,
  ContractGeneratorProofReport? ProofPreparationFailure = null, int ProofPreparationElapsedMilliseconds = 0);

/// <summary>Selects draft packets from resolved dependencies without parsing unrelated registered payloads.</summary>
internal static class ContractRuntimeSelectedDraftPreparation {
  private sealed record RuntimeResolution(ContractRuntimePreparedSources? Preparation, string? Failure);

  internal static async Task<ContractRuntimeSelectedDraftSources> PrepareAsync(Program original,
    IReadOnlyList<ContractSource> sources, Method originalGoal, IReadOnlyList<ContractRuntimeDraft> drafts,
    ContractSource generator, bool proveGeneratorPreconditions, DafnyOptions options,
    CancellationToken cancellationToken, Action<string, string>? phaseObserver = null, ContractEntry? selectedEntry = null) {
    var entry = (selectedEntry ?? new ContractEntry(originalGoal.FullDafnyName)) with { Symbol = originalGoal.FullDafnyName };
    var indexed = ContractRuntimeSourcePreparation.IndexDrafts(original, drafts);
    var selected = new HashSet<string>(StringComparer.Ordinal);
    var runtime = await StabilizeRuntimeAsync(selected);
    if (runtime.Preparation == null) { throw new NotSupportedException(runtime.Failure); }
    var fallback = runtime.Preparation;
    if (!proveGeneratorPreconditions) { return new(fallback); }

    var proofClock = Stopwatch.StartNew();
    var runtimeSelectedCount = selected.Count;
    selected = new(selected, StringComparer.Ordinal);
    var candidate = fallback;
    var randomSource = ContractGeneratorProof.ExtractPinnedPbtRandomSource();
    while (true) {
      cancellationToken.ThrowIfCancellationRequested();
      // Keep authored lemma bodies: visibility erasure would discard their newly introduced calls.
      var authoredSources = WithRuntime(candidate.Sources);
      var reporter = new BatchErrorReporter(options);
      var authored = await ContractSourceSnapshot.ParseAsync(reporter, authoredSources, cancellationToken,
        deferredGhostDiagnostics: new List<DafnyDiagnostic>(), phaseObserver: phaseObserver);
      if (reporter.ErrorCount != 0) {
        return ProofFailure(selected.Count == runtimeSelectedCount
            ? ContractGeneratorProofStatus.Unsupported : ContractGeneratorProofStatus.Failed,
          "Authored generator proof sources do not resolve normally: " + Diagnostics(reporter, candidate.SourceMap));
      }
      var goal = SelectGoal(authored);
      var generated = ContractRuntimeGeneratorSignature.Select(authored, goal, candidate.GeneratorMethodName);
      var build = ContractGeneratorProof.PrepareProofSources(authored, authoredSources, goal, generated,
        randomSource, out var preparationFailure, cancellationToken: cancellationToken);
      if (build == null) {
        return ProofFailure(ContractGeneratorProofStatus.Unsupported, preparationFailure!);
      }
      reporter = new BatchErrorReporter(options);
      var proofProgram = await ContractSourceSnapshot.ParseAsync(reporter, build.Sources, cancellationToken,
        deferredGhostDiagnostics: new List<DafnyDiagnostic>(), phaseObserver: phaseObserver);
      if (reporter.ErrorCount != 0) {
        return ProofFailure(ContractGeneratorProofStatus.Failed,
          "Generated proof dependency resolution failed: " + Diagnostics(reporter));
      }
      var proofGoal = SelectGoal(proofProgram);
      var proofGenerator = ContractRuntimeGeneratorSignature.Select(proofProgram, proofGoal,
        candidate.GeneratorMethodName);
      var dependencies = ContractGeneratorProof.DraftDependencies(proofProgram, build.Sources, proofGoal,
        proofGenerator, randomSource);
      if (!Select(dependencies, selected, includeGhostMethods: true)) {
        // The ordinary proof and executable diagnostic will authenticate this one final source set.
        return new(candidate);
      }
      RuntimeResolution augmented;
      try {
        augmented = await StabilizeRuntimeAsync(selected);
      } catch (ContractRuntimeDraftPreparationException error) {
        return ProofFailure(ContractGeneratorProofStatus.Failed, error.Message);
      }
      if (augmented.Preparation == null) {
        return ProofFailure(ContractGeneratorProofStatus.Failed, augmented.Failure!);
      }
      candidate = augmented.Preparation;
    }

    ContractRuntimeSelectedDraftSources ProofFailure(ContractGeneratorProofStatus status, string diagnostics) =>
      new(fallback, new(status, diagnostics, [], []),
        (int)Math.Min(int.MaxValue, proofClock.ElapsedMilliseconds));

    Method SelectGoal(Program program) => ContractCallableSelector.SelectMethod(program,
      entry, requireConcreteReceiver: false, allowLemmaContract: true);

    bool Select(IEnumerable<MethodOrFunction> dependencies, HashSet<string> selection, bool includeGhostMethods) {
      var added = false;
      foreach (var dependency in dependencies) {
        if (!includeGhostMethods && (dependency.IsGhost && dependency is not Function ||
            dependency.EnclosingClass is TraitDecl && !dependency.IsStatic ||
            !sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == dependency.Origin.Uri))) {
          continue;
        }
        if (indexed.ContainsKey(dependency.FullDafnyName)) {
          added |= selection.Add(dependency.FullDafnyName);
        }
      }
      return added;
    }

    async Task<RuntimeResolution> StabilizeRuntimeAsync(HashSet<string> selection) {
      while (true) {
        cancellationToken.ThrowIfCancellationRequested();
        var preparation = await ContractRuntimeSourcePreparation.PrepareSelectedAsync(original, sources, originalGoal,
          indexed.Where(pair => selection.Contains(pair.Key)).Select(pair => pair.Value).ToArray(),
          generator, options, cancellationToken);
        var reporter = new BatchErrorReporter(options);
        var raw = await ContractSourceSnapshot.ParseAsync(reporter, preparation.Sources, cancellationToken,
          resolve: false, phaseObserver: phaseObserver);
        if (reporter.ErrorCount != 0) { return new(null, Diagnostics(reporter, preparation.SourceMap)); }
        var visible = ContractRuntimeObligationTransformer.MakeGeneratorVisible(raw, preparation.Sources,
          new HashSet<string>());
        reporter = new BatchErrorReporter(options);
        var program = await ContractSourceSnapshot.ParseAsync(reporter, WithRuntime(visible), cancellationToken,
          deferredGhostDiagnostics: new List<DafnyDiagnostic>(), phaseObserver: phaseObserver);
        if (reporter.ErrorCount != 0) {
          return new(null, "Draft or generator resolution failed: " + Diagnostics(reporter, preparation.SourceMap));
        }
        var goal = SelectGoal(program);
        var generated = ContractRuntimeGeneratorSignature.Select(program, goal, preparation.GeneratorMethodName);
        var root = ContractCallableSelector.NativeCallable(program, goal);
        MethodOrFunction[] roots = goal is Lemma ? new MethodOrFunction[] { generated } : new MethodOrFunction[] { root, generated };
        var dependencies = ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, roots,
          goal is Lemma ? goal.Ins.Select(formal => formal.Type) : null);
        if (!Select(dependencies, selection, includeGhostMethods: false)) {
          return new(preparation, null);
        }
      }
    }
  }

  private static IReadOnlyList<ContractSource> WithRuntime(IReadOnlyList<ContractSource> sources) {
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    return sources.Append(new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))).ToArray();
  }

  private static string Diagnostics(BatchErrorReporter reporter, ContractRuntimeSourceMap? sourceMap = null) =>
    string.Join("\n", reporter.AllMessages.Where(message => message.Level == ErrorLevel.Error).Select(message => {
      var token = message.Range.StartToken;
      try {
        if (sourceMap != null) {
          var location = sourceMap.ResolveLocation(token.Uri, token.pos);
          return location.Path + ":" + location.Line + ":" + location.Column + ": " + message.Message;
        }
      } catch (ArgumentException) {
        // The embedded runtime and generated proof clauses have no authored source segment.
      }
      return token.Uri + ":" + token.line + ":" + token.col + ": " + message.Message;
    }));
}
