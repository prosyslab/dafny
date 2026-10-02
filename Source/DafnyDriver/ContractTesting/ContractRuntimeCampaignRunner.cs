#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;

namespace Microsoft.Dafny;

/// <summary>Compiles a detached runtime diagnostic and runs each generated sample in its own process.</summary>
public static class ContractRuntimeCampaignRunner {
  private sealed class CampaignDeadlineExpiredException : Exception {
  }

  private sealed record MembershipProof(string IdentitySha256, string QuerySha256, string SourceSetSha256,
    string SourcePath, string CanonicalSourcePath, string QueryName, string Role, int SampleOrdinal,
    string QueryArtifact, string ResultArtifact, string ResultSha256, ContractQueryOutcome Outcome);

  public static ContractRuntimeCampaignResult Failure(ContractRuntimeStatus status, string reason, string seed = "") =>
    new(ContractJson.SchemaVersion, status, reason, seed, new(), [], [], [], [], null, [], []);

  public static async Task<ContractRuntimeCampaignResult> RunAsync(ContractRuntimeCampaignRequest request,
    DafnyOptions options, string directory, CancellationToken cancellationToken) {
    Validate(request);
    var clock = Stopwatch.StartNew();
    var phases = new ContractPhaseRecorder(Path.Combine(directory, "campaign-phases.jsonl"));
    var profile = new ContractProfileRecorder(Path.Combine(directory, "campaign-profile.json"));
    phases.Record("campaign", "started");
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    // The detached diagnostic may use any declaration; this reveals every export instead of rewriting export text.
    options.DisableScopes = true;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, cancellationToken,
      phaseObserver: (phase, state) => phases.Record("original:" + phase, state));
    if (reporter.ErrorCount > 0) { return Failure(ContractRuntimeStatus.Error, Diagnostics(reporter), request.Seed); }
    var goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false);
    if (goal.FunctionFromWhichThisIsByMethodDecl is { ByMethodBody: null } || goal.Body == null) {
      return Failure(ContractRuntimeStatus.Unsupported, "Runtime goals require an implemented method or function-by-method.", request.Seed);
    }
    var originalProgram = program;
    var source = ContractSourceSnapshot.Find(request.Sources, goal.Origin.Uri);
    var originalPrepared = new ContractPreparedProgram(originalProgram, goal, source,
      new(source.Path, goal.Origin.line, goal.Origin.col, goal.FullDafnyName, source.Sha256),
      OriginalCallable: goal.FunctionFromWhichThisIsByMethodDecl ?? (MethodOrFunction)goal, Sources: request.Sources);
    var missing = MissingDrafts(program, request.Sources, goal, request.Drafts ?? []);
    var generator = request.Generator == null ? new ContractRuntimeMissingGenerator(goal.FullDafnyName,
      "method {:pbt_generator \"" + goal.FullDafnyName + "\"} Generate(r: PbtRandom.Source) returns (" +
      string.Join(", ", (goal.IsStatic ? Enumerable.Empty<string>() : ["receiver: " + goal.EnclosingClass.Name]).Concat(goal.Ins.Select(f => f.Name + ": " + f.Type))) + ")") : null;
    if (missing.Count > 0 || generator != null) {
      return Failure(missing.Count > 0 ? ContractRuntimeStatus.DraftsRequired : ContractRuntimeStatus.GeneratorRequired,
        missing.Count > 0 ? "Reachable implementations require drafts." : "The goal requires a generator.", request.Seed) with {
        MissingDrafts = missing,
        MissingGenerator = generator
      };
    }
    foreach (var formal in goal.Ins) {
      if (!ContractRuntimeObligationTransformer.CompilableType(formal.Type)) {
        return Failure(ContractRuntimeStatus.Unsupported, "non_compilable_input_type: " + formal.Name, request.Seed);
      }
    }
    phases.Record("source_preparation", "started");
    var sourcePreparation = await ContractRuntimeSourcePreparation.PrepareAsync(program, request.Sources, goal,
      request.Drafts ?? [], request.Generator!, options, cancellationToken);
    phases.Record("source_preparation", "completed");
    var visibilityReporter = new BatchErrorReporter(options);
    var visibilityProgram = await ContractSourceSnapshot.ParseAsync(visibilityReporter, sourcePreparation.Sources, cancellationToken, resolve: false,
      phaseObserver: (phase, state) => phases.Record("visibility:" + phase, state));
    if (visibilityReporter.ErrorCount > 0) { return Failure(ContractRuntimeStatus.Unsupported, Diagnostics(visibilityReporter), request.Seed); }
    var runtimeSource = ContractRuntimeInstrumentation.DafnySource;
    var snapshots = ContractRuntimeObligationTransformer.MakeGeneratorVisible(visibilityProgram, sourcePreparation.Sources, new HashSet<string>()).ToList();
    snapshots.Add(new("PbtRuntime.dfy", runtimeSource, ContractHarnessBuilder.Hash(runtimeSource)));
    // This pass defers only explicitly identified ghost-context errors. It supplies the complete
    // typed dependency graph; only a later ordinary resolve may authorize executable compilation.
    var deferred = new List<DafnyDiagnostic>();
    reporter = new BatchErrorReporter(options);
    program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, cancellationToken,
      deferredGhostDiagnostics: deferred, phaseObserver: (phase, state) => phases.Record("reachability:" + phase, state));
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "reachability-diagnostics.txt"),
      string.Join("\n", deferred.Select(diagnostic => diagnostic.Message)), cancellationToken);
    if (reporter.ErrorCount > 0) {
      return Failure(ContractRuntimeStatus.Unsupported, "Draft or generator resolution failed: " +
        Diagnostics(reporter, sourcePreparation.SourceMap), request.Seed);
    }
    goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false);
    ContractDiagnosticConstruction.AuditResolved(program, goal, sourcePreparation.DiagnosticConstructors ?? new HashSet<string>());
    var generatedMethod = ContractRuntimeObligationTransformer.Members(program).OfType<Method>()
      .Single(m => m.Name == "Generate" && m.EnclosingClass.EnclosingModuleDefinition == goal.EnclosingClass.EnclosingModuleDefinition);
    var unresolved = MissingDrafts(program, snapshots, goal, [], sourcePreparation.SourceMap)
      .Concat(MissingDrafts(program, snapshots, generatedMethod, [], sourcePreparation.SourceMap)).DistinctBy(d => d.Symbol).ToList();
    if (unresolved.Count > 0) {
      return Failure(ContractRuntimeStatus.DraftsRequired, "A draft or generator reaches further missing implementations.", request.Seed) with { MissingDrafts = unresolved };
    }
    ContractRuntimeTransformation transformation = null!;
    var rejectedDeclarations = new Dictionary<string, string>();
    var decisionCaps = new Dictionary<string, ContractRuntimeDecisionMethod>();
    IReadOnlySet<string> compiledChecks = new HashSet<string>();
    const int maximumAttempts = 8;
    for (var attempt = 0; ; attempt++) {
      phases.Record("transformation:" + attempt, "started");
      transformation = new ContractRuntimeObligationTransformer(program, snapshots, goal, sourcePreparation.SourceMap, rejectedDeclarations, decisionCaps,
        sourcePreparation.DiagnosticConstructors, ContractRuntimeTypeEvidence.SourceSetHash(request.Sources)).Transform();
      phases.Record("transformation:" + attempt, "completed");
      Directory.CreateDirectory(directory);
      await WriteJsonAsync(Path.Combine(directory, "transformed-sources.json"), transformation.Sources);
      await WriteJsonAsync(Path.Combine(directory, "transformed-sources-" + attempt + ".json"), transformation.Sources);
      var transformedReporter = new BatchErrorReporter(options);
      var transformedProgram = await ContractSourceSnapshot.ParseAsync(transformedReporter, transformation.Sources, cancellationToken,
        phaseObserver: (phase, state) => phases.Record("transformed:" + attempt + ":" + phase, state));
      await File.WriteAllTextAsync(Path.Combine(directory, "transformed-diagnostics-" + attempt + ".txt"),
        Diagnostics(transformedReporter), cancellationToken);
      if (transformedReporter.ErrorCount == 0) {
        // Ghost inference can silently erase a check whose rendered form is not compilable. Such an obligation
        // is lowered to a closed query, then to unchecked, until every remaining decision is present in compiled code.
        compiledChecks = ContractRuntimeObligationTransformer.CompiledCheckLiterals(transformedProgram);
        var lowered = false;
        foreach (var clause in transformation.Clauses.Where(c => c.Obligation.DecisionMethod != ContractRuntimeDecisionMethod.Unchecked &&
                   !ContractRuntimeObligationTransformer.IsCompiled(compiledChecks, c.Obligation.Id))) {
          var next = clause.Obligation.DecisionMethod == ContractRuntimeDecisionMethod.Runtime ? ContractRuntimeDecisionMethod.ClosedSmt : ContractRuntimeDecisionMethod.Unchecked;
          var prefix = ContractRuntimeObligationTransformer.IdPrefix(clause.Obligation.Id);
          if (!decisionCaps.TryGetValue(prefix, out var cap) || cap < next) { decisionCaps[prefix] = next; lowered = true; }
        }
        if (!lowered || attempt >= maximumAttempts - 1) { break; }
        continue;
      }
      if (transformedProgram.ModuleSigs == null) {
        return Failure(ContractRuntimeStatus.Unsupported, "Diagnostic parsing failed: " + Diagnostics(transformedReporter), request.Seed) with {
          DeghostExclusions = transformation.Exclusions
        };
      }
      var added = false;
      foreach (var error in transformedReporter.AllMessages.Where(m => m.Level == ErrorLevel.Error)) {
        var token = error.Range.StartToken;
        // A rendered runtime check that does not resolve (for example equality on a type without compiled
        // equality) falls back to its closed form instead of failing the whole diagnostic.
        var line = transformation.Sources.FirstOrDefault(s => ContractSourceSnapshot.UriFor(s.Path) == token.Uri)?.Content.Split('\n').ElementAtOrDefault(token.line - 1);
        var marker = line?.IndexOf("PbtChecks.Check(\"", StringComparison.Ordinal) ?? -1;
        if (marker >= 0) {
          var literal = line![(marker + "PbtChecks.Check(\"".Length)..];
          var clause = transformation.Clauses.FirstOrDefault(c => literal.StartsWith(ContractRuntimeObligationTransformer.Literal(c.Obligation.Id) + "\"", StringComparison.Ordinal));
          if (clause != null) {
            var prefix = ContractRuntimeObligationTransformer.IdPrefix(clause.Obligation.Id);
            if (!decisionCaps.TryGetValue(prefix, out var cap) || cap < ContractRuntimeDecisionMethod.ClosedSmt) {
              decisionCaps[prefix] = ContractRuntimeDecisionMethod.ClosedSmt;
              added = true;
            }
            continue;
          }
        }
        foreach (var member in ContractRuntimeObligationTransformer.Members(transformedProgram)
                   .Where(m => m.Origin.Uri == token.Uri && m.StartToken.pos <= token.pos && token.pos <= m.EndToken.pos + m.EndToken.val.Length)) {
          var original = ContractRuntimeObligationTransformer.Members(program).SingleOrDefault(m => m.FullDafnyName == member.FullDafnyName);
          if (original is Function { IsGhost: true }) {
            added |= rejectedDeclarations.TryAdd(original.FullDafnyName, "resolver rejected compiled copy: " + error.Message);
          }
          if (member is Method { Body: { } body } && original is Method { Body: { } originalBody }) {
            foreach (var declaration in body.Descendants().OfType<VarDeclStmt>().Where(v => v.StartToken.pos <= token.pos && token.pos <= v.EndToken.pos + v.EndToken.val.Length)) {
              foreach (var local in declaration.Locals.Where(v => originalBody.Descendants().OfType<VarDeclStmt>().SelectMany(d => d.Locals).Any(o => o.IsGhost && o.Name == v.Name))) {
                added |= rejectedDeclarations.TryAdd(original.FullDafnyName + "." + local.Name, "resolver rejected compiled copy: " + error.Message);
              }
            }
          }
        }
      }
      if (!added || attempt >= maximumAttempts - 1) {
        return Failure(ContractRuntimeStatus.Unsupported, "Diagnostic resolution failed: " + Diagnostics(transformedReporter), request.Seed) with {
          DeghostExclusions = transformation.Exclusions.Concat(rejectedDeclarations.Select(p => new ContractRuntimeDeghostExclusion(p.Key, p.Value))).Distinct().ToList()
        };
      }
    }
    phases.Record("compilation", "started");
    var compile = await ContractCompilerWorker.CompileRuntimeAsync(transformation, request, directory, options, cancellationToken);
    phases.Record("compilation", "completed");
    if (compile.Status != ContractTestStatus.Passed) { return Failure(ContractRuntimeStatus.Unsupported, compile.Reason, request.Seed); }
    var population = new ContractRuntimePopulation();
    // A check still absent from compiled code can never be evaluated; it is reported as unchecked, never as runtime.
    var obligations = transformation.Clauses.ToDictionary(c => c.Obligation.Id, c =>
      ContractRuntimeObligationTransformer.IsCompiled(compiledChecks, c.Obligation.Id) ? c.Obligation :
      c.Obligation with { DecisionMethod = ContractRuntimeDecisionMethod.Unchecked, UncheckedReason = c.Obligation.UncheckedReason ?? "runtime_check_not_compiled" });
    var clauses = transformation.Clauses.ToDictionary(c => c.Obligation.Id);
    var violations = new List<ContractRuntimeViolation>();
    var calleeViolations = new List<ContractRuntimeCalleeViolation>();
    var errors = new List<ContractRuntimeError>();
    var samples = new List<Sample>();
    // A closed decision may run a query for the clause and one for its negation.
    var reserve = Math.Min(2L * request.MaxClosedQueries * request.ClosedQueryTimeoutMilliseconds, request.TimeoutMilliseconds / 2);
    var ordinals = request.ReplayOrdinal is { } replay ? [replay] : Enumerable.Range(0, request.SampleCount);
    foreach (var ordinal in ordinals) {
      cancellationToken.ThrowIfCancellationRequested();
      var remaining = request.TimeoutMilliseconds - reserve - clock.ElapsedMilliseconds;
      if (remaining <= 0) { break; }
      var observationPath = Path.Combine(directory, "sample-" + ordinal + ".jsonl");
      await File.WriteAllTextAsync(observationPath, "", cancellationToken);
      using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      timeout.CancelAfter((int)Math.Min(remaining, request.SampleTimeoutMilliseconds));
      phases.Record("sample:" + ordinal, "started");
      var execution = await profile.MeasureAsync("sample_process", () => ContractExecutionProcess.RunAsync("dotnet", [compile.AssemblyPath!,
        "--pbt-seed",
        request.Seed,
        "--pbt-ordinal",
        ordinal.ToString(CultureInfo.InvariantCulture),
        "--pbt-out",
        observationPath], directory, timeout.Token));
      phases.Record("sample:" + ordinal, execution.Cancelled ? "cancelled" : "completed");
      profile.Flush();
      var records = new List<JsonElement>();
      var truncated = false;
      int? firstMalformedRecord = null;
      foreach (var line in (await File.ReadAllLinesAsync(observationPath, cancellationToken)).Where(l => l.Length > 0)) {
        try {
          records.Add(JsonDocument.Parse(line).RootElement.Clone());
        } catch (JsonException) {
          // A sample killed while appending leaves a partial final record; it invalidates only that sample.
          truncated = true;
          firstMalformedRecord ??= records.Count;
        }
      }
      samples.Add(new(ordinal, SampleInputs(records), records, execution.Cancelled, execution.ExitCode != 0, execution.StandardError,
        truncated, firstMalformedRecord));
    }
    var queryCache = new Dictionary<string, (bool? Passed, string? Reason)>();
    var initialHeapCache = new Dictionary<string, (bool? Passed, string? Reason, bool Constructive)>();
    var membershipProofs = new ContractNativeFactCache<MembershipProof>();
    var membershipReuseReceipts = 0;
    var callObservedCertificates = 0;
    var closedQueries = 0;
    var specifications = new ContractSpecificationChecker(originalProgram, request.Sources, ClosedQueryOptions());
    var specificationAttempts = new Dictionary<string, bool>();
    var scalarDependencyScopes = new Dictionary<string, ContractSpecificationScope?>();
    var draftedSymbols = (request.Drafts ?? []).Select(draft => draft.Symbol).ToHashSet(StringComparer.Ordinal);
    var decidedGoalEvaluations = 0;
    void RequireCampaignTime() {
      cancellationToken.ThrowIfCancellationRequested();
      if (clock.ElapsedMilliseconds >= request.TimeoutMilliseconds) {
        throw new CampaignDeadlineExpiredException();
      }
    }
    foreach (var originalSample in samples) {
      var classificationStarted = Stopwatch.GetTimestamp();
      try {
        // Later execution is unnecessary for a safety counterexample. Restrict every
        // validation input, including runtime type evidence, to this exact finite prefix.
        var originalComplete = originalSample.Records.Any(r => Kind(r) == "complete");
        var prefixLength = originalComplete ? 0 : CounterexamplePrefixLength(originalSample, obligations);
        var sample = originalSample;
        if (prefixLength > 0) {
          var prefix = originalSample.Records.Take(prefixLength).ToList();
          sample = originalSample with { Records = prefix, Inputs = SampleInputs(prefix) };
        }
        ContractRuntimeTypeEvidence? runtimeTypeEvidence = null;
        var evidencePhases = new ContractPhaseRecorder(Path.Combine(directory, "runtime-evidence-" + sample.Ordinal + ".phases.jsonl"));
        try {
          runtimeTypeEvidence = ContractPhaseRecorder.Measure(phases.Record, "runtime_evidence:" + sample.Ordinal, cancellationToken,
            () => ContractRuntimeTypeEvidence.Collect(originalProgram, request.Sources, clauses, sample.Records, compiledChecks, draftedSymbols,
              cancellationToken, ContractQueryDeadline.AfterMilliseconds(Math.Max(0, request.TimeoutMilliseconds - clock.ElapsedMilliseconds)), evidencePhases.Record));
        } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
          // Partial collection cannot be reused: a later false check could contradict it.
          evidencePhases.Record("collection", "cancelled");
        }
        var kinds = sample.Records.Select(Kind).ToHashSet();
        var complete = kinds.Contains("complete");
        if (kinds.Contains("generated")) { population = population with { Generated = population.Generated + 1 }; }
        if (kinds.Contains("executed")) { population = population with { Executed = population.Executed + 1 }; }
        var stoppedAtCall = false; var rejected = kinds.Contains("rejected"); var uncheckedPrecondition = false; var badCallee = false; var uncheckedCallee = false;
        var pending = new List<ContractRuntimeViolation>();
        var failed = new List<ContractRuntimeObligation>();
        var decided = 0;
        ContractRuntimeHeapCheck? heapCheck = null;
        string? heapFailure = null;
        var heapPrepared = false;
        var initialCaptures = HeapCaptures(sample.Records, "entry");
        if (initialCaptures.Count == 1) {
          var (validTypes, initialError) = await ValidateInitialHeapAsync(initialCaptures[0], sample, runtimeTypeEvidence);
          if (initialError != null) { AddError(initialError); }
          rejected |= validTypes == false;
          uncheckedPrecondition |= validTypes == null;
        } else if (complete || prefixLength > 0) {
          uncheckedPrecondition = true;
          AddError("entry_heap_capture_missing_or_duplicated");
        }
        var observedPrefix = new List<JsonElement>();
        foreach (var record in sample.Records) {
          observedPrefix.Add(record);
          if (Kind(record) is not ("check" or "checkpoint")) { continue; }
          var id = record.GetProperty("id").GetString()!;
          var obligation = obligations[id];
          var clause = clauses[id];
          var isRuntime = Kind(record) == "check";
          var unvalidatedCallees = clause.UnvalidatedCallees;
          var passed = isRuntime ? record.GetProperty("passed").GetBoolean() : (bool?)null;
          Dictionary<string, ContractValue>? decodedValues = null;
          Dictionary<string, ContractValue> Values() => decodedValues ??=
            JsonSerializer.Deserialize<Dictionary<string, ContractValue>>(record.GetProperty("values"), ContractJson.Options)!;
          // Failed runtime records can contribute rejection or counterexample evidence and retain strict value validation.
          if (passed == false) { _ = Values(); }
          string? uncheckedReason = obligation.UncheckedReason;
          if (!isRuntime && obligation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt) {
            var values = Values();
            var clauseHeap = heapCheck;
            var clauseHeapFailure = heapFailure;
            if (clause.CallHeapScope != null) {
              (clauseHeap, clauseHeapFailure) = await PrepareObservedCallAsync(sample, observedPrefix, record, clause, runtimeTypeEvidence);
            } else if (clause.EntryHeapPostcondition != null && !heapPrepared) {
              heapPrepared = true;
              (heapCheck, heapFailure) = PrepareObservedHeap(sample);
              clauseHeap = heapCheck;
              clauseHeapFailure = heapFailure;
            }
            if (clause.EntryHeapPostcondition != null && clauseHeap != null) {
              foreach (var pair in clauseHeap.Evidence) { values[pair.Key] = pair.Value; }
            }
            var cacheMaterial = clause.EntryHeapPostcondition != null && clauseHeap != null
              ? JsonSerializer.Serialize(new { clauseHeap.Request, clauseHeap.Outputs, clauseHeap.Observations }, ContractJson.Options)
              : JsonSerializer.Serialize(values, ContractJson.Options);
            var cacheKey = id + ":" + ContractHarnessBuilder.Hash(cacheMaterial);
            (bool? Passed, string? Reason) decision;
            if (unvalidatedCallees && clause.EntryHeapPostcondition is { } dependencyPostcondition &&
                clauseHeapFailure == null && clauseHeap != null && !rejected && !uncheckedPrecondition && !badCallee && !uncheckedCallee) {
              unvalidatedCallees = !await ValidateSpecificationsAsync(
                specifications.LogicalScope(clauseHeap.Prepared.Method.Ens[dependencyPostcondition].E));
            }
            if (clause.EntryHeapPostcondition != null && (clauseHeapFailure != null || badCallee || uncheckedCallee || unvalidatedCallees)) {
              decision = (null, clauseHeapFailure ?? "callee_contract_unvalidated");
            } else if (clock.ElapsedMilliseconds >= request.TimeoutMilliseconds) {
              decision = (null, "campaign_timeout");
            } else {
              try {
                if (!ContractQueryDeadline.TryReadCached(queryCache, cacheKey, RequireCampaignTime, out decision)) {
                  if (clause.EntryHeapPostcondition == null && closedQueries >= request.MaxClosedQueries) {
                    decision = (null, "closed_query_budget_exhausted");
                  } else if (clock.ElapsedMilliseconds >= request.TimeoutMilliseconds) {
                    decision = (null, "campaign_timeout");
                  } else {
                    if (clause.EntryHeapPostcondition is { } postcondition) {
                      decision = await DecideHeapAsync(clauseHeap!, postcondition, runtimeTypeEvidence, sample.Ordinal);
                    } else {
                      closedQueries++;
                      decision = await DecideClosedAsync(clause, values);
                    }
                  }
                  RequireCampaignTime();
                  if (decision.Passed != null) { queryCache.TryAdd(cacheKey, decision); }
                }
                RequireCampaignTime();
              } catch (CampaignDeadlineExpiredException) {
                decision = (null, "campaign_timeout");
              }
            }
            cancellationToken.ThrowIfCancellationRequested();
            passed = decision.Passed; uncheckedReason = decision.Reason;
            if (passed != null && unvalidatedCallees && (clause.EntryHeapPostcondition != null || obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition || (passed == false ? GoalKind(obligation.Kind) : obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition))) {
              if (clause.EntryHeapPostcondition == null && !rejected && !uncheckedPrecondition && !badCallee && !uncheckedCallee) {
                if (!scalarDependencyScopes.TryGetValue(id, out var dependencyScope)) {
                  var originalExpression = ContractRuntimeClauseDependencies.OriginalExpression(originalProgram, request.Sources, clause);
                  dependencyScope = originalExpression == null ? null : specifications.LogicalScope(originalExpression);
                  scalarDependencyScopes.Add(id, dependencyScope);
                }
                if (dependencyScope != null) {
                  unvalidatedCallees = !await ValidateSpecificationsAsync(dependencyScope);
                }
              }
              // Solver evaluation uses function bodies without checking their own contracts, so a clause that could
              // indict the goal (or admit an input) through an unvalidated callee stays undecided.
              if (unvalidatedCallees) { passed = null; uncheckedReason = "callee_contract_unvalidated"; }
            }
          }
          obligation = obligation with {
            Evaluations = isRuntime ? obligation.Evaluations with { Runtime = obligation.Evaluations.Runtime + 1 } :
            passed != null ? obligation.Evaluations with { ClosedSmt = obligation.Evaluations.ClosedSmt + 1 } :
            obligation.Evaluations with { Unchecked = obligation.Evaluations.Unchecked + 1 },
            UncheckedReason = uncheckedReason ?? obligation.UncheckedReason
          };
          obligations[id] = obligation;
          if (passed == false) { failed.Add(obligation); }
          if (passed != null && GoalKind(obligation.Kind)) { decided++; }
          if (obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition) { rejected |= passed == false; uncheckedPrecondition |= passed == null; } else if (obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition) {
            badCallee |= passed == false; uncheckedCallee |= passed == null;
            if (passed == false) { calleeViolations.Add(new(id, obligation.Callee!, request.Drafts?.Any(d => d.Symbol == obligation.Callee) == true, sample.Ordinal, sample.Inputs, Values())); }
          } else if (passed == false) {
            var iteration = record.GetProperty("iteration").GetInt32();
            pending.Add(new(id, obligation.Kind, sample.Ordinal, iteration < 0 ? null : iteration,
              isRuntime ? ContractRuntimeDecisionMethod.Runtime : ContractRuntimeDecisionMethod.ClosedSmt, sample.Inputs, Values()));
            if (obligation.Kind == ContractRuntimeObligationKind.CallPrecondition) { stoppedAtCall = true; break; }
          }
        }
        var validatedPrefix = prefixLength > 0 && pending.Any(violation =>
          violation.ObligationId == sample.Records[^1].GetProperty("id").GetString()) &&
          kinds.Contains("generated") && kinds.Contains("executed") && !kinds.Contains("runtime_error") &&
          originalPrepared.Method.Ins.All(formal => sample.Inputs.ContainsKey(formal.Name)) &&
          (originalPrepared.Method.IsStatic || sample.Inputs.ContainsKey("receiver"));
        // Obligation violation counts include only failures that decide this sample's classification.
        Func<ContractRuntimeObligationKind, bool> counted = _ => false;
        if (rejected) {
          population = population with { PreconditionRejected = population.PreconditionRejected + 1 };
          counted = kind => kind == ContractRuntimeObligationKind.EntryPrecondition;
        } else if (uncheckedPrecondition) {
          population = population with { PreconditionUnchecked = population.PreconditionUnchecked + 1 };
        } else if (badCallee) {
          population = population with { CalleeContractViolations = population.CalleeContractViolations + 1 };
          counted = kind => kind == ContractRuntimeObligationKind.CalleePostcondition;
        } else if (uncheckedCallee) {
          population = population with { CalleeContractUnchecked = population.CalleeContractUnchecked + 1 };
        } else if (heapFailure != null) {
          population = population with { RuntimeErrors = population.RuntimeErrors + 1 };
          AddError(heapFailure);
        } else if (sample.Timeout && !complete && !stoppedAtCall && !validatedPrefix) {
          // A sample that already recorded completion is not recounted as a timeout because of process teardown.
          population = population with { Timeouts = population.Timeouts + 1 }; AddError("sample_timeout");
        } else if ((sample.Truncated || !complete) && !validatedPrefix) {
          population = population with { RuntimeErrors = population.RuntimeErrors + 1 }; var error = sample.Records.LastOrDefault(r => Kind(r) == "runtime_error");
          AddError(sample.Truncated ? "truncated observation record" : error.ValueKind == JsonValueKind.Undefined ? sample.Diagnostics : error.GetProperty("message").GetString()!,
            error.ValueKind == JsonValueKind.Undefined ? null : error.GetProperty("location").GetString());
        } else {
          population = population with { Valid = population.Valid + 1, ViolatingSamples = population.ViolatingSamples + (pending.Count > 0 ? 1 : 0) };
          violations.AddRange(pending);
          decidedGoalEvaluations += decided;
          counted = GoalKind;
          if (validatedPrefix) {
            await using var rawTrace = File.OpenRead(Path.Combine(directory, "sample-" + sample.Ordinal + ".jsonl"));
            var traceHash = Convert.ToHexString(await System.Security.Cryptography.SHA256.HashDataAsync(rawTrace, cancellationToken)).ToLowerInvariant();
            await WriteJsonAsync(Path.Combine(directory, "prefix-certificate-" + sample.Ordinal + ".json"), new {
              sourceSetHash = ContractRuntimeTypeEvidence.SourceSetHash(request.Sources),
              request.Seed,
              sample.Ordinal,
              endpointId = sample.Records[^1].GetProperty("id").GetString(),
              recordCount = prefixLength,
              originalRecordCount = originalSample.Records.Count,
              originalTimeout = originalSample.Timeout,
              originalComplete,
              originalError = originalSample.Error,
              originalTruncated = originalSample.Truncated,
              firstMalformedRecord = originalSample.FirstMalformedRecord,
              traceHash
            });
          }
        }
        foreach (var failure in failed.Where(f => counted(f.Kind))) {
          obligations[failure.Id] = obligations[failure.Id] with { Violations = obligations[failure.Id].Violations + 1 };
        }
        void AddError(string message, string? location = null) { if (errors.Count < 20) { errors.Add(new(sample.Ordinal, message, location)); } }
      }
      finally {
        profile.Record("result_classification", classificationStarted);
        profile.Flush();
      }
    }
    // Valid samples support "no violation" only when at least one goal obligation was actually decided in them.
    var status = population.ViolatingSamples > 0 ? ContractRuntimeStatus.ViolationFound :
      population.Valid > 0 && decidedGoalEvaluations > 0 ? ContractRuntimeStatus.NoViolationFound : ContractRuntimeStatus.Inconclusive;
    var reason = status != ContractRuntimeStatus.Inconclusive ? "" :
      population.Valid == 0 ? "No valid sample completed." : "No goal obligation was decided in a valid sample.";
    phases.Record("campaign", "completed");
    return new(1, status, reason, request.Seed, population, obligations.Values.ToList(),
      violations.GroupBy(v => v.ObligationId).SelectMany(g => g.OrderBy(v => JsonSerializer.Serialize(v.Inputs, ContractJson.Options).Length)
        .ThenBy(v => v.SampleOrdinal).Take(request.MaxViolationsPerObligation)).ToList(), calleeViolations, [], null, transformation.Exclusions, errors);

    DafnyOptions ClosedQueryOptions() =>
      new(options) { TimeLimit = (uint)Math.Max(1, (request.ClosedQueryTimeoutMilliseconds + 999) / 1000) };

    Task WriteJsonAsync<T>(string path, T value) =>
      File.WriteAllTextAsync(path, JsonSerializer.Serialize(value, ContractJson.Options), cancellationToken);

    // Decides the captured entry state's typed validity; null carries the reason it stays unchecked.
    async Task<(bool? Valid, string? Error)> ValidateInitialHeapAsync(JsonElement capture, Sample sample,
      ContractRuntimeTypeEvidence? runtimeTypeEvidence) {
      try {
        RequireCampaignTime();
        var initial = Decode<List<ContractHeapObject>>(capture.GetProperty("heap"));
        bool? validTypes;
        try {
          RequireCampaignTime();
          validTypes = ContractPhaseRecorder.Measure(phases.Record, "initial_type_check:" + sample.Ordinal, cancellationToken,
            () => ContractRuntimeHeapChecking.CheckInitialTypes(originalProgram, initial, specifications));
          RequireCampaignTime();
        } catch (NotSupportedException) {
          RequireCampaignTime();
          var scope = ContractPhaseRecorder.Measure(phases.Record, "initial_dependency_scope:" + sample.Ordinal, cancellationToken,
            () => specifications.Scope([], ContractRuntimeHeapChecking.InitialTypes(originalProgram, initial)));
          RequireCampaignTime();
          var validSpecifications = await ValidateSpecificationsAsync(scope);
          RequireCampaignTime();
          if (!validSpecifications) { throw; }
          validTypes = ContractRuntimeHeapChecking.CheckInitialTypes(originalProgram, initial, specifications);
          RequireCampaignTime();
        }
        if (validTypes != null) { return (validTypes, null); }
        RequireCampaignTime();
        var initialCheck = ContractPhaseRecorder.Measure(phases.Record, "initial_preparation:" + sample.Ordinal, cancellationToken,
          () => ContractRuntimeHeapChecking.PrepareInitial(originalProgram, request, sample.Inputs, initial, specifications));
        RequireCampaignTime();
        var initialKey = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(initialCheck.Request, ContractJson.Options));
        if (!ContractQueryDeadline.TryReadCached(initialHeapCache, initialKey, RequireCampaignTime, out var validation)) {
          validation = await CertifyInitialHeapAsync(initialCheck, initialKey, sample, runtimeTypeEvidence);
          RequireCampaignTime();
          if (validation.Passed == true) { initialHeapCache.TryAdd(initialKey, validation); }
        }
        RequireCampaignTime();
        return (validation.Passed, validation.Passed == null ? validation.Reason ?? "initial_heap_type_constraints_undecided" : null);
      } catch (CampaignDeadlineExpiredException) {
        return (null, "campaign_timeout");
      } catch (Exception error) when (error is JsonException or ArgumentException or NotSupportedException) {
        return (null, "initial_heap_validation_unavailable: " + error.Message);
      }
    }

    // Admits an initial state by a certified construction plan, else by original premise consistency.
    async Task<(bool? Passed, string? Reason, bool Constructive)> CertifyInitialHeapAsync(ContractRuntimeHeapCheck initialCheck,
      string initialKey, Sample sample, ContractRuntimeTypeEvidence? runtimeTypeEvidence, int? invocation = null) {
      // Native type WD includes plain specification functions too: absence of
      // an explicit requires/ensures clause is not proof that a body is defined.
      RequireCampaignTime();
      var preparation = ContractPhaseRecorder.Measure(phases.Record, "initial_construction_scope:" + sample.Ordinal, cancellationToken,
        () => ContractInitialTypeProof.Prepare(initialCheck, specifications));
      RequireCampaignTime();
      var constructionSpecificationsValid = await ValidateSpecificationsAsync(preparation.Scope);
      RequireCampaignTime();
      if (!constructionSpecificationsValid) {
        return (null, "initial_heap_specification_unvalidated", false);
      }
      RequireCampaignTime();
      var typeProof = ContractPhaseRecorder.Measure(phases.Record, "initial_construction_plan:" + sample.Ordinal, cancellationToken,
        () => ContractInitialTypeProof.TryPrepare(preparation, specifications, runtimeTypeEvidence));
      if (typeProof is null) {
        RequireCampaignTime();
        var premise = await QueryHeapAsync(initialCheck, ContractQueryKind.PremiseConsistency, observed: false, sampleOrdinal: sample.Ordinal);
        return (premise.Outcome == ContractQueryOutcome.Sat ? true : premise.Outcome == ContractQueryOutcome.Unsat ? false : null, premise.Reason, false);
      }
      (bool? Passed, string? Reason, bool Constructive) validation;
      if (typeProof.RequiresNativeProof) {
        RequireCampaignTime();
        var membership = await QueryHeapAsync(typeProof.Initial, ContractQueryKind.ClosedClause,
          observed: false, initialTypeProof: typeProof, sampleOrdinal: sample.Ordinal);
        validation = (membership.Outcome == ContractQueryOutcome.Unsat ? true : null,
          membership.Reason ?? (membership.Outcome == ContractQueryOutcome.Unsat ? null : "initial_heap_membership_unproved"),
          membership.Outcome == ContractQueryOutcome.Unsat);
      } else {
        cancellationToken.ThrowIfCancellationRequested();
        var withinBudget = clock.ElapsedMilliseconds < request.TimeoutMilliseconds;
        validation = (withinBudget ? true : null, withinBudget ? null : "campaign_timeout", withinBudget);
      }
      await WriteJsonAsync(Path.Combine(directory, "initial-type-certificate-" + sample.Ordinal + (invocation is { } callId ? "-call-" + callId : "") + ".json"), new {
        initialKey,
        typeProof.RuntimeChecks,
        typeProof.RequiresNativeProof,
        typeProof.HostMembershipChecks,
        typeProof.IndependentGlobals,
        passed = validation.Passed,
        reason = validation.Reason,
        validation.Constructive
      });
      return validation;
    }

    // Binds the sample's entry and return captures to an original-source heap query.
    (ContractRuntimeHeapCheck? Check, string? Failure) PrepareObservedHeap(Sample sample) {
      var entryCaptures = HeapCaptures(sample.Records, "entry");
      var returnCaptures = HeapCaptures(sample.Records, "return");
      if (entryCaptures.Count != 1 || returnCaptures.Count != 1) {
        return (null, "entry_heap_capture_missing_or_duplicated");
      }
      try {
        var check = ContractRuntimeHeapChecking.Prepare(originalProgram, request, sample.Inputs,
          Decode<List<ContractHeapObject>>(entryCaptures[0].GetProperty("heap")),
          Decode<List<ContractHeapObject>>(returnCaptures[0].GetProperty("heap")),
          Decode<Dictionary<string, ContractValue>>(returnCaptures[0].GetProperty("outputs")));
        return (check, check.FrameViolation);
      } catch (Exception error) when (error is JsonException or ArgumentException or NotSupportedException) {
        return (null, "entry_heap_unavailable: " + error.Message);
      }
    }

    // Read only records preceding this checkpoint; later calls/returns cannot supply its old state.
    async Task<(ContractRuntimeHeapCheck? Check, string? Failure)> PrepareObservedCallAsync(Sample sample,
      IReadOnlyList<JsonElement> prefix, JsonElement record, ContractRuntimeClause clause,
      ContractRuntimeTypeEvidence? runtimeTypeEvidence) {
      if (!record.TryGetProperty("call_invocation", out var encodedInvocation) ||
          encodedInvocation.ValueKind != JsonValueKind.Number || !encodedInvocation.TryGetInt32(out var invocation)) {
        return (null, "call_heap_invocation_missing");
      }
      var captures = ContractRuntimeHeapChecking.MatchCallCaptures(prefix, clause.CallHeapScope!, invocation);
      if (captures == null) { return (null, "call_heap_capture_missing_or_mismatched"); }
      try {
        RequireCampaignTime();
        var original = ContractRuntimeClauseDependencies.OriginalExpression(originalProgram, request.Sources, clause);
        var callRequest = request with { Entry = new ContractEntry(clause.CallHeapScope!) };
        var inputs = Decode<Dictionary<string, ContractValue>>(captures.Value.Entry.GetProperty("inputs"));
        var initial = Decode<List<ContractHeapObject>>(captures.Value.Entry.GetProperty("heap"));
        var check = ContractRuntimeHeapChecking.Prepare(originalProgram, callRequest, inputs, initial,
          Decode<List<ContractHeapObject>>(captures.Value.Return.GetProperty("heap")),
          Decode<Dictionary<string, ContractValue>>(captures.Value.Return.GetProperty("outputs")));
        if (original == null || clause.EntryHeapPostcondition is not { } index ||
            index >= check.Prepared.Method.Ens.Count || check.Prepared.Method.Ens[index].E != original) {
          return (null, "call_heap_original_contract_unavailable");
        }
        if (check.FrameViolation != null) { return (null, check.FrameViolation); }
        var initialCheck = ContractRuntimeHeapChecking.PrepareInitial(originalProgram, callRequest, inputs, initial, specifications);
        var initialKey = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(initialCheck.Request, ContractJson.Options));
        if (!ContractQueryDeadline.TryReadCached(initialHeapCache, initialKey, RequireCampaignTime, out var validation)) {
          validation = await CertifyInitialHeapAsync(initialCheck, initialKey, sample, runtimeTypeEvidence, invocation);
          RequireCampaignTime();
          if (validation.Passed == true) { initialHeapCache.TryAdd(initialKey, validation); }
        }
        RequireCampaignTime();
        return validation.Passed == true ? (check, null) : (null, validation.Reason ?? "call_heap_initial_state_unproved");
      } catch (CampaignDeadlineExpiredException) {
        return (null, "campaign_timeout");
      } catch (Exception error) when (error is JsonException or ArgumentException or NotSupportedException) {
        return (null, "call_heap_unavailable: " + error.Message);
      }
    }

    async Task<bool> ValidateSpecificationsAsync(ContractSpecificationScope scope) {
      try {
        var key = scope.CacheIdentity;
        if (ContractQueryDeadline.TryReadCached(specificationAttempts, key, RequireCampaignTime, out var previous)) {
          var accepted = previous && specifications.Accept(scope);
          RequireCampaignTime();
          return accepted;
        }
        await WriteJsonAsync(Path.Combine(directory, "specification-scope-" + specificationAttempts.Count + ".json"),
          new { scope.Symbols, scope.Role, scope.RequiredNativeChecks, scope.Failure, modules = specifications.PendingModules(scope) });
        var success = scope.Failure == null;
        foreach (var module in success ? specifications.PendingModules(scope) : []) {
          var remaining = request.TimeoutMilliseconds - clock.ElapsedMilliseconds;
          if (closedQueries >= request.MaxClosedQueries || remaining <= 0) { success = false; break; }
          closedQueries++;
          var deadline = ContractQueryDeadline.AfterMilliseconds(Math.Min(request.ClosedQueryTimeoutMilliseconds, remaining));
          using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
          timeout.CancelAfter((int)Math.Min(request.ClosedQueryTimeoutMilliseconds, remaining));
          var path = Path.Combine(directory, "specification-query-" + closedQueries);
          var queryPhases = new ContractPhaseRecorder(path + ".phases.jsonl");
          await WriteJsonAsync(path + ".scope.json", new { module, scope.Symbols, scope.Role, scope.RequiredNativeChecks });
          try {
            var result = await specifications.CheckModuleAsync(scope, module, timeout.Token, queryPhases.Record, deadline);
            await WriteJsonAsync(path + ".result.json", result);
            if (!result.Verified) { success = false; break; }
          } catch (OperationCanceledException error) when (!cancellationToken.IsCancellationRequested) {
            queryPhases.Record("query", "cancelled");
            await WriteJsonAsync(path + ".result.json", new ContractSpecificationResult(false, error.Message, [], []));
            success = false;
            break;
          }
        }
        RequireCampaignTime();
        success = success && specifications.Accept(scope);
        RequireCampaignTime();
        specificationAttempts.Add(key, success);
        return success;
      } catch (CampaignDeadlineExpiredException) {
        return false;
      }
    }

    // A closed decision reports a violation only when the negated clause is proven for the captured values.
    async Task<(bool? Passed, string? Reason)> DecideHeapAsync(ContractRuntimeHeapCheck check, int postcondition,
      ContractRuntimeTypeEvidence? runtimeTypeEvidence, int sampleOrdinal) {
      string? stopped = null;
      var initialKey = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(check.Request, ContractJson.Options));
      // Only a source-and-value-identical native certificate can replace the initial
      // consistency query. A host-only field check never creates this cache entry.
      if (!ContractQueryDeadline.TryReadCached(initialHeapCache, initialKey, RequireCampaignTime, out var initialValidation) || initialValidation.Passed != true) {
        var premise = await Query(ContractQueryKind.PremiseConsistency, observed: false);
        if (premise != ContractQueryOutcome.Sat) { return (null, stopped ?? "entry_heap_premise_undecided"); }
      }
      if (check.Prepared.Method.Req.Count > 0) {
        var precondition = await Query(ContractQueryKind.EntryPrecondition, observed: false);
        if (precondition != ContractQueryOutcome.Unsat) { return (null, stopped ?? "entry_heap_precondition_undecided"); }
      }
      ContractInitialTypeProof? observedProof = null;
      if (initialValidation is { Passed: true, Constructive: true }) {
        if (!await ValidateSpecificationsAsync(ContractInitialTypeProof.RequiredObservedScope(originalProgram, check, specifications))) {
          return (null, "observed_heap_specification_unvalidated");
        }
        observedProof = ContractInitialTypeProof.TryPrepareObserved(originalProgram, check, specifications, runtimeTypeEvidence);
      }
      if (observedProof != null) {
        var passed = true;
        string? reason = null;
        if (observedProof.RequiresNativeProof) {
          var membership = await QueryHeapAsync(check, ContractQueryKind.ClosedClause,
            initialTypeProof: observedProof, sampleOrdinal: sampleOrdinal);
          passed = membership.Outcome == ContractQueryOutcome.Unsat;
          reason = membership.Reason;
        }
        cancellationToken.ThrowIfCancellationRequested();
        passed &= clock.ElapsedMilliseconds < request.TimeoutMilliseconds;
        if (!passed) { reason ??= "observed_heap_membership_unproved_or_expired"; }
        await WriteJsonAsync(Path.Combine(directory, "observed-type-certificate-" + sampleOrdinal + (check.Request.Entry.Symbol != request.Entry.Symbol ? "-call-" + ++callObservedCertificates : "") + ".json"), new {
          initialKey,
          initialValidation.Constructive,
          observedKey = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(new { check.Request, check.Observations, check.Outputs }, ContractJson.Options)),
          observedProof.RuntimeChecks,
          observedProof.RequiresNativeProof,
          observedProof.HostMembershipChecks,
          observedProof.IndependentGlobals,
          passed,
          reason
        });
        if (!passed) { return (null, reason); }
      } else {
        var observation = await Query(ContractQueryKind.PremiseConsistency);
        if (observation != ContractQueryOutcome.Sat) { return (null, stopped ?? "entry_heap_observation_inconsistent_or_undecided"); }
      }
      var holds = await Query(ContractQueryKind.ObservedPostcondition);
      if (holds == ContractQueryOutcome.Unsat) { return (true, null); }
      if (holds == ContractQueryOutcome.Error || stopped != null) { return (null, stopped ?? "closed_query_error"); }
      var fails = await Query(ContractQueryKind.ObservedPostcondition, negate: true);
      return fails == ContractQueryOutcome.Unsat ? (false, null) : (null, stopped ?? "closed_query_undecided");

      async Task<ContractQueryOutcome> Query(ContractQueryKind kind, bool observed = true, bool negate = false) {
        var result = await QueryHeapAsync(check, kind, observed, negate, postcondition, sampleOrdinal: sampleOrdinal);
        stopped ??= result.Reason;
        return result.Outcome;
      }
    }

    async Task<(ContractQueryOutcome Outcome, string? Reason)> QueryHeapAsync(ContractRuntimeHeapCheck check,
      ContractQueryKind kind, bool observed = true, bool negate = false, int? postcondition = null,
      ContractInitialTypeProof? initialTypeProof = null, int? sampleOrdinal = null) {
      cancellationToken.ThrowIfCancellationRequested();
      var budget = request.TimeoutMilliseconds - clock.ElapsedMilliseconds;
      if (budget <= 0) { return (ContractQueryOutcome.Timeout, "campaign_timeout"); }
      var deadline = ContractQueryDeadline.AfterMilliseconds(Math.Min(request.ClosedQueryTimeoutMilliseconds, budget));
      using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      timeout.CancelAfter((int)Math.Min(request.ClosedQueryTimeoutMilliseconds, budget));
      var role = initialTypeProof == null ? (observed ? "observed_heap" : "initial_heap") :
        initialTypeProof.Observed ? "observed" : "initial";
      string? query = null;
      string? identityMaterial = null;
      ContractNativeFactIdentity? identity = null;
      IReadOnlyList<ContractSource>? membershipSources = null;
      string? identitySha256 = null;
      string? querySha256 = null;
      string? sourceSetSha256 = null;
      NotSupportedException? constructionError = null;
      {
        try {
          query = initialTypeProof != null ? initialTypeProof.BuildQuery() :
            ContractQueryBuilder.Build(check.Prepared, check.Request, kind,
              observed ? check.Outputs : null, negate, observed ? check.Observations : null,
              choiceConstraints: check.InitialTypeConstraints,
              postconditionClause: postcondition is { } index ? check.Prepared.Method.Ens[index].E : null);
          membershipSources = check.Prepared.DiagnosticSourceSnapshots;
          var sources = membershipSources.Select(source => new ContractNativeFactSource(
            source.Path, ContractSourceSnapshot.UriFor(source.Path).AbsoluteUri, source.Content)).ToList();
          identity = new(query, sources, check.Prepared.Source.Path,
            ContractSourceSnapshot.UriFor(check.Prepared.Source.Path).AbsoluteUri,
            ContractQueryBuilder.Name(check.Prepared));
          identityMaterial = identity.Material(kind);
          identitySha256 = ContractHarnessBuilder.Hash(identityMaterial);
          querySha256 = ContractHarnessBuilder.Hash(identity.Query);
          sourceSetSha256 = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(identity.Sources, ContractJson.Options));
        } catch (NotSupportedException error) {
          constructionError = error;
        }
        MembershipProof? proof = null;
        var reused = false;
        if (identityMaterial != null) {
          try {
            reused = membershipProofs.TryReuse(identity!, kind, timeout.Token, deadline, out proof);
          } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
            return (ContractQueryOutcome.Timeout, "closed_query_timeout");
          }
        }
        if (reused) {
          var reusedProof = proof!;
          var reusedIdentity = identity!;
          if (QueryExpired()) { return (ContractQueryOutcome.Timeout, "closed_query_timeout"); }
          if (sampleOrdinal == null) {
            throw new ArgumentException("Membership proof reuse requires the current sample ordinal.", nameof(sampleOrdinal));
          }
          var receiptOrdinal = membershipReuseReceipts + 1;
          var receiptPath = Path.Combine(directory,
            (initialTypeProof != null ? "membership-proof-reuse-" + role : "heap-fact-reuse") + "-" + sampleOrdinal + "-" + receiptOrdinal + ".json");
          var pendingReceiptPath = receiptPath + ".pending";
          var receipt = JsonSerializer.Serialize(new {
            kind = initialTypeProof != null ? "native_membership_proof_reuse" : "native_heap_fact_reuse",
            queryKind = kind,
            receiptOrdinal,
            sampleOrdinal,
            role,
            identitySha256,
            querySha256,
            sourceSetSha256,
            reusedIdentity.SourcePath,
            reusedIdentity.CanonicalSourcePath,
            reusedIdentity.QueryName,
            originalProof = reusedProof
          }, ContractJson.Options);
          try {
            await File.WriteAllTextAsync(pendingReceiptPath, receipt, timeout.Token);
            ContractQueryDeadline.Check(deadline, timeout.Token);
          } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
            return (ContractQueryOutcome.Timeout, "closed_query_timeout");
          }
          File.Move(pendingReceiptPath, receiptPath);
          membershipReuseReceipts = receiptOrdinal;
          return (reusedProof.Outcome, null);
        }
        if (closedQueries >= request.MaxClosedQueries) {
          return (ContractQueryOutcome.Unknown, "closed_query_budget_exhausted");
        }
      }
      closedQueries++;
      var queryPath = Path.Combine(directory, (initialTypeProof == null ? "heap-query-" : role + "-type-query-") + closedQueries);
      var queryPhases = new ContractPhaseRecorder(queryPath + ".phases.jsonl");
      try {
        ContractQueryDeadline.Check(deadline, timeout.Token);
        if (constructionError != null) {
          await WriteJsonAsync(queryPath + ".result.json", new ContractQueryResult(kind, ContractQueryOutcome.Unknown, constructionError.Message));
          return (ContractQueryOutcome.Unknown, "entry_heap_unavailable: " + constructionError.Message);
        }
        if (query == null) {
          try {
            query = ContractQueryBuilder.Build(check.Prepared, check.Request, kind,
              observed ? check.Outputs : null, negate, observed ? check.Observations : null,
              choiceConstraints: check.InitialTypeConstraints,
              postconditionClause: postcondition is { } index ? check.Prepared.Method.Ens[index].E : null);
          } catch (NotSupportedException error) {
            await WriteJsonAsync(queryPath + ".result.json", new ContractQueryResult(kind, ContractQueryOutcome.Unknown, error.Message));
            return (ContractQueryOutcome.Unknown, "entry_heap_unavailable: " + error.Message);
          }
        }
        await File.WriteAllTextAsync(queryPath + ".dfy", query, cancellationToken);
        var result = await ContractSolver.CheckAsync(query, kind, ClosedQueryOptions(), timeout.Token,
          queryName: identity?.QueryName ?? ContractQueryBuilder.Name(check.Prepared),
          sourceSnapshots: membershipSources ?? check.Prepared.DiagnosticSourceSnapshots,
          sourcePath: check.Prepared.Source.Path,
          phaseObserver: queryPhases.Record, deadlineTimestamp: deadline);
        var resultJson = JsonSerializer.Serialize(result, ContractJson.Options);
        await File.WriteAllTextAsync(queryPath + ".result.json", resultJson, cancellationToken);
        if (identityMaterial != null) {
          var resultSha256 = ContractHarnessBuilder.Hash(resultJson);
          if (QueryExpired()) { return (ContractQueryOutcome.Timeout, "closed_query_timeout"); }
          var completedIdentity = identity!;
          membershipProofs.Record(identity!, kind, result.Outcome, new(
            identitySha256!, querySha256!, sourceSetSha256!,
            completedIdentity.SourcePath, completedIdentity.CanonicalSourcePath, completedIdentity.QueryName,
            role, sampleOrdinal ?? -1,
            Path.GetFileName(queryPath + ".dfy"), Path.GetFileName(queryPath + ".result.json"),
            resultSha256, result.Outcome), timeout.Token, deadline);
        }
        return (result.Outcome, result.Outcome == ContractQueryOutcome.Timeout ? "closed_query_timeout" :
          result.Outcome == ContractQueryOutcome.Error ? "closed_query_error" : null);
      } catch (OperationCanceledException error) when (!cancellationToken.IsCancellationRequested) {
        queryPhases.Record("query", "cancelled");
        await WriteJsonAsync(queryPath + ".result.json", new ContractQueryResult(kind, ContractQueryOutcome.Timeout, error.Message));
        return (ContractQueryOutcome.Timeout, "closed_query_timeout");
      }

      bool QueryExpired() {
        try {
          ContractQueryDeadline.Check(deadline, timeout.Token);
          return false;
        } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
          return true;
        }
      }
    }

    async Task<(bool? Passed, string? Reason)> DecideClosedAsync(ContractRuntimeClause clause, IReadOnlyDictionary<string, ContractValue> values) {
      var originalClause = ContractRuntimeObligationTransformer.BindOriginalOwner(originalProgram, clause);
      if (originalClause == null) { return (null, "closed_query_original_owner_unavailable"); }
      clause = originalClause;
      var holds = await QueryAsync(clause, values, false);
      if (holds == ContractQueryOutcome.Unsat) { return (true, null); }
      var fails = holds == ContractQueryOutcome.Error ? ContractQueryOutcome.Error : await QueryAsync(clause, values, true);
      if (fails == ContractQueryOutcome.Unsat) { return (false, null); }
      return (null, holds == ContractQueryOutcome.Timeout || fails == ContractQueryOutcome.Timeout ? "closed_query_timeout" :
        holds == ContractQueryOutcome.Error || fails == ContractQueryOutcome.Error ? "closed_query_error" : "closed_query_undecided");
    }

    // Unsat means the asserted formula is proven under the value bindings.
    async Task<ContractQueryOutcome> QueryAsync(ContractRuntimeClause clause, IReadOnlyDictionary<string, ContractValue> values, bool negate) {
      var budget = request.TimeoutMilliseconds - clock.ElapsedMilliseconds;
      if (budget <= 0) { return ContractQueryOutcome.Timeout; }
      var deadline = ContractQueryDeadline.AfterMilliseconds(Math.Min(request.ClosedQueryTimeoutMilliseconds, budget));
      using var queryTimeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      queryTimeout.CancelAfter((int)Math.Min(request.ClosedQueryTimeoutMilliseconds, budget));
      var path = Path.Combine(directory, "closed-query-" + closedQueries + (negate ? "-negative" : "-positive"));
      var queryPhases = new ContractPhaseRecorder(path + ".phases.jsonl");
      try {
        var source = ContractQueryBuilder.BuildClosedClause(originalPrepared, clause, values, negate);
        await File.WriteAllTextAsync(path + ".dfy", source, cancellationToken);
        var query = await ContractSolver.CheckAsync(source,
          ContractQueryKind.ClosedClause, ClosedQueryOptions(), queryTimeout.Token, queryName: ContractQueryBuilder.Name(originalPrepared),
          sourceSnapshots: originalPrepared.SourceSnapshots,
          sourcePath: ContractSourceSnapshot.Find(originalPrepared.SourceSnapshots, clause.Owner.Origin.Uri).Path,
          phaseObserver: queryPhases.Record, deadlineTimestamp: deadline);
        await WriteJsonAsync(path + ".result.json", query);
        return query.Outcome;
      } catch (OperationCanceledException error) when (!cancellationToken.IsCancellationRequested) {
        queryPhases.Record("query", "cancelled");
        await WriteJsonAsync(path + ".result.json", new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Timeout, error.Message));
        return ContractQueryOutcome.Timeout;
      }
    }
  }

  private static bool GoalKind(ContractRuntimeObligationKind kind) => kind is ContractRuntimeObligationKind.Postcondition or
    ContractRuntimeObligationKind.LoopInvariantEntry or ContractRuntimeObligationKind.LoopInvariantMaintenance or ContractRuntimeObligationKind.CallPrecondition;

  private sealed record Sample(int Ordinal, IReadOnlyDictionary<string, ContractValue> Inputs,
    IReadOnlyList<JsonElement> Records, bool Timeout, bool Error, string Diagnostics, bool Truncated, int? FirstMalformedRecord);

  private static string? Kind(JsonElement record) => record.GetProperty("kind").GetString();

  private static T Decode<T>(JsonElement value) => JsonSerializer.Deserialize<T>(value.GetRawText(), ContractJson.Options)!;

  private static Dictionary<string, ContractValue> SampleInputs(IEnumerable<JsonElement> records) =>
    records.Where(record => Kind(record) == "input")
      .ToDictionary(record => record.GetProperty("name").GetString()!, record => Decode<ContractValue>(record.GetProperty("value")));

  private static List<JsonElement> HeapCaptures(IEnumerable<JsonElement> records, string phase) =>
    records.Where(record => Kind(record) == "heap_capture" && record.GetProperty("phase").GetString() == phase).ToList();

  // A failed runtime loop invariant is a complete safety counterexample; later records are not needed.
  private static int CounterexamplePrefixLength(Sample sample, IReadOnlyDictionary<string, ContractRuntimeObligation> obligations) {
    for (var index = 0; index < (sample.FirstMalformedRecord ?? sample.Records.Count); index++) {
      var record = sample.Records[index];
      if (Kind(record) == "check" && !record.GetProperty("passed").GetBoolean() &&
          obligations.TryGetValue(record.GetProperty("id").GetString()!, out var endpoint) &&
          endpoint.DecisionMethod == ContractRuntimeDecisionMethod.Runtime &&
          endpoint.Kind is ContractRuntimeObligationKind.LoopInvariantEntry or ContractRuntimeObligationKind.LoopInvariantMaintenance) {
        return index + 1;
      }
    }
    return 0;
  }
  private static string Diagnostics(BatchErrorReporter reporter) => string.Join("\n", reporter.AllMessages.Where(m => m.Level == ErrorLevel.Error).Select(m => m.Range.StartToken.Uri + ":" + m.Range.StartToken.line + ":" + m.Range.StartToken.col + ": " + m.Message));

  // Prepared-snapshot positions are reported at their supplied source, draft or generator location when known.
  private static string Diagnostics(BatchErrorReporter reporter, ContractRuntimeSourceMap map) {
    return string.Join("\n", reporter.AllMessages.Where(m => m.Level == ErrorLevel.Error).Select(m => Location(m.Range.StartToken) + ": " + m.Message));
    string Location(Token token) {
      try {
        var location = map.ResolveLocation(token.Uri, token.pos);
        return location.Path + ":" + location.Line + ":" + location.Column;
      } catch (ArgumentException) {
        return token.Uri + ":" + token.line + ":" + token.col;
      }
    }
  }

  private static IReadOnlyList<ContractRuntimeMissingDraft> MissingDrafts(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, IReadOnlyList<ContractRuntimeDraft> drafts, ContractRuntimeSourceMap? sourceMap = null) {
    var supplied = drafts.Select(d => d.Symbol).ToHashSet();
    // A function-by-method descriptor is detached from the call graph; its original function reaches the by-method body.
    var root = goal.FunctionFromWhichThisIsByMethodDecl ?? (MethodOrFunction)goal;
    return ContractRuntimeObligationTransformer.ExecutionReachable(program, [root])
      .Where(c => c != root && c != goal && c != (root as Function)?.ByMethodDecl && (!c.IsGhost || c is Function) &&
        !supplied.Contains(c.FullDafnyName) && c.EnclosingClass.EnclosingModuleDefinition.Name is not ("PbtRuntime" or "PbtRandom") &&
        // Built-in and library declarations outside the supplied snapshot cannot be drafted.
        sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == c.Origin.Uri))
      .Where(c => c is Method m && (m.Body == null || m.Body.Body is [AssertStmt { Expr.Resolved: LiteralExpr { Value: false } }]) || c is Function { Body: null })
      // A bodyless trait member dispatches to class overrides, which are reachable and checked themselves.
      .Where(c => !(c.EnclosingClass is TraitDecl && !c.IsStatic && (c is Function || ((Method)c).Body == null)))
      .Select(c => {
        var source = ContractSourceSnapshot.Find(sources, c.Origin.Uri);
        // Declarations reached after draft/generator insertion are reported at their supplied original location.
        var location = sourceMap?.ResolveLocation(c.Origin.Uri, c.Origin.pos);
        return new ContractRuntimeMissingDraft(c.FullDafnyName,
          c is Function ? ContractRuntimeDraftKind.Function : Attributes.Contains(c.Attributes, "extern") ? ContractRuntimeDraftKind.ExternMethod : ContractRuntimeDraftKind.Method,
          location?.Path ?? source.Path, location?.Line ?? c.Origin.line, OriginalSignature(c, source),
          string.Join("\n", c.Req.Select(r => "requires " + Printer.ExprToString(program.Options, r.E)).Concat(c.Ens.Select(e => "ensures " + Printer.ExprToString(program.Options, e.E)))));
      }).ToList();
  }

  private static string OriginalSignature(MethodOrFunction callable, ContractSource source) {
    var end = callable.EndToken.pos + callable.EndToken.val.Length;
    var token = callable.StartToken;
    while (token != null && token.pos < end) {
      if (token.val is "requires" or "ensures" or "reads" or "modifies" or "decreases" ||
          callable is MethodOrConstructor { Body: { } body } && token.pos == body.StartToken.pos ||
          callable is Function { Body: { } expression } && token.pos == expression.StartToken.pos - 1) {
        end = token.pos; break;
      }
      token = token.Next;
    }
    var bytes = System.Text.Encoding.UTF8.GetBytes(source.Content);
    return System.Text.Encoding.UTF8.GetString(bytes, callable.StartToken.pos, end - callable.StartToken.pos).Trim();
  }

  private static void Validate(ContractRuntimeCampaignRequest request) {
    if (request.SchemaVersion != 1 || request.Sources == null || request.Sources.Count == 0 || request.Entry == null ||
        !ulong.TryParse(request.Seed, NumberStyles.None, CultureInfo.InvariantCulture, out _) || request.SampleCount <= 0 ||
        request.SampleTimeoutMilliseconds <= 0 || request.TimeoutMilliseconds <= 0 || request.MaxClosedQueries < 0 ||
        request.ClosedQueryTimeoutMilliseconds <= 0 || request.MaxViolationsPerObligation <= 0 || request.ReplayOrdinal < 0) {
      throw new ArgumentException("Invalid runtime campaign schema, seed, sources, entry, or budgets.");
    }
    var files = request.Sources.Concat((request.Drafts ?? []).Select(d => new ContractSource(d.Path, d.Content, d.Sha256)))
      .Concat(request.Generator == null ? [] : [request.Generator]).ToList();
    if (files.Any(f => f == null || string.IsNullOrWhiteSpace(f.Path) || Path.IsPathRooted(f.Path) ||
          f.Path.Replace('\\', '/').Split('/').Any(part => part is ".." or ".") || f.Content == null || ContractHarnessBuilder.Hash(f.Content) != f.Sha256) ||
        files.Select(f => ContractSourceSnapshot.UriFor(f.Path)).Distinct().Count() != files.Count) {
      throw new ArgumentException("Runtime source, draft, and generator paths must be distinct and hashes must match.");
    }
  }
}
