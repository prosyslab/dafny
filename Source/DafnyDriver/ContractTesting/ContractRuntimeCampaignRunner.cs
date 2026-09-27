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
  public static ContractRuntimeCampaignResult Failure(ContractRuntimeStatus status, string reason, string seed = "") =>
    new(ContractJson.SchemaVersion, status, reason, seed, new(), [], [], [], [], null, [], []);

  public static async Task<ContractRuntimeCampaignResult> RunAsync(ContractRuntimeCampaignRequest request,
    DafnyOptions options, string directory, CancellationToken cancellationToken) {
    Validate(request);
    var clock = Stopwatch.StartNew();
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    // The detached diagnostic may use any declaration; this reveals every export instead of rewriting export text.
    options.DisableScopes = true;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, cancellationToken);
    if (reporter.ErrorCount > 0) { return Failure(ContractRuntimeStatus.Error, Diagnostics(reporter), request.Seed); }
    var goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false);
    if (goal.FunctionFromWhichThisIsByMethodDecl is { ByMethodBody: null } || goal.Body == null) {
      return Failure(ContractRuntimeStatus.Unsupported, "Runtime goals require an implemented method or function-by-method.", request.Seed);
    }
    var source = ContractSourceSnapshot.Find(request.Sources, goal.Origin.Uri);
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
    var sourcePreparation = await ContractRuntimeSourcePreparation.PrepareAsync(program, request.Sources, goal,
      request.Drafts ?? [], request.Generator!, options, cancellationToken);
    var visibilityReporter = new BatchErrorReporter(options);
    var visibilityProgram = await ContractSourceSnapshot.ParseAsync(visibilityReporter, sourcePreparation.Sources, cancellationToken, resolve: false);
    if (visibilityReporter.ErrorCount > 0) { return Failure(ContractRuntimeStatus.Unsupported, Diagnostics(visibilityReporter), request.Seed); }
    var runtimeSource = ContractRuntimeInstrumentation.DafnySource;
    var snapshots = ContractRuntimeObligationTransformer.MakeGeneratorVisible(visibilityProgram, sourcePreparation.Sources, new HashSet<string>()).ToList();
    snapshots.Add(new("PbtRuntime.dfy", runtimeSource, ContractHarnessBuilder.Hash(runtimeSource)));
    // Resolve names before changing ghostness, so unrelated logical constructors stay untouched.
    // This pass may report ghost-context errors in the generator; the final resolve must be clean.
    var reachabilityReporter = new BatchErrorReporter(options);
    var reachabilityProgram = await ContractSourceSnapshot.ParseAsync(reachabilityReporter, snapshots, cancellationToken);
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "reachability-diagnostics.txt"), Diagnostics(reachabilityReporter), cancellationToken);
    if (reachabilityProgram.ModuleSigs == null) {
      return Failure(ContractRuntimeStatus.Unsupported, "Generator parsing failed: " + Diagnostics(reachabilityReporter), request.Seed);
    }
    // An error in an imported module (for example a draft body that uses ghost state) leaves the modules that depend
    // on it unresolved; their members then have no enclosing class. The goal is looked up only among resolved members,
    // and an unresolved goal module is reported with the resolver diagnostics instead of being searched.
    var goalName = (goal.FunctionFromWhichThisIsByMethodDecl ?? (MemberDecl)goal).FullDafnyName;
    var reachabilityGoals = ContractRuntimeObligationTransformer.Members(reachabilityProgram)
      .Where(m => m.EnclosingClass != null && m.FullDafnyName == goalName).OfType<MethodOrFunction>().ToList();
    if (reachabilityGoals.Count != 1) {
      return Failure(ContractRuntimeStatus.Unsupported, "Draft or generator resolution failed before the goal module resolved: " +
        Diagnostics(reachabilityReporter, sourcePreparation.SourceMap), request.Seed);
    }
    var constructors = ContractRuntimeObligationTransformer.DiagnosticReachable(reachabilityProgram, reachabilityGoals[0],
        reachabilityGoals[0].EnclosingClass.EnclosingModuleDefinition).OfType<Constructor>().Select(c => c.FullDafnyName).ToHashSet();
    snapshots = ContractRuntimeObligationTransformer.MakeGeneratorVisible(visibilityProgram, sourcePreparation.Sources, constructors).ToList();
    snapshots.Add(new("PbtRuntime.dfy", runtimeSource, ContractHarnessBuilder.Hash(runtimeSource)));
    reporter = new BatchErrorReporter(options);
    program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, cancellationToken);
    if (reporter.ErrorCount > 0) { return Failure(ContractRuntimeStatus.Unsupported, "Generator resolution failed: " + Diagnostics(reporter, sourcePreparation.SourceMap), request.Seed); }
    goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false);
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
      transformation = new ContractRuntimeObligationTransformer(program, snapshots, goal, sourcePreparation.SourceMap, rejectedDeclarations, decisionCaps).Transform();
      Directory.CreateDirectory(directory);
      await File.WriteAllTextAsync(Path.Combine(directory, "transformed-sources.json"), JsonSerializer.Serialize(transformation.Sources, ContractJson.Options), cancellationToken);
      await File.WriteAllTextAsync(Path.Combine(directory, "transformed-sources-" + attempt + ".json"), JsonSerializer.Serialize(transformation.Sources, ContractJson.Options), cancellationToken);
      var transformedReporter = new BatchErrorReporter(options);
      var transformedProgram = await ContractSourceSnapshot.ParseAsync(transformedReporter, transformation.Sources, cancellationToken);
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
        var marker = line?.IndexOf("PbtBridge.Check(\"", StringComparison.Ordinal) ?? -1;
        if (marker >= 0) {
          var literal = line![(marker + "PbtBridge.Check(\"".Length)..];
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
    var compile = await ContractCompilerWorker.CompileRuntimeAsync(transformation, request, directory, options, cancellationToken);
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
      var execution = await ContractExecutionProcess.RunAsync("dotnet", [compile.AssemblyPath!,
        "--pbt-seed",
        request.Seed,
        "--pbt-ordinal",
        ordinal.ToString(CultureInfo.InvariantCulture),
        "--pbt-out",
        observationPath], directory, timeout.Token);
      var records = new List<JsonElement>();
      var truncated = false;
      foreach (var line in (await File.ReadAllLinesAsync(observationPath, cancellationToken)).Where(l => l.Length > 0)) {
        try {
          records.Add(JsonDocument.Parse(line).RootElement.Clone());
        } catch (JsonException) {
          // A sample killed while appending leaves a partial final record; it invalidates only that sample.
          truncated = true;
        }
      }
      var inputs = records.Where(r => r.GetProperty("kind").GetString() == "input").ToDictionary(r => r.GetProperty("name").GetString()!,
        r => JsonSerializer.Deserialize<ContractValue>(r.GetProperty("value").GetRawText(), ContractJson.Options)!);
      samples.Add(new(ordinal, inputs, records, execution.Cancelled, execution.ExitCode != 0, execution.StandardError, truncated));
    }
    var queryCache = new Dictionary<string, (bool? Passed, string? Reason)>();
    var closedQueries = 0;
    var decidedGoalEvaluations = 0;
    foreach (var sample in samples) {
      var kinds = sample.Records.Select(r => r.GetProperty("kind").GetString()).ToHashSet();
      var complete = kinds.Contains("complete");
      if (kinds.Contains("generated")) { population = population with { Generated = population.Generated + 1 }; }
      if (kinds.Contains("executed")) { population = population with { Executed = population.Executed + 1 }; }
      var stoppedAtCall = false; var rejected = kinds.Contains("rejected"); var uncheckedPrecondition = false; var badCallee = false; var uncheckedCallee = false;
      var pending = new List<ContractRuntimeViolation>();
      var failed = new List<ContractRuntimeObligation>();
      var decided = 0;
      foreach (var record in sample.Records.Where(r => r.GetProperty("kind").GetString() is "check" or "checkpoint")) {
        var id = record.GetProperty("id").GetString()!;
        var obligation = obligations[id];
        var clause = clauses[id];
        var isRuntime = record.GetProperty("kind").GetString() == "check";
        var passed = isRuntime ? record.GetProperty("passed").GetBoolean() : (bool?)null;
        var values = JsonSerializer.Deserialize<Dictionary<string, ContractValue>>(record.GetProperty("values").GetRawText(), ContractJson.Options)!;
        string? uncheckedReason = obligation.UncheckedReason;
        if (!isRuntime && obligation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt) {
          var cacheKey = id + ":" + ContractHarnessBuilder.Hash(record.GetProperty("values").GetRawText());
          if (!queryCache.TryGetValue(cacheKey, out var decision)) {
            if (closedQueries >= request.MaxClosedQueries) {
              decision = (null, "closed_query_budget_exhausted");
            } else if (clock.ElapsedMilliseconds >= request.TimeoutMilliseconds) {
              decision = (null, "campaign_timeout");
            } else {
              closedQueries++;
              decision = await DecideClosedAsync(clause, values);
            }
            queryCache.Add(cacheKey, decision);
          }
          passed = decision.Passed; uncheckedReason = decision.Reason;
          if (passed != null && clause.UnvalidatedCallees && (obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition || (passed == false ? GoalKind(obligation.Kind) : obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition))) {
            // Solver evaluation uses function bodies without checking their own contracts, so a clause that could
            // indict the goal (or admit an input) through an unvalidated callee stays undecided.
            passed = null; uncheckedReason = "callee_contract_unvalidated";
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
          if (passed == false) { calleeViolations.Add(new(id, obligation.Callee!, request.Drafts?.Any(d => d.Symbol == obligation.Callee) == true, sample.Ordinal, sample.Inputs, values)); }
        } else if (passed == false) {
          var iteration = record.GetProperty("iteration").GetInt32();
          pending.Add(new(id, obligation.Kind, sample.Ordinal, iteration < 0 ? null : iteration,
            isRuntime ? ContractRuntimeDecisionMethod.Runtime : ContractRuntimeDecisionMethod.ClosedSmt, sample.Inputs, values));
          if (obligation.Kind == ContractRuntimeObligationKind.CallPrecondition) { stoppedAtCall = true; break; }
        }
      }
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
      } else if (sample.Timeout && !complete && !stoppedAtCall) {
        // A sample that already recorded completion is not recounted as a timeout because of process teardown.
        population = population with { Timeouts = population.Timeouts + 1 }; AddError("sample_timeout");
      } else if (sample.Truncated || !complete) {
        population = population with { RuntimeErrors = population.RuntimeErrors + 1 }; var error = sample.Records.LastOrDefault(r => r.GetProperty("kind").GetString() == "runtime_error");
        AddError(sample.Truncated ? "truncated observation record" : error.ValueKind == JsonValueKind.Undefined ? sample.Diagnostics : error.GetProperty("message").GetString()!,
          error.ValueKind == JsonValueKind.Undefined ? null : error.GetProperty("location").GetString());
      } else {
        population = population with { Valid = population.Valid + 1, ViolatingSamples = population.ViolatingSamples + (pending.Count > 0 ? 1 : 0) };
        violations.AddRange(pending);
        decidedGoalEvaluations += decided;
        counted = GoalKind;
      }
      foreach (var failure in failed.Where(f => counted(f.Kind))) {
        obligations[failure.Id] = obligations[failure.Id] with { Violations = obligations[failure.Id].Violations + 1 };
      }
      void AddError(string message, string? location = null) { if (errors.Count < 20) { errors.Add(new(sample.Ordinal, message, location)); } }
    }
    // Valid samples support "no violation" only when at least one goal obligation was actually decided in them.
    var status = population.ViolatingSamples > 0 ? ContractRuntimeStatus.ViolationFound :
      population.Valid > 0 && decidedGoalEvaluations > 0 ? ContractRuntimeStatus.NoViolationFound : ContractRuntimeStatus.Inconclusive;
    var reason = status != ContractRuntimeStatus.Inconclusive ? "" :
      population.Valid == 0 ? "No valid sample completed." : "No goal obligation was decided in a valid sample.";
    return new(1, status, reason, request.Seed, population, obligations.Values.ToList(),
      violations.GroupBy(v => v.ObligationId).SelectMany(g => g.OrderBy(v => JsonSerializer.Serialize(v.Inputs, ContractJson.Options).Length)
        .ThenBy(v => v.SampleOrdinal).Take(request.MaxViolationsPerObligation)).ToList(), calleeViolations, [], null, transformation.Exclusions, errors);

    // A closed decision reports a violation only when the negated clause is proven for the captured values.
    async Task<(bool? Passed, string? Reason)> DecideClosedAsync(ContractRuntimeClause clause, IReadOnlyDictionary<string, ContractValue> values) {
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
      using var queryTimeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      queryTimeout.CancelAfter((int)Math.Min(request.ClosedQueryTimeoutMilliseconds, budget));
      try {
        var query = await ContractSolver.CheckAsync(ContractQueryBuilder.BuildClosedClause(transformation.Prepared, clause, values, negate),
          ContractQueryKind.ClosedClause, new DafnyOptions(options) { TimeLimit = (uint)Math.Max(1, (request.ClosedQueryTimeoutMilliseconds + 999) / 1000) }, queryTimeout.Token, queryName: ContractQueryBuilder.Name(transformation.Prepared),
          sourceSnapshots: transformation.Prepared.SourceSnapshots,
          sourcePath: ContractSourceSnapshot.Find(transformation.Prepared.SourceSnapshots, clause.Owner.Origin.Uri).Path);
        return query.Outcome;
      } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
        return ContractQueryOutcome.Timeout;
      }
    }
  }

  private static bool GoalKind(ContractRuntimeObligationKind kind) => kind is ContractRuntimeObligationKind.Postcondition or
    ContractRuntimeObligationKind.LoopInvariantEntry or ContractRuntimeObligationKind.LoopInvariantMaintenance or ContractRuntimeObligationKind.CallPrecondition;

  private sealed record Sample(int Ordinal, IReadOnlyDictionary<string, ContractValue> Inputs,
    IReadOnlyList<JsonElement> Records, bool Timeout, bool Error, string Diagnostics, bool Truncated);
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
