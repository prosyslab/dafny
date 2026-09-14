using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Fairly composes independent precondition, actual-body and specification input goals.</summary>
public static class ContractInputGenerator {
  private sealed record Goal(string Id, ContractInputGoalKind Kind, string? Constraint,
    ContractBodyGoal? Body = null, string? Unsupported = null);
  private sealed record CandidateRecheck(ContractQueryResult Premise, ContractQueryResult Property) {
    public bool IsValid => Premise.Outcome == ContractQueryOutcome.Sat &&
                           Property.Outcome == ContractQueryOutcome.Unsat;
  }
  private sealed record RefinementQuerySource(string Content, string Path);

  public static void ValidateRequest(ContractGenerationRequest request) {
    if (request.SchemaVersion != ContractJson.SchemaVersion || request.Sources == null || request.Sources.Count == 0 ||
        request.Entry == null || string.IsNullOrWhiteSpace(request.Entry.Symbol) || request.TimeoutMilliseconds <= 0) {
      throw new ArgumentException("Generation requires schema version 1, immutable source snapshots, an entry and a positive deadline.");
    }
    if (request.Entry.InputMode == ContractInputMode.EntryReachable
          ? string.IsNullOrWhiteSpace(request.Entry.ReachableFrom) || request.Entry.Receiver != null || request.Entry.ReachableInvocation < 0
          : request.Entry.ReachableFrom != null || request.Entry.ReachableReceiver != null || request.Entry.ReachableInvocation != 0) {
      throw new ArgumentException("Reachable generation requires an outer symbol, no unit receiver and a nonnegative invocation.");
    }
    var bounds = request.Bounds ?? new();
    if (bounds.MaxInputs <= 0 || bounds.MaxSequenceLength < 0 || bounds.MaxDatatypeDepth < 0 || bounds.MaxHeapObjects < 0 ||
        bounds.MaxCallDepth < 0 || bounds.MaxLoopIterations < 0 || bounds.MaxGoals <= 0) {
      throw new ArgumentException("Generation bounds must be nonnegative and input/goal limits positive.");
    }
    foreach (var source in request.Sources) {
      if (string.IsNullOrWhiteSpace(source.Path) || source.Content == null || ContractHarnessBuilder.Hash(source.Content) != source.Sha256) {
        throw new ArgumentException("Generation source snapshot hash mismatch.");
      }
    }
    if ((request.CandidateInputs == null) != (request.RequiredGoalId == null)) {
      throw new ArgumentException("Candidate reduction rechecks require both candidateInputs and requiredGoalId.");
    }
    foreach (var value in request.CandidateInputs?.Values ?? []) {
      ContractModelCodec.Validate(value);
    }
    if (request.GenerationStrategy == ContractGenerationStrategy.SolverGoals) {
      if (request.PatternCampaign != null || request.CampaignFeedback != null) {
        throw new ArgumentException("solver_goals generation does not accept a patternCampaign or campaignFeedback.");
      }
    } else if (request.GenerationStrategy == ContractGenerationStrategy.InputPatterns) {
      if (request.PatternCampaign == null || request.CandidateInputs != null || request.RequiredGoalId != null ||
          request.CandidateHeap != null || request.GoalKinds != null) {
        throw new ArgumentException(
          "input_patterns generation requires a patternCampaign and cannot be combined with solver goal or reduction fields.");
      }
      ContractPatternCodec.Validate(request.PatternCampaign);
      if (request.CampaignFeedback != null) {
        ContractPatternCodec.Validate(request.CampaignFeedback);
      }
    } else {
      throw new ArgumentException("Unknown contract input generation strategy.");
    }
  }

  public static async Task<ContractGenerationResult> GenerateAsync(ContractGenerationRequest request,
    DafnyOptions options, CancellationToken cancellationToken, Func<ContractGenerationResult, Task>? onProgress = null) {
    ValidateRequest(request);
    options = new DafnyOptions(options) { DisallowIncludes = true };
    using var deadline = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    deadline.CancelAfter(Math.Min(request.TimeoutMilliseconds,
      request.CampaignFeedback?.RemainingMilliseconds ?? request.TimeoutMilliseconds));
    var token = deadline.Token;
    var bounds = request.Bounds ?? new();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, token);
    if (reporter.HasErrors) {
      return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    var reachable = request.Entry.InputMode == ContractInputMode.EntryReachable;
    var executionEntry = reachable
      ? new ContractEntry(request.Entry.ReachableFrom!, Receiver: request.Entry.ReachableReceiver) : request.Entry;
    Method? selectedTarget = null;
    Method method;
    try {
      if (reachable) {
        selectedTarget = ContractCallableSelector.SelectMethod(program,
          new ContractEntry(request.Entry.Symbol, request.Entry.TypeArguments), requireConcreteReceiver: false);
      }
      method = ContractCallableSelector.SelectMethod(program, executionEntry, requireConcreteReceiver: false);
    } catch (NotSupportedException error) {
      return ContractGenerationResult.Failure(ContractTestStatus.Unsupported, error.Message);
    }
    var source = ContractSourceSnapshot.Find(request.Sources, method.Origin.Uri);
    var targetSource = selectedTarget == null ? null : ContractSourceSnapshot.Find(request.Sources, selectedTarget.Origin.Uri);
    var prepared = new ContractPreparedProgram(program, method, source,
      new(source.Path, method.Origin.line, method.Origin.col, method.FullDafnyName, source.Sha256),
      OriginalCallable: method is ContractConcreteMethod concreteMethod ? concreteMethod.OriginalCallable : method.FunctionFromWhichThisIsByMethodDecl, Sources: request.Sources);
    var receiverName = method.IsStatic ? null : prepared.ReceiverName;
    Expression? receiver = receiverName == null ? null : new IdentifierExpr(method.Origin,
      new BoundVar(method.Origin, receiverName, UserDefinedType.FromTopLevelDecl(method.Origin,
        ((ClassLikeDecl)method.EnclosingClass).NonNullTypeDecl!)));
    if (request.CandidateInputs != null && !method.Ins.Select(formal => formal.Name).ToHashSet().SetEquals(request.CandidateInputs.Keys)) {
      return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput, "Candidate input names do not match the selected callable.");
    }
    if (request.CandidateInputs != null) {
      try {
        var candidate = new ContractTestRequest(ContractJson.SchemaVersion, request.Sources, request.Entry,
          request.CandidateInputs, request.CandidateHeap, request.Dependencies, request.TimeoutMilliseconds);
        ContractHarnessBuilder.ValidateRequest(candidate);
        _ = ContractHarnessBuilder.Prepare(program, candidate);
      } catch (ArgumentException error) {
        return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput, error.Message);
      } catch (NotSupportedException error) {
        return ContractGenerationResult.Failure(ContractTestStatus.Unsupported, error.Message);
      }
    }
    if (request.GenerationStrategy == ContractGenerationStrategy.InputPatterns) {
      if (!method.IsStatic || reachable) {
        return ContractGenerationResult.Failure(ContractTestStatus.Unsupported,
          "M1 pattern campaigns currently require a static unit-mode entry; receiver patterns belong to logical heap support.");
      }
      ContractPatternCampaign campaign;
      string? executorBaselineId;
      try {
        ContractPatternCompiler.Validate(method, request.PatternCampaign!, bounds);
        campaign = ContractPatternCompiler.AddExecutorBaseline(method, request.PatternCampaign!, bounds,
          out executorBaselineId);
        ContractPatternCompiler.Validate(method, campaign, bounds);
      } catch (ArgumentException error) {
        return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput, error.Message);
      } catch (NotSupportedException error) {
        return ContractGenerationResult.Failure(ContractTestStatus.Unsupported, error.Message);
      }
      return await GeneratePatternsAsync(request with { PatternCampaign = campaign }, options, token,
        program, prepared, method, source, bounds, executorBaselineId, onProgress, cancellationToken);
    }
    IReadOnlyList<ContractInputShape> shapes;
    try {
      shapes = new ContractTypeShapeGenerator(bounds).Generate(program, method, receiverName);
    } catch (NotSupportedException error) {
      return ContractGenerationResult.Failure(ContractTestStatus.Unsupported, error.Message);
    }
    var goals = new List<Goal> { new("precondition", ContractInputGoalKind.Precondition, "true") };
    ContractBodyExpansionResult? expansion = null;
    var frontiers = new List<ContractBodyFrontier>();
    if (method.Body != null && (request.GoalKinds == null || request.GoalKinds.Contains(ContractInputGoalKind.ImplementationPath))) {
      try {
        expansion = new ContractBodyExpander(program,
          new(bounds.MaxCallDepth, bounds.MaxLoopIterations, bounds.MaxGoals)).Expand(method, receiver, selectedTarget?.FullDafnyName, request.Entry.ReachableInvocation);
        goals.AddRange(expansion.Goals.Where(goal => !reachable || goal.Kind == ContractBodyGoalKind.EntryReachable).Select(goal => new Goal(goal.Id, ContractInputGoalKind.ImplementationPath, null, goal)));
        frontiers.AddRange(expansion.Frontier);
      } catch (NotSupportedException error) {
        goals.Add(new("body_unsupported", ContractInputGoalKind.ImplementationPath, null, Unsupported: error.Message));
      }
    }
    if (request.GoalKinds == null || request.GoalKinds.Contains(ContractInputGoalKind.SpecificationCase)) {
      if (reachable) {
        const string reason = "Selected target specification projection through the actual outer prefix is not supported.";
        goals.Add(new("spec_reachable_unsupported", ContractInputGoalKind.SpecificationCase, null, Unsupported: reason));
        frontiers.Add(new("spec_reachable_unsupported", reason, new(selectedTarget!.FullDafnyName,
          selectedTarget.StartToken.pos, selectedTarget.EntireRange.Length, selectedTarget.Origin.line, selectedTarget.Origin.col)));
      } else {
        goals.AddRange(new ContractScenarioExtractor(program, method, bounds.MaxGoals, receiver).Extract().Select(scenario =>
          new Goal(scenario.Id, ContractInputGoalKind.SpecificationCase, scenario.InputConstraint,
            Unsupported: scenario.InputConstraint == null ? scenario.Reason : null)));
      }
    }
    goals = FairGoalOrder(goals);
    if (request.RequiredGoalId != null) {
      goals = goals.Where(goal => goal.Id == request.RequiredGoalId).ToList();
      if (goals.Count != 1) {
        return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput, "The original selected generation goal does not exist.");
      }
    }
    var inputs = new List<ContractGeneratedInput>();
    var outcomes = new List<ContractInputGoalResult>();
    var seen = new HashSet<string>(StringComparer.Ordinal);
    var blocked = new Dictionary<string, List<string>>();
    var exhausted = new HashSet<(string Goal, int Shape)>();
    var attempted = new HashSet<string>(StringComparer.Ordinal);
    var duplicates = 0;
    var unsat = 0;
    var unknown = 0;
    var unsupported = 0;
    var precondition = Conjunction(method.Req.Select(clause => ContractQueryBuilder.RenderExpression(prepared, clause.E)));
    var module = method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName;
    var queryName = ContractBodyNames.Family(program, ContractQueryBuilder.QueryName);
    var location = new ContractSourceLocation(source.Path, method.Origin.line, method.Origin.col, method.FullDafnyName, source.Sha256);
    var round = 0;
    ContractTestStatus? interrupted = null;
    ContractGenerationResult Snapshot() {
      var pending = goals.Where(goal => outcomes.All(outcome => outcome.Id != goal.Id)).Select(goal =>
        new ContractInputGoalResult(goal.Id, goal.Kind, ContractQueryOutcome.Unknown,
          "Goal not attempted within the recorded input, shape or time budget.", location)).ToArray();
      return new(ContractJson.SchemaVersion, interrupted ?? (inputs.Count > 0 ? ContractTestStatus.Passed : ContractTestStatus.Inconclusive),
        interrupted != null ? "Generation stopped at its deadline or cancellation; completed candidates and unattempted goals are retained."
          : inputs.Count > 0 ? "Generated concrete inputs with original premise/goal rechecks; runtime testing and trace replay are separate."
          : "No rechecked input was obtained in the recorded bounded search.", inputs.ToArray(), outcomes.Concat(pending).ToArray(), frontiers.ToArray(),
        new(goals.Count, attempted.Count, inputs.Count, duplicates, unsat, unknown + pending.Length, unsupported));
    }
    try {
      while (inputs.Count < bounds.MaxInputs && shapes.Count > 0 && exhausted.Count < goals.Count * shapes.Count) {
        token.ThrowIfCancellationRequested();
        foreach (var goal in goals) {
          if (inputs.Count >= bounds.MaxInputs) {
            break;
          }
          var shapeIndex = round % shapes.Count;
          if (exhausted.Contains((goal.Id, shapeIndex))) {
            continue;
          }
          if (goal.Unsupported != null) {
            unsupported++;
            outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Unknown, goal.Unsupported, location));
            for (var index = 0; index < shapes.Count; index++) {
              exhausted.Add((goal.Id, index));
            }
            continue;
          }
          var shape = shapes[shapeIndex];
          var captures = goal.Body != null && expansion!.CapturedCalls.Count > 0
            ? new ContractAbstractCapturePlan(expansion, shape, module) : null;
          var blockingKey = shape.HeapLayout + (captures == null ? "" : "|" + goal.Id);
          if (!blocked.TryGetValue(blockingKey, out var blockedLayout)) {
            blockedLayout = [];
            blocked[blockingKey] = blockedLayout;
          }
          var constraints = shape.Constraints.Concat(blockedLayout).Append(precondition).ToList();
          if (request.CandidateInputs != null) {
            var candidateHeap = request.CandidateHeap ?? [];
            if ((shape.Objects?.Count ?? 0) != candidateHeap.Count || candidateHeap.Any(item =>
                  !(shape.Objects ?? []).Any(slot => "object" + slot.Id == item.Id && slot.TypeName == item.Type && slot.Elements?.Count == item.Elements?.Count))) {
              exhausted.Add((goal.Id, shapeIndex));
              continue;
            }
            constraints.AddRange(request.CandidateInputs.Select(input => input.Key + " == " + shape.ConcreteExpression(input.Value, module)));
            if (receiverName != null) {
              constraints.Add(receiverName + " == " + shape.ConcreteExpression(executionEntry.Receiver!, module));
            }
            constraints.AddRange(HeapFacts(candidateHeap, shape, module));
          }
          if (goal.Constraint != null) {
            constraints.Add(goal.Constraint);
          }
          var body = goal.Body == null ? Target("false") : ContractPathExplorer.TargetBody(expansion!, goal.Id);
          if (captures != null) { body = captures.Apply(body); }
          attempted.Add(goal.Id);
          var traceEvents = goal.Body == null ? null : expansion!.TraceEvents;
          var querySource = QuerySource(program, options, source, method, shape, constraints, body, traceEvents, captures?.Parameters);
          var query = await ContractSolver.CheckAsync(querySource, ContractQueryKind.ContractRealization, options, token, true, queryName: queryName, sourceSnapshots: request.Sources, sourcePath: source.Path);
          if (query.Outcome != ContractQueryOutcome.Sat) {
            if (query.Outcome == ContractQueryOutcome.Unsat) { unsat++; } else { unknown++; }
            outcomes.Add(new(goal.Id, goal.Kind, query.Outcome, query.Outcome == ContractQueryOutcome.Unsat
              ? "No new model in this explicitly bounded input shape." : query.Diagnostics, location));
            exhausted.Add((goal.Id, shapeIndex));
            continue;
          }
          if (!ContractModelRealizer.TryExtractModelValues(query.Diagnostics, options, shape.Leaves, out var values, out var completed)) {
            unknown++;
            outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Unknown, "Input model was not concretely materialized.", location));
            exhausted.Add((goal.Id, shapeIndex));
            continue;
          }
          IReadOnlyDictionary<string, ContractValue>? traceValues = null;
          if (traceEvents != null && ContractModelRealizer.TryExtractModelValues(query.Diagnostics, options,
                traceEvents.Select(item => (item.Name, (Microsoft.Dafny.Type)Microsoft.Dafny.Type.Int)).ToList(), out var extractedTrace, out _)) {
            traceValues = extractedTrace;
          }
          IReadOnlyList<ContractAbstractChoice>? replayChoices = null;
          IReadOnlyList<string> captureBindings = [];
          if (captures != null) {
            if (!ContractModelRealizer.TryExtractModelValues(query.Diagnostics, options, captures.Parameters,
                  out var capturedValues, out var capturedCompleted) ||
                !captures.TryMaterialize(capturedValues, capturedCompleted, out replayChoices, out captureBindings)) {
              unsupported++;
              if (frontiers.All(item => item.Id != "capture_" + goal.Id)) {
                frontiers.Add(new("capture_" + goal.Id, "Native call values or fresh references exceed the materialized shape.", goal.Body!.Location));
              }
              outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Unknown,
                "Native call capture could not materialize values or referenced objects within the recorded heap shape.", location));
              exhausted.Add((goal.Id, shapeIndex));
              continue;
            }
          }
          var concreteRoots = shape.Materialize(values);
          var concrete = concreteRoots.Where(input => input.Key != receiverName).ToDictionary(input => input.Key, input => input.Value);
          var concreteEntry = receiverName == null ? request.Entry : reachable
            ? request.Entry with { ReachableReceiver = concreteRoots[receiverName] }
            : request.Entry with { Receiver = concreteRoots[receiverName] };
          var heap = shape.MaterializeHeap(values);
          var key = JsonSerializer.Serialize(new {
            Inputs = concreteRoots.OrderBy(pair => pair.Key).ToDictionary(pair => pair.Key, pair => pair.Value),
            Heap = heap,
            ReplayChoices = replayChoices?.Select(choice => new { choice.Symbol, choice.TypeArguments, choice.Inputs, choice.Outputs, choice.Receiver, choice.PreHeap, choice.PostHeap })
          }, ContractJson.Options);
          if (!seen.Add(key)) {
            duplicates++;
            exhausted.Add((goal.Id, shapeIndex));
            continue;
          }
          var fixedBindings = shape.Constraints.Concat(values.Select(value => value.Key + " == " + ContractModelCodec.ToDafny(value.Value, module))).ToList();
          // Restore original P/G as the checked property; generated assumptions never prove themselves.
          var property = Conjunction(new[] { precondition, goal.Constraint ?? "true" });
          var recheck = await RecheckCandidateAsync(program, options, source, method, shape, fixedBindings,
            property, queryName, request.Sources, token);
          var queries = new List<ContractQueryResult> { query, recheck.Premise, recheck.Property };
          var valid = recheck.IsValid;
          if (valid && goal.Body != null) {
            var path = await ContractSolver.CheckAsync(QuerySource(program, options, source, method, shape,
                fixedBindings.Append(precondition).Concat(traceValues?.Select(item => item.Key + " == " +
                  ContractModelCodec.ToDafny(item.Value, module)) ?? []).Concat(captureBindings),
                captures?.Apply(ContractPathExplorer.TargetBody(expansion!, goal.Id)) ?? ContractPathExplorer.TargetBody(expansion!, goal.Id),
                traceEvents, captures?.Parameters),
              ContractQueryKind.ContractRealization, options, token, queryName: queryName, sourceSnapshots: request.Sources, sourcePath: source.Path);
            queries.Add(path);
            valid = path.Outcome == ContractQueryOutcome.Sat;
          }
          var concreteFacts = concreteRoots.Select(input => input.Key + " == " + shape.ConcreteExpression(input.Value, module))
            .Concat(HeapFacts(heap, shape, module));
          blockedLayout.Add("!(" + Conjunction(concreteFacts.Concat(captureBindings)) + ")");
          if (!valid) {
            unknown++;
            outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Unknown, "Materialized input failed the original premise/goal recheck.", location));
            continue;
          }
          var test = new ContractTestRequest(ContractJson.SchemaVersion, request.Sources, concreteEntry, concrete,
            Heap: heap.Count == 0 ? null : heap, Dependencies: request.Dependencies, TimeoutMilliseconds: request.TimeoutMilliseconds,
            ReplayChoices: replayChoices, ReplayPrefix: replayChoices != null);
          try {
            // Existing realization checks reject unavailable fields, type mismatches and unsupported alias graphs.
            _ = ContractHarnessBuilder.Prepare(program, test);
          } catch (NotSupportedException error) {
            unsupported++;
            outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Unknown, error.Message, location));
            exhausted.Add((goal.Id, shapeIndex));
            continue;
          }
          inputs.Add(new(test, goal.Id, goal.Kind, queries,
            goal.Body == null ? null : ContractPathExplorer.Candidate(expansion!, goal.Body, traceValues,
              goal.Body.Kind == ContractBodyGoalKind.EntryReachable
                ? new ContractExpectedEntry(selectedTarget!.FullDafnyName, request.Entry.ReachableInvocation, targetSource!.Sha256) : null)));
          outcomes.Add(new(goal.Id, goal.Kind, ContractQueryOutcome.Sat,
            completed ? "Completed model candidate passed original input/goal rechecks." : "Concrete solver input passed original input/goal rechecks.", location));
          if (onProgress != null) {
            await onProgress(Snapshot());
          }
        }
        round++;
        if (request.CandidateInputs != null && inputs.Count > 0) {
          break;
        }
      }
    } catch (OperationCanceledException) when (token.IsCancellationRequested) {
      interrupted = cancellationToken.IsCancellationRequested ? ContractTestStatus.Cancelled : ContractTestStatus.Timeout;
    }
    return Snapshot();
  }

  private static async Task<ContractGenerationResult> GeneratePatternsAsync(ContractGenerationRequest request,
    DafnyOptions options, CancellationToken token, Program program, ContractPreparedProgram prepared, Method method,
    ContractSource source, ContractGenerationBounds bounds, string? executorBaselineId,
    Func<ContractGenerationResult, Task>? onProgress, CancellationToken callerCancellation) {
    var campaign = request.PatternCampaign!;
    var configuredLimit = campaign.MaxSamples ?? checked(bounds.MaxInputs * 10);
    var sampleLimit = Math.Min(configuredLimit,
      request.CampaignFeedback?.RemainingSamples ?? configuredLimit);
    var ordinalOffset = (long)(request.CampaignFeedback?.SampleOrdinalOffset ?? 0);
    if (ordinalOffset + sampleLimit > int.MaxValue) {
      return ContractGenerationResult.Failure(ContractTestStatus.InvalidInput,
        "Campaign feedback round exceeds the reproducible sample ordinal range.");
    }
    var inputs = new List<ContractGeneratedInput>();
    var outcomes = new List<ContractInputGoalResult>();
    var seen = new HashSet<string>(StringComparer.Ordinal);
    var seenInputHashes = (request.CampaignFeedback?.SeenInputSha256 ?? [])
      .ToHashSet(StringComparer.Ordinal);
    var duplicates = 0;
    var unknown = 0;
    var unsupported = 0;
    var samples = 0;
    var rejected = 0;
    var preconditionFalse = 0;
    var preconditionUnknown = 0;
    var verifiedRefinements = new Dictionary<string, string>(StringComparer.Ordinal);
    var refinementReductions = new Dictionary<string, ContractRefinementReductionCacheEntry>(StringComparer.Ordinal);
    var precondition = Conjunction(method.Req.Select(clause => ContractQueryBuilder.RenderExpression(prepared, clause.E)));
    var module = method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName;
    var queryName = ContractBodyNames.Family(program, ContractQueryBuilder.QueryName);
    var location = new ContractSourceLocation(source.Path, method.Origin.line, method.Origin.col,
      method.FullDafnyName, source.Sha256);
    ContractTestStatus? interrupted = null;

    ContractGenerationResult Snapshot() => new(ContractJson.SchemaVersion,
      interrupted ?? (inputs.Count > 0 ? ContractTestStatus.Passed : ContractTestStatus.Inconclusive),
      interrupted != null
        ? "Pattern generation stopped at its deadline or cancellation; rechecked inputs are retained."
        : inputs.Count > 0
          ? "Generated data-only pattern samples that passed the original entry precondition recheck."
          : "No pattern sample passed the original entry precondition in the recorded sample budget.",
      inputs.ToArray(), outcomes.ToArray(), [],
      new(sampleLimit, samples, inputs.Count, duplicates, 0, unknown, unsupported,
        samples, rejected, preconditionFalse, preconditionUnknown));

    try {
      for (var ordinal = 0; ordinal < sampleLimit && inputs.Count < bounds.MaxInputs; ordinal++) {
        token.ThrowIfCancellationRequested();
        ContractPatternSample sample;
        var goalId = "pattern:" + ordinal;
        try {
          sample = ContractPatternSampler.Sample(campaign, (int)ordinalOffset + ordinal,
            (int)ordinalOffset + ordinal, executorBaselineId);
          goalId = "pattern:" + sample.Provenance.PatternId + ":" + sample.Provenance.SampleOrdinal;
          samples++;
        } catch (ArgumentException error) {
          samples++;
          rejected++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            error.Message, location));
          continue;
        } catch (NotSupportedException error) {
          samples++;
          rejected++;
          unsupported++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            error.Message, location));
          continue;
        }

        var key = JsonSerializer.Serialize(new {
          Inputs = sample.Inputs.OrderBy(pair => pair.Key).ToDictionary(pair => pair.Key, pair => pair.Value),
          sample.Heap
        }, ContractJson.Options);
        var inputHash = ContractPatternSampler.SampleSha256(sample.Inputs, sample.Heap);
        if (!seen.Add(key) || !seenInputHashes.Add(inputHash)) {
          duplicates++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            "Deterministic pattern sample duplicates an earlier concrete candidate.", location));
          continue;
        }

        var test = new ContractTestRequest(ContractJson.SchemaVersion, request.Sources, request.Entry,
          sample.Inputs, sample.Heap.Count == 0 ? null : sample.Heap, request.Dependencies,
          request.TimeoutMilliseconds);
        ContractPreparedProgram samplePrepared;
        try {
          ContractHarnessBuilder.ValidateRequest(test);
          samplePrepared = ContractHarnessBuilder.Prepare(program, test);
        } catch (ArgumentException error) {
          rejected++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            "Sample does not realize the resolved entry signature: " + error.Message, location));
          continue;
        } catch (NotSupportedException error) {
          rejected++;
          unsupported++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            error.Message, location));
          continue;
        }

        ContractInputShape shape;
        IReadOnlyList<string> fixedBindings;
        try {
          shape = new ContractTypeShapeGenerator(bounds).FromConcrete(program, method, sample.Inputs,
            samplePrepared.Heap);
          fixedBindings = shape.Constraints.Concat(
            shape.ConcreteBindings(sample.Inputs, sample.Heap, module)).ToList();
        } catch (ArgumentException error) {
          rejected++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            "Sample does not realize one exact resolved structural shape: " + error.Message, location));
          continue;
        }
        if (method.Req.Count == 0 && !shape.HasRefinement) {
          inputs.Add(new(test, goalId, ContractInputGoalKind.Pattern, [],
            PatternProvenance: sample.Provenance));
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Sat,
            "Complete pattern sample has the resolved precondition true and no refinement obligations; SMT recheck was unnecessary.",
            location));
          if (onProgress != null) {
            await onProgress(Snapshot());
          }
          continue;
        }
        var refinementResult = method.Req.Count == 0
          ? await shape.RefinementObligationsAsync(sample.Inputs, sample.Heap, samplePrepared,
            verifiedRefinements, refinementReductions, token)
          : null;
        if (refinementResult is { Kind: ContractRefinementResultKind.Failure, Diagnostic: { } refinementFailure }) {
          rejected++;
          unknown++;
          preconditionUnknown++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Error,
            refinementFailure.ToString(), location));
          continue;
        }
        if (refinementResult is { Kind: ContractRefinementResultKind.Complete }) {
          var refinementObligations = refinementResult.Obligations;
          var refinementQueries = new List<ContractQueryResult>();
          var reductionDiagnostics = new List<string>();
          var cacheHits = 0;
          ContractQueryResult? failedRefinement = null;
          foreach (var obligation in refinementObligations) {
            if (verifiedRefinements.TryGetValue(obligation.Sha256, out var cached)) {
              if (cached == obligation.Canonical) {
                cacheHits++;
                reductionDiagnostics.Add(obligation.TypeName + ": cached decision=" +
                  (obligation.Reduction?.Decision.ToString() ?? "previously verified") +
                  ", residual=" + (obligation.Reduction?.ResidualKind.ToString() ?? "none") +
                  ", exhaustion=" + string.Join(",", obligation.Reduction?.ExhaustionReasons ?? []));
                continue;
              }
              failedRefinement = new(ContractQueryKind.ContractRealization, ContractQueryOutcome.Error,
                "A refinement obligation SHA-256 collision prevented cache reuse.");
              break;
            }
            if (obligation.Reduction == null) {
              failedRefinement = new(ContractQueryKind.ContractRealization, ContractQueryOutcome.Error,
                "A refinement obligation was neither cached nor reduced.");
              break;
            }
            reductionDiagnostics.Add(obligation.TypeName + ": decision=" + obligation.Reduction.Decision +
              ", residual=" + obligation.Reduction.ResidualKind + ", exhaustion=" +
              string.Join(",", obligation.Reduction.ExhaustionReasons));
            if (obligation.Reduction.Decision == ContractReductionDecision.False) {
              failedRefinement = new(ContractQueryKind.ContractRealization, ContractQueryOutcome.Sat,
                "Concrete refinement membership reduced to false without an SMT query.");
              break;
            }
            if (obligation.Reduction.Decision == ContractReductionDecision.Residual) {
              var membership = ContractQueryBuilder.RenderExpression(samplePrepared,
                obligation.Reduction.SubstitutedExpression);
              if (!TryRefinementQuerySource(samplePrepared.SourceSnapshots, obligation.QuerySite,
                    queryName, membership, out var querySource)) {
                failedRefinement = new(ContractQueryKind.ContractRealization, ContractQueryOutcome.Error,
                  "The refinement declaration query site does not identify exactly one original supplied source snapshot.");
                break;
              }
              var query = await ContractSolver.CheckAsync(
                querySource.Content,
                ContractQueryKind.ContractRealization, options, token, queryName: queryName,
                sourceSnapshots: samplePrepared.SourceSnapshots, sourcePath: querySource.Path);
              refinementQueries.Add(query);
              if (query.Outcome != ContractQueryOutcome.Unsat) {
                failedRefinement = query;
                break;
              }
            }
            verifiedRefinements.Add(obligation.Sha256, obligation.Canonical);
          }
          if (failedRefinement == null) {
            inputs.Add(new(test, goalId, ContractInputGoalKind.Pattern, refinementQueries,
              PatternProvenance: sample.Provenance));
            outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Sat,
              "Complete pattern sample's direct refinement memberships were verified by resolved reduction" +
              " with residual SMT fallback; ran " + refinementQueries.Count + " SMT queries and reused " +
              cacheHits + " cached SHA-256 obligations." +
              (reductionDiagnostics.Count == 0 ? "" : " " + string.Join("; ", reductionDiagnostics)), location));
            if (onProgress != null) {
              await onProgress(Snapshot());
            }
            continue;
          }
          if (failedRefinement.Outcome == ContractQueryOutcome.Sat) {
            rejected++;
            preconditionFalse++;
          } else {
            unknown++;
            preconditionUnknown++;
          }
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, failedRefinement.Outcome,
            "A direct refinement membership was false or not verified and the sample was filtered; ran " +
            refinementQueries.Count + " SMT queries and reused " + cacheHits +
            " cached SHA-256 obligations. " + failedRefinement.Diagnostics +
            (reductionDiagnostics.Count == 0 ? "" : " " + string.Join("; ", reductionDiagnostics)), location));
          continue;
        }
        var fallbackDiagnostic = refinementResult?.Diagnostic == null ? "" : " " + refinementResult.Diagnostic;
        var accepted = await RecheckCandidateAsync(program, options, source, method, shape, fixedBindings,
          precondition, queryName, samplePrepared.DiagnosticSourceSnapshots, token);

        if (accepted.IsValid) {
          inputs.Add(new(test, goalId, ContractInputGoalKind.Pattern,
            [accepted.Premise, accepted.Property], PatternProvenance: sample.Provenance));
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Sat,
            "Complete pattern sample passed the original entry precondition recheck." + fallbackDiagnostic, location));
          if (onProgress != null) {
            await onProgress(Snapshot());
          }
          continue;
        }
        if (accepted.Premise.Outcome == ContractQueryOutcome.Sat &&
            accepted.Property.Outcome == ContractQueryOutcome.Sat) {
          preconditionFalse++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Sat,
            "Complete pattern sample falsifies the original entry precondition and was filtered." +
            fallbackDiagnostic, location));
        } else if (accepted.Premise.Outcome is ContractQueryOutcome.Unknown or ContractQueryOutcome.Timeout or ContractQueryOutcome.Error ||
                   accepted.Property.Outcome is ContractQueryOutcome.Unknown or ContractQueryOutcome.Timeout or ContractQueryOutcome.Error) {
          unknown++;
          preconditionUnknown++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            "Original entry precondition recheck was unknown, timed out or failed; the sample was filtered." +
            fallbackDiagnostic, location));
        } else {
          rejected++;
          outcomes.Add(new(goalId, ContractInputGoalKind.Pattern, ContractQueryOutcome.Unknown,
            "Concrete pattern sample was inconsistent with its exact resolved structural shape." +
            fallbackDiagnostic, location));
        }
      }
    } catch (OperationCanceledException) when (token.IsCancellationRequested) {
      interrupted = callerCancellation.IsCancellationRequested ? ContractTestStatus.Cancelled : ContractTestStatus.Timeout;
    }
    return Snapshot();
  }

  private static async Task<CandidateRecheck> RecheckCandidateAsync(Program program, DafnyOptions options,
    ContractSource source, Method method, ContractInputShape shape, IReadOnlyList<string> fixedBindings,
    string property, string queryName, IReadOnlyList<ContractSource> sources, CancellationToken token) {
    // P and the selected property stay in the assertion. Candidate bindings are premises and cannot prove themselves.
    var premise = await ContractSolver.CheckAsync(
      QuerySource(program, options, source, method, shape, fixedBindings, Target("false")),
      ContractQueryKind.PremiseConsistency, options, token, queryName: queryName,
      sourceSnapshots: sources, sourcePath: source.Path);
    var check = await ContractSolver.CheckAsync(
      QuerySource(program, options, source, method, shape, fixedBindings, Target(property)),
      ContractQueryKind.EntryPrecondition, options, token, queryName: queryName,
      sourceSnapshots: sources, sourcePath: source.Path);
    return new(premise, check);
  }

  private static bool TryRefinementQuerySource(IReadOnlyList<ContractSource> sources,
    ContractRefinementQuerySite? querySite, string queryName, string membership,
    out RefinementQuerySource querySource) {
    querySource = null!;
    if (querySite == null) {
      return false;
    }
    var matchingSources = sources.Where(source => source.Sha256 == querySite.SourceSha256 &&
      ContractSourceSnapshot.UriFor(source.Path) == ContractSourceSnapshot.UriFor(querySite.SourcePath)).ToList();
    if (matchingSources.Count != 1) {
      return false;
    }
    if (!TryCharacterIndexForUtf8ByteOffset(matchingSources[0].Content, querySite.BytePosition,
          out var characterIndex)) {
      return false;
    }
    var declaration = "\nmethod " + queryName + "()\n{\n" +
                      Target(membership) + "\n}\n";
    var source = matchingSources[0];
    querySource = new RefinementQuerySource(source.Content.Insert(characterIndex, declaration), source.Path);
    return true;
  }

  // Dafny Token.pos is a UTF-8 byte offset, while string.Insert indexes UTF-16 code units.
  private static bool TryCharacterIndexForUtf8ByteOffset(string content, int bytePosition,
    out int characterIndex) {
    characterIndex = 0;
    if (bytePosition < 0) {
      return false;
    }
    if (bytePosition == 0) {
      return true;
    }
    var utf8 = new UTF8Encoding(encoderShouldEmitUTF8Identifier: false, throwOnInvalidBytes: true);
    long bytes = 0;
    for (var index = 0; index < content.Length;) {
      var width = 1;
      if (char.IsHighSurrogate(content[index])) {
        if (index + 1 >= content.Length || !char.IsLowSurrogate(content[index + 1])) {
          return false;
        }
        width = 2;
      } else if (char.IsLowSurrogate(content[index])) {
        return false;
      }
      int scalarBytes;
      try {
        scalarBytes = utf8.GetByteCount(content.AsSpan(index, width));
      } catch (EncoderFallbackException) {
        return false;
      }
      bytes += scalarBytes;
      index += width;
      if (bytes == bytePosition) {
        characterIndex = index;
        return true;
      }
      if (bytes > bytePosition) {
        return false;
      }
    }
    return false;
  }

  private static List<Goal> FairGoalOrder(IReadOnlyList<Goal> goals) {
    var ordered = goals.Where(goal => goal.Kind == ContractInputGoalKind.Precondition).ToList();
    using var specification = goals.Where(goal => goal.Kind == ContractInputGoalKind.SpecificationCase).GetEnumerator();
    using var implementation = goals.Where(goal => goal.Kind == ContractInputGoalKind.ImplementationPath).GetEnumerator();
    var hasSpecification = specification.MoveNext();
    var hasImplementation = implementation.MoveNext();
    while (hasSpecification || hasImplementation) {
      if (hasSpecification) { ordered.Add(specification.Current); hasSpecification = specification.MoveNext(); }
      if (hasImplementation) { ordered.Add(implementation.Current); hasImplementation = implementation.MoveNext(); }
    }
    return ordered;
  }

  private static IEnumerable<string> HeapFacts(IReadOnlyList<ContractHeapObject> heap, ContractInputShape shape, string module) {
    foreach (var item in heap) {
      var name = shape.Objects!.Single(slot => "object" + slot.Id == item.Id).VariableName;
      foreach (var field in item.Fields) {
        yield return name + "." + field.Key + " == " + shape.ConcreteExpression(field.Value, module);
      }
      if (item.Elements != null) {
        yield return name + ".Length == " + item.Dimensions![0];
        for (var index = 0; index < item.Elements.Count; index++) {
          yield return name + "[" + index + "] == " + shape.ConcreteExpression(item.Elements[index], module);
        }
      }
    }
  }

  private static string QuerySource(Program program, DafnyOptions options, ContractSource source, Method method, ContractInputShape shape,
    IEnumerable<string> constraints, string body, IReadOnlyList<ContractBodyTraceEvent>? traceEvents = null,
    IReadOnlyList<(string Name, Microsoft.Dafny.Type Type)>? captures = null) {
    var parameters = method.Ins.Select(formal => formal.Name + ": " + formal.Type)
      .Concat(shape.Leaves.Select(leaf => leaf.Name + ": " + leaf.Type))
      .Concat(shape.ObjectParameters(program, method))
      .Concat(traceEvents?.Select(item => item.Name + ": int") ?? [])
      .Concat(captures?.Select(item => item.Name + ": " + item.Type) ?? [])
      .Concat(shape.ReceiverName == null ? [] : new[] { shape.ReceiverName + ": " + method.EnclosingClass.Name });
    Expression? receiver = shape.ReceiverName == null ? null : new IdentifierExpr(method.Origin,
      new BoundVar(method.Origin, shape.ReceiverName, UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)));
    var substituter = new Substituter(receiver!, [], []);
    var modifies = method.Mod.Expressions?.Count > 0 ? "modifies " +
      Printer.FrameExprListToString(options, method.Mod.Expressions.Select(substituter.SubstFrameExpr).ToList()) : "";
    var declaration = "\nstatic method " + ContractBodyNames.Family(program, ContractQueryBuilder.QueryName) + "(" + string.Join(", ", parameters) + ")\n" +
      string.Join("\n", constraints.Select(constraint => "requires " + constraint)) + "\n" + modifies + "\n{\n" + body + "\n}\n";
    return source.Content.Insert(method.StartToken.pos, declaration);
  }
  private static string Target(string expression) => "assert {:error \"" + ContractQueryBuilder.TargetMarker + "\"} " + expression + ";";
  private static string Conjunction(IEnumerable<string> expressions) => string.Join(" && ", expressions.Select(expression => "(" + expression + ")").DefaultIfEmpty("true"));
}
