using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public sealed class ContractTestRunner(IContractProgramCompiler compiler) {
  public async Task<ContractTestResult> RunAsync(ContractPreparedProgram prepared, ContractTestRequest request,
    string outputDirectory, CancellationToken cancellationToken) {
    var queries = new List<ContractQueryResult>();
    var session = new ContractRuntimeSession();
    var compileRequest = request;
    var outerLocation = prepared.Location;
    var reachableMode = prepared.ReachableTarget != null;
    ContractReachability? reachability = null;
    ContractExecutionEvidence? executionEvidence = null;
    request = ContractHarnessBuilder.ExecutionRequest(request);
    IReadOnlyDictionary<string, ContractValue>? finalObservations = null;
    IReadOnlyList<ContractBranchObservation>? branches = null;
    var premise = await Query(ContractQueryKind.PremiseConsistency);
    if (premise.Outcome != ContractQueryOutcome.Sat) {
      return Result(ContractTestStatus.Inconclusive, "The concrete input premise was not established satisfiable.");
    }
    var precondition = await Query(ContractQueryKind.EntryPrecondition);
    if (precondition.Outcome == ContractQueryOutcome.Sat) {
      var opposite = await Query(ContractQueryKind.EntryPrecondition, negate: true);
      return opposite.Outcome == ContractQueryOutcome.Unsat
        ? Result(ContractTestStatus.InvalidInput, "The concrete input violates the entry precondition.")
        : Result(ContractTestStatus.Inconclusive, "The entry precondition is not determined by the concrete input observations.");
    }
    if (precondition.Outcome != ContractQueryOutcome.Unsat) {
      return Result(ContractTestStatus.Inconclusive, "Entry precondition could not be decided.");
    }
    var compile = await compiler.CompileAsync(new ContractCompileRequest(ContractJson.SchemaVersion, compileRequest, outputDirectory), cancellationToken);
    if (compile.Status != ContractTestStatus.Passed) {
      return Result(compile.Status, compile.Reason);
    }
    if (compile.Entry != prepared.Location || compile.AssemblyPath == null || compile.ObservationPath == null ||
        Convert.ToHexString(SHA256.HashData(await File.ReadAllBytesAsync(compile.AssemblyPath, cancellationToken))).ToLowerInvariant() != compile.AssemblySha256) {
      return Result(ContractTestStatus.Error, "Compiler source mapping or executable artifact hash mismatch.");
    }
    executionEvidence = new(compile.AssemblySha256!, ContractHarnessBuilder.QualifiedDiagnosticName(prepared, ContractHarnessBuilder.MainName), compile.Entry!);
    var execution = await session.ExecuteAsync(prepared, compileRequest, compile.AssemblyPath, compile.ObservationPath, outputDirectory, cancellationToken);
    branches = ContractStateObserver.Branches(await ContractStateObserver.ReadAsync(compile.ObservationPath, cancellationToken));
    queries.AddRange(session.Queries);
    if (session.ReachableStart is { } selected) {
      request = compileRequest with {
        Entry = new ContractEntry(selected.Symbol, Receiver: selected.Receiver),
        Inputs = selected.Inputs,
        Heap = selected.Heap
      };
      prepared = ContractHarnessBuilder.Prepare(prepared.Program, request);
      reachability = new(outerLocation, selected.Invocation!.Value, selected.Inputs, selected.Receiver, selected.Heap ?? []);
    }
    if (execution.Cancelled) {
      return Result(ContractTestStatus.Cancelled, "Runtime cancelled and process tree reaped.");
    }
    if (session.Failure is { } failure) {
      var failureStatus = failure.Status switch {
        ContractRealizationStatus.CallPreconditionViolation => ContractTestStatus.Counterexample,
        ContractRealizationStatus.Unsupported => ContractTestStatus.Unsupported,
        ContractRealizationStatus.Timeout => ContractTestStatus.Timeout,
        ContractRealizationStatus.Error => ContractTestStatus.Error,
        _ => ContractTestStatus.Inconclusive
      };
      return Result(failureStatus, session.FailureSymbol + ": " + failure.Reason) with {
        StandardOutput = execution.StandardOutput,
        StandardError = execution.StandardError,
        Violation = failure.Status == ContractRealizationStatus.CallPreconditionViolation ? ContractViolationKind.CallPrecondition : null
      };
    }
    if (execution.ExitCode != 0) {
      var failureObservations = await ContractStateObserver.ReadAsync(compile.ObservationPath, cancellationToken);
      var assertionFailed = failureObservations.TryGetValue("$bodyAssertion", out var failedAssertion) &&
                            failedAssertion == new ContractValue(ContractValueKind.Boolean, "false");
      var unsupported = failureObservations.Keys.FirstOrDefault(key => key.StartsWith("$unsupported/", StringComparison.Ordinal));
      return Result(assertionFailed
        ? ContractTestStatus.Counterexample : unsupported != null ? ContractTestStatus.Unsupported : ContractTestStatus.Error,
        unsupported != null ? unsupported["$unsupported/".Length..] : "Diagnostic body execution failed.") with {
        StandardOutput = execution.StandardOutput,
        StandardError = execution.StandardError,
        Violation = assertionFailed ? ContractViolationKind.BodyAssertion : null
      };
    }
    finalObservations = await ContractStateObserver.ReadAsync(compile.ObservationPath, cancellationToken);
    if (reachableMode) {
      if (session.ReachableStart == null || session.ReachableEnd == null) {
        return Result(ContractTestStatus.Inconclusive, "The requested invocation was not reached and returned by actual outer execution.") with {
          StandardOutput = execution.StandardOutput,
          StandardError = execution.StandardError
        };
      }
      var observations = finalObservations.Where(pair => pair.Key.StartsWith("$", StringComparison.Ordinal) &&
        !pair.Key.StartsWith("$initial/", StringComparison.Ordinal) && !pair.Key.StartsWith("$final/", StringComparison.Ordinal))
        .ToDictionary(pair => pair.Key, pair => pair.Value);
      foreach (var output in session.ReachableEnd.Outputs!) {
        observations.Add(output.Key, output.Value);
      }
      CaptureHeap(session.ReachableStart.Heap ?? [], "initial", observations);
      CaptureHeap(session.ReachableEnd.Heap ?? [], "final", observations);
      finalObservations = observations;
    }
    var outputs = finalObservations.Where(pair => !pair.Key.StartsWith("$", StringComparison.Ordinal))
      .ToDictionary(pair => pair.Key, pair => pair.Value);
    if (!prepared.Method.Outs.Select(formal => formal.Name).ToHashSet().SetEquals(outputs.Keys)) {
      return Result(ContractTestStatus.Error, "The runtime did not observe exactly the selected declaration's outputs.");
    }
    if (prepared.Heap?.ValidateInitialObservations(finalObservations) is { } heapError) {
      return Result(ContractTestStatus.Error, heapError);
    }
    // Validate that the entire observed heap can be represented before assigning a property verdict.
    _ = prepared.Heap?.QueryAssignments(finalObservations);
    var frameViolation = finalObservations.Keys.FirstOrDefault(key => key.StartsWith("$frameViolation/", StringComparison.Ordinal));
    var frameError = frameViolation != null
      ? "Frame violation: write outside the active method's modifies clause at " + frameViolation["$frameViolation/".Length..]
      : prepared.Heap?.CheckFrame(prepared.Method, request.Inputs, finalObservations, request.Entry.Receiver);
    var observedPremise = await Query(ContractQueryKind.PremiseConsistency, outputs);
    if (observedPremise.Outcome != ContractQueryOutcome.Sat) {
      return Result(ContractTestStatus.Inconclusive, "The fixed runtime observations are inconsistent with the query environment or their consistency is undecided.");
    }
    var postcondition = await Query(ContractQueryKind.ObservedPostcondition, outputs);
    var status = postcondition.Outcome switch {
      ContractQueryOutcome.Sat => ContractTestStatus.Counterexample,
      ContractQueryOutcome.Unsat => ContractTestStatus.Passed,
      _ => ContractTestStatus.Inconclusive
    };
    if (status == ContractTestStatus.Counterexample) {
      var opposite = await Query(ContractQueryKind.ObservedPostcondition, outputs, negate: true);
      if (opposite.Outcome != ContractQueryOutcome.Unsat) {
        status = ContractTestStatus.Inconclusive;
      }
    }
    if (frameError != null) {
      return Result(ContractTestStatus.Counterexample, frameError) with {
        Outputs = outputs,
        InitialHeap = Heap(true),
        FinalHeap = Heap(false),
        Violation = ContractViolationKind.Frame,
        StandardOutput = execution.StandardOutput,
        StandardError = execution.StandardError
      };
    }
    return new ContractTestResult(ContractJson.SchemaVersion, status, "Original postcondition checked against observed body outputs.",
      outputs, queries, prepared.Location, execution.StandardOutput, execution.StandardError,
      session.Choices.Count > 0, session.Choices, Heap(true), Heap(false),
      status == ContractTestStatus.Counterexample ? ContractViolationKind.Postcondition : null, branches, reachability, executionEvidence);

    async Task<ContractQueryResult> Query(ContractQueryKind kind, IReadOnlyDictionary<string, ContractValue>? outputs = null, bool negate = false) {
      var choices = ContractModelRealizer.PureChoiceConstraints(prepared, session.Choices,
        prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
      var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, kind, outputs, negate, finalObservations, choices),
        kind, prepared.Program.Options, cancellationToken, queryName: ContractQueryBuilder.Name(prepared),
        sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
      queries.Add(query);
      return query;
    }

    ContractTestResult Result(ContractTestStatus status, string reason) =>
      new(ContractJson.SchemaVersion, status, reason, Queries: queries, Entry: prepared.Location,
        UsedContractModels: session.Choices.Count > 0, AbstractChoices: session.Choices, Branches: branches,
        Reachability: reachability, Execution: executionEvidence);

    static void CaptureHeap(IReadOnlyList<ContractHeapObject> heap, string phase, Dictionary<string, ContractValue> observations) {
      foreach (var item in heap) {
        foreach (var field in item.Fields) {
          observations.Add("$" + phase + "/" + item.Id + "/" + field.Key, field.Value);
        }
        if (item.Elements != null) {
          observations.Add("$" + phase + "/" + item.Id + "/$length", new(ContractValueKind.Integer, item.Elements.Count.ToString(System.Globalization.CultureInfo.InvariantCulture)));
          for (var index = 0; index < item.Elements.Count; index++) {
            observations.Add("$" + phase + "/" + item.Id + "/[" + index + "]", item.Elements[index]);
          }
        }
      }
    }

    IReadOnlyList<ContractHeapObject>? Heap(bool initial) => request.Heap?.Select(item => new ContractHeapObject(item.Id,
      item.Type, item.Fields.Keys.ToDictionary(field => field,
        field => finalObservations!["$" + (initial ? "initial" : "final") + "/" + item.Id + "/" + field]),
      item.Dimensions, item.Elements?.Select((_, index) =>
        finalObservations!["$" + (initial ? "initial" : "final") + "/" + item.Id + "/[" + index + "]"]).ToList())).ToList();
  }
}
