using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using System.Text.Json;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractStubRuntime {
  public static string RuntimeSource(string observationPath, ContractPreparedProgram prepared, bool runtimeReferences = false,
    IReadOnlySet<Field>? compiledGhostFields = null) {
    var program = prepared.Program;
    var trackedGhostFields = prepared.Heap?.TrackedGhostFields ?? new HashSet<Field>();
    // Runtime diagnostics never dispatch through observed call stubs, so they need no concrete call evidence.
    var concreteTypes = runtimeReferences ? new Dictionary<string, List<string>>() : prepared.ConcreteCalls.ToDictionary(pair => pair.Key,
      pair => pair.Value.ConcreteTypeArguments.Select(type => type.ToString()).ToList());
    string RuntimeTypeName(TopLevelDecl declaration) =>
      ((declaration.EnclosingModuleDefinition.TryToAvoidName ? declaration.EnclosingModuleDefinition.GetCompileName(program.Options) + "." : "") +
       declaration.GetFullCompileName(program.Options)).Replace("@", "");
    var heapShapes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<ClassDecl>()
      .Where(declaration => declaration.TypeArgs.Count == 0)
      .Select(declaration => new {
        runtimeType = RuntimeTypeName(declaration),
        type = declaration.FullDafnyName,
        fields = declaration.Members.OfType<Field>().Where(field => (!field.IsGhost || compiledGhostFields?.Contains(field) == true) && !field.IsStatic)
          .Select(field => new {
            name = field.Name,
            runtimeName = field.GetCompileName(program.Options).Replace("@", ""),
            mutable = field.IsMutable,
            shape = TypeShape(field.Type)
          }).ToList(),
        logicalFields = declaration.Members.OfType<Field>().Where(field =>
            field.IsGhost && !field.IsStatic && trackedGhostFields.Contains(field))
          .Select(field => new { name = field.Name, mutable = field.IsMutable }).ToList()
      }).ToList();
    var shapes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<DatatypeDecl>()
      .Where(datatype => datatype.TypeArgs.Count == 0 || runtimeReferences && datatype is not CoDatatypeDecl)
      .SelectMany(datatype => datatype.Ctors.Where(constructor => !constructor.IsGhost && constructor.Formals.All(formal => !formal.IsGhost))
        .Select(constructor => new {
          runtimeType = (RuntimeTypeName(datatype) + (datatype.IsRecordType ? "" : "_" + constructor.GetCompileName(program.Options)) +
            (datatype.TypeArgs.Count == 0 ? "" : "`" + datatype.TypeArgs.Count)).Replace("@", ""),
          constructor = datatype.FullDafnyName + "." + constructor.Name,
          typeArguments = datatype.TypeArgs.Count,
          fields = constructor.Formals.Select((formal, index) => new {
            name = formal.Name,
            runtimeName = "_" + (formal.HasName ? formal.CompileName : "a" + index),
            shape = TypeShape(formal.Type, datatype.TypeArgs)
          }).ToList()
        })).ToList();
    // The configuration class follows the library text because the first library file starts with using directives;
    // the later files use fully qualified names so that concatenation stays valid.
    return ContractRuntimeLibrary.Read("PbtObservation.cs") + ContractRuntimeLibrary.Read("ContractRuntimeProfile.cs") +
      ContractRuntimeLibrary.Read("PbtSmt.cs") + $$"""
      namespace DafnyContractRuntime {
      internal static class ContractRuntimeConfiguration {
        internal const bool RuntimeReferences = {{(runtimeReferences ? "true" : "false")}};
        internal const bool ProfileRuntime = {{(runtimeReferences ? "true" : "false")}};
        internal const string ObservationPath = {{JsonSerializer.Serialize(observationPath)}};
        internal const string ConcreteTypes = {{JsonSerializer.Serialize(JsonSerializer.Serialize(concreteTypes))}};
        internal const string HeapShapes = {{JsonSerializer.Serialize(JsonSerializer.Serialize(heapShapes))}};
        internal const string DatatypeShapes = {{JsonSerializer.Serialize(JsonSerializer.Serialize(shapes))}};
      }
      }

      """;
  }

  internal static string TypeShapeToken(Microsoft.Dafny.Type type, IReadOnlyList<TypeParameter>? parameters = null) => Convert.ToBase64String(
    System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(TypeShape(type, parameters))));

  private static object TypeShape(Microsoft.Dafny.Type type, IReadOnlyList<TypeParameter>? parameters = null) {
    if (type.IsArrayType) {
      return new Dictionary<string, object> { ["kind"] = "reference", ["type"] = ContractHeapFactory.ArrayTypeName(type) };
    }
    type = type.NormalizeToAncestorType();
    if (type.AsTypeParameter is { } parameter) {
      return new Dictionary<string, object> { ["kind"] = "parameter", ["index"] = parameters?.ToList().IndexOf(parameter) ?? -1 };
    }
    if (type.AsDatatype != null) {
      return new Dictionary<string, object> {
        ["kind"] = "datatype",
        ["arguments"] = type.TypeArgs.Select(argument => TypeShape(argument, parameters)).ToList()
      };
    }
    if (type.AsBitVectorType is { } bitvector) {
      return new Dictionary<string, object> { ["kind"] = "bitvector", ["width"] = bitvector.Width };
    }
    if (type.IsIntegerType) {
      return new Dictionary<string, object> { ["kind"] = "integer" };
    }
    if (type.AsSeqType is { } sequence) {
      return new Dictionary<string, object> { ["kind"] = "sequence", ["element"] = TypeShape(sequence.Arg, parameters) };
    }
    if (type.AsSetType is { } set) {
      return new Dictionary<string, object> { ["kind"] = "set", ["element"] = TypeShape(set.Arg, parameters) };
    }
    if (type.AsMultiSetType is { } multiset) {
      return new Dictionary<string, object> { ["kind"] = "multiset", ["element"] = TypeShape(multiset.Arg, parameters) };
    }
    if (type.AsMapType is { } map) {
      return new Dictionary<string, object> {
        ["kind"] = "map",
        ["key"] = TypeShape(map.Domain, parameters),
        ["value"] = TypeShape(map.Range, parameters)
      };
    }
    return new Dictionary<string, object> { ["kind"] = "other" };
  }
}


public sealed record ContractAbstractChoice(string Symbol, IReadOnlyDictionary<string, ContractValue> Inputs,
  IReadOnlyDictionary<string, ContractValue>? Outputs, ContractRealizationStatus Status, bool TypeFrameOnly,
  bool ExactUnboundedContradiction = false, bool ModelCompleted = false,
  IReadOnlyList<ContractHeapObject>? PreHeap = null, IReadOnlyList<ContractHeapObject>? PostHeap = null,
  ContractValue? Receiver = null, IReadOnlyList<string>? TypeArguments = null);

public sealed class ContractRuntimeSession {
  public List<ContractAbstractChoice> Choices { get; } = [];
  public List<ContractQueryResult> Queries { get; } = [];
  public ContractRealizationResult? Failure { get; private set; }
  public string? FailureSymbol { get; private set; }
  public ContractCallObservation? ReachableStart { get; private set; }
  public ContractCallObservation? ReachableEnd { get; private set; }

  public async Task<ContractProcessResult> ExecuteAsync(ContractPreparedProgram prepared, ContractTestRequest request,
    string assemblyPath, string observationPath, string outputDirectory, CancellationToken cancellationToken) {
    using var lifetime = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    var execution = ContractExecutionProcess.RunAsync("dotnet", [assemblyPath], outputDirectory, lifetime.Token);
    var handled = new HashSet<string>(StringComparer.Ordinal);
    var nextReplayChoice = 0;
    var concreteCalls = prepared.ConcreteCalls;
    try {
      while (!execution.IsCompleted) {
        foreach (var path in Directory.EnumerateFiles(outputDirectory, Path.GetFileName(observationPath) + ".rpc.*.request")) {
          if (!handled.Add(path)) {
            continue;
          }
          var call = JsonSerializer.Deserialize<ContractCallObservation>(await File.ReadAllTextAsync(path, cancellationToken), ContractJson.Options)
            ?? throw new JsonException("Null contract runtime request.");
          var expectedTypes = concreteCalls.TryGetValue(call.Symbol, out var concrete)
            ? concrete.ConcreteTypeArguments.Select(type => type.ToString()).ToList() : [];
          if (!(call.TypeArguments ?? []).SequenceEqual(expectedTypes)) {
            throw new JsonException("Runtime type arguments do not match the original resolved call sites.");
          }
          ContractRealizationResult realization;
          if (call.Operation == ContractRuntimeOperation.Realize) {
            ContractAbstractChoice? replay = null;
            if (request.ReplayChoices != null && (!request.ReplayPrefix || nextReplayChoice < request.ReplayChoices.Count)) {
              if (nextReplayChoice < request.ReplayChoices.Count) {
                replay = request.ReplayChoices[nextReplayChoice++];
              }
              if (replay == null || replay.Symbol != call.Symbol || replay.Status != ContractRealizationStatus.Realized ||
                  replay.Outputs == null || !SameInputs(replay.Inputs, call.Inputs) || !SameHeap(replay.PreHeap, call.Heap) ||
                  !SameReceiver(replay.Receiver, call.Receiver) || !(replay.TypeArguments ?? []).SequenceEqual(expectedTypes)) {
                realization = new(ContractRealizationStatus.Error, null, [], "Replay choices do not match the actual modeled call sequence and inputs.");
              } else {
                realization = await ContractModelRealizer.RealizeAsync(prepared, request, call.Symbol, call.Inputs,
                  cancellationToken, Choices, replay.Outputs, call.Heap, replay.PostHeap, call.Receiver);
              }
            } else {
              realization = await ContractModelRealizer.RealizeAsync(prepared, request, call.Symbol, call.Inputs, cancellationToken, Choices,
                currentHeap: call.Heap, receiver: call.Receiver);
            }
          } else if (call.Operation == ContractRuntimeOperation.EntryStart) {
            if (ReachableStart != null || call.Symbol != prepared.ReachableTarget?.FullDafnyName || call.Invocation != request.Entry.ReachableInvocation) {
              realization = new(ContractRealizationStatus.Error, null, [], "Unexpected selected entry invocation.");
            } else {
              ReachableStart = call;
              realization = await CheckPreconditionAsync(prepared, request, call, observationPath, cancellationToken);
            }
          } else if (call.Operation == ContractRuntimeOperation.EntryEnd) {
            if (ReachableStart == null || ReachableEnd != null || call.Symbol != ReachableStart.Symbol ||
                call.Invocation != ReachableStart.Invocation || call.Outputs == null) {
              realization = new(ContractRealizationStatus.Error, null, [], "Selected entry return does not match its invocation.");
            } else {
              ReachableEnd = call;
              realization = new(ContractRealizationStatus.Realized, call.Outputs, [], "The selected invocation returned concrete outputs.", PostHeap: call.Heap);
            }
          } else {
            realization = await CheckPreconditionAsync(prepared, request, call, observationPath, cancellationToken);
          }
          if (call.Operation == ContractRuntimeOperation.Realize) {
            Choices.Add(new ContractAbstractChoice(call.Symbol, call.Inputs, realization.Outputs, realization.Status,
              realization.TypeFrameOnly, realization.ExactUnboundedContradiction, realization.ModelCompleted,
              PreHeap: call.Heap, PostHeap: realization.PostHeap, Receiver: call.Receiver, TypeArguments: expectedTypes));
          }
          if (realization.Status != ContractRealizationStatus.Realized) {
            Failure = realization;
            FailureSymbol = call.Symbol;
          }
          Queries.AddRange(realization.Queries);
          var response = Path.ChangeExtension(path, ".response");
          await File.WriteAllTextAsync(response + ".tmp", JsonSerializer.Serialize(realization, ContractJson.Options), cancellationToken);
          File.Move(response + ".tmp", response);
        }
        await Task.WhenAny(execution, Task.Delay(5, cancellationToken));
        cancellationToken.ThrowIfCancellationRequested();
      }
      if (request.ReplayChoices != null && nextReplayChoice != request.ReplayChoices.Count && Failure == null) {
        Failure = new(ContractRealizationStatus.Error, null, [], "Execution did not consume all recorded replay choices.");
      }
      return await execution;
    }
    finally {
      await lifetime.CancelAsync();
      await execution;
    }
  }

  private static bool SameInputs(IReadOnlyDictionary<string, ContractValue> expected, IReadOnlyDictionary<string, ContractValue> actual) =>
    expected.Count == actual.Count && expected.All(pair => actual.TryGetValue(pair.Key, out var value) && ContractHeapFactory.ValuesEqual(pair.Value, value));

  private static bool SameReceiver(ContractValue? expected, ContractValue? actual) =>
    expected == null || actual == null ? expected == actual : ContractHeapFactory.ValuesEqual(expected, actual);

  private static bool SameHeap(IReadOnlyList<ContractHeapObject>? expected, IReadOnlyList<ContractHeapObject>? actual) =>
    (expected?.Count ?? 0) == (actual?.Count ?? 0) && (expected ?? []).All(item =>
      (actual ?? []).Count(other => other.Id == item.Id && other.Type == item.Type && SameInputs(item.Fields, other.Fields) &&
        (item.Dimensions ?? []).SequenceEqual(other.Dimensions ?? []) &&
        (item.Elements?.Count ?? 0) == (other.Elements?.Count ?? 0) &&
        (item.Elements ?? []).Select((value, index) => ContractHeapFactory.ValuesEqual(value, other.Elements![index])).All(equal => equal)) == 1);

  private async Task<ContractRealizationResult> CheckPreconditionAsync(ContractPreparedProgram prepared,
    ContractTestRequest request, ContractCallObservation call, string observationPath, CancellationToken cancellationToken) {
    var concreteEntry = prepared.ConcreteCalls.TryGetValue(call.Symbol, out var concrete);
    if (call.Heap?.Count is null or 0 && call.Receiver == null && !concreteEntry) {
      return await ContractModelRealizer.CheckPreconditionAsync(prepared, request, call.Symbol, call.Inputs,
        cancellationToken, Choices);
    }
    var childRequest = request with {
      Entry = new ContractEntry(call.Symbol,
      concreteEntry ? concrete!.ConcreteTypeArguments.Select(type => type.ToString()).ToList() : null, Receiver: call.Receiver),
      Inputs = call.Inputs,
      Heap = call.Heap
    };
    var child = ContractHarnessBuilder.Prepare(prepared.Program, childRequest);
    var queries = new List<ContractQueryResult>();
    var choices = ContractModelRealizer.PureChoiceConstraints(child, Choices,
      child.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
    var premise = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(child, childRequest, ContractQueryKind.PremiseConsistency, choiceConstraints: choices),
      ContractQueryKind.PremiseConsistency, prepared.Program.Options, cancellationToken, queryName: ContractQueryBuilder.Name(child),
      sourceSnapshots: child.DiagnosticSourceSnapshots, sourcePath: child.Source.Path);
    queries.Add(premise);
    if (premise.Outcome != ContractQueryOutcome.Sat) {
      return new(ContractRealizationStatus.Inconclusive, null, queries, "Call-state premise was not established satisfiable before body entry.");
    }
    var check = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(child, childRequest, ContractQueryKind.CallPrecondition, choiceConstraints: choices),
      ContractQueryKind.CallPrecondition, prepared.Program.Options, cancellationToken, queryName: ContractQueryBuilder.Name(child),
      sourceSnapshots: child.DiagnosticSourceSnapshots, sourcePath: child.Source.Path);
    queries.Add(check);
    if (check.Outcome == ContractQueryOutcome.Unsat) {
      return new(ContractRealizationStatus.Realized, new Dictionary<string, ContractValue>(), queries, "Call precondition holds before body entry.");
    }
    if (check.Outcome == ContractQueryOutcome.Sat) {
      var opposite = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(child, childRequest, ContractQueryKind.CallPrecondition, negate: true, choiceConstraints: choices),
        ContractQueryKind.CallPrecondition, prepared.Program.Options, cancellationToken, queryName: ContractQueryBuilder.Name(child),
        sourceSnapshots: child.DiagnosticSourceSnapshots, sourcePath: child.Source.Path);
      queries.Add(opposite);
      if (opposite.Outcome == ContractQueryOutcome.Unsat) {
        return new(ContractRealizationStatus.CallPreconditionViolation, null, queries, "Call precondition is false before body entry.");
      }
    }
    return new(ContractRealizationStatus.Inconclusive, null, queries, "Call precondition could not be established before body entry.");
  }
}
