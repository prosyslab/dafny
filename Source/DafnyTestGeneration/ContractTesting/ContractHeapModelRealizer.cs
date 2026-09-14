using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static partial class ContractModelRealizer {
  private sealed record PostCell(HeapSlot Object, HeapCell Cell, OutputFormal Parameter);

  private static async Task<ContractRealizationResult> RealizeHeapAsync(ContractPreparedProgram prepared,
    ContractTestRequest request, MethodOrFunction callable, IReadOnlyDictionary<string, ContractValue> inputs,
    CancellationToken cancellationToken, IReadOnlyList<ContractAbstractChoice>? priorChoices,
    IReadOnlyDictionary<string, ContractValue>? replayOutputs, IReadOnlyList<ContractHeapObject>? currentHeap,
    IReadOnlyList<ContractHeapObject>? replayHeap, ContractValue? receiver) {
    if (callable.TypeArgs.Count != 0) {
      return new(ContractRealizationStatus.Unsupported, null, [],
        "Heap realization requires a monomorphic absent callable with observable fields.");
    }
    if (currentHeap == null) {
      return new(ContractRealizationStatus.Error, null, [],
        "Heap realization requires the actual call-entry heap; the initial test heap is not a substitute.");
    }
    var childRequest = request with {
      Entry = new ContractEntry(callable.FullDafnyName,
        callable is ContractConcreteMethod concrete ? concrete.ConcreteTypeArguments.Select(type => type.ToString()).ToList() : null,
        Receiver: receiver),
      Inputs = inputs,
      Heap = currentHeap
    };
    var childPrepared = ContractHarnessBuilder.Prepare(prepared.Program, childRequest);
    // The selector's function descriptor maps result references to one output formal.
    // Its empty modifies frame keeps heap-reading function models observationally pure.
    var child = childPrepared.Method;
    var heap = childPrepared.Heap;
    if (heap == null) {
      return new(ContractRealizationStatus.Unsupported, null, [], "No concrete call-entry heap was available.");
    }
    var outputs = OutputFormals(child, prepared.Program);
    if (outputs.Any(output => !ContractHarnessBuilder.SupportedType(output.Type))) {
      return new(ContractRealizationStatus.Unsupported, null, [], "Unsupported heap-call output model type.");
    }
    var allowed = ModifiedFields(child, inputs, receiver, heap);
    var fields = new List<PostCell>();
    var names = child.Ins.Select(input => input.Name).Concat(outputs.Select(output => output.Name))
      .Concat(heap.Slots.Select(slot => slot.VariableName)).Append(childPrepared.ReceiverName).ToHashSet();
    foreach (var slot in heap.Slots) {
      foreach (var field in slot.Cells.Where(field => allowed.Contains((slot.Object.Id, field.Name)))) {
        if (!ContractHarnessBuilder.SupportedType(field.Type)) {
          return new(ContractRealizationStatus.Unsupported, null, [],
            "Modeled mutable reference fields require reference-choice materialization: " + slot.Object.Id + "." + field.Name);
        }
        var name = ContractBodyNames.Family(prepared.Program, "contractPost") + fields.Count;
        while (!names.Add(name)) {
          name += "0";
        }
        fields.Add(new(slot, field, new OutputFormal(name, field.Type)));
      }
    }
    var slots = outputs.Concat(fields.Select(field => field.Parameter)).ToList();
    var precondition = Conjunction(child.Req.Select(clause => ContractQueryBuilder.RenderExpression(childPrepared, clause.E)));
    var postcondition = Conjunction(child.Ens.Select(clause => ContractQueryBuilder.RenderExpression(childPrepared, clause.E)));
    var choices = PureChoiceConstraints(prepared, priorChoices ?? [], child.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
    var queries = new List<ContractQueryResult>();
    async Task<ContractQueryResult> Check(string assertion, ContractQueryKind kind,
      bool transition = false, bool assumePostcondition = false, bool assumePrecondition = false,
      IReadOnlyDictionary<string, ContractValue>? values = null, bool captureModel = false) {
      var parameters = child.Ins.Select(input => input.Name + ": " + input.Type).ToList();
      if (!child.IsStatic) {
        parameters.Add(childPrepared.ReceiverName + ": " + child.EnclosingClass.Name);
      }
      if (transition) {
        parameters.AddRange(slots.Select(slot => slot.Name + ": " + slot.Type));
      }
      parameters.Add(heap.QueryParameters);
      var assumptions = child.Ins.Select(input => input.Name + " == " + heap.InputExpression(input.Name)).ToList();
      assumptions.AddRange(heap.InitialConstraints);
      assumptions.AddRange(choices);
      if (!child.IsStatic) {
        assumptions.Add(childPrepared.ReceiverName + " == " + heap.ReferenceExpression(receiver!.Value!));
      }
      if (assumePrecondition) {
        assumptions.Add(precondition);
      }
      if (values != null) {
        assumptions.AddRange(slots.Select(slot => slot.Name + " == " + heap.ValueExpression(values[slot.Name], slot.Type)));
      }
      var assignments = transition ? string.Join("\n", fields.Select(field =>
        field.Cell.Access + " := " + field.Parameter.Name + ";")) : "";
      var declaration = "\nmethod " + ContractQueryBuilder.Name(prepared) + "(" + string.Join(", ", parameters) + ")\n" +
        string.Join("\n", assumptions.Select(assumption => "requires " + assumption)) + "\n" + heap.QueryModifies +
        "\n{\n" + assignments + "\n" + (assumePostcondition ? "assume " + postcondition + ";\n" : "") +
        "assert {:error \"" + ContractQueryBuilder.TargetMarker + "\"} " + assertion + ";\n}\n";
      var source = ContractHarnessBuilder.Insert(childPrepared, declaration);
      var result = await ContractSolver.CheckAsync(source, kind, prepared.Program.Options, cancellationToken, captureModel,
        ContractQueryBuilder.Name(prepared), childPrepared.DiagnosticSourceSnapshots, childPrepared.Source.Path);
      queries.Add(result);
      return result;
    }
    ContractRealizationResult Unresolved(ContractQueryResult query, string reason) => new(
      query.Outcome switch {
        ContractQueryOutcome.Timeout => ContractRealizationStatus.Timeout,
        ContractQueryOutcome.Error => ContractRealizationStatus.Error,
        _ => ContractRealizationStatus.Inconclusive
      }, null, queries, reason, child.Ens.Count == 0);

    var premise = await Check("false", ContractQueryKind.PremiseConsistency);
    if (premise.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(premise, "The actual call-entry heap/input premise was not established satisfiable.");
    }
    var pre = await Check(precondition, ContractQueryKind.CallPrecondition);
    if (pre.Outcome != ContractQueryOutcome.Unsat) {
      if (pre.Outcome == ContractQueryOutcome.Sat) {
        var opposite = await Check("!(" + precondition + ")", ContractQueryKind.CallPrecondition);
        if (opposite.Outcome == ContractQueryOutcome.Unsat) {
          return new(ContractRealizationStatus.CallPreconditionViolation, null, queries,
            "The original precondition is false in the actual call-entry heap.");
        }
        return Unresolved(opposite, "The call precondition is not fixed by the supplied heap.");
      }
      return Unresolved(pre, "The original heap-call precondition could not be decided.");
    }
    IReadOnlyDictionary<string, ContractValue> values;
    var completed = false;
    if (replayOutputs != null || replayHeap != null) {
      if (replayOutputs == null || replayHeap == null || !outputs.Select(output => output.Name).ToHashSet().SetEquals(replayOutputs.Keys)) {
        return new(ContractRealizationStatus.Error, null, queries, "Heap replay requires the complete output and post-heap tuple.");
      }
      var replayRequest = childRequest with { Heap = replayHeap };
      _ = ContractHeapFactory.Prepare(prepared.Program, replayRequest);
      if (!currentHeap.Select(item => (item.Id, item.Type)).ToHashSet().SetEquals(replayHeap.Select(item => (item.Id, item.Type))) ||
          currentHeap.Count != replayHeap.Count) {
        return new(ContractRealizationStatus.Error, null, queries, "Replay changed the modeled heap object identities or types.");
      }
      var replayObjects = replayHeap.ToDictionary(item => item.Id);
      foreach (var slot in heap.Slots) {
        if (slot.IsArray && !(slot.Object.Dimensions ?? []).SequenceEqual(replayObjects[slot.Object.Id].Dimensions ?? [])) {
          return new(ContractRealizationStatus.Error, null, queries, "Replay changed an existing array object's dimensions.");
        }
        foreach (var field in slot.Cells.Where(field => !allowed.Contains((slot.Object.Id, field.Name)))) {
          if (!ContractHeapFactory.ValuesEqual(field.InitialValue, CellValue(replayObjects[slot.Object.Id], field))) {
            return new(ContractRealizationStatus.Error, null, queries, "Replay changed a field outside the original call frame.");
          }
        }
      }
      var combined = replayOutputs.ToDictionary(pair => pair.Key, pair => pair.Value);
      foreach (var field in fields) {
        combined.Add(field.Parameter.Name, CellValue(replayObjects[field.Object.Object.Id], field.Cell));
      }
      values = combined;
    } else {
      var relation = await Check("false", ContractQueryKind.ContractRealization, transition: true,
        assumePostcondition: true, assumePrecondition: true, captureModel: true);
      if (relation.Outcome != ContractQueryOutcome.Sat) {
        return Unresolved(relation, relation.Outcome == ContractQueryOutcome.Unsat
          ? "No model in the represented heap transition space; allocation/reference shapes are incomplete, so this is not an unbounded contradiction."
          : "The original heap transition relation could not be solved.");
      }
      if (!TryExtractOutputs(relation.Diagnostics, prepared.Program.Options, slots, out values, out completed)) {
        return new(ContractRealizationStatus.Inconclusive, null, queries,
          "A complete correlated output/post-heap model could not be materialized.");
      }
    }
    var concretePremise = await Check("false", ContractQueryKind.PremiseConsistency, transition: true,
      assumePrecondition: true, values: values);
    if (concretePremise.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(concretePremise, "The materialized output/post-heap tuple has an inconsistent premise.");
    }
    var recheck = await Check(postcondition, ContractQueryKind.ContractRealization, transition: true,
      assumePrecondition: true, values: values);
    if (recheck.Outcome != ContractQueryOutcome.Unsat) {
      return Unresolved(recheck, "The materialized output/post-heap tuple did not establish the original Q.");
    }
    var postHeap = currentHeap.Select(item => {
      var updated = item.Fields.ToDictionary(pair => pair.Key, pair => pair.Value);
      var elements = item.Elements?.ToList();
      foreach (var field in fields.Where(field => field.Object.Object.Id == item.Id)) {
        if (field.Cell.Index is { } index) {
          elements![index] = values[field.Parameter.Name];
        } else {
          updated[field.Cell.Name] = values[field.Parameter.Name];
        }
      }
      return item with { Fields = updated, Elements = elements };
    }).ToList();
    return new(ContractRealizationStatus.Realized, outputs.ToDictionary(output => output.Name, output => values[output.Name]),
      queries, "One correlated output/post-heap model passed original P/Q and frame rechecks at the actual call-entry state.",
      child.Ens.Count == 0, ModelCompleted: completed, PostHeap: postHeap);
  }

  private static ContractValue CellValue(ContractHeapObject item, HeapCell cell) =>
    cell.Index is { } index ? item.Elements![index] : item.Fields[cell.Name];

  private static HashSet<(string Object, string Field)> ModifiedFields(Method method,
    IReadOnlyDictionary<string, ContractValue> inputs, ContractValue? receiver, ContractHeapPlan heap) {
    ContractValue Reference(Expression expression) => expression.Resolved switch {
      ThisExpr when receiver != null => receiver,
      IdentifierExpr identifier when inputs.TryGetValue(identifier.Name, out var value) => value,
      MemberSelectExpr member => heap.Slots.Single(slot => slot.Object.Id == Reference(member.Obj).Value).Object.Fields[member.MemberName],
      _ => throw new NotSupportedException("The modeled call frame requires concrete reference expressions.")
    };
    var allowed = new HashSet<(string Object, string Field)>();
    foreach (var frame in method.Mod.Expressions ?? []) {
      var value = Reference(frame.E);
      if (value.Kind == ContractValueKind.Null) {
        continue;
      }
      var slot = heap.Slots.SingleOrDefault(slot => value.Kind == ContractValueKind.Reference && slot.Object.Id == value.Value)
        ?? throw new ArgumentException("The modeled call frame references an unknown heap object.");
      foreach (var field in slot.Cells.Where(field => frame.FieldName == null || field.Name == frame.FieldName)) {
        allowed.Add((slot.Object.Id, field.Name));
      }
    }
    return allowed;
  }
}
