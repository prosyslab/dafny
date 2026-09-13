using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractPathExplorer {
  public static string TargetBody(ContractBodyExpansionResult expansion, string goalId) {
    if (!expansion.Goals.Any(goal => goal.Id == goalId)) {
      throw new ArgumentException("The selected body goal does not exist.", nameof(goalId));
    }
    var capture = string.Join("\n", expansion.TraceEvents.Select(item =>
      "assume " + item.Name + " == " + item.Name + "Local;"));
    return expansion.BodySource.Replace(ContractBodyExpansionResult.Marker(goalId),
      capture + "\nassert {:error \"" + ContractQueryBuilder.TargetMarker + "\"} false;", StringComparison.Ordinal);
  }

  public static ContractPathCandidate Candidate(ContractBodyExpansionResult expansion, ContractBodyGoal goal,
    IReadOnlyDictionary<string, ContractValue>? traceValues, ContractExpectedEntry? expectedEntry = null) {
    if (traceValues == null || goal.BranchValue == null && expectedEntry == null) {
      return new(goal.Id, [], expansion.AbstractCalls, expansion.TrustDependencies, ContractTraceReplayStatus.Unsupported);
    }
    var ordered = expansion.TraceEvents.Select(item => (Event: item,
      Order: int.Parse(traceValues[item.Name].Value!, System.Globalization.CultureInfo.InvariantCulture)))
      .Where(item => item.Order > 0).OrderBy(item => item.Order).ToList();
    if (!ordered.Select(item => item.Order).SequenceEqual(Enumerable.Range(1, ordered.Count)) ||
        (expectedEntry == null && (ordered.Count == 0 || ordered[^1].Event.Location != goal.Location || ordered[^1].Event.Value != goal.BranchValue))) {
      return new(goal.Id, [], expansion.AbstractCalls, expansion.TrustDependencies, ContractTraceReplayStatus.Unsupported);
    }
    return new(goal.Id, ordered.Select(item => new ContractBranchObservation(item.Event.Location.Symbol,
      item.Event.Location.Position, item.Event.Location.Line, item.Event.Location.Column, item.Event.Value)).ToList(),
      expansion.AbstractCalls, expansion.TrustDependencies, ExpectedEntry: expectedEntry);
  }
}

/// <summary>Captures native call values and bounded heap identities; Dafny still defines every call relation.</summary>
internal sealed class ContractAbstractCapturePlan {
  private sealed record Slot(string Name, DafnyType Type, string Expression, DafnyType OriginalType);
  private sealed record Call(ContractBodyAbstractCall Source, Slot Order, IReadOnlyList<Slot> Inputs,
    IReadOnlyList<Slot> Outputs, Slot? Receiver, IReadOnlyList<Slot> PreHeap, IReadOnlyList<Slot> PostHeap);
  private readonly ContractInputShape shape;
  private readonly string module;
  private readonly string counter;
  private readonly List<Call> calls = [];
  private readonly List<Slot> slots = [];

  public ContractAbstractCapturePlan(ContractBodyExpansionResult expansion, ContractInputShape shape, string module) {
    this.shape = shape;
    this.module = module;
    counter = expansion.CapturedCalls[0].Id + "Count";
    Slot Add(string name, DafnyType type, string expression) {
      var encoded = expression;
      if (type.IsRefType) {
        encoded = "-2";
        foreach (var item in (shape.Objects ?? []).Reverse()) {
          var objectType = item.ElementType == null
            ? UserDefinedType.FromTopLevelDecl(item.Class.Origin, item.Class)
            : (DafnyType)new UserDefinedType(item.Class.Origin, item.TypeName, [item.ElementType]) { ResolvedClass = item.Class };
          if (objectType.IsSubtypeOf(type, false, true)) {
            encoded = "(if " + expression + " == " + item.VariableName + " then " + item.Id + " else " + encoded + ")";
          }
        }
        if (!type.IsNonNullRefType) { encoded = "(if " + expression + " == null then -1 else " + encoded + ")"; }
      }
      var slot = new Slot(name, type.IsRefType ? DafnyType.Int : type, encoded, type);
      slots.Add(slot);
      return slot;
    }
    IReadOnlyList<Slot> Heap(string prefix) => (shape.Objects ?? []).SelectMany(item =>
      item.Fields.Select(field => Add(prefix + "Object" + item.Id + "Field" + field.Key, field.Value.Type,
        item.VariableName + "." + field.Key)).Concat((item.Elements ?? []).Select((element, index) =>
        Add(prefix + "Object" + item.Id + "Element" + index, element.Type, item.VariableName + "[" + index + "]")))).ToList();
    foreach (var item in expansion.CapturedCalls) {
      var order = Add(item.Id + "Order", DafnyType.Int, counter);
      calls.Add(new(item, order,
        item.Inputs.Select((value, index) => Add(item.Id + "Input" + index, value.Type, value.Expression)).ToList(),
        item.Outputs.Select((value, index) => Add(item.Id + "Output" + index, value.Type, value.Expression)).ToList(),
        item.Receiver == null ? null : Add(item.Id + "Receiver", item.Receiver.Type, item.Receiver.Expression),
        Heap(item.Id + "Pre"), Heap(item.Id + "Post")));
    }
  }

  public IReadOnlyList<(string Name, DafnyType Type)> Parameters => slots.Select(slot => (slot.Name, slot.Type)).ToList();
  public string Apply(string body) {
    foreach (var call in calls) {
      var before = call.Inputs.Concat(call.Receiver == null ? [] : new[] { call.Receiver }).Concat(call.PreHeap);
      var after = call.Outputs.Concat(call.PostHeap).Append(call.Order);
      body = body.Replace(call.Source.BeforeMarker, Assign(before), StringComparison.Ordinal)
        .Replace(call.Source.AfterMarker, Assign(after) + "\n" + counter + " := " + counter + " + 1;", StringComparison.Ordinal);
    }
    var captures = string.Join("\n", slots.Select(slot => "assume " + slot.Name + " == " + slot.Name + "Local;"));
    var target = "assert {:error \"" + ContractQueryBuilder.TargetMarker + "\"} false;";
    return "ghost var " + counter + ": int := 1;\n" + string.Join("\n", slots.Select(slot =>
      "ghost var " + slot.Name + "Local: " + slot.Type + " := " + (calls.Any(call => call.Order == slot) ? "0" : slot.Name) + ";")) +
      "\n" + body.Replace(target, captures + "\n" + target, StringComparison.Ordinal);
  }
  private static string Assign(IEnumerable<Slot> values) => string.Join("\n", values.Select(slot => slot.Name + "Local := " + slot.Expression + ";"));

  public bool TryMaterialize(IReadOnlyDictionary<string, ContractValue> values, bool completed,
    out IReadOnlyList<ContractAbstractChoice> choices, out IReadOnlyList<string> bindings) {
    var result = new List<ContractAbstractChoice>();
    var fixedSlots = new List<Slot>();
    var pure = new HashSet<string>(StringComparer.Ordinal);
    var ordered = calls.Select(call => (Call: call, Order: int.Parse(values[call.Order.Name].Value!,
      System.Globalization.CultureInfo.InvariantCulture))).Where(call => call.Order > 0).OrderBy(call => call.Order).ToList();
    choices = []; bindings = [];
    if (!ordered.Select(call => call.Order).SequenceEqual(Enumerable.Range(1, ordered.Count))) { return false; }
    ContractValue? Decode(Slot slot) {
      var value = values[slot.Name];
      bool KnownReferences(ContractValue item) => item.Kind == ContractValueKind.Reference
        ? (shape.Objects ?? []).Any(candidate => "object" + candidate.Id == item.Value)
        : (item.Items ?? []).Concat(item.Fields?.Values ?? [])
          .Concat((item.Entries ?? []).SelectMany(entry => new[] { entry.Key, entry.Value }))
          .All(KnownReferences);
      if (!slot.OriginalType.IsRefType) { return KnownReferences(value) ? value : null; }
      if (value.Value == "-1" && !slot.OriginalType.IsNonNullRefType) { return new(ContractValueKind.Null); }
      return (shape.Objects ?? []).Any(item => item.Id == value.Value) ? new(ContractValueKind.Reference, "object" + value.Value) : null;
    }
    IReadOnlyList<ContractHeapObject>? Heap(IReadOnlyList<Slot> heapSlots) {
      var cells = heapSlots.Select(Decode).ToList();
      if (cells.Any(cell => cell == null)) { return null; }
      var index = 0;
      return (shape.Objects ?? []).Select(item => new ContractHeapObject("object" + item.Id, item.TypeName,
        item.Fields.ToDictionary(field => field.Key, _ => cells[index++]!),
        item.Elements == null ? null : [item.Elements.Count], item.Elements?.Select(_ => cells[index++]!).ToList())).ToList();
    }
    foreach (var (call, _) in ordered) {
      var arguments = call.Inputs.Select(Decode).ToList();
      var outputs = call.Outputs.Select(Decode).ToList();
      var receiver = call.Receiver == null ? null : Decode(call.Receiver);
      var pre = Heap(call.PreHeap);
      var post = Heap(call.PostHeap);
      if (arguments.Any(value => value == null) || outputs.Any(value => value == null) ||
          call.Receiver != null && receiver == null || pre == null || post == null) { return false; }
      var inputMap = call.Source.Inputs.Select((value, index) => (value.Name, Value: arguments[index]!)).ToDictionary(item => item.Name, item => item.Value);
      var outputMap = call.Source.Outputs.Select((value, index) => (value.Name, Value: outputs[index]!)).ToDictionary(item => item.Name, item => item.Value);
      var choice = new ContractAbstractChoice(call.Source.Callable.FullDafnyName, inputMap, outputMap,
        ContractRealizationStatus.Realized, call.Source.Callable.Ens.Count == 0, ModelCompleted: completed,
        PreHeap: pre, PostHeap: post, Receiver: receiver,
        TypeArguments: call.Source.TypeArguments?.Count > 0 ? call.Source.TypeArguments.Select(type => type.ToString()).ToList() : null);
      var key = JsonSerializer.Serialize(new { choice.Symbol, choice.TypeArguments, choice.Inputs, choice.Receiver, choice.PreHeap }, ContractJson.Options);
      if (call.Source.Callable is not Microsoft.Dafny.Function || pure.Add(key)) { result.Add(choice); }
      fixedSlots.AddRange(call.Inputs.Concat(call.Outputs).Concat(call.PreHeap).Concat(call.PostHeap)
        .Concat(call.Receiver == null ? [] : new[] { call.Receiver }));
    }
    choices = result;
    bindings = fixedSlots.Concat(calls.Select(call => call.Order)).Select(slot => slot.Name + " == " +
      shape.ConcreteExpression(values[slot.Name], module)).ToList();
    return true;
  }
}
