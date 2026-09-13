#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Text;
using System.Text.Json;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractSourceEdit(Uri SourceUri, int Position, string Text);

public sealed class ContractHeapPlan {
  public IReadOnlyList<(int Position, string Text)> SourceInsertions { get; }
  public IReadOnlyList<ContractSourceEdit> SourceEdits { get; }
  public string AllocationStatements { get; }
  public string InitialCaptureStatements { get; }
  public string FinalCaptureStatements { get; }
  public string QueryParameters { get; }
  public IReadOnlyList<string> InitialConstraints { get; }
  public string QueryModifies { get; }

  private readonly IReadOnlyDictionary<string, ContractValue> inputs;
  private readonly IReadOnlyDictionary<string, HeapSlot> slots;
  private readonly IReadOnlyList<HeapSlot> orderedSlots;
  internal IReadOnlyList<HeapSlot> Slots => orderedSlots;
  internal string ValueExpression(ContractValue value, DafnyType? type) => ContractHeapFactory.ValueExpression(value, type, slots);

  internal string LogicalFieldsBase64(string id) {
    if (!slots.TryGetValue(id, out var slot)) {
      throw new ArgumentException($"Unknown heap object id '{id}'.", nameof(id));
    }
    var logical = slot.Fields.Where(field => field.IsGhost).ToDictionary(field => field.Name,
      field => slot.Object.Fields[field.Name]);
    return Convert.ToBase64String(Encoding.UTF8.GetBytes(
      JsonSerializer.Serialize(logical, ContractJson.Options)));
  }

  internal ContractHeapPlan(
    IReadOnlyList<(int Position, string Text)> sourceInsertions,
    string allocationStatements,
    string initialCaptureStatements,
    string finalCaptureStatements,
    string queryParameters,
    IReadOnlyList<string> initialConstraints,
    string queryModifies,
    IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyDictionary<string, HeapSlot> slots,
    IReadOnlyList<HeapSlot> orderedSlots, IReadOnlyList<ContractSourceEdit> sourceEdits) {
    SourceInsertions = sourceInsertions;
    SourceEdits = sourceEdits;
    AllocationStatements = allocationStatements;
    InitialCaptureStatements = initialCaptureStatements;
    FinalCaptureStatements = finalCaptureStatements;
    QueryParameters = queryParameters;
    InitialConstraints = initialConstraints;
    QueryModifies = queryModifies;
    this.inputs = inputs;
    this.slots = slots;
    this.orderedSlots = orderedSlots;
  }

  public string ReferenceExpression(string id) {
    if (!slots.TryGetValue(id, out var slot)) {
      throw new ArgumentException($"Unknown heap object id '{id}'.", nameof(id));
    }
    return slot.VariableName;
  }

  public string InputExpression(string name) {
    if (!inputs.TryGetValue(name, out var value)) {
      throw new ArgumentException($"Unknown contract input '{name}'.", nameof(name));
    }
    return ContractHeapFactory.ValueExpression(value, null, slots);
  }

  public string QueryAssignments(IReadOnlyDictionary<string, ContractValue> observations) {
    ArgumentNullException.ThrowIfNull(observations);
    var lengthError = ValidateLengths(observations, false);
    if (lengthError != null) { throw new ArgumentException(lengthError, nameof(observations)); }
    var assignments = new List<string>();
    foreach (var slot in orderedSlots) {
      foreach (var cell in slot.Cells) {
        var key = FinalObservationKey(slot.Object.Id, cell.Name);
        if (!observations.TryGetValue(key, out var value)) {
          throw new ArgumentException($"Missing final heap observation '{key}'.", nameof(observations));
        }
        if (!cell.Mutable) {
          if (!ContractHeapFactory.ValuesEqual(cell.InitialValue, value)) {
            throw new NotSupportedException(
              $"Immutable heap field '{slot.Object.Id}.{cell.Name}' changed in the modeled post-state.");
          }
          continue;
        }
        assignments.Add(cell.Access + " := " +
          ContractHeapFactory.ValueExpression(value, cell.Type, slots) + ";");
      }
    }
    return string.Join("\n", assignments);
  }

  public string? ValidateInitialObservations(IReadOnlyDictionary<string, ContractValue> observations) {
    ArgumentNullException.ThrowIfNull(observations);
    var lengthError = ValidateLengths(observations, true);
    if (lengthError != null) { return lengthError; }
    foreach (var slot in orderedSlots) {
      foreach (var cell in slot.Cells) {
        var key = InitialObservationKey(slot.Object.Id, cell.Name);
        if (!observations.TryGetValue(key, out var observed)) {
          return $"Missing initial heap observation '{key}'.";
        }
        if (!ContractHeapFactory.ValuesEqual(cell.InitialValue, observed)) {
          return $"Initial heap observation '{key}' does not match the requested state.";
        }
      }
    }
    return null;
  }

  public string? CheckFrame(Method method, IReadOnlyDictionary<string, ContractValue> actualInputs,
    IReadOnlyDictionary<string, ContractValue> observations, ContractValue? receiver = null) {
    ArgumentNullException.ThrowIfNull(method);
    ArgumentNullException.ThrowIfNull(actualInputs);
    ArgumentNullException.ThrowIfNull(observations);
    var lengthError = ValidateLengths(observations, false);
    if (lengthError != null) { return lengthError; }
    var allowedIds = new HashSet<string>(StringComparer.Ordinal);
    foreach (var frameExpression in method.Mod?.Expressions ?? Enumerable.Empty<FrameExpression>()) {
      var expression = frameExpression.E.Resolved ?? frameExpression.E;
      var value = expression is ThisExpr ? receiver : expression is IdentifierExpr { Var: Formal formal } &&
        actualInputs.TryGetValue(formal.Name, out var input) ? input : null;
      if (frameExpression.FieldName != null || value == null ||
          value.Kind != ContractValueKind.Reference || value.Value == null || !slots.ContainsKey(value.Value)) {
        throw new NotSupportedException(
          $"Only modifies clauses naming the receiver or reference formals are supported at '{method.FullDafnyName}'.");
      }
      allowedIds.Add(value.Value);
    }

    foreach (var slot in orderedSlots.Where(slot => !allowedIds.Contains(slot.Object.Id))) {
      foreach (var cell in slot.Cells) {
        var key = FinalObservationKey(slot.Object.Id, cell.Name);
        if (!observations.TryGetValue(key, out var observed)) {
          return $"Missing final heap observation '{key}'.";
        }
        if (!ContractHeapFactory.ValuesEqual(cell.InitialValue, observed)) {
          return $"Frame violation: '{slot.Object.Id}.{cell.Name}' changed outside the modifies clause.";
        }
      }
    }
    return null;
  }

  private string? ValidateLengths(IReadOnlyDictionary<string, ContractValue> observations, bool initial) {
    foreach (var slot in orderedSlots.Where(slot => slot.IsArray)) {
      var key = initial ? InitialObservationKey(slot.Object.Id, "$length") : FinalObservationKey(slot.Object.Id, "$length");
      if (!observations.TryGetValue(key, out var value) || value.Kind != ContractValueKind.Integer ||
          value.Value != slot.Object.Dimensions![0].ToString(System.Globalization.CultureInfo.InvariantCulture)) {
        return "Array length observation '" + key + "' does not match its immutable dimension.";
      }
    }
    return null;
  }

  internal static string InitialObservationKey(string id, string field) => $"$initial/{id}/{field}";
  internal static string FinalObservationKey(string id, string field) => $"$final/{id}/{field}";
}

internal sealed record HeapCell(string Name, string Access, DafnyType Type,
  ContractValue InitialValue, bool RuntimeVisible = true, bool Mutable = true, int? Index = null);
internal sealed record HeapSlot(ContractHeapObject Object, ClassDecl Class,
  IReadOnlyList<Field> Fields, string VariableName, string SourceTypeName, string SourceModuleName,
  DafnyType? ElementType = null) {
  public bool IsArray => ElementType != null;
  public IReadOnlyList<HeapCell> Cells => IsArray
    ? Object.Elements!.Select((value, index) => new HeapCell("[" + index + "]", VariableName + "[" + index + "]",
      ElementType!, value, Index: index)).ToList()
    : Fields.Select(field => new HeapCell(field.Name, VariableName + "." + field.Name, field.Type,
      Object.Fields[field.Name], !field.IsGhost, field.IsMutable)).ToList();
}

/// <summary>
/// Builds diagnostic source fragments for a finite, explicitly supplied unit-mode heap.
/// </summary>
public static class ContractHeapFactory {
  private const string ConstructorName = "ContractDiagnosticCreate";
  private static readonly Regex IdPattern = new("^[A-Za-z_][A-Za-z0-9_-]*$", RegexOptions.CultureInvariant);

  public static ContractHeapPlan Prepare(Program program, ContractTestRequest request) =>
    Prepare(program, request, ResolvedArrayTypes);

  internal static ContractHeapPlan Prepare(Program program, ContractTestRequest request,
    Func<Program, IReadOnlyDictionary<string, DafnyType>> resolveArrayTypes) {
    ArgumentNullException.ThrowIfNull(program);
    ArgumentNullException.ThrowIfNull(request);
    ArgumentNullException.ThrowIfNull(resolveArrayTypes);
    if (request.Entry.InputMode != ContractInputMode.Unit) {
      throw new NotSupportedException("Synthetic heap realization supports unit-mode entries only.");
    }

    var entry = ContractCallableSelector.SelectMethod(program, request.Entry);
    var heapObjects = request.Heap ?? [];
    var duplicateId = heapObjects.GroupBy(item => item.Id, StringComparer.Ordinal)
      .FirstOrDefault(group => group.Count() > 1)?.Key;
    if (duplicateId != null) {
      throw new ArgumentException($"Duplicate heap object id '{duplicateId}'.", nameof(request));
    }

    var classes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<ClassDecl>().ToList();
    IReadOnlyDictionary<string, DafnyType>? arrayTypes = null;
    var slots = new Dictionary<string, HeapSlot>(StringComparer.Ordinal);
    var heapPrefix = ContractBodyNames.Family(program, "contractHeap");
    for (var index = 0; index < heapObjects.Count; index++) {
      var item = heapObjects[index];
      if (string.IsNullOrWhiteSpace(item.Id) || !IdPattern.IsMatch(item.Id)) {
        throw new ArgumentException($"Heap object id '{item.Id}' is not a supported stable id.", nameof(request));
      }
      if (item.Dimensions != null || item.Elements != null) {
        if (item.Dimensions is not { Count: 1 } || item.Dimensions[0] < 0 || item.Elements == null ||
            item.Elements.Count != item.Dimensions[0] || item.Fields.Count != 0) {
          throw new ArgumentException("A one-dimensional array requires one nonnegative dimension, exactly that many elements, and empty fields.");
        }
        arrayTypes ??= resolveArrayTypes(program);
        if (!arrayTypes.TryGetValue(item.Type, out var arrayType)) {
          throw new ArgumentException("The array heap type does not match a resolved one-dimensional array type in the source: " + item.Type);
        }
        slots.Add(item.Id, new HeapSlot(item, arrayType.AsArrayType!, [], heapPrefix + index,
          ArrayTypeName(arrayType), entry.EnclosingClass.EnclosingModuleDefinition.FullDafnyName,
          arrayType.NormalizeExpand().TypeArgs[0]));
        continue;
      }
      var matches = classes.Where(candidate => candidate.FullDafnyName == item.Type ||
                                                candidate.FullName == item.Type).ToList();
      if (matches.Count != 1) {
        throw new ArgumentException($"Expected one concrete class named '{item.Type}', found {matches.Count}.",
          nameof(request));
      }
      var classDecl = matches[0];
      ValidateClass(program, entry, classDecl);
      var fields = ValidateFields(program, entry, classDecl, item);
      var sourceTypeName = SourceTypeName(program, entry, classDecl);
      slots.Add(item.Id, new HeapSlot(item, classDecl, fields, heapPrefix + index, sourceTypeName,
        entry.EnclosingClass.EnclosingModuleDefinition.FullDafnyName));
    }

    ValidateInputReferences(entry, request.Inputs, slots);
    ValidateFieldValues(slots);
    var orderedSlots = TopologicalOrder(slots);
    var insertions = BuildConstructorInsertions(slots.Values);
    var allocations = orderedSlots.Select(slot => Allocation(slot, slots));
    var initialCaptures = CaptureStatements(orderedSlots, true);
    var finalCaptures = CaptureStatements(orderedSlots, false);
    var parameters = string.Join(", ", slots.Values.Select(slot =>
      $"{slot.VariableName}: {slot.SourceTypeName}"));
    var constraints = InitialConstraints(slots.Values, slots);
    var modifies = slots.Count == 0 ? "" : "modifies " +
      string.Join(", ", slots.Values.Select(slot => slot.VariableName));

    return new ContractHeapPlan(insertions.Where(edit => edit.SourceUri == entry.Origin.Uri).Select(edit => (edit.Position, edit.Text)).ToList(), string.Join("\n", allocations), initialCaptures,
      finalCaptures, parameters, constraints, modifies,
      new Dictionary<string, ContractValue>(request.Inputs), slots, orderedSlots, insertions);
  }

  internal static string SourceTypeName(Program program, Method entry, ClassDecl declaration) {
    var visited = new HashSet<ModuleSignature>();
    string? Find(ModuleSignature signature) {
      if (!visited.Add(signature)) { return null; }
      foreach (var pair in signature.TopLevels) {
        if (pair.Value == declaration || pair.Value is NonNullTypeDecl nonNull && nonNull.Class == declaration) {
          return pair.Key.TrimEnd('?');
        }
      }
      foreach (var pair in signature.TopLevels.Where(pair => pair.Value is ModuleDecl)) {
        var nested = Find(((ModuleDecl)pair.Value).AccessibleSignature());
        if (nested != null) { return pair.Key + "." + nested; }
      }
      return null;
    }
    return Find(program.ModuleSigs[entry.EnclosingClass.EnclosingModuleDefinition]) ??
      throw new NotSupportedException("No visible source-level type name is available for " + declaration.FullDafnyName + ".");
  }

  internal static string ArrayTypeName(DafnyType type) => "array<" + type.NormalizeExpand().TypeArgs[0] + ">";

  private static IReadOnlyDictionary<string, DafnyType> ResolvedArrayTypes(Program program) {
    var result = new Dictionary<string, DafnyType>(StringComparer.Ordinal);
    void Visit(DafnyType type) {
      if (type.AsArrayType is { Dims: 1 }) { result.TryAdd(ArrayTypeName(type), type); }
      foreach (var argument in type.TypeArgs) { Visit(argument); }
    }
    foreach (var node in program.RawModules().SelectMany(module => module.Descendants())) {
      if (node is IVariable variable) { Visit(variable.Type); }
      if (node is Field field) { Visit(field.Type); }
      if (node is Expression { Type: { } type }) { Visit(type); }
    }
    return result;
  }

  private static string Allocation(HeapSlot slot, IReadOnlyDictionary<string, HeapSlot> slots) {
    if (!slot.IsArray) {
      return $"var {slot.VariableName} := new {slot.SourceTypeName}.{ConstructorName}(" +
        string.Join(", ", slot.Fields.Select(field => ValueExpression(slot.Object.Fields[field.Name], field.Type, slots))) + ");";
    }
    var values = slot.Object.Elements!;
    var initializer = "";
    if (values.Count > 0) {
      var expression = ValueExpression(values[^1], slot.ElementType, slots);
      for (var index = values.Count - 2; index >= 0; index--) {
        expression = "if contractArrayIndex == " + index + " then " + ValueExpression(values[index], slot.ElementType, slots) + " else " + expression;
      }
      initializer = "(contractArrayIndex => " + expression + ")";
    }
    return "var " + slot.VariableName + " := new " + slot.ElementType + "[" + values.Count + "]" + initializer + ";";
  }

  private static void ValidateClass(Program program, Method entry, ClassDecl classDecl) {
    var scope = program.ModuleSigs[entry.EnclosingClass.EnclosingModuleDefinition].VisibilityScope;
    if (classDecl.EnclosingModuleDefinition.ModuleKind != ModuleKindEnum.Concrete ||
        classDecl.TypeArgs.Count != 0 || classDecl.Traits.Count != 0 || classDecl.HasExternAttribute ||
        !classDecl.IsRevealedInScope(scope) || !classDecl.IsVisibleInScope(scope)) {
      throw new NotSupportedException(
        $"Heap type '{classDecl.FullDafnyName}' must be a visible concrete non-generic class without parents.");
    }
    if (classDecl.Members.Any(member => member.Name == ConstructorName)) {
      throw new ArgumentException(
        $"Heap type '{classDecl.FullDafnyName}' declares reserved member '{ConstructorName}'.");
    }
  }

  private static IReadOnlyList<Field> ValidateFields(Program program, Method entry, ClassDecl classDecl, ContractHeapObject item) {
    var declaredFields = classDecl.Members.OfType<Field>()
      .Where(field => field.Origin.line > 0 && !field.IsStatic).ToList();
    var scope = program.ModuleSigs[entry.EnclosingClass.EnclosingModuleDefinition].VisibilityScope;
    var unavailable = declaredFields.FirstOrDefault(field =>
      !field.IsRevealedInScope(scope) || !field.IsVisibleInScope(scope));
    if (unavailable != null) {
      throw new NotSupportedException(
        $"Heap type '{classDecl.FullDafnyName}' contains unavailable field '{unavailable.Name}'.");
    }
    var declaredNames = declaredFields.Select(field => field.Name).ToHashSet(StringComparer.Ordinal);
    if (!declaredNames.SetEquals(item.Fields.Keys)) {
      throw new ArgumentException(
        $"Heap object '{item.Id}' fields must exactly match the available instance fields of '{classDecl.FullDafnyName}'.");
    }
    return declaredFields;
  }

  private static void ValidateInputReferences(Method entry, IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyDictionary<string, HeapSlot> slots) {
    if (!entry.Ins.Select(formal => formal.Name).ToHashSet(StringComparer.Ordinal).SetEquals(inputs.Keys)) {
      throw new ArgumentException("Input names must exactly match the selected declaration's formals.", nameof(inputs));
    }
    foreach (var formal in entry.Ins) {
      var value = inputs[formal.Name];
      if (!IsReferenceType(formal.Type, out var expectedClass, out var permitsNull)) {
        if (value.Kind is ContractValueKind.Reference or ContractValueKind.Null ||
            !ValueMatchesType(value, formal.Type)) {
          throw new ArgumentException($"Input '{formal.Name}' has an incompatible concrete value.", nameof(inputs));
        }
        _ = ValueExpression(value, formal.Type, slots);
        continue;
      }
      if (value.Kind == ContractValueKind.Null && permitsNull) {
        continue;
      }
      if (value.Kind != ContractValueKind.Reference || value.Value == null ||
          !slots.TryGetValue(value.Value, out var target) || !IsExactReferenceType(formal.Type, target, out _)) {
        throw new ArgumentException($"Input '{formal.Name}' does not name a compatible heap object.", nameof(inputs));
      }
    }
  }

  private static void ValidateFieldValues(IReadOnlyDictionary<string, HeapSlot> slots) {
    foreach (var slot in slots.Values) {
      foreach (var cell in slot.Cells) {
        var value = cell.InitialValue;
        if (IsReferenceType(cell.Type, out _, out var permitsNull)) {
          if (value.Kind == ContractValueKind.Null && permitsNull) { continue; }
          if (value.Kind != ContractValueKind.Reference || value.Value == null ||
              !slots.TryGetValue(value.Value, out var target) || !IsExactReferenceType(cell.Type, target, out _)) {
            throw new ArgumentException("Heap cell '" + slot.Object.Id + "." + cell.Name + "' does not name a compatible heap object.");
          }
        } else if (!ValueMatchesType(value, cell.Type)) {
          throw new ArgumentException("Heap cell '" + slot.Object.Id + "." + cell.Name + "' has an incompatible concrete value.");
        }
        _ = ValueExpression(value, cell.Type, slots);
      }
    }
  }

  private static IReadOnlyList<HeapSlot> TopologicalOrder(IReadOnlyDictionary<string, HeapSlot> slots) {
    var result = new List<HeapSlot>();
    var visiting = new HashSet<string>(StringComparer.Ordinal);
    var visited = new HashSet<string>(StringComparer.Ordinal);
    void Visit(HeapSlot slot) {
      if (visited.Contains(slot.Object.Id)) {
        return;
      }
      if (!visiting.Add(slot.Object.Id)) {
        throw new NotSupportedException("Cyclic synthetic heap graphs are not supported.");
      }
      foreach (var cell in slot.Cells) {
        foreach (var reference in References(cell.InitialValue)) { Visit(slots[reference]); }
      }
      visiting.Remove(slot.Object.Id);
      visited.Add(slot.Object.Id);
      result.Add(slot);
    }
    foreach (var slot in slots.Values) {
      Visit(slot);
    }
    return result;
  }

  private static IReadOnlyList<ContractSourceEdit> BuildConstructorInsertions(
    IEnumerable<HeapSlot> slots) {
    return slots.Where(slot => !slot.IsArray).GroupBy(slot => slot.Class).Select(group => {
      var slot = group.First();
      var parameters = string.Join(", ", slot.Fields.Select(field =>
        (field.IsGhost ? "ghost " : "") + field.Name + ": " + field.Type));
      var assignments = string.Join("\n", slot.Fields.Select(field => $"    this.{field.Name} := {field.Name};"));
      var body = assignments.Length == 0 ? "" : "\n" + assignments + "\n  ";
      var declaration = $"\n  constructor {ConstructorName}({parameters}) {{" + body + "}\n";
      return new ContractSourceEdit(slot.Class.Origin.Uri, slot.Class.EndToken.pos, declaration);
    }).ToList();
  }

  private static string CaptureStatements(IEnumerable<HeapSlot> slots, bool initial) {
    var captures = slots.SelectMany(slot => slot.Cells.Where(cell => cell.RuntimeVisible).Select(cell =>
      (Id: slot.Object.Id, Name: cell.Name, Access: cell.Access,
        Shape: ContractStubRuntime.TypeShapeToken(cell.Type)))
      .Concat(slot.IsArray
        ? [(Id: slot.Object.Id, Name: "$length", Access: slot.VariableName + ".Length",
          Shape: "eyJraW5kIjoiaW50ZWdlciJ9")]
        : []));
    return string.Join("\n", captures.Select(cell => $"{ContractHarnessBuilder.BridgeName}.Capture(\"" +
      (initial ? ContractHeapPlan.InitialObservationKey(cell.Id, cell.Name) :
        ContractHeapPlan.FinalObservationKey(cell.Id, cell.Name)) + $"\", {cell.Access}, \"{cell.Shape}\");"));
  }

  private static IReadOnlyList<string> InitialConstraints(IEnumerable<HeapSlot> orderedSlots,
    IReadOnlyDictionary<string, HeapSlot> slots) {
    var ordered = orderedSlots.ToList();
    var result = ordered.Select(slot => slot.VariableName + " != null").ToList();
    for (var left = 0; left < ordered.Count; left++) {
      for (var right = left + 1; right < ordered.Count; right++) {
        if (ordered[left].SourceTypeName == ordered[right].SourceTypeName) {
          result.Add(ordered[left].VariableName + " != " + ordered[right].VariableName);
        }
      }
    }
    foreach (var slot in ordered) {
      if (slot.IsArray) { result.Add(slot.VariableName + ".Length == " + slot.Object.Dimensions![0]); }
      result.AddRange(slot.Cells.Select(cell => cell.Access + " == " + ValueExpression(cell.InitialValue, cell.Type, slots)));
    }
    return result;
  }

  private static IEnumerable<string> References(ContractValue value) {
    if (value.Kind == ContractValueKind.Reference) { yield return value.Value!; }
    foreach (var nested in (value.Items ?? []).Concat(value.Fields?.Values ?? [])) {
      foreach (var reference in References(nested)) { yield return reference; }
    }
    foreach (var entry in value.Entries ?? []) {
      foreach (var reference in References(entry.Key).Concat(References(entry.Value))) {
        yield return reference;
      }
    }
  }

  internal static string ValueExpression(ContractValue value, DafnyType? expectedType,
    IReadOnlyDictionary<string, HeapSlot> slots) {
    if (expectedType?.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: SubsetTypeDecl subset
    } subsetType) {
      return ValueExpression(value, subset.RhsWithArgument(subsetType.TypeArgs), slots);
    }
    if (expectedType?.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: NewtypeDecl newtype
    } newtypeType) {
      return ValueExpression(value, newtype.ConcreteBaseType(newtypeType.TypeArgs), slots);
    }
    if (value.Kind == ContractValueKind.Reference) {
      if (value.Value == null || !slots.TryGetValue(value.Value, out var slot)) {
        throw new ArgumentException("Reference value does not name a heap object.", nameof(value));
      }
      if (expectedType != null && !IsExactReferenceType(expectedType, slot, out _)) {
        throw new ArgumentException("Reference value has an incompatible heap type.", nameof(value));
      }
      return slot.VariableName;
    }
    var module = slots.Values.FirstOrDefault()?.SourceModuleName;
    if (value.Kind == ContractValueKind.Sequence && value.Items != null) {
      if (expectedType != null && expectedType.AsSeqType == null) {
        throw new ArgumentException("Sequence value does not match the expected heap value type.");
      }
      return "[" + string.Join(", ", value.Items.Select(item => ValueExpression(item, expectedType?.AsSeqType?.Arg, slots))) + "]";
    }
    if (value.Kind == ContractValueKind.Set && value.Items != null) {
      var set = expectedType?.AsSetType;
      if (expectedType != null && set is not { Finite: true }) {
        throw new ArgumentException("Set value does not match the expected heap value type.");
      }
      return "{" + string.Join(", ", value.Items.Select(item => ValueExpression(item, set?.Arg, slots))) + "}";
    }
    if (value.Kind == ContractValueKind.Multiset && value.Items != null) {
      var multiset = expectedType?.AsMultiSetType;
      if (expectedType != null && multiset == null) {
        throw new ArgumentException("Multiset value does not match the expected heap value type.");
      }
      return "multiset{" + string.Join(", ", value.Items.Select(item => ValueExpression(item, multiset?.Arg, slots))) + "}";
    }
    if (value.Kind == ContractValueKind.Map && value.Entries != null) {
      var map = expectedType?.AsMapType;
      if (expectedType != null && map is not { Finite: true }) {
        throw new ArgumentException("Map value does not match the expected heap value type.");
      }
      return "map[" + string.Join(", ", value.Entries.Select(entry =>
        ValueExpression(entry.Key, map?.Domain, slots) + " := " +
        ValueExpression(entry.Value, map?.Range, slots))) + "]";
    }
    if (value.Kind == ContractValueKind.Datatype && value.Fields != null && value.Constructor != null) {
      // Reuse the codec's constructor/field identifier checks before rendering nested heap references.
      _ = ContractModelCodec.ToDafny(value with {
        Fields = value.Fields.ToDictionary(field => field.Key,
        _ => new ContractValue(ContractValueKind.Boolean, "false"))
      }, module);
      Dictionary<string, DafnyType>? fieldTypes = null;
      if (expectedType != null) {
        var datatype = expectedType.AsDatatype ?? throw new ArgumentException("Datatype value does not match the expected heap value type.");
        var constructor = datatype.Ctors.SingleOrDefault(candidate => value.Constructor == candidate.FullName ||
          value.Constructor == datatype.Name + "." + candidate.Name ||
          value.Constructor == datatype.FullDafnyName + "." + candidate.Name || value.Constructor == candidate.Name);
        if (constructor == null || !constructor.Formals.Select(formal => formal.Name).ToHashSet().SetEquals(value.Fields.Keys)) {
          throw new ArgumentException("Datatype constructor and fields do not match the expected heap value type.");
        }
        var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, expectedType.TypeArgs);
        fieldTypes = constructor.Formals.ToDictionary(formal => formal.Name, formal => formal.Type.Subst(substitution));
      }
      return ContractModelCodec.LocalName(value.Constructor, module) + "(" + string.Join(", ", value.Fields.Select(field =>
        field.Key + " := " + ValueExpression(field.Value, fieldTypes?[field.Key], slots))) + ")";
    }
    if (expectedType != null && !ValueMatchesType(value, expectedType)) {
      throw new ArgumentException("Concrete heap value does not match its expected type.");
    }
    return ContractModelCodec.ToDafny(value, slots.Values.FirstOrDefault()?.SourceModuleName);
  }

  private static bool IsExactReferenceType(DafnyType type, HeapSlot expected, out bool permitsNull) {
    return IsReferenceType(type, out var actualClass, out permitsNull) && actualClass == expected.Class &&
      (!expected.IsArray || type.NormalizeExpand().TypeArgs[0].Equals(expected.ElementType));
  }

  private static bool IsReferenceType(DafnyType type, out ClassDecl classDecl, out bool permitsNull) {
    classDecl = null!;
    permitsNull = false;
    if (type.NormalizeExpand() is not UserDefinedType userDefinedType) {
      return false;
    }
    switch (userDefinedType.ResolvedClass) {
      case NonNullTypeDecl { Class: ClassDecl nonNullClass }:
        classDecl = nonNullClass;
        return true;
      case ClassDecl nullableClass:
        classDecl = nullableClass;
        permitsNull = true;
        return true;
      default:
        return false;
    }
  }

  private static bool ValueMatchesType(ContractValue value, DafnyType type) {
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } subsetType) {
      return ValueMatchesType(value, subset.RhsWithArgument(subsetType.TypeArgs));
    }
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: NewtypeDecl newtype } newtypeType) {
      return ValueMatchesType(value, newtype.ConcreteBaseType(newtypeType.TypeArgs));
    }
    if (type.IsRefType) { return value.Kind == ContractValueKind.Reference || value.Kind == ContractValueKind.Null && !type.IsNonNullRefType; }
    if (type.IsIntegerType) {
      return value.Kind == ContractValueKind.Integer;
    }
    if (type.AsBitVectorType is { } bitvectorType) {
      return value.Kind == ContractValueKind.Bitvector && value.Width == bitvectorType.Width;
    }
    if (type.IsBoolType) {
      return value.Kind == ContractValueKind.Boolean;
    }
    if (type.IsCharType) {
      return value.Kind == ContractValueKind.Character;
    }
    if (type.AsSeqType is { } sequenceType) {
      return value.Kind == ContractValueKind.Sequence && value.Items != null &&
             value.Items.All(item => ValueMatchesType(item, sequenceType.Arg));
    }
    if (type.AsSetType is { Finite: true } setType) {
      return value.Kind == ContractValueKind.Set && value.Items != null &&
             value.Items.All(item => ValueMatchesType(item, setType.Arg));
    }
    if (type.AsMultiSetType is { } multisetType) {
      return value.Kind == ContractValueKind.Multiset && value.Items != null &&
             value.Items.All(item => ValueMatchesType(item, multisetType.Arg));
    }
    if (type.AsMapType is { Finite: true } mapType) {
      return value.Kind == ContractValueKind.Map && value.Entries != null &&
             value.Entries.All(entry => ValueMatchesType(entry.Key, mapType.Domain) &&
                                        ValueMatchesType(entry.Value, mapType.Range));
    }
    if (type.IsDatatype) {
      return value.Kind == ContractValueKind.Datatype;
    }
    return false;
  }

  internal static bool ValuesEqual(ContractValue left, ContractValue right) =>
    ContractModelCodec.ValuesEqual(left, right);
}
