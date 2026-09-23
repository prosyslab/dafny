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
  public static string BridgeSource(string observationPath, ContractPreparedProgram prepared) {
    var program = prepared.Program;
    var trackedGhostFields = prepared.Heap?.TrackedGhostFields ?? new HashSet<Field>();
    var concreteTypes = prepared.ConcreteCalls.ToDictionary(pair => pair.Key,
      pair => pair.Value.ConcreteTypeArguments.Select(type => type.ToString()).ToList());
    string RuntimeTypeName(TopLevelDecl declaration) =>
      ((declaration.EnclosingModuleDefinition.TryToAvoidName ? declaration.EnclosingModuleDefinition.GetCompileName(program.Options) + "." : "") +
       declaration.GetFullCompileName(program.Options)).Replace("@", "");
    var heapShapes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<ClassDecl>()
      .Where(declaration => declaration.TypeArgs.Count == 0)
      .Select(declaration => new {
        runtimeType = RuntimeTypeName(declaration),
        type = declaration.FullDafnyName,
        fields = declaration.Members.OfType<Field>().Where(field => !field.IsGhost && !field.IsStatic)
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
      .Where(datatype => datatype.TypeArgs.Count == 0)
      .SelectMany(datatype => datatype.Ctors.Where(constructor => !constructor.IsGhost && constructor.Formals.All(formal => !formal.IsGhost))
        .Select(constructor => new {
          runtimeType = (RuntimeTypeName(datatype) + (datatype.IsRecordType ? "" : "_" + constructor.GetCompileName(program.Options))).Replace("@", ""),
          constructor = datatype.FullDafnyName + "." + constructor.Name,
          fields = constructor.Formals.Select((formal, index) => new {
            name = formal.Name,
            runtimeName = "_" + (formal.HasName ? formal.CompileName : "a" + index),
            shape = TypeShape(formal.Type)
          }).ToList()
        })).ToList();
    return """
    using System;
    using System.Collections;
    using System.Collections.Generic;
    using System.Globalization;
    using System.IO;
    using System.Numerics;
    using System.Text.Json;
    using System.Threading;
    namespace DafnyContractRuntime {
    public static class ContractDiagnosticBridge {
      private static string currentCall = "";
      private static readonly Dictionary<string, object> currentInputs = new();
      private static readonly Dictionary<string, JsonElement> pureChoices = new();
      private static readonly Dictionary<object, string> references = new(ReferenceEqualityComparer.Instance);
      private static readonly Dictionary<string, string> referenceTypes = new(StringComparer.Ordinal);
      private static readonly Dictionary<string, Dictionary<string, JsonElement>> logicalFields = new(StringComparer.Ordinal);
      private static readonly Stack<(string Symbol, HashSet<string> Allowed)> frames = new();
      private static int writeCount;
      private static int branchCount;
      private static bool frameViolationRecorded;
      private static BigInteger targetCallCount;
      private static string targetSymbol;
      private static int targetInvocation;
      private static readonly JsonElement shapes = JsonDocument.Parse(DATATYPE_SHAPES).RootElement.Clone();
      private static readonly JsonElement heapShapes = JsonDocument.Parse(HEAP_SHAPES).RootElement.Clone();
      private static readonly Dictionary<string, string[]> concreteTypes = JsonSerializer.Deserialize<Dictionary<string, string[]>>(CONCRETE_TYPES);
      private static Exception Unsupported(string reason) {
        File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
          name = "$unsupported/" + reason, value = new { kind = "boolean", value = "false" }
        }) + "\n");
        return new NotSupportedException(reason);
      }
      private static object Encode(object value, JsonElement? shape = null) {
        if (value == null) { return new { kind = "null" }; }
        if (references.TryGetValue(value, out var id)) { return new { kind = "reference", value = id }; }
        if (shape?.GetProperty("kind").GetString() == "integer") {
          var integerValue = value switch {
            byte item => new BigInteger(item), sbyte item => new BigInteger(item),
            ushort item => new BigInteger(item), short item => new BigInteger(item),
            uint item => new BigInteger(item), int item => new BigInteger(item),
            ulong item => new BigInteger(item), long item => new BigInteger(item), BigInteger item => item,
            _ => throw Unsupported("Integer observation has an incompatible runtime representation.")
          };
          return new { kind = "integer", value = integerValue.ToString(CultureInfo.InvariantCulture) };
        }
        if (shape?.GetProperty("kind").GetString() == "bitvector") {
          var bitvector = value switch {
            byte item => new BigInteger(item), ushort item => new BigInteger(item),
            uint item => new BigInteger(item), ulong item => new BigInteger(item), BigInteger item => item,
            _ => throw Unsupported("Bitvector observation has an incompatible runtime representation.")
          };
          return new { kind = "bitvector", value = bitvector.ToString(CultureInfo.InvariantCulture),
            width = shape.Value.GetProperty("width").GetInt32() };
        }
        if (value is BigInteger integer) {
          return new { kind = "integer", value = integer.ToString(CultureInfo.InvariantCulture) };
        }
        if (value is bool boolean) {
          return new { kind = "boolean", value = boolean ? "true" : "false" };
        }
        if (value is char || value is Dafny.Rune) {
          return new { kind = "character", value = value.ToString() };
        }
        var setInterface = value.GetType().GetInterfaces().FirstOrDefault(candidate =>
          candidate.IsGenericType && candidate.GetGenericTypeDefinition() == typeof(Dafny.ISet<>));
        if (setInterface != null) {
          var encodedItems = new List<(string SortKey, object Item)>();
          var enumerable = (IEnumerable)setInterface.GetProperty("Elements").GetValue(value);
          foreach (var item in enumerable) {
            var encoded = Encode(item, shape?.GetProperty("element"));
            encodedItems.Add((JsonSerializer.Serialize(encoded), encoded));
          }
          return new { kind = "set", items = encodedItems.OrderBy(item => item.SortKey, StringComparer.Ordinal)
            .Select(item => item.Item).ToList() };
        }
        var multisetInterface = value.GetType().GetInterfaces().FirstOrDefault(candidate =>
          candidate.IsGenericType && candidate.GetGenericTypeDefinition() == typeof(Dafny.IMultiSet<>));
        if (multisetInterface != null) {
          var encodedItems = new List<(string SortKey, object Item)>();
          var enumerable = (IEnumerable)multisetInterface.GetProperty("Elements").GetValue(value);
          foreach (var item in enumerable) {
            var encoded = Encode(item, shape?.GetProperty("element"));
            encodedItems.Add((JsonSerializer.Serialize(encoded), encoded));
          }
          return new { kind = "multiset", items = encodedItems.OrderBy(item => item.SortKey, StringComparer.Ordinal)
            .Select(item => item.Item).ToList() };
        }
        var mapInterface = value.GetType().GetInterfaces().FirstOrDefault(candidate =>
          candidate.IsGenericType && candidate.GetGenericTypeDefinition() == typeof(Dafny.IMap<,>));
        if (mapInterface != null) {
          var encodedEntries = new List<(string SortKey, object Entry)>();
          var enumerable = (IEnumerable)mapInterface.GetProperty("ItemEnumerable").GetValue(value);
          foreach (var item in enumerable) {
            var pairInterface = item.GetType().GetInterfaces().First(candidate =>
              candidate.IsGenericType && candidate.GetGenericTypeDefinition() == typeof(Dafny.IPair<,>));
            var key = Encode(pairInterface.GetProperty("Car").GetValue(item), shape?.GetProperty("key"));
            var mapped = Encode(pairInterface.GetProperty("Cdr").GetValue(item), shape?.GetProperty("value"));
            encodedEntries.Add((JsonSerializer.Serialize(key), new { key, value = mapped }));
          }
          return new { kind = "map", entries = encodedEntries.OrderBy(entry => entry.SortKey, StringComparer.Ordinal)
            .Select(entry => entry.Entry).ToList() };
        }
        if (value is IEnumerable sequence) {
          var items = new List<object>();
          foreach (var item in sequence) { items.Add(Encode(item, shape?.GetProperty("element"))); }
          return new { kind = "sequence", items };
        }
        foreach (var datatypeShape in shapes.EnumerateArray()) {
          if (datatypeShape.GetProperty("runtimeType").GetString() != value.GetType().FullName) { continue; }
          var fields = new Dictionary<string, object>();
          foreach (var field in datatypeShape.GetProperty("fields").EnumerateArray()) {
            var member = value.GetType().GetField(field.GetProperty("runtimeName").GetString());
            if (member == null) { throw Unsupported("Missing datatype runtime field metadata."); }
            fields.Add(field.GetProperty("name").GetString(), Encode(member.GetValue(value), field.GetProperty("shape")));
          }
          return new { kind = "datatype", constructor = datatypeShape.GetProperty("constructor").GetString(), fields };
        }
        throw Unsupported("Unsupported runtime observation type: " + value.GetType());
      }
      private static bool SameJson(JsonElement left, JsonElement right) {
        if (left.ValueKind != right.ValueKind) { return false; }
        if (left.ValueKind == JsonValueKind.Object) {
          var count = 0;
          foreach (var property in left.EnumerateObject()) {
            count++;
            if (!right.TryGetProperty(property.Name, out var other) || !SameJson(property.Value, other)) {
              return false;
            }
          }
          var otherCount = 0;
          foreach (var ignored in right.EnumerateObject()) { otherCount++; }
          return count == otherCount;
        }
        if (left.ValueKind == JsonValueKind.Array) {
          if (left.GetArrayLength() != right.GetArrayLength()) { return false; }
          for (var index = 0; index < left.GetArrayLength(); index++) {
            if (!SameJson(left[index], right[index])) { return false; }
          }
          return true;
        }
        return left.GetRawText() == right.GetRawText();
      }
      public static void Register<T>(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> typeName,
          T value, Dafny.ISequence<Dafny.Rune> logicalBase64) {
        var id = name.ToVerbatimString(false);
        references.Add(value, id);
        referenceTypes.Add(id, typeName.ToVerbatimString(false));
        var shape = HeapShape(value);
        var supplied = JsonDocument.Parse(System.Text.Encoding.UTF8.GetString(
          Convert.FromBase64String(logicalBase64.ToVerbatimString(false)))).RootElement;
        var state = new Dictionary<string, JsonElement>(StringComparer.Ordinal);
        foreach (var field in shape.GetProperty("logicalFields").EnumerateArray()) {
          var fieldName = field.GetProperty("name").GetString();
          if (!supplied.TryGetProperty(fieldName, out var initial)) {
            throw Unsupported("Incomplete initial logical heap fields.");
          }
          state.Add(fieldName, initial.Clone());
        }
        var suppliedCount = 0;
        foreach (var ignored in supplied.EnumerateObject()) { suppliedCount++; }
        if (suppliedCount != state.Count) { throw Unsupported("Unexpected initial logical heap field."); }
        logicalFields.Add(id, state);
      }
      private static JsonElement HeapShape(object value) {
        foreach (var shape in heapShapes.EnumerateArray()) {
          if (shape.GetProperty("runtimeType").GetString() == value.GetType().FullName) { return shape; }
        }
        throw Unsupported("Missing concrete class runtime metadata.");
      }
      private static object SnapshotHeap() {
        var heap = new List<object>();
        foreach (var reference in references) {
          if (reference.Key is Array array) {
            if (array.Rank != 1) { throw Unsupported("Only one-dimensional array observations are implemented."); }
            var elements = new List<object>();
            foreach (var element in array) { elements.Add(Encode(element)); }
            heap.Add(new { id = reference.Value, type = referenceTypes[reference.Value], fields = new Dictionary<string, object>(),
              dimensions = new[] { array.Length }, elements });
            continue;
          }
          var shape = HeapShape(reference.Key);
          var fields = new Dictionary<string, object>();
          foreach (var field in shape.GetProperty("fields").EnumerateArray()) {
            var member = reference.Key.GetType().GetProperty(field.GetProperty("runtimeName").GetString());
            if (member == null) { throw Unsupported("Missing concrete class runtime field."); }
            fields.Add(field.GetProperty("name").GetString(), Encode(member.GetValue(reference.Key), field.GetProperty("shape")));
          }
          foreach (var field in logicalFields[reference.Value]) { fields.Add(field.Key, field.Value); }
          heap.Add(new { id = reference.Value, type = shape.GetProperty("type").GetString(), fields });
        }
        return heap;
      }
      private static void ApplyHeap(JsonElement heap) {
        if (heap.ValueKind == JsonValueKind.Null) { return; }
        var updates = new List<(object Receiver, Action Store, string Name)>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var item in heap.EnumerateArray()) {
          var id = item.GetProperty("id").GetString();
          if (!seen.Add(id)) { throw Unsupported("Duplicate modeled heap identity."); }
          object receiver = null;
          foreach (var pair in references) { if (pair.Value == id) { receiver = pair.Key; break; } }
          if (receiver == null) { throw Unsupported("Modeled heap allocation is not implemented."); }
          if (referenceTypes[id] != item.GetProperty("type").GetString()) { throw Unsupported("Modeled heap identity changed type."); }
          if (receiver is Array array) {
            var dimensions = item.GetProperty("dimensions");
            var elements = item.GetProperty("elements");
            if (array.Rank != 1 || dimensions.GetArrayLength() != 1 || dimensions[0].GetInt32() != array.Length ||
                elements.GetArrayLength() != array.Length || item.GetProperty("fields").EnumerateObject().MoveNext()) {
              throw Unsupported("Modeled array identity changed dimensions or fields.");
            }
            for (var index = 0; index < array.Length; index++) {
              var targetIndex = index;
              var decoded = Decode(elements[index], array.GetType().GetElementType());
              if (JsonSerializer.Serialize(Encode(array.GetValue(index))) != JsonSerializer.Serialize(Encode(decoded))) {
                updates.Add((receiver, () => array.SetValue(decoded, targetIndex), "element"));
              }
            }
            continue;
          }
          var shape = HeapShape(receiver);
          if (shape.GetProperty("type").GetString() != item.GetProperty("type").GetString()) {
            throw Unsupported("Modeled heap identity changed type.");
          }
          var fields = item.GetProperty("fields");
          var fieldCount = 0;
          foreach (var field in shape.GetProperty("fields").EnumerateArray()) {
            var name = field.GetProperty("name").GetString();
            var member = receiver.GetType().GetProperty(field.GetProperty("runtimeName").GetString());
            if (member == null || !fields.TryGetProperty(name, out var value)) { throw Unsupported("Incomplete modeled heap field."); }
            var decoded = Decode(value, member.PropertyType);
            var fieldShape = field.GetProperty("shape");
            if (JsonSerializer.Serialize(Encode(member.GetValue(receiver), fieldShape)) !=
                JsonSerializer.Serialize(Encode(decoded, fieldShape))) {
              if (!field.GetProperty("mutable").GetBoolean()) {
                throw Unsupported("Modeled immutable runtime field changed.");
              }
              updates.Add((receiver, () => member.SetValue(receiver, decoded), name));
            }
            fieldCount++;
          }
          foreach (var field in shape.GetProperty("logicalFields").EnumerateArray()) {
            var name = field.GetProperty("name").GetString();
            if (!fields.TryGetProperty(name, out var value)) {
              throw Unsupported("Incomplete modeled logical heap field.");
            }
            var prior = logicalFields[id][name];
            if (!SameJson(prior, value)) {
              if (!field.GetProperty("mutable").GetBoolean()) {
                throw Unsupported("Modeled immutable logical field changed.");
              }
              var update = value.Clone();
              updates.Add((receiver, () => logicalFields[id][name] = update, name));
            }
            fieldCount++;
          }
          var actualCount = 0;
          foreach (var field in fields.EnumerateObject()) { actualCount++; }
          if (actualCount != fieldCount) { throw Unsupported("Unexpected modeled heap field."); }
        }
        if (seen.Count != references.Count) { throw Unsupported("Incomplete modeled heap identities."); }
        // Decode the correlated tuple completely before committing any heap write.
        foreach (var update in updates) {
          Write(update.Receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(update.Name));
          update.Store();
        }
      }
      private static JsonElement Shape(Dafny.ISequence<Dafny.Rune> encoded) => JsonDocument.Parse(
        System.Text.Encoding.UTF8.GetString(Convert.FromBase64String(encoded.ToVerbatimString(false)))).RootElement.Clone();
      public static void Capture<T>(Dafny.ISequence<Dafny.Rune> name, T value,
          Dafny.ISequence<Dafny.Rune> shape) {
        File.AppendAllText(OBSERVATION_PATH,
          JsonSerializer.Serialize(new { name = name.ToVerbatimString(false),
            value = Encode(value, Shape(shape)) }) + "\n");
      }
      public static void Snapshot(Dafny.ISequence<Dafny.Rune> phase) {
        var prefix = "$" + phase.ToVerbatimString(false) + "/";
        var snapshot = JsonDocument.Parse(JsonSerializer.Serialize(SnapshotHeap())).RootElement;
        foreach (var item in snapshot.EnumerateArray()) {
          var id = item.GetProperty("id").GetString();
          foreach (var field in item.GetProperty("fields").EnumerateObject()) {
            File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
              name = prefix + id + "/" + field.Name, value = field.Value
            }) + "\n");
          }
          if (item.TryGetProperty("elements", out var elements)) {
            File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
              name = prefix + id + "/$length", value = new { kind = "integer", value = elements.GetArrayLength().ToString(CultureInfo.InvariantCulture) }
            }) + "\n");
            var index = 0;
            foreach (var element in elements.EnumerateArray()) {
              File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
                name = prefix + id + "/[" + index++ + "]", value = element
              }) + "\n");
            }
          }
        }
      }
      public static void Begin(Dafny.ISequence<Dafny.Rune> name) {
        currentCall = name.ToVerbatimString(false);
        currentInputs.Clear();
      }
      public static void Input<T>(Dafny.ISequence<Dafny.Rune> name, T value,
          Dafny.ISequence<Dafny.Rune> shape) {
        currentInputs.Add(name.ToVerbatimString(false), Encode(value, Shape(shape)));
      }
      public static void End() {
        Request(currentCall, JsonSerializer.Serialize(currentInputs), "precondition");
      }
      public static bool CheckPrecondition(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> arguments) {
        Request(name.ToVerbatimString(false), arguments.ToVerbatimString(false), "precondition");
        return true;
      }
      public static bool Trace(Dafny.ISequence<Dafny.Rune> symbol, BigInteger position, BigInteger line, BigInteger column, bool value) {
        File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
          name = "$branch/" + branchCount++ + "/" + symbol.ToVerbatimString(false) + "/" + position + "/" + line + "/" + column,
          value = new { kind = "boolean", value = value ? "true" : "false" }
        }) + "\n");
        return value;
      }
      public static T Unreachable<T>() {
        throw new InvalidOperationException("A successful precondition check must return true.");
      }
      public static void AssertionFailed() {
        File.AppendAllText(OBSERVATION_PATH,
          JsonSerializer.Serialize(new { name = "$bodyAssertion", value = new { kind = "boolean", value = "false" } }) + "\n");
        throw new InvalidOperationException("Diagnostic body assertion failed.");
      }
      public static void EnterFrame(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> modifies) {
        var allowed = new HashSet<string>(StringComparer.Ordinal);
        foreach (var value in JsonDocument.Parse(modifies.ToVerbatimString(false)).RootElement.EnumerateArray()) {
          if (value.GetProperty("kind").GetString() != "reference") {
            throw Unsupported("Unsupported runtime modifies value.");
          }
          allowed.Add(value.GetProperty("value").GetString());
        }
        frames.Push((name.ToVerbatimString(false), allowed));
      }
      public static void ExitFrame() {
        frames.Pop();
      }
      public static T Write<T>(T receiver, Dafny.ISequence<Dafny.Rune> field) {
        if (receiver == null || !references.TryGetValue(receiver, out var id)) {
          throw Unsupported("Field write receiver is outside the finite observed heap.");
        }
        var fieldName = field.ToVerbatimString(false);
        File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
          name = "$write/" + writeCount++ + "/" + fieldName, value = new { kind = "reference", value = id }
        }) + "\n");
        foreach (var frame in frames) {
          if (!frame.Allowed.Contains(id) && !frameViolationRecorded) {
            frameViolationRecorded = true;
            File.AppendAllText(OBSERVATION_PATH, JsonSerializer.Serialize(new {
              name = "$frameViolation/" + frame.Symbol + "/" + id + "/" + fieldName,
              value = new { kind = "boolean", value = "false" }
            }) + "\n");
          }
        }
        return receiver;
      }
      public static Dafny.ISequence<Dafny.Rune> Serialize<T>(T value, Dafny.ISequence<Dafny.Rune> shape) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(JsonSerializer.Serialize(
          Encode(value, Shape(shape))));
      }
      private static JsonElement Request(string symbol, string inputs, string operation, int? invocation = null, string outputs = null) {
        var prefix = OBSERVATION_PATH + ".rpc." + Guid.NewGuid().ToString("N");
        var formalInputs = JsonSerializer.Deserialize<Dictionary<string, JsonElement>>(inputs);
        JsonElement? receiver = formalInputs.Remove("$this", out var receiverValue) ? receiverValue : null;
        File.WriteAllText(prefix + ".tmp", JsonSerializer.Serialize(new { symbol, inputs = formalInputs, operation, receiver,
          typeArguments = concreteTypes.TryGetValue(symbol, out var types) ? types : Array.Empty<string>(),
          heap = SnapshotHeap(), invocation, outputs = outputs == null ? null : JsonSerializer.Deserialize<Dictionary<string, JsonElement>>(outputs) }));
        File.Move(prefix + ".tmp", prefix + ".request");
        while (!File.Exists(prefix + ".response")) { Thread.Sleep(5); }
        var response = JsonDocument.Parse(File.ReadAllText(prefix + ".response")).RootElement.Clone();
        if (response.GetProperty("status").GetString() != "realized") {
          throw new InvalidOperationException("contract_rpc_" + response.GetProperty("status").GetString());
        }
        if (operation == "realize" && response.TryGetProperty("postHeap", out var postHeap)) { ApplyHeap(postHeap); }
        return response;
      }
      public static BigInteger StartTarget(Dafny.ISequence<Dafny.Rune> symbol, Dafny.ISequence<Dafny.Rune> arguments, BigInteger invocation) {
        var current = targetCallCount++;
        if (current != invocation) { return BigInteger.Zero; }
        targetSymbol = symbol.ToVerbatimString(false);
        targetInvocation = checked((int)current);
        Request(targetSymbol, arguments.ToVerbatimString(false), "entry_start", targetInvocation);
        return current + BigInteger.One;
      }
      public static void EndTarget(BigInteger token, Dafny.ISequence<Dafny.Rune> outputs) {
        if (token.IsZero) { return; }
        if (token != new BigInteger(targetInvocation) + BigInteger.One) { throw new InvalidOperationException("Mismatched target invocation."); }
        Request(targetSymbol, "{}", "entry_end", targetInvocation, outputs.ToVerbatimString(false));
        Environment.Exit(0);
      }
      public static T EndTargetValue<T>(BigInteger token, Dafny.ISequence<Dafny.Rune> outputName, T value,
          Dafny.ISequence<Dafny.Rune> shape) {
        EndTarget(token, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(JsonSerializer.Serialize(
          new Dictionary<string, object> { [outputName.ToVerbatimString(false)] =
            Encode(value, Shape(shape)) })));
        return value;
      }
      public static Dafny.ISequence<Dafny.Rune> Realize(Dafny.ISequence<Dafny.Rune> name,
          Dafny.ISequence<Dafny.Rune> arguments, bool pure) {
        var symbol = name.ToVerbatimString(false);
        var inputs = arguments.ToVerbatimString(false);
        var key = symbol + ":" + inputs + ":" + JsonSerializer.Serialize(SnapshotHeap());
        JsonElement response;
        if (!pure || !pureChoices.TryGetValue(key, out response)) {
          response = Request(symbol, inputs, "realize");
          if (pure) { pureChoices.Add(key, response); }
        }
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(response.GetRawText());
      }
      public static T Choose<T>(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> arguments,
          Dafny.ISequence<Dafny.Rune> outputName, bool pure) {
        return Output<T>(Realize(name, arguments, pure), outputName);
      }
      public static T Output<T>(Dafny.ISequence<Dafny.Rune> realization, Dafny.ISequence<Dafny.Rune> outputName) {
        var observation = JsonDocument.Parse(realization.ToVerbatimString(false)).RootElement.GetProperty("outputs").GetProperty(outputName.ToVerbatimString(false));
        return (T)Decode(observation, typeof(T));
      }
      private static object Decode(JsonElement observation, Type target) {
        switch (observation.GetProperty("kind").GetString()) {
          case "reference":
            foreach (var reference in references) {
              if (reference.Value == observation.GetProperty("value").GetString() && target.IsInstanceOfType(reference.Key)) { return reference.Key; }
            }
            throw Unsupported("Modeled reference does not name an existing compatible object.");
          case "integer":
            var integer = BigInteger.Parse(observation.GetProperty("value").GetString(), CultureInfo.InvariantCulture);
            if (target == typeof(byte)) { return checked((byte)integer); }
            if (target == typeof(sbyte)) { return checked((sbyte)integer); }
            if (target == typeof(ushort)) { return checked((ushort)integer); }
            if (target == typeof(short)) { return checked((short)integer); }
            if (target == typeof(uint)) { return checked((uint)integer); }
            if (target == typeof(int)) { return checked((int)integer); }
            if (target == typeof(ulong)) { return checked((ulong)integer); }
            if (target == typeof(long)) { return checked((long)integer); }
            if (target == typeof(BigInteger)) { return integer; }
            throw Unsupported("Modeled integer has an incompatible runtime type.");
          case "bitvector":
            var bitvector = BigInteger.Parse(observation.GetProperty("value").GetString(), CultureInfo.InvariantCulture);
            if (target == typeof(byte)) { return checked((byte)bitvector); }
            if (target == typeof(ushort)) { return checked((ushort)bitvector); }
            if (target == typeof(uint)) { return checked((uint)bitvector); }
            if (target == typeof(ulong)) { return checked((ulong)bitvector); }
            if (target == typeof(BigInteger)) { return bitvector; }
            throw Unsupported("Modeled bitvector has an incompatible runtime type.");
          case "boolean": return observation.GetProperty("value").GetString() == "true";
          case "character": return new Dafny.Rune(char.ConvertToUtf32(observation.GetProperty("value").GetString(), 0));
          case "null" when !target.IsValueType: return null;
          case "sequence" when target.IsGenericType && target.GetGenericTypeDefinition() == typeof(Dafny.ISequence<>):
            var elementType = target.GetGenericArguments()[0];
            var items = observation.GetProperty("items");
            var array = Array.CreateInstance(elementType, items.GetArrayLength());
            var index = 0;
            foreach (var item in items.EnumerateArray()) { array.SetValue(Decode(item, elementType), index++); }
            return typeof(Dafny.Sequence<>).MakeGenericType(elementType).GetMethod("FromArray").Invoke(null, new object[] { array });
          case "set" when target.IsGenericType && target.GetGenericTypeDefinition() == typeof(Dafny.ISet<>):
            var setElementType = target.GetGenericArguments()[0];
            var setItems = observation.GetProperty("items");
            var setArray = Array.CreateInstance(setElementType, setItems.GetArrayLength());
            var setIndex = 0;
            foreach (var item in setItems.EnumerateArray()) { setArray.SetValue(Decode(item, setElementType), setIndex++); }
            return typeof(Dafny.Set<>).MakeGenericType(setElementType).GetMethod("FromElements").Invoke(null,
              new object[] { setArray });
          case "multiset" when target.IsGenericType && target.GetGenericTypeDefinition() == typeof(Dafny.IMultiSet<>):
            var multisetElementType = target.GetGenericArguments()[0];
            var multisetItems = observation.GetProperty("items");
            var multisetArray = Array.CreateInstance(multisetElementType, multisetItems.GetArrayLength());
            var multisetIndex = 0;
            foreach (var item in multisetItems.EnumerateArray()) {
              multisetArray.SetValue(Decode(item, multisetElementType), multisetIndex++);
            }
            return typeof(Dafny.MultiSet<>).MakeGenericType(multisetElementType).GetMethod("FromElements").Invoke(null,
              new object[] { multisetArray });
          case "map" when target.IsGenericType && target.GetGenericTypeDefinition() == typeof(Dafny.IMap<,>):
            var mapTypes = target.GetGenericArguments();
            var pairType = typeof(Dafny.IPair<,>).MakeGenericType(mapTypes);
            var concretePairType = typeof(Dafny.Pair<,>).MakeGenericType(mapTypes);
            var encodedEntries = observation.GetProperty("entries");
            var pairs = Array.CreateInstance(pairType, encodedEntries.GetArrayLength());
            var pairIndex = 0;
            foreach (var entry in encodedEntries.EnumerateArray()) {
              var pair = Activator.CreateInstance(concretePairType, new object[] {
                Decode(entry.GetProperty("key"), mapTypes[0]),
                Decode(entry.GetProperty("value"), mapTypes[1])
              });
              pairs.SetValue(pair, pairIndex++);
            }
            return typeof(Dafny.Map<,>).MakeGenericType(mapTypes).GetMethod("FromElements").Invoke(null,
              new object[] { pairs });
          case "datatype":
            foreach (var shape in shapes.EnumerateArray()) {
              if (shape.GetProperty("constructor").GetString() != observation.GetProperty("constructor").GetString()) { continue; }
              var runtimeType = target.Assembly.GetType(shape.GetProperty("runtimeType").GetString());
              if (runtimeType == null || !target.IsAssignableFrom(runtimeType)) { break; }
              var fields = shape.GetProperty("fields");
              foreach (var constructor in runtimeType.GetConstructors()) {
                var parameters = constructor.GetParameters();
                if (parameters.Length != fields.GetArrayLength()) { continue; }
                var arguments = new object[parameters.Length];
                var parameterIndex = 0;
                foreach (var field in fields.EnumerateArray()) {
                  arguments[parameterIndex] = Decode(observation.GetProperty("fields").GetProperty(field.GetProperty("name").GetString()), parameters[parameterIndex].ParameterType);
                  parameterIndex++;
                }
                return constructor.Invoke(arguments);
              }
            }
            break;
        }
        throw Unsupported("Unsupported contract-model runtime result type: " + target);
      }
    }
    }
    """.Replace("OBSERVATION_PATH", JsonSerializer.Serialize(observationPath))
      .Replace("CONCRETE_TYPES", JsonSerializer.Serialize(JsonSerializer.Serialize(concreteTypes)))
      .Replace("HEAP_SHAPES", JsonSerializer.Serialize(JsonSerializer.Serialize(heapShapes)))
      .Replace("DATATYPE_SHAPES", JsonSerializer.Serialize(JsonSerializer.Serialize(shapes)));
  }

  internal static string TypeShapeToken(Microsoft.Dafny.Type type) => Convert.ToBase64String(
    System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(TypeShape(type))));

  private static object TypeShape(Microsoft.Dafny.Type type) {
    type = type.NormalizeToAncestorType();
    if (type.AsBitVectorType is { } bitvector) {
      return new Dictionary<string, object> { ["kind"] = "bitvector", ["width"] = bitvector.Width };
    }
    if (type.IsIntegerType) {
      return new Dictionary<string, object> { ["kind"] = "integer" };
    }
    if (type.AsSeqType is { } sequence) {
      return new Dictionary<string, object> { ["kind"] = "sequence", ["element"] = TypeShape(sequence.Arg) };
    }
    if (type.AsSetType is { } set) {
      return new Dictionary<string, object> { ["kind"] = "set", ["element"] = TypeShape(set.Arg) };
    }
    if (type.AsMultiSetType is { } multiset) {
      return new Dictionary<string, object> { ["kind"] = "multiset", ["element"] = TypeShape(multiset.Arg) };
    }
    if (type.AsMapType is { } map) {
      return new Dictionary<string, object> {
        ["kind"] = "map",
        ["key"] = TypeShape(map.Domain),
        ["value"] = TypeShape(map.Range)
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
