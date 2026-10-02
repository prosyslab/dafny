using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using System.Threading;
using DafnyContractRuntime;
namespace DafnyPbtRuntime {
  /// <summary>Encodes runtime values and the observed heap and appends observation records; it never contacts the SMT parent.</summary>
  public static class Observation {
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<string, JsonElement> shapeCache = new(StringComparer.Ordinal);
    private static readonly Dictionary<object, string> references = new(ReferenceEqualityComparer.Instance);
    private static readonly Dictionary<string, string> referenceTypes = new(StringComparer.Ordinal);
    private static readonly Dictionary<string, Dictionary<string, JsonElement>> logicalFields = new(StringComparer.Ordinal);
    private static readonly Stack<(string Symbol, HashSet<string> Allowed)> frames = new();
    private static int writeCount;
    private static int branchCount;
    private static bool frameViolationRecorded;
    private static readonly JsonElement shapes = JsonDocument.Parse(ContractRuntimeConfiguration.DatatypeShapes).RootElement.Clone();
    private static readonly JsonElement heapShapes = JsonDocument.Parse(ContractRuntimeConfiguration.HeapShapes).RootElement.Clone();
    // Reflection metadata is independent of the values supplied to an observation.
    private static readonly Dictionary<string, JsonElement> datatypeShapes = shapes.EnumerateArray()
      .GroupBy(shape => shape.GetProperty("runtimeType").GetString(), StringComparer.Ordinal)
      .ToDictionary(group => group.Key, group => group.First(), StringComparer.Ordinal);
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<Type, Type[]> runtimeInterfaces = new();
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<(Type Type, string Name), System.Reflection.FieldInfo> datatypeFields = new();
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<object, System.Collections.Concurrent.ConcurrentDictionary<string, JsonElement>> immutableEncodings = new();
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<object, object> immutableValues = new();
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<object, System.Collections.Concurrent.ConcurrentDictionary<(string Name, string Shape), Dafny.ISequence<Dafny.Rune>>> immutableNamedEncodings = new();
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<object, NamedFragment> namedFragments = new();
    internal static readonly Dictionary<string, string[]> ConcreteTypes = JsonSerializer.Deserialize<Dictionary<string, string[]>>(ContractRuntimeConfiguration.ConcreteTypes);
    private sealed class NamedFragment {
      public JsonElement Values { get; }
      public NamedFragment(JsonElement values) { Values = values; }
    }
    [System.Text.Json.Serialization.JsonConverter(typeof(OrderedValuesConverter))]
    public sealed class OrderedValues {
      internal IReadOnlyList<JsonElement> Fragments { get; }
      internal OrderedValues(IReadOnlyList<JsonElement> fragments) { Fragments = fragments; }
    }
    public sealed class OrderedValuesConverter : System.Text.Json.Serialization.JsonConverter<OrderedValues> {
      public override OrderedValues Read(ref Utf8JsonReader reader, Type typeToConvert, JsonSerializerOptions options) {
        throw new NotSupportedException("Runtime observation values are write-only.");
      }
      public override void Write(Utf8JsonWriter writer, OrderedValues value, JsonSerializerOptions options) {
        writer.WriteStartObject();
        foreach (var fragment in value.Fragments) {
          foreach (var property in fragment.EnumerateObject()) { property.WriteTo(writer); }
        }
        writer.WriteEndObject();
      }
    }
    internal static Exception Unsupported(string reason) {
      File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
        name = "$unsupported/" + reason,
        value = new { kind = "boolean", value = "false" }
      }) + "\n");
      return new NotSupportedException(reason);
    }
    /// <summary>Decodes concrete Dafny strings without allocating one string per BMP scalar.</summary>
    public static string Text(Dafny.ISequence<Dafny.Rune> value) {
      var type = value.GetType();
      if (!IsRuntimeSequence(type.IsGenericType ? type.GetGenericTypeDefinition() : type)) {
        return value.ToVerbatimString(false);
      }
      var result = new System.Text.StringBuilder();
      foreach (var rune in value) {
        var scalar = rune.Value;
        if ((uint)scalar <= 0xffff && (scalar < 0xd800 || scalar > 0xdfff)) {
          result.Append((char)scalar);
        } else {
          result.Append(char.ConvertFromUtf32(scalar));
        }
      }
      return result.ToString();
    }
    private static bool IsRuntimeSequence(Type definition) =>
      definition.Assembly == typeof(Dafny.Sequence<>).Assembly &&
      definition.FullName is "Dafny.ArraySequence`1" or "Dafny.ConcatSequence`1";
    // Interface lists are cached per runtime type; no observed value is cached here.
    private static Type[] Interfaces(Type type) => runtimeInterfaces.GetOrAdd(type, item => item.GetInterfaces());
    private static Type GenericInterface(Type[] interfaces, params Type[] definitions) =>
      interfaces.FirstOrDefault(candidate => candidate.IsGenericType && definitions.Contains(candidate.GetGenericTypeDefinition()));
    private static Type RequireGenericInterface(Type type, params Type[] definitions) =>
      Interfaces(type).First(candidate => candidate.IsGenericType && definitions.Contains(candidate.GetGenericTypeDefinition()));
    internal static object Encode(object value, JsonElement? shape = null) {
      if (value != null && references.TryGetValue(value, out var reference)) { return new { kind = "reference", value = reference }; }
      if (value == null || value.GetType().IsValueType) { return EncodeValue(value, shape); }
      var key = shape?.GetRawText() ?? "";
      if (immutableEncodings.TryGetValue(value, out var encodings) && encodings.TryGetValue(key, out var existing)) {
        return existing;
      }
      var encoded = EncodeValue(value, shape);
      if (!ImmutableValue(value, new HashSet<object>(ReferenceEqualityComparer.Instance))) { return encoded; }
      // Store detached JSON only after encoding and recursively establishing immutable structure.
      var serialized = JsonSerializer.SerializeToElement(encoded);
      immutableEncodings.GetOrCreateValue(value).TryAdd(key, serialized);
      return serialized;
    }
    // Interface implementations and heap references do not establish immutability.
    private static bool ImmutableValue(object value, HashSet<object> visiting) {
      if (value == null || value is BigInteger or bool or char or Dafny.Rune or byte or sbyte or short or ushort or int or uint or long or ulong) { return true; }
      if (references.ContainsKey(value)) { return false; }
      if (immutableValues.TryGetValue(value, out _)) { return true; }
      if (!visiting.Add(value)) { return false; }
      try {
        var type = value.GetType();
        var definition = type.IsGenericType ? type.GetGenericTypeDefinition() : type;
        if (definition == typeof(Dafny.Map<,>)) {
          var map = RequireGenericInterface(type, typeof(Dafny.IMap<,>));
          foreach (var item in (IEnumerable)map.GetProperty("ItemEnumerable").GetValue(value)) {
            var pair = RequireGenericInterface(item.GetType(), typeof(Dafny.IPair<,>));
            if (!ImmutableValue(pair.GetProperty("Car").GetValue(item), visiting) ||
                !ImmutableValue(pair.GetProperty("Cdr").GetValue(item), visiting)) { return false; }
          }
        } else if (definition == typeof(Dafny.Set<>) || definition == typeof(Dafny.MultiSet<>)) {
          var collection = RequireGenericInterface(type, typeof(Dafny.ISet<>), typeof(Dafny.IMultiSet<>));
          foreach (var item in (IEnumerable)collection.GetProperty("Elements").GetValue(value)) {
            if (!ImmutableValue(item, visiting)) { return false; }
          }
        } else if (IsRuntimeSequence(definition)) {
          foreach (var item in (IEnumerable)value) {
            if (!ImmutableValue(item, visiting)) { return false; }
          }
        } else if (datatypeShapes.TryGetValue(definition.FullName, out var datatype)) {
          foreach (var field in datatype.GetProperty("fields").EnumerateArray()) {
            var member = datatypeFields.GetOrAdd((type, field.GetProperty("runtimeName").GetString()), key =>
              key.Type.GetField(key.Name) ?? throw Unsupported("Missing datatype runtime field metadata."));
            if (!member.IsInitOnly || !ImmutableValue(member.GetValue(value), visiting)) { return false; }
          }
        } else { return false; }
        immutableValues.GetValue(value, _ => new object());
        return true;
      }
      finally {
        visiting.Remove(value);
      }
    }
    private static object EncodeValue(object value, JsonElement? shape) {
      if (value == null) { return new { kind = "null" }; }
      if (references.TryGetValue(value, out var id)) { return new { kind = "reference", value = id }; }
      if (shape?.GetProperty("kind").GetString() == "parameter") {
        throw Unsupported("Runtime observation has an unresolved Dafny type parameter.");
      }
      if (shape?.GetProperty("kind").GetString() == "integer") {
        var integerValue = value switch {
          byte item => new BigInteger(item),
          sbyte item => new BigInteger(item),
          ushort item => new BigInteger(item),
          short item => new BigInteger(item),
          uint item => new BigInteger(item),
          int item => new BigInteger(item),
          ulong item => new BigInteger(item),
          long item => new BigInteger(item),
          BigInteger item => item,
          _ => throw Unsupported("Integer observation has an incompatible runtime representation.")
        };
        return new { kind = "integer", value = integerValue.ToString(CultureInfo.InvariantCulture) };
      }
      if (shape?.GetProperty("kind").GetString() == "bitvector") {
        var bitvector = value switch {
          byte item => new BigInteger(item),
          ushort item => new BigInteger(item),
          uint item => new BigInteger(item),
          ulong item => new BigInteger(item),
          BigInteger item => item,
          _ => throw Unsupported("Bitvector observation has an incompatible runtime representation.")
        };
        return new {
          kind = "bitvector",
          value = bitvector.ToString(CultureInfo.InvariantCulture),
          width = shape.Value.GetProperty("width").GetInt32()
        };
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
      var runtimeType = value.GetType();
      var interfaces = Interfaces(runtimeType);
      var setInterface = GenericInterface(interfaces, typeof(Dafny.ISet<>));
      if (setInterface != null) {
        var encodedItems = new List<(string SortKey, object Item)>();
        var enumerable = (IEnumerable)setInterface.GetProperty("Elements").GetValue(value);
        foreach (var item in enumerable) {
          var encoded = Encode(item, shape?.GetProperty("element"));
          encodedItems.Add((JsonSerializer.Serialize(encoded), encoded));
        }
        return new {
          kind = "set",
          items = encodedItems.OrderBy(item => item.SortKey, StringComparer.Ordinal)
          .Select(item => item.Item).ToList()
        };
      }
      var multisetInterface = GenericInterface(interfaces, typeof(Dafny.IMultiSet<>));
      if (multisetInterface != null) {
        var encodedItems = new List<(string SortKey, object Item)>();
        var enumerable = (IEnumerable)multisetInterface.GetProperty("Elements").GetValue(value);
        foreach (var item in enumerable) {
          var encoded = Encode(item, shape?.GetProperty("element"));
          encodedItems.Add((JsonSerializer.Serialize(encoded), encoded));
        }
        return new {
          kind = "multiset",
          items = encodedItems.OrderBy(item => item.SortKey, StringComparer.Ordinal)
          .Select(item => item.Item).ToList()
        };
      }
      var mapInterface = GenericInterface(interfaces, typeof(Dafny.IMap<,>));
      if (mapInterface != null) {
        var encodedEntries = new List<(string SortKey, object Entry)>();
        var enumerable = (IEnumerable)mapInterface.GetProperty("ItemEnumerable").GetValue(value);
        foreach (var item in enumerable) {
          var pairInterface = RequireGenericInterface(item.GetType(), typeof(Dafny.IPair<,>));
          var key = Encode(pairInterface.GetProperty("Car").GetValue(item), shape?.GetProperty("key"));
          var mapped = Encode(pairInterface.GetProperty("Cdr").GetValue(item), shape?.GetProperty("value"));
          encodedEntries.Add((JsonSerializer.Serialize(key), new { key, value = mapped }));
        }
        return new {
          kind = "map",
          entries = encodedEntries.OrderBy(entry => entry.SortKey, StringComparer.Ordinal)
          .Select(entry => entry.Entry).ToList()
        };
      }
      if (ContractRuntimeConfiguration.RuntimeReferences && value is Array) {
        // A Dafny array is a heap reference; its length and elements are captured as flat named values.
        var reference = "pbt-reference-" + references.Count;
        references.Add(value, reference);
        if (shape is { } arrayShape && arrayShape.TryGetProperty("type", out var arrayType)) {
          referenceTypes.Add(reference, arrayType.GetString());
        }
        return new { kind = "reference", value = reference };
      }
      if (value is IEnumerable sequence) {
        var items = new List<object>();
        foreach (var item in sequence) { items.Add(Encode(item, shape?.GetProperty("element"))); }
        return new { kind = "sequence", items };
      }
      var definition = runtimeType.IsGenericType ? runtimeType.GetGenericTypeDefinition() : runtimeType;
      if (datatypeShapes.TryGetValue(definition.FullName, out var datatypeShape)) {
        JsonElement? arguments = shape is { } concrete && concrete.TryGetProperty("arguments", out var concreteArguments)
          ? concreteArguments : null;
        var arity = datatypeShape.GetProperty("typeArguments").GetInt32();
        if (arity > 0 && (arguments == null || arguments.Value.GetArrayLength() != arity)) {
          throw Unsupported("Generic datatype observation requires concrete Dafny type arguments.");
        }
        var fields = new Dictionary<string, object>();
        foreach (var field in datatypeShape.GetProperty("fields").EnumerateArray()) {
          var member = datatypeFields.GetOrAdd((runtimeType, field.GetProperty("runtimeName").GetString()), key =>
            key.Type.GetField(key.Name) ?? throw Unsupported("Missing datatype runtime field metadata."));
          var fieldShape = field.GetProperty("shape");
          fields.Add(field.GetProperty("name").GetString(), Encode(member.GetValue(value),
            arity == 0 ? fieldShape : ResolveShape(fieldShape, arguments)));
        }
        return new { kind = "datatype", constructor = datatypeShape.GetProperty("constructor").GetString(), fields };
      }
      if (ContractRuntimeConfiguration.RuntimeReferences && heapShapes.EnumerateArray().Any(item => item.GetProperty("runtimeType").GetString() == value.GetType().FullName)) {
        var reference = "pbt-reference-" + references.Count;
        references.Add(value, reference);
        referenceTypes.Add(reference, HeapShape(value).GetProperty("type").GetString());
        logicalFields.Add(reference, new Dictionary<string, JsonElement>(StringComparer.Ordinal));
        return new { kind = "reference", value = reference };
      }
      throw Unsupported("Unsupported runtime observation type: " + value.GetType());
    }
    private static JsonElement ResolveShape(JsonElement shape, JsonElement? arguments) {
      if (shape.GetProperty("kind").GetString() == "parameter") {
        var index = shape.GetProperty("index").GetInt32();
        if (arguments == null || index < 0 || index >= arguments.Value.GetArrayLength()) {
          throw Unsupported("Datatype field has an unresolved Dafny type parameter.");
        }
        return arguments.Value[index];
      }
      var resolved = new Dictionary<string, object>();
      foreach (var property in shape.EnumerateObject()) {
        resolved.Add(property.Name, property.Value.ValueKind switch {
          JsonValueKind.Object => ResolveShape(property.Value, arguments),
          JsonValueKind.Array => property.Value.EnumerateArray().Select(item => ResolveShape(item, arguments)).ToArray(),
          _ => (object)property.Value
        });
      }
      return JsonSerializer.SerializeToElement(resolved);
    }
    public static Dafny.ISequence<Dafny.Rune> InstantiateShape(Dafny.ISequence<Dafny.Rune> shape,
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> arguments) {
      var concrete = new List<JsonElement>();
      foreach (var argument in arguments.Elements) { concrete.Add(Shape(argument)); }
      var resolved = ResolveShape(Shape(shape), JsonSerializer.SerializeToElement(concrete));
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(Convert.ToBase64String(System.Text.Encoding.UTF8.GetBytes(resolved.GetRawText())));
    }
    private static void AddRuntimeFields(string name, object value, Dictionary<string, object> values, HashSet<object> visiting) {
      if (value is Array array) {
        if (!visiting.Add(value)) { return; }
        try {
          for (var dimension = 0; dimension < array.Rank; dimension++) {
            values.Add(name + (array.Rank == 1 ? ".Length" : ".Length" + dimension), new { kind = "integer", value = array.GetLength(dimension).ToString(CultureInfo.InvariantCulture) });
          }
          if (array.Rank == 1) {
            for (var index = 0; index < array.Length; index++) {
              var elementName = name + "[" + index.ToString(CultureInfo.InvariantCulture) + "]";
              var element = array.GetValue(index);
              values.Add(elementName, Encode(element));
              AddRuntimeFields(elementName, element, values, visiting);
            }
          }
        }
        finally {
          visiting.Remove(value);
        }
        return;
      }
      if (value == null || !heapShapes.EnumerateArray().Any(item => item.GetProperty("runtimeType").GetString() == value.GetType().FullName)) { return; }
      if (!visiting.Add(value)) { return; }
      try {
        var shape = HeapShape(value);
        foreach (var field in shape.GetProperty("fields").EnumerateArray()) {
          var member = value.GetType().GetProperty(field.GetProperty("runtimeName").GetString());
          if (member == null) { throw Unsupported("Missing concrete class runtime field."); }
          var fieldName = name + "." + field.GetProperty("name").GetString();
          var fieldValue = member.GetValue(value);
          values.Add(fieldName, Encode(fieldValue, field.GetProperty("shape")));
          AddRuntimeFields(fieldName, fieldValue, values, visiting);
        }
      }
      finally {
        visiting.Remove(value);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> SerializeNamed<T>(Dafny.ISequence<Dafny.Rune> name, T value,
        Dafny.ISequence<Dafny.Rune> shape) {
      var profileStarted = ContractRuntimeProfile.Start();
      try {
        var nameText = Text(name);
        var concreteShape = Shape(shape);
        var key = (nameText, concreteShape.GetRawText());
        if (value != null && !references.ContainsKey(value) &&
            immutableNamedEncodings.TryGetValue(value, out var named) && named.TryGetValue(key, out var existing)) {
          return existing;
        }
        var values = new Dictionary<string, object>(StringComparer.Ordinal) { [nameText] = Encode(value, concreteShape) };
        if (ContractRuntimeConfiguration.RuntimeReferences) {
          AddRuntimeFields(nameText, value, values, new HashSet<object>(ReferenceEqualityComparer.Instance));
        }
        var encodedValues = JsonSerializer.SerializeToElement(values);
        var json = encodedValues.GetRawText();
        var result = Dafny.Sequence<Dafny.Rune>.UnicodeFromString(json.Substring(1, json.Length - 2));
        namedFragments.Add(result, new NamedFragment(encodedValues));
        if (value != null && !references.ContainsKey(value) && immutableValues.TryGetValue(value, out _)) {
          immutableNamedEncodings.GetOrCreateValue(value).TryAdd(key, result);
        }
        return result;
      }
      finally {
        ContractRuntimeProfile.RecordValueEncoding(profileStarted);
      }
    }
    public static OrderedValues PrepareValues(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fragments) {
      var profileStarted = ContractRuntimeProfile.Start();
      try {
        var associated = new JsonElement[fragments.Count];
        var index = 0;
        foreach (var fragment in fragments) {
          if (!namedFragments.TryGetValue(fragment, out var encoded)) {
            var text = "{" + string.Join(",", fragments.Select(Text)) + "}";
            using var parsed = JsonDocument.Parse(text);
            return new OrderedValues(new[] { parsed.RootElement.Clone() });
          }
          associated[index++] = encoded.Values;
        }
        return new OrderedValues(associated);
      }
      finally {
        ContractRuntimeProfile.RecordValueEncoding(profileStarted);
      }
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
      var id = Text(name);
      references.Add(value, id);
      // Registration changes the encoding identity, even if a caller catches a later metadata error.
      immutableEncodings.Clear();
      immutableValues.Clear();
      immutableNamedEncodings.Clear();
      namedFragments.Clear();
      referenceTypes.Add(id, Text(typeName));
      var shape = HeapShape(value);
      var supplied = JsonDocument.Parse(System.Text.Encoding.UTF8.GetString(
        Convert.FromBase64String(Text(logicalBase64)))).RootElement;
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
    internal static object SnapshotHeap() {
      var heap = new List<object>();
      // Reading a field may discover another object. Grow the closure without invalidating enumeration.
      for (var referenceIndex = 0; referenceIndex < references.Count; referenceIndex++) {
        var reference = references.ElementAt(referenceIndex);
        if (reference.Key is Array array) {
          if (array.Rank != 1) { throw Unsupported("Only one-dimensional array observations are implemented."); }
          var elements = new List<object>();
          foreach (var element in array) { elements.Add(Encode(element)); }
          if (!referenceTypes.TryGetValue(reference.Value, out var arrayType)) {
            throw Unsupported("Array heap observation has no resolved element type.");
          }
          heap.Add(new {
            id = reference.Value,
            type = arrayType,
            fields = new Dictionary<string, object>(),
            dimensions = new[] { array.Length },
            elements
          });
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
    public static string RuntimeHeap() {
      var profileStarted = ContractRuntimeProfile.Start();
      try {
        return JsonSerializer.Serialize(SnapshotHeap());
      }
      finally {
        ContractRuntimeProfile.RecordValueEncoding(profileStarted);
      }
    }
    internal static void ApplyHeap(JsonElement heap) {
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
    internal static JsonElement Shape(Dafny.ISequence<Dafny.Rune> encoded) => shapeCache.GetOrAdd(Text(encoded), key => {
      using var document = JsonDocument.Parse(System.Text.Encoding.UTF8.GetString(Convert.FromBase64String(key)));
      return document.RootElement.Clone();
    });
    public static void Capture<T>(Dafny.ISequence<Dafny.Rune> name, T value,
        Dafny.ISequence<Dafny.Rune> shape) {
      File.AppendAllText(ContractRuntimeConfiguration.ObservationPath,
        JsonSerializer.Serialize(new {
          name = Text(name),
          value = Encode(value, Shape(shape))
        }) + "\n");
    }
    public static void Snapshot(Dafny.ISequence<Dafny.Rune> phase) {
      var prefix = "$" + Text(phase) + "/";
      var snapshot = JsonDocument.Parse(JsonSerializer.Serialize(SnapshotHeap())).RootElement;
      foreach (var item in snapshot.EnumerateArray()) {
        var id = item.GetProperty("id").GetString();
        foreach (var field in item.GetProperty("fields").EnumerateObject()) {
          File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
            name = prefix + id + "/" + field.Name,
            value = field.Value
          }) + "\n");
        }
        if (item.TryGetProperty("elements", out var elements)) {
          File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
            name = prefix + id + "/$length",
            value = new { kind = "integer", value = elements.GetArrayLength().ToString(CultureInfo.InvariantCulture) }
          }) + "\n");
          var index = 0;
          foreach (var element in elements.EnumerateArray()) {
            File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
              name = prefix + id + "/[" + index++ + "]",
              value = element
            }) + "\n");
          }
        }
      }
    }
    public static bool Trace(Dafny.ISequence<Dafny.Rune> symbol, BigInteger position, BigInteger line, BigInteger column, bool value) {
      File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
        name = "$branch/" + branchCount++ + "/" + Text(symbol) + "/" + position + "/" + line + "/" + column,
        value = new { kind = "boolean", value = value ? "true" : "false" }
      }) + "\n");
      return value;
    }
    public static T Unreachable<T>() {
      throw new InvalidOperationException("A successful precondition check must return true.");
    }
    public static void AssertionFailed() {
      File.AppendAllText(ContractRuntimeConfiguration.ObservationPath,
        JsonSerializer.Serialize(new { name = "$bodyAssertion", value = new { kind = "boolean", value = "false" } }) + "\n");
      throw new InvalidOperationException("Diagnostic body assertion failed.");
    }
    public static void EnterFrame(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> modifies) {
      var allowed = new HashSet<string>(StringComparer.Ordinal);
      foreach (var value in JsonDocument.Parse(Text(modifies)).RootElement.EnumerateArray()) {
        if (value.GetProperty("kind").GetString() != "reference") {
          throw Unsupported("Unsupported runtime modifies value.");
        }
        allowed.Add(value.GetProperty("value").GetString());
      }
      frames.Push((Text(name), allowed));
    }
    public static void ExitFrame() {
      frames.Pop();
    }
    public static T Write<T>(T receiver, Dafny.ISequence<Dafny.Rune> field) {
      if (receiver == null || !references.TryGetValue(receiver, out var id)) {
        throw Unsupported("Field write receiver is outside the finite observed heap.");
      }
      var fieldName = Text(field);
      File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
        name = "$write/" + writeCount++ + "/" + fieldName,
        value = new { kind = "reference", value = id }
      }) + "\n");
      foreach (var frame in frames) {
        if (!frame.Allowed.Contains(id) && !frameViolationRecorded) {
          frameViolationRecorded = true;
          File.AppendAllText(ContractRuntimeConfiguration.ObservationPath, JsonSerializer.Serialize(new {
            name = "$frameViolation/" + frame.Symbol + "/" + id + "/" + fieldName,
            value = new { kind = "boolean", value = "false" }
          }) + "\n");
        }
      }
      return receiver;
    }
    public static Dafny.ISequence<Dafny.Rune> Serialize<T>(T value, Dafny.ISequence<Dafny.Rune> shape) {
      var profileStarted = ContractRuntimeProfile.Start();
      try {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(JsonSerializer.Serialize(
          Encode(value, Shape(shape))));
      }
      finally {
        ContractRuntimeProfile.RecordValueEncoding(profileStarted);
      }
    }
    internal static object Decode(JsonElement observation, Type target) {
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
