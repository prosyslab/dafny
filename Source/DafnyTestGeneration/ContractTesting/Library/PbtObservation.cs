using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using DafnyContractRuntime;
namespace DafnyPbtRuntime {
  /// <summary>Encodes runtime values and the observed heap for generated runtime-check records; it never contacts the parent process.</summary>
  public static class Observation {
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<string, JsonElement> shapeCache = new(StringComparer.Ordinal);
    private static readonly Dictionary<object, string> references = new(ReferenceEqualityComparer.Instance);
    private static readonly Dictionary<string, string> referenceTypes = new(StringComparer.Ordinal);
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
    internal static JsonElement Shape(Dafny.ISequence<Dafny.Rune> encoded) => shapeCache.GetOrAdd(Text(encoded), key => {
      using var document = JsonDocument.Parse(System.Text.Encoding.UTF8.GetString(Convert.FromBase64String(key)));
      return document.RootElement.Clone();
    });
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
  }
}
