using System;
using System.Buffers;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractModelCodec {
  public static void Validate(ContractValue value) {
    if (value == null) {
      throw new ArgumentException("A concrete value must be a typed object, not JSON null.");
    }
    var valid = value.Kind switch {
      ContractValueKind.Integer or ContractValueKind.Boolean or ContractValueKind.Character or ContractValueKind.Reference =>
        value.Value != null && value.Items == null && value.Constructor == null && value.Fields == null && value.Entries == null &&
        value.Width == null,
      ContractValueKind.Bitvector => value.Value != null && value.Width is >= 0 and <= 65536 && value.Items == null &&
        value.Constructor == null && value.Fields == null && value.Entries == null,
      ContractValueKind.Sequence => value.Value == null && value.Items != null && value.Constructor == null && value.Fields == null && value.Entries == null && value.Width == null,
      ContractValueKind.Set or ContractValueKind.Multiset => value.Value == null && value.Items != null &&
        value.Constructor == null && value.Fields == null && value.Entries == null && value.Width == null,
      ContractValueKind.Map => value.Value == null && value.Items == null && value.Constructor == null && value.Fields == null && value.Entries != null && value.Width == null,
      ContractValueKind.Datatype => value.Value == null && value.Items == null && value.Constructor != null && value.Fields != null && value.Entries == null && value.Width == null,
      ContractValueKind.Null => value.Value == null && value.Items == null && value.Constructor == null && value.Fields == null && value.Entries == null && value.Width == null,
      _ => false
    };
    if (!valid) {
      throw new ArgumentException("Concrete value payload does not match its kind: " + value.Kind);
    }
    if (value.Kind == ContractValueKind.Bitvector &&
        (!BigInteger.TryParse(value.Value, NumberStyles.None, CultureInfo.InvariantCulture, out var bitvector) ||
         bitvector < 0 || bitvector >= BigInteger.One << value.Width!.Value)) {
      throw new ArgumentException("Concrete bitvector values must fit their declared nonnegative width.");
    }
    foreach (var item in value.Items ?? []) {
      Validate(item);
    }
    foreach (var item in value.Fields?.Values ?? []) {
      Validate(item);
    }
    foreach (var entry in value.Entries ?? []) {
      if (entry == null || entry.Key == null || entry.Value == null) {
        throw new ArgumentException("Concrete map entries require typed key and value objects.");
      }
      Validate(entry.Key);
      Validate(entry.Value);
    }
    if (value.Kind == ContractValueKind.Map && HasDuplicateMapKeys(value.Entries!)) {
      throw new ArgumentException("Concrete map values cannot contain duplicate keys.");
    }
    if (value.Kind == ContractValueKind.Set && HasDuplicateValues(value.Items!)) {
      throw new ArgumentException("Concrete set values cannot contain duplicate elements.");
    }
  }

  public static string ToDafny(ContractValue value, string? moduleName = null) {
    return value.Kind switch {
      ContractValueKind.Integer when BigInteger.TryParse(value.Value, NumberStyles.AllowLeadingSign,
        CultureInfo.InvariantCulture, out var integer) => integer.ToString(CultureInfo.InvariantCulture),
      ContractValueKind.Bitvector when value.Width is >= 0 && BigInteger.TryParse(value.Value, NumberStyles.None,
        CultureInfo.InvariantCulture, out var bitvector) && bitvector < BigInteger.One << value.Width.Value =>
        "(" + bitvector.ToString(CultureInfo.InvariantCulture) + " as bv" + value.Width.Value + ")",
      ContractValueKind.Boolean when value.Value is "true" or "false" => value.Value,
      ContractValueKind.Character when value.Value != null &&
        Rune.DecodeFromUtf16(value.Value.AsSpan(), out var rune, out var consumed) == OperationStatus.Done && consumed == value.Value.Length =>
        "'" + (rune.IsBmp ? EscapeCharacter((char)rune.Value) : "\\U{" + rune.Value.ToString("X", CultureInfo.InvariantCulture) + "}") + "'",
      ContractValueKind.Sequence when value.Items != null => "[" + string.Join(", ", value.Items.Select(item => ToDafny(item, moduleName))) + "]",
      ContractValueKind.Set when value.Items != null => "{" + string.Join(", ", value.Items.Select(item => ToDafny(item, moduleName))) + "}",
      ContractValueKind.Multiset when value.Items != null => "multiset{" + string.Join(", ", value.Items.Select(item => ToDafny(item, moduleName))) + "}",
      ContractValueKind.Map when value.Entries != null => "map[" + string.Join(", ", value.Entries.Select(entry =>
        ToDafny(entry.Key, moduleName) + " := " + ToDafny(entry.Value, moduleName))) + "]",
      ContractValueKind.Datatype when value.Constructor != null && value.Fields != null &&
        Regex.IsMatch(value.Constructor, "^[A-Za-z_][A-Za-z_0-9]*(\\.[A-Za-z_][A-Za-z_0-9]*)*$") &&
        value.Fields.Keys.All(name => Regex.IsMatch(name, "^[A-Za-z_][A-Za-z_0-9]*$")) =>
        LocalName(value.Constructor, moduleName) + "(" + string.Join(", ", value.Fields.Select(field => field.Key + " := " + ToDafny(field.Value, moduleName))) + ")",
      ContractValueKind.Null => "null",
      _ => throw new NotSupportedException($"Cannot realize {value.Kind} as a concrete Dafny value.")
    };
  }

  internal static bool ValuesEqual(ContractValue left, ContractValue right) {
    if (left.Kind != right.Kind || left.Value != right.Value || left.Constructor != right.Constructor ||
        left.Width != right.Width) {
      return false;
    }
    if (left.Items == null || right.Items == null) {
      if (left.Items != right.Items) {
        return false;
      }
    } else if (left.Kind == ContractValueKind.Set) {
      if (left.Items.Count != right.Items.Count || left.Items.Any(item =>
            right.Items.Count(other => ValuesEqual(item, other)) != 1)) {
        return false;
      }
    } else if (left.Kind == ContractValueKind.Multiset) {
      if (!UnorderedValuesEqual(left.Items, right.Items)) {
        return false;
      }
    } else if (left.Items.Count != right.Items.Count ||
               left.Items.Where((item, index) => !ValuesEqual(item, right.Items[index])).Any()) {
      return false;
    }
    if (left.Fields == null || right.Fields == null) {
      if (left.Fields != right.Fields) {
        return false;
      }
    } else if (left.Fields.Count != right.Fields.Count || left.Fields.Any(pair =>
                 !right.Fields.TryGetValue(pair.Key, out var value) || !ValuesEqual(pair.Value, value))) {
      return false;
    }
    if (left.Entries == null || right.Entries == null) {
      return left.Entries == right.Entries;
    }
    return left.Entries.Count == right.Entries.Count && left.Entries.All(entry =>
      right.Entries.Count(other => ValuesEqual(entry.Key, other.Key) && ValuesEqual(entry.Value, other.Value)) == 1);
  }

  internal static bool HasDuplicateMapKeys(IReadOnlyList<ContractMapEntry> entries) =>
    entries.Select((entry, index) => (entry.Key, index)).Any(item =>
      entries.Take(item.index).Any(prior => ValuesEqual(prior.Key, item.Key)));

  internal static bool HasDuplicateValues(IReadOnlyList<ContractValue> values) =>
    values.Select((value, index) => (value, index)).Any(item =>
      values.Take(item.index).Any(prior => ValuesEqual(prior, item.value)));

  private static bool UnorderedValuesEqual(IReadOnlyList<ContractValue> left,
    IReadOnlyList<ContractValue> right) {
    if (left.Count != right.Count) {
      return false;
    }
    var matched = new bool[right.Count];
    foreach (var value in left) {
      var index = Enumerable.Range(0, right.Count)
        .FirstOrDefault(index => !matched[index] && ValuesEqual(value, right[index]), -1);
      if (index < 0) {
        return false;
      }
      matched[index] = true;
    }
    return true;
  }

  public static string LocalName(string name, string? moduleName) =>
    !string.IsNullOrEmpty(moduleName) && name.StartsWith(moduleName + ".", StringComparison.Ordinal)
      ? name[(moduleName.Length + 1)..] : name;

  private static string EscapeCharacter(char value) {
    return value switch {
      '\'' => "\\'",
      '\\' => "\\\\",
      '\n' => "\\n",
      '\r' => "\\r",
      '\t' => "\\t",
      _ when char.IsControl(value) || char.IsSurrogate(value) => "\\u" + ((int)value).ToString("X4"),
      _ => value.ToString()
    };
  }
}
