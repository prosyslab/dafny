using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Samples a complete, data-only input pattern from a SHA-256 counter stream.</summary>
public static class ContractPatternSampler {
  public static ContractPatternSample Sample(ContractPatternCampaign campaign, int sampleOrdinal) =>
    Sample(campaign, sampleOrdinal, sampleOrdinal);

  internal static ContractPatternSample Sample(ContractPatternCampaign campaign, int sampleOrdinal,
    int campaignOrdinal, string? oneShotBaselineId = null) {
    ContractPatternCodec.Validate(campaign);
    if (sampleOrdinal < 0 || campaignOrdinal < 0) {
      throw new ArgumentOutOfRangeException(nameof(sampleOrdinal));
    }
    var selector = new CounterStream(campaign.Seed, sampleOrdinal, "$campaign");
    ContractCompleteInputPattern complete;
    if (oneShotBaselineId != null) {
      var baselines = campaign.Patterns.Where(pattern => pattern.Id == oneShotBaselineId).ToList();
      var submitted = campaign.Patterns.Where(pattern => pattern.Id != oneShotBaselineId).ToList();
      if (baselines.Count != 1 || submitted.Count == 0) {
        throw new ArgumentException("A one-shot baseline campaign requires one named baseline and submitted patterns.");
      }
      if (campaignOrdinal == 0) {
        complete = baselines[0];
      } else {
        var submittedOrdinal = campaignOrdinal - 1;
        complete = submittedOrdinal < submitted.Count
          ? submitted[submittedOrdinal]
          : Weighted(submitted, item => item.Weight, selector);
      }
    } else {
      complete = campaignOrdinal < campaign.Patterns.Count
        ? campaign.Patterns[campaignOrdinal]
        : Weighted(campaign.Patterns, item => item.Weight, selector);
    }
    var stream = new CounterStream(campaign.Seed, sampleOrdinal, complete.Id);
    var bindings = new Dictionary<string, ContractValue>(StringComparer.Ordinal);
    var definitions = new Dictionary<string, ContractInputPattern>(StringComparer.Ordinal);
    foreach (var pattern in complete.Inputs.Values) {
      CollectBindings(pattern, definitions);
    }
    var activeBindings = new HashSet<string>(StringComparer.Ordinal);
    var heap = new Dictionary<string, ContractHeapObject>(StringComparer.Ordinal);
    foreach (var item in complete.Heap ?? []) {
      if (!heap.TryAdd(item.Id, item)) {
        throw new ArgumentException("Duplicate pattern heap object id '" + item.Id + "'.");
      }
    }
    var inputs = new Dictionary<string, ContractValue>(StringComparer.Ordinal);
    foreach (var input in complete.Inputs) {
      inputs.Add(input.Key, Sample(input.Value, stream, bindings, definitions, activeBindings, heap));
    }
    var normalized = Normalize(inputs, heap.Values.ToList());
    var inputSha256 = SampleSha256(normalized.Inputs, normalized.Heap);
    return new(normalized.Inputs, normalized.Heap,
      new(ContractPatternCodec.SchemaVersion, campaign.InputSchemaSha256, PatternSetSha256(campaign),
        complete.Id, campaign.Seed, sampleOrdinal, inputSha256));
  }

  public static string PatternSetSha256(ContractPatternCampaign campaign) {
    ContractPatternCodec.Validate(campaign);
    var canonical = JsonSerializer.Serialize(new {
      campaign.SchemaVersion,
      campaign.InputSchemaSha256,
      campaign.Patterns
    }, ContractJson.Options);
    return ContractHarnessBuilder.Hash(canonical);
  }

  public static string SampleSha256(IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyList<ContractHeapObject> heap) {
    var options = new JsonSerializerOptions(ContractJson.Options) {
      DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull
    };
    var canonical = JsonSerializer.Serialize(new {
      Inputs = inputs.OrderBy(pair => pair.Key).ToDictionary(pair => pair.Key, pair => pair.Value),
      Heap = heap
    }, options);
    return ContractHarnessBuilder.Hash(canonical);
  }

  private static ContractValue Sample(ContractInputPattern pattern, CounterStream stream,
    IDictionary<string, ContractValue> bindings, IReadOnlyDictionary<string, ContractInputPattern> definitions,
    ISet<string> activeBindings, IDictionary<string, ContractHeapObject> heap) {
    switch (pattern.Kind) {
      case ContractInputPatternKind.Literal:
        return pattern.Value!;
      case ContractInputPatternKind.OneOf:
        return Sample(Weighted(pattern.Choices!, item => item.Weight, stream).Pattern, stream,
          bindings, definitions, activeBindings, heap);
      case ContractInputPatternKind.Boolean:
        return new(ContractValueKind.Boolean, stream.NextInt(2) == 0 ? "false" : "true");
      case ContractInputPatternKind.IntegerRange:
        var minimum = BigInteger.Parse(pattern.MinValue!, CultureInfo.InvariantCulture);
        var maximum = BigInteger.Parse(pattern.MaxValue!, CultureInfo.InvariantCulture);
        var boundaries = pattern.BoundaryValues!.Select(value => BigInteger.Parse(value,
          CultureInfo.InvariantCulture)).Distinct().ToList();
        var chooseBoundary = boundaries.Count > 0 && stream.NextInt(boundaries.Count + 1) < boundaries.Count;
        var integer = chooseBoundary ? boundaries[stream.NextInt(boundaries.Count)] :
          minimum + stream.NextBigInteger(maximum - minimum + BigInteger.One);
        return new(ContractValueKind.Integer, integer.ToString(CultureInfo.InvariantCulture));
      case ContractInputPatternKind.BitvectorRange:
        var bitvectorMinimum = BigInteger.Parse(pattern.MinValue!, CultureInfo.InvariantCulture);
        var bitvectorMaximum = BigInteger.Parse(pattern.MaxValue!, CultureInfo.InvariantCulture);
        var bitvectorBoundaries = pattern.BoundaryValues!.Select(value => BigInteger.Parse(value,
          CultureInfo.InvariantCulture)).Distinct().ToList();
        var chooseBitvectorBoundary = bitvectorBoundaries.Count > 0 &&
                                      stream.NextInt(bitvectorBoundaries.Count + 1) < bitvectorBoundaries.Count;
        var bitvector = chooseBitvectorBoundary ? bitvectorBoundaries[stream.NextInt(bitvectorBoundaries.Count)] :
          bitvectorMinimum + stream.NextBigInteger(bitvectorMaximum - bitvectorMinimum + BigInteger.One);
        return new(ContractValueKind.Bitvector, bitvector.ToString(CultureInfo.InvariantCulture), Width: pattern.Width);
      case ContractInputPatternKind.Character:
        var characters = pattern.Alphabet!.EnumerateRunes().ToList();
        return new(ContractValueKind.Character, characters[stream.NextInt(characters.Count)].ToString());
      case ContractInputPatternKind.String:
        var alphabet = pattern.Alphabet!.EnumerateRunes().ToList();
        var stringLength = stream.NextInt(pattern.MaxLength!.Value - pattern.MinLength!.Value + 1) + pattern.MinLength.Value;
        return new(ContractValueKind.Sequence, Items: Enumerable.Range(0, stringLength)
          .Select(_ => new ContractValue(ContractValueKind.Character,
            alphabet[stream.NextInt(alphabet.Count)].ToString())).ToList());
      case ContractInputPatternKind.Sequence:
        var sequenceLength = stream.NextInt(pattern.MaxLength!.Value - pattern.MinLength!.Value + 1) + pattern.MinLength.Value;
        return new(ContractValueKind.Sequence, Items: Enumerable.Range(0, sequenceLength)
          .Select(_ => Sample(pattern.Element!, stream, bindings, definitions, activeBindings, heap)).ToList());
      case ContractInputPatternKind.Set:
        var setSize = stream.NextInt(pattern.MaxSize!.Value - pattern.MinSize!.Value + 1) + pattern.MinSize.Value;
        var setItems = new List<ContractValue>();
        var setAttempts = 0;
        var setAttemptLimit = Math.Max(64, checked(setSize * 32));
        while (setItems.Count < setSize && setAttempts++ < setAttemptLimit) {
          var item = Sample(pattern.Element!, stream, bindings, definitions, activeBindings, heap);
          if (!setItems.Any(prior => ContractModelCodec.ValuesEqual(prior, item))) {
            setItems.Add(item);
          }
        }
        if (setItems.Count != setSize) {
          throw new ArgumentException("Set pattern could not produce the requested number of distinct elements.");
        }
        return new(ContractValueKind.Set, Items: setItems);
      case ContractInputPatternKind.Multiset:
        var multisetSize = stream.NextInt(pattern.MaxSize!.Value - pattern.MinSize!.Value + 1) + pattern.MinSize.Value;
        return new(ContractValueKind.Multiset, Items: Enumerable.Range(0, multisetSize)
          .Select(_ => Sample(pattern.Element!, stream, bindings, definitions, activeBindings, heap)).ToList());
      case ContractInputPatternKind.Map:
        var entryCount = stream.NextInt(pattern.MaxEntries!.Value - pattern.MinEntries!.Value + 1) +
                         pattern.MinEntries.Value;
        var entries = new List<ContractMapEntry>();
        var attempts = 0;
        var attemptLimit = Math.Max(64, checked(entryCount * 32));
        while (entries.Count < entryCount && attempts++ < attemptLimit) {
          var key = Sample(pattern.KeyPattern!, stream, bindings, definitions, activeBindings, heap);
          if (entries.Any(entry => ContractModelCodec.ValuesEqual(entry.Key, key))) {
            continue;
          }
          var mappedValue = Sample(pattern.ValuePattern!, stream, bindings, definitions, activeBindings, heap);
          entries.Add(new(key, mappedValue));
        }
        if (entries.Count != entryCount) {
          throw new ArgumentException("Map pattern could not produce the requested number of distinct keys.");
        }
        return new(ContractValueKind.Map, Entries: entries);
      case ContractInputPatternKind.Datatype:
        return new(ContractValueKind.Datatype, Constructor: pattern.Constructor,
          Fields: pattern.Fields!.ToDictionary(field => field.Key,
            field => Sample(field.Value, stream, bindings, definitions, activeBindings, heap), StringComparer.Ordinal));
      case ContractInputPatternKind.Null:
        return new(ContractValueKind.Null);
      case ContractInputPatternKind.Reference:
        if (heap.ContainsKey(pattern.ObjectId!)) {
          throw new ArgumentException("Reference pattern object id '" + pattern.ObjectId +
            "' is already defined; use bind/reuse or a literal reference to alias an object.");
        }
        var fields = pattern.Fields!.ToDictionary(field => field.Key,
          field => Sample(field.Value, stream, bindings, definitions, activeBindings, heap), StringComparer.Ordinal);
        heap.Add(pattern.ObjectId!, new(pattern.ObjectId!, pattern.Type!, fields));
        return new(ContractValueKind.Reference, pattern.ObjectId);
      case ContractInputPatternKind.Bind:
        if (bindings.TryGetValue(pattern.Name!, out var boundValue)) {
          return boundValue;
        }
        if (!activeBindings.Add(pattern.Name!)) {
          throw new ArgumentException("Cyclic input-pattern binding '" + pattern.Name + "'.");
        }
        var value = Sample(pattern.Pattern!, stream, bindings, definitions, activeBindings, heap);
        activeBindings.Remove(pattern.Name!);
        bindings.Add(pattern.Name!, value);
        return value;
      case ContractInputPatternKind.Reuse:
        if (bindings.TryGetValue(pattern.Name!, out var reused)) {
          return reused;
        }
        if (!definitions.TryGetValue(pattern.Name!, out var definition)) {
          throw new ArgumentException("Input-pattern binding '" + pattern.Name + "' has no definition.");
        }
        return Sample(definition, stream, bindings, definitions, activeBindings, heap);
      default:
        throw new ArgumentOutOfRangeException(nameof(pattern.Kind));
    }
  }

  private static void CollectBindings(ContractInputPattern pattern,
    IDictionary<string, ContractInputPattern> definitions) {
    if (pattern.Kind == ContractInputPatternKind.Bind &&
        !definitions.TryAdd(pattern.Name!, pattern)) {
      throw new ArgumentException("Duplicate input-pattern binding '" + pattern.Name + "'.");
    }
    foreach (var child in pattern.Choices?.Select(choice => choice.Pattern) ?? []) {
      CollectBindings(child, definitions);
    }
    if (pattern.Element != null) {
      CollectBindings(pattern.Element, definitions);
    }
    if (pattern.KeyPattern != null) {
      CollectBindings(pattern.KeyPattern, definitions);
    }
    if (pattern.ValuePattern != null) {
      CollectBindings(pattern.ValuePattern, definitions);
    }
    foreach (var child in pattern.Fields?.Values ?? []) {
      CollectBindings(child, definitions);
    }
    if (pattern.Pattern != null) {
      CollectBindings(pattern.Pattern, definitions);
    }
  }

  private static T Weighted<T>(IReadOnlyList<T> items, Func<T, int> weight, CounterStream stream) {
    var total = items.Aggregate(0L, (sum, item) => checked(sum + weight(item)));
    if (total > int.MaxValue) {
      throw new ArgumentException("Pattern weights exceed the supported deterministic range.");
    }
    var selected = stream.NextInt((int)total);
    foreach (var item in items) {
      selected -= weight(item);
      if (selected < 0) {
        return item;
      }
    }
    throw new InvalidOperationException("Weighted pattern selection did not choose an item.");
  }

  private sealed record NormalizedSample(IReadOnlyDictionary<string, ContractValue> Inputs,
    IReadOnlyList<ContractHeapObject> Heap);

  private static NormalizedSample Normalize(IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyList<ContractHeapObject> heap) {
    var objects = heap.ToDictionary(item => item.Id, StringComparer.Ordinal);
    var ordered = new List<ContractHeapObject>();
    var active = new HashSet<string>(StringComparer.Ordinal);
    var visited = new HashSet<string>(StringComparer.Ordinal);
    void Visit(string id) {
      if (!objects.TryGetValue(id, out var item)) {
        throw new ArgumentException("Pattern value references unknown heap object '" + id + "'.");
      }
      if (visited.Contains(id)) {
        return;
      }
      if (!active.Add(id)) {
        throw new NotSupportedException("Cyclic pattern heap graphs are not supported by the concrete M1 sampler.");
      }
      foreach (var reference in item.Fields.Values.Concat(item.Elements ?? []).SelectMany(References).Distinct()) {
        Visit(reference);
      }
      active.Remove(id);
      visited.Add(id);
      ordered.Add(item);
    }
    foreach (var reference in inputs.Values.SelectMany(References).Distinct()) {
      Visit(reference);
    }
    foreach (var item in heap.OrderBy(item => item.Id, StringComparer.Ordinal)) {
      Visit(item.Id);
    }
    var ids = ordered.Select((item, index) => (item.Id, Canonical: "object" + index))
      .ToDictionary(pair => pair.Id, pair => pair.Canonical, StringComparer.Ordinal);
    ContractValue Rewrite(ContractValue value) => value.Kind switch {
      ContractValueKind.Reference => value with { Value = ids[value.Value!] },
      ContractValueKind.Sequence or ContractValueKind.Set or ContractValueKind.Multiset =>
        value with { Items = value.Items!.Select(Rewrite).ToList() },
      ContractValueKind.Map => value with {
        Entries = value.Entries!.Select(entry => new ContractMapEntry(Rewrite(entry.Key), Rewrite(entry.Value))).ToList()
      },
      ContractValueKind.Datatype => value with {
        Fields = value.Fields!.ToDictionary(field => field.Key, field => Rewrite(field.Value), StringComparer.Ordinal)
      },
      _ => value
    };
    var normalizedInputs = inputs.ToDictionary(input => input.Key, input => Rewrite(input.Value), StringComparer.Ordinal);
    var normalizedHeap = ordered.Select(item => item with {
      Id = ids[item.Id],
      Fields = item.Fields.ToDictionary(field => field.Key, field => Rewrite(field.Value), StringComparer.Ordinal),
      Elements = item.Elements?.Select(Rewrite).ToList()
    }).ToList();
    return new(normalizedInputs, normalizedHeap);
  }

  private static IEnumerable<string> References(ContractValue value) {
    if (value.Kind == ContractValueKind.Reference) {
      yield return value.Value!;
    }
    foreach (var nested in (value.Items ?? []).Concat(value.Fields?.Values ?? [])) {
      foreach (var reference in References(nested)) {
        yield return reference;
      }
    }
    foreach (var entry in value.Entries ?? []) {
      foreach (var reference in References(entry.Key).Concat(References(entry.Value))) {
        yield return reference;
      }
    }
  }

  private sealed class CounterStream(ulong seed, int sampleOrdinal, string domain) {
    private ulong counter;

    public int NextInt(int exclusiveMaximum) {
      if (exclusiveMaximum <= 0) {
        throw new ArgumentOutOfRangeException(nameof(exclusiveMaximum));
      }
      return (int)(NextUInt64() % (ulong)exclusiveMaximum);
    }

    public BigInteger NextBigInteger(BigInteger exclusiveMaximum) {
      if (exclusiveMaximum <= BigInteger.Zero) {
        throw new ArgumentOutOfRangeException(nameof(exclusiveMaximum));
      }
      var byteCount = exclusiveMaximum.GetByteCount(isUnsigned: true);
      var bytes = new byte[byteCount];
      var offset = 0;
      while (offset < bytes.Length) {
        var block = NextBlock();
        var count = Math.Min(block.Length, bytes.Length - offset);
        block.AsSpan(0, count).CopyTo(bytes.AsSpan(offset));
        offset += count;
      }
      return new BigInteger(bytes, isUnsigned: true, isBigEndian: true) % exclusiveMaximum;
    }

    private ulong NextUInt64() => BinaryPrimitives.ReadUInt64BigEndian(NextBlock());

    private byte[] NextBlock() {
      var domainBytes = Encoding.UTF8.GetBytes(domain);
      var bytes = new byte[8 + 4 + 8 + 4 + domainBytes.Length];
      BinaryPrimitives.WriteUInt64BigEndian(bytes.AsSpan(0, 8), seed);
      BinaryPrimitives.WriteInt32BigEndian(bytes.AsSpan(8, 4), sampleOrdinal);
      BinaryPrimitives.WriteUInt64BigEndian(bytes.AsSpan(12, 8), counter++);
      BinaryPrimitives.WriteInt32BigEndian(bytes.AsSpan(20, 4), domainBytes.Length);
      domainBytes.CopyTo(bytes.AsSpan(24));
      return SHA256.HashData(bytes);
    }
  }
}
