using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractGenerationStrategy { SolverGoals, InputPatterns }

public enum ContractInputPatternKind {
  Literal,
  OneOf,
  Boolean,
  IntegerRange,
  BitvectorRange,
  Character,
  String,
  Sequence,
  Set,
  Multiset,
  Map,
  Datatype,
  Null,
  Reference,
  Bind,
  Reuse
}

public sealed record ContractWeightedInputPattern(
  [property: JsonRequired] int Weight,
  [property: JsonRequired] ContractInputPattern Pattern);

/// <summary>
/// A data-only input generator node. Variant payloads are checked by <see cref="ContractPatternCodec"/>;
/// none of the fields contain Dafny expressions or statements.
/// </summary>
public sealed record ContractInputPattern(
  [property: JsonRequired] ContractInputPatternKind Kind,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractValue? Value = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] IReadOnlyList<ContractWeightedInputPattern>? Choices = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? MinValue = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? MaxValue = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] IReadOnlyList<string>? BoundaryValues = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? Width = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? Alphabet = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MinLength = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MaxLength = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractInputPattern? Element = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MinSize = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MaxSize = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MinEntries = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] int? MaxEntries = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractInputPattern? KeyPattern = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractInputPattern? ValuePattern = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? Constructor = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] IReadOnlyDictionary<string, ContractInputPattern>? Fields = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? Type = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? ObjectId = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? Name = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractInputPattern? Pattern = null);

public sealed record ContractCompleteInputPattern(
  [property: JsonRequired] string Id,
  [property: JsonRequired] int Weight,
  [property: JsonRequired] IReadOnlyDictionary<string, ContractInputPattern> Inputs,
  IReadOnlyList<ContractHeapObject>? Heap = null);

public sealed record ContractPatternCampaign(
  [property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] string InputSchemaSha256,
  [property: JsonRequired] ulong Seed,
  [property: JsonRequired] IReadOnlyList<ContractCompleteInputPattern> Patterns,
  int? MaxSamples = null);

public sealed record ContractCampaignFeedback(
  [property: JsonRequired] int Round,
  IReadOnlyList<string>? SeenInputSha256,
  IReadOnlyList<string>? ObservedBranchIds,
  IReadOnlyList<string>? ObservedSpecificationCaseIds,
  [property: JsonRequired] int RemainingSamples,
  [property: JsonRequired] int RemainingMilliseconds,
  int SampleOrdinalOffset = 0);

public sealed record ContractPatternProvenance(int PatternSchemaVersion, string InputSchemaSha256,
  string PatternSetSha256, string PatternId, ulong Seed, int SampleOrdinal, string? InputSha256 = null);

public sealed record ContractPatternSample(IReadOnlyDictionary<string, ContractValue> Inputs,
  IReadOnlyList<ContractHeapObject> Heap, ContractPatternProvenance Provenance);

public static class ContractPatternCodec {
  public const int SchemaVersion = 1;
  private static readonly Regex Identifier = new("^[A-Za-z_][A-Za-z0-9_]*$", RegexOptions.CultureInvariant);
  private static readonly Regex QualifiedIdentifier = new(
    "^[A-Za-z_][A-Za-z0-9_]*(\\.[A-Za-z_][A-Za-z0-9_]*)*$", RegexOptions.CultureInvariant);
  private static readonly Regex StableId = new("^[A-Za-z_][A-Za-z0-9_-]*$", RegexOptions.CultureInvariant);
  private static readonly Regex Sha256 = new("^[0-9a-f]{64}$", RegexOptions.CultureInvariant);
  private static readonly Regex TypeName = new("^[A-Za-z_][A-Za-z0-9_.?<>,]*$", RegexOptions.CultureInvariant);

  public static void Validate(ContractPatternCampaign campaign) {
    if (campaign == null || campaign.SchemaVersion != SchemaVersion ||
        campaign.InputSchemaSha256 == null || !Sha256.IsMatch(campaign.InputSchemaSha256) ||
        campaign.Patterns == null || campaign.Patterns.Count == 0 || campaign.MaxSamples is <= 0) {
      throw new ArgumentException(
        "A pattern campaign requires schema version 1, an input-schema SHA-256, patterns and a positive optional sample limit.");
    }
    var duplicate = campaign.Patterns.GroupBy(pattern => pattern.Id, StringComparer.Ordinal)
      .FirstOrDefault(group => group.Count() > 1)?.Key;
    if (duplicate != null) {
      throw new ArgumentException("Duplicate complete input pattern id '" + duplicate + "'.");
    }
    foreach (var pattern in campaign.Patterns) {
      if (pattern == null || string.IsNullOrWhiteSpace(pattern.Id) || !StableId.IsMatch(pattern.Id) ||
          pattern.Weight <= 0 || pattern.Inputs == null) {
        throw new ArgumentException("Complete input patterns require a stable id, positive weight and an inputs object.");
      }
      foreach (var node in pattern.Inputs.Values) {
        Validate(node, new HashSet<ContractInputPattern>(ReferenceEqualityComparer.Instance));
      }
      foreach (var item in pattern.Heap ?? []) {
        if (item == null || !IsStableId(item.Id) || !IsTypeName(item.Type) || item.Fields == null) {
          throw new ArgumentException(
            "Concrete pattern heap objects require a stable id, qualified class type and fields object.");
        }
        if (item.Dimensions != null || item.Elements != null) {
          if (item.Dimensions is not { Count: 1 } || item.Dimensions[0] < 0 || item.Elements == null ||
              item.Elements.Count != item.Dimensions[0] || item.Fields.Count != 0) {
            throw new ArgumentException(
              "Concrete pattern array objects require one dimension, exact elements and no fields.");
          }
        }
        foreach (var value in item.Fields.Values.Concat(item.Elements ?? [])) {
          ValidateLiteral(value);
        }
      }
    }
  }

  public static void Validate(ContractCampaignFeedback feedback) {
    if (feedback == null || feedback.Round < 0 || feedback.RemainingSamples < 0 ||
        feedback.SampleOrdinalOffset < 0 ||
        feedback.RemainingMilliseconds < 0 ||
        (feedback.SeenInputSha256 ?? []).Any(digest => digest == null || !Sha256.IsMatch(digest))) {
      throw new ArgumentException(
        "Campaign feedback requires nonnegative budgets and lowercase SHA-256 input digests.");
    }
    ValidateDistinctIds(feedback.ObservedBranchIds, "observedBranchIds");
    ValidateDistinctIds(feedback.ObservedSpecificationCaseIds, "observedSpecificationCaseIds");
  }

  public static void Validate(ContractInputPattern pattern) =>
    Validate(pattern, new HashSet<ContractInputPattern>(ReferenceEqualityComparer.Instance));

  internal static bool IsIdentifier(string? value) => value != null && Identifier.IsMatch(value);
  internal static bool IsQualifiedIdentifier(string? value) => value != null && QualifiedIdentifier.IsMatch(value);
  internal static bool IsStableId(string? value) => value != null && StableId.IsMatch(value);

  internal static bool IsTypeName(string? value) {
    if (value == null || !TypeName.IsMatch(value)) {
      return false;
    }
    var depth = 0;
    foreach (var character in value) {
      if (character == '<') {
        depth++;
      } else if (character == '>' && --depth < 0) {
        return false;
      }
    }
    return depth == 0;
  }

  private static void Validate(ContractInputPattern pattern, HashSet<ContractInputPattern> active) {
    if (pattern == null || !active.Add(pattern)) {
      throw new ArgumentException("Input pattern nodes must be non-null and acyclic.");
    }
    var allowed = pattern.Kind switch {
      ContractInputPatternKind.Literal => pattern.Value != null && Only(pattern, nameof(pattern.Value)),
      ContractInputPatternKind.OneOf => pattern.Choices is { Count: > 0 } &&
        pattern.Choices.All(choice => choice != null && choice.Weight > 0 && choice.Pattern != null) &&
        Only(pattern, nameof(pattern.Choices)),
      ContractInputPatternKind.Boolean => Only(pattern),
      ContractInputPatternKind.IntegerRange => ValidIntegerRange(pattern) &&
        Only(pattern, nameof(pattern.MinValue), nameof(pattern.MaxValue), nameof(pattern.BoundaryValues)),
      ContractInputPatternKind.BitvectorRange => ValidBitvectorRange(pattern) &&
        Only(pattern, nameof(pattern.MinValue), nameof(pattern.MaxValue), nameof(pattern.BoundaryValues), nameof(pattern.Width)),
      ContractInputPatternKind.Character => ValidAlphabet(pattern.Alphabet) && Only(pattern, nameof(pattern.Alphabet)),
      ContractInputPatternKind.String => ValidLengths(pattern) && ValidAlphabet(pattern.Alphabet) &&
        Only(pattern, nameof(pattern.MinLength), nameof(pattern.MaxLength), nameof(pattern.Alphabet)),
      ContractInputPatternKind.Sequence => ValidLengths(pattern) && pattern.Element != null &&
        Only(pattern, nameof(pattern.MinLength), nameof(pattern.MaxLength), nameof(pattern.Element)),
      ContractInputPatternKind.Set or ContractInputPatternKind.Multiset => ValidSizes(pattern) &&
        pattern.Element != null && Only(pattern, nameof(pattern.MinSize), nameof(pattern.MaxSize), nameof(pattern.Element)),
      ContractInputPatternKind.Map => ValidEntries(pattern) && pattern.KeyPattern != null &&
        pattern.ValuePattern != null && Only(pattern, nameof(pattern.MinEntries), nameof(pattern.MaxEntries),
          nameof(pattern.KeyPattern), nameof(pattern.ValuePattern)),
      ContractInputPatternKind.Datatype => IsQualifiedIdentifier(pattern.Constructor) && pattern.Fields != null &&
        pattern.Fields.Keys.All(IsIdentifier) && Only(pattern, nameof(pattern.Constructor), nameof(pattern.Fields)),
      ContractInputPatternKind.Null => Only(pattern),
      ContractInputPatternKind.Reference => IsQualifiedIdentifier(pattern.Type) && IsStableId(pattern.ObjectId) &&
        pattern.Fields != null && pattern.Fields.Keys.All(IsIdentifier) &&
        Only(pattern, nameof(pattern.Type), nameof(pattern.ObjectId), nameof(pattern.Fields)),
      ContractInputPatternKind.Bind => IsIdentifier(pattern.Name) && pattern.Pattern != null &&
        Only(pattern, nameof(pattern.Name), nameof(pattern.Pattern)),
      ContractInputPatternKind.Reuse => IsIdentifier(pattern.Name) && Only(pattern, nameof(pattern.Name)),
      _ => false
    };
    if (!allowed) {
      throw new ArgumentException("Input pattern payload does not match its kind: " + pattern.Kind);
    }
    if (pattern.Value != null) {
      ValidateLiteral(pattern.Value);
    }
    foreach (var child in pattern.Choices?.Select(choice => choice.Pattern) ?? []) {
      Validate(child, active);
    }
    if (pattern.Element != null) {
      Validate(pattern.Element, active);
    }
    if (pattern.KeyPattern != null) {
      Validate(pattern.KeyPattern, active);
    }
    if (pattern.ValuePattern != null) {
      Validate(pattern.ValuePattern, active);
    }
    foreach (var child in pattern.Fields?.Values ?? []) {
      Validate(child, active);
    }
    if (pattern.Pattern != null) {
      Validate(pattern.Pattern, active);
    }
    active.Remove(pattern);
  }

  private static bool ValidIntegerRange(ContractInputPattern pattern) {
    if (!BigInteger.TryParse(pattern.MinValue, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var minimum) ||
        !BigInteger.TryParse(pattern.MaxValue, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var maximum) ||
        minimum > maximum || pattern.BoundaryValues == null) {
      return false;
    }
    return pattern.BoundaryValues.All(value => BigInteger.TryParse(value, NumberStyles.AllowLeadingSign,
      CultureInfo.InvariantCulture, out var boundary) && minimum <= boundary && boundary <= maximum);
  }

  private static bool ValidLengths(ContractInputPattern pattern) =>
    pattern.MinLength is >= 0 && pattern.MaxLength is >= 0 && pattern.MinLength <= pattern.MaxLength;

  private static bool ValidBitvectorRange(ContractInputPattern pattern) {
    if (pattern.Width is not >= 0 or > 65536 || !ValidIntegerRange(pattern)) {
      return false;
    }
    var maximum = (BigInteger.One << pattern.Width.Value) - BigInteger.One;
    return BigInteger.Parse(pattern.MinValue!, CultureInfo.InvariantCulture) >= 0 &&
           BigInteger.Parse(pattern.MaxValue!, CultureInfo.InvariantCulture) <= maximum;
  }

  private static bool ValidEntries(ContractInputPattern pattern) =>
    pattern.MinEntries is >= 0 && pattern.MaxEntries is >= 0 && pattern.MinEntries <= pattern.MaxEntries;

  private static bool ValidSizes(ContractInputPattern pattern) =>
    pattern.MinSize is >= 0 && pattern.MaxSize is >= 0 && pattern.MinSize <= pattern.MaxSize;

  private static bool ValidAlphabet(string? alphabet) => alphabet != null && alphabet.EnumerateRunes().Any();

  private static void ValidateDistinctIds(IReadOnlyList<string>? values, string label) {
    values ??= [];
    if (values.Any(string.IsNullOrWhiteSpace) || values.Distinct(StringComparer.Ordinal).Count() != values.Count) {
      throw new ArgumentException(label + " must contain distinct nonempty ids.");
    }
  }

  private static void ValidateLiteral(ContractValue value) {
    ContractModelCodec.Validate(value);
    switch (value.Kind) {
      case ContractValueKind.Reference:
        if (!IsStableId(value.Value)) {
          throw new ArgumentException("Literal references require a stable object id.");
        }
        return;
      case ContractValueKind.Sequence:
      case ContractValueKind.Set:
      case ContractValueKind.Multiset:
        foreach (var item in value.Items!) {
          ValidateLiteral(item);
        }
        return;
      case ContractValueKind.Map:
        foreach (var entry in value.Entries!) {
          ValidateLiteral(entry.Key);
          ValidateLiteral(entry.Value);
        }
        return;
      case ContractValueKind.Datatype:
        if (!IsQualifiedIdentifier(value.Constructor) || !value.Fields!.Keys.All(IsIdentifier)) {
          throw new ArgumentException("Literal datatype constructor and field names must be identifiers.");
        }
        foreach (var item in value.Fields.Values) {
          ValidateLiteral(item);
        }
        return;
      case ContractValueKind.Null:
        return;
      default:
        _ = ContractModelCodec.ToDafny(value);
        return;
    }
  }

  private static bool Only(ContractInputPattern pattern, params string[] fields) {
    var allowed = fields.ToHashSet(StringComparer.Ordinal);
    return (pattern.Value == null || allowed.Contains(nameof(pattern.Value))) &&
      (pattern.Choices == null || allowed.Contains(nameof(pattern.Choices))) &&
      (pattern.MinValue == null || allowed.Contains(nameof(pattern.MinValue))) &&
      (pattern.MaxValue == null || allowed.Contains(nameof(pattern.MaxValue))) &&
      (pattern.BoundaryValues == null || allowed.Contains(nameof(pattern.BoundaryValues))) &&
      (pattern.Width == null || allowed.Contains(nameof(pattern.Width))) &&
      (pattern.Alphabet == null || allowed.Contains(nameof(pattern.Alphabet))) &&
      (pattern.MinLength == null || allowed.Contains(nameof(pattern.MinLength))) &&
      (pattern.MaxLength == null || allowed.Contains(nameof(pattern.MaxLength))) &&
      (pattern.Element == null || allowed.Contains(nameof(pattern.Element))) &&
      (pattern.MinSize == null || allowed.Contains(nameof(pattern.MinSize))) &&
      (pattern.MaxSize == null || allowed.Contains(nameof(pattern.MaxSize))) &&
      (pattern.MinEntries == null || allowed.Contains(nameof(pattern.MinEntries))) &&
      (pattern.MaxEntries == null || allowed.Contains(nameof(pattern.MaxEntries))) &&
      (pattern.KeyPattern == null || allowed.Contains(nameof(pattern.KeyPattern))) &&
      (pattern.ValuePattern == null || allowed.Contains(nameof(pattern.ValuePattern))) &&
      (pattern.Constructor == null || allowed.Contains(nameof(pattern.Constructor))) &&
      (pattern.Fields == null || allowed.Contains(nameof(pattern.Fields))) &&
      (pattern.Type == null || allowed.Contains(nameof(pattern.Type))) &&
      (pattern.ObjectId == null || allowed.Contains(nameof(pattern.ObjectId))) &&
      (pattern.Name == null || allowed.Contains(nameof(pattern.Name))) &&
      (pattern.Pattern == null || allowed.Contains(nameof(pattern.Pattern)));
  }
}
