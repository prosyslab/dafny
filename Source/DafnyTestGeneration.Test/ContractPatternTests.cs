#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractPatternTests {
  private const string InputSchemaSha256 =
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

  private static ContractValue Integer(string value) => new(ContractValueKind.Integer, value);

  private static ContractValue Bitvector(string value, int width) =>
    new(ContractValueKind.Bitvector, value, Width: width);

  private static ContractInputPattern Literal(ContractValue value) =>
    new(ContractInputPatternKind.Literal, Value: value);

  private static ContractInputPattern MapPattern(int minEntries, int maxEntries,
    ContractInputPattern key, ContractInputPattern value) =>
    new(ContractInputPatternKind.Map, MinEntries: minEntries, MaxEntries: maxEntries,
      KeyPattern: key, ValuePattern: value);

  private static ContractInputPattern CollectionPattern(ContractInputPatternKind kind,
    int minSize, int maxSize, ContractInputPattern element) =>
    new(kind, MinSize: minSize, MaxSize: maxSize, Element: element);

  private static ContractInputPattern BitvectorPattern(int width, string minimum, string maximum) =>
    new(ContractInputPatternKind.BitvectorRange, MinValue: minimum, MaxValue: maximum,
      BoundaryValues: [minimum, maximum], Width: width);

  private static ContractPatternCampaign Campaign(int maxSamples,
    params ContractCompleteInputPattern[] patterns) =>
    new(ContractPatternCodec.SchemaVersion, InputSchemaSha256, 712367, patterns, maxSamples);

  // The versioned pattern payload round-trips without null variant fields and rejects unknown JSON fields.
  [Fact]
  public void PatternJsonIsStrictAndVersioned() {
    var request = ContractInputTests.Request("method Entry(x:int) { }", count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(1, new ContractCompleteInputPattern("integer", 1,
        new Dictionary<string, ContractInputPattern> {
          ["x"] = new(ContractInputPatternKind.IntegerRange,
            MinValue: "-2", MaxValue: "2", BoundaryValues: ["-2", "0", "2"])
        })),
      CampaignFeedback = new(0, [], ["body0"], ["spec0"], 1, 1000)
    };
    var json = JsonSerializer.Serialize(request, ContractJson.Options);
    Assert.Contains("\"generationStrategy\":\"input_patterns\"", json);
    Assert.Contains("\"inputSchemaSha256\":\"" + InputSchemaSha256 + "\"", json);
    Assert.DoesNotContain("\"alphabet\":null", json);
    var roundTrip = JsonSerializer.Deserialize<ContractGenerationRequest>(json, ContractJson.Options);
    Assert.NotNull(roundTrip?.PatternCampaign);
    Assert.Equal("body0", Assert.Single(roundTrip!.CampaignFeedback!.ObservedBranchIds!));
    ContractInputGenerator.ValidateRequest(roundTrip);

    var invalid = json.Replace("\"minValue\":\"-2\"", "\"minValue\":\"-2\",\"dafnySource\":\"assume false\"",
      StringComparison.Ordinal);
    Assert.Throws<JsonException>(() =>
      JsonSerializer.Deserialize<ContractGenerationRequest>(invalid, ContractJson.Options));
  }

  // Variant validation prevents a node from smuggling fields belonging to a different pattern kind.
  [Fact]
  public void PatternVariantRejectsIrrelevantPayload() {
    var invalid = new ContractInputPattern(ContractInputPatternKind.Boolean, Alphabet: "ab");
    Assert.Throws<ArgumentException>(() => ContractPatternCodec.Validate(invalid));
  }

  // Map values and patterns round-trip as closed schema-1 data while duplicate literal keys are rejected.
  [Fact]
  public void MapJsonIsStrictAndRejectsDuplicateLiteralKeys() {
    var value = new ContractValue(ContractValueKind.Map, Entries: [
      new(Integer("7"), new(ContractValueKind.Boolean, "true"))
    ]);
    var pattern = MapPattern(1, 2,
      new(ContractInputPatternKind.IntegerRange, MinValue: "0", MaxValue: "9", BoundaryValues: ["0", "9"]),
      new(ContractInputPatternKind.Boolean));

    var valueJson = JsonSerializer.Serialize(value, ContractJson.Options);
    var patternJson = JsonSerializer.Serialize(pattern, ContractJson.Options);
    var decodedValue = JsonSerializer.Deserialize<ContractValue>(valueJson, ContractJson.Options)!;
    var decodedPattern = JsonSerializer.Deserialize<ContractInputPattern>(patternJson, ContractJson.Options)!;
    ContractModelCodec.Validate(decodedValue);
    ContractPatternCodec.Validate(decodedPattern);
    Assert.Equal("map[7 := true]", ContractModelCodec.ToDafny(decodedValue));
    Assert.Equal(ContractInputPatternKind.Map, decodedPattern.Kind);
    Assert.DoesNotContain("\"value\":null", patternJson);
    Assert.Throws<JsonException>(() => JsonSerializer.Deserialize<ContractInputPattern>(
      patternJson.Replace("\"minEntries\":1", "\"minEntries\":1,\"expression\":\"map[]\"",
        StringComparison.Ordinal), ContractJson.Options));

    var duplicate = new ContractValue(ContractValueKind.Map, Entries: [
      new(Integer("7"), new(ContractValueKind.Boolean, "true")),
      new(Integer("7"), new(ContractValueKind.Boolean, "false"))
    ]);
    Assert.Throws<ArgumentException>(() => ContractModelCodec.Validate(duplicate));
  }

  // Finite set and multiset literals round-trip with distinct-set and multiplicity semantics.
  [Fact]
  public void SetAndMultisetJsonPreserveCollectionSemantics() {
    var set = new ContractValue(ContractValueKind.Set, Items: [Integer("1"), Integer("2")]);
    var multiset = new ContractValue(ContractValueKind.Multiset, Items: [Integer("1"), Integer("1")]);

    var decodedSet = JsonSerializer.Deserialize<ContractValue>(
      JsonSerializer.Serialize(set, ContractJson.Options), ContractJson.Options)!;
    var decodedMultiset = JsonSerializer.Deserialize<ContractValue>(
      JsonSerializer.Serialize(multiset, ContractJson.Options), ContractJson.Options)!;
    ContractModelCodec.Validate(decodedSet);
    ContractModelCodec.Validate(decodedMultiset);
    Assert.Equal("{1, 2}", ContractModelCodec.ToDafny(decodedSet));
    Assert.Equal("multiset{1, 1}", ContractModelCodec.ToDafny(decodedMultiset));
    Assert.Throws<ArgumentException>(() => ContractModelCodec.Validate(
      new(ContractValueKind.Set, Items: [Integer("1"), Integer("1")])));
  }

  // Bitvector DTOs round-trip only when their unsigned value and range fit the declared width.
  [Fact]
  public void BitvectorJsonStrictlyValidatesWidthAndRange() {
    var value = Bitvector("255", 8);
    var pattern = BitvectorPattern(8, "0", "255");

    var decodedValue = JsonSerializer.Deserialize<ContractValue>(
      JsonSerializer.Serialize(value, ContractJson.Options), ContractJson.Options)!;
    var decodedPattern = JsonSerializer.Deserialize<ContractInputPattern>(
      JsonSerializer.Serialize(pattern, ContractJson.Options), ContractJson.Options)!;
    ContractModelCodec.Validate(decodedValue);
    ContractPatternCodec.Validate(decodedPattern);
    Assert.Equal("(255 as bv8)", ContractModelCodec.ToDafny(decodedValue));
    Assert.Throws<ArgumentException>(() => ContractModelCodec.Validate(Bitvector("256", 8)));
    Assert.Throws<ArgumentException>(() => ContractPatternCodec.Validate(BitvectorPattern(8, "0", "256")));
  }

  // Collection pattern payloads are closed data and reject source-expression fields.
  [Fact]
  public void SetPatternJsonRejectsSourceExpression() {
    var pattern = CollectionPattern(ContractInputPatternKind.Set, 0, 2,
      new(ContractInputPatternKind.IntegerRange, MinValue: "0", MaxValue: "2", BoundaryValues: []));
    var json = JsonSerializer.Serialize(pattern, ContractJson.Options);

    var decoded = JsonSerializer.Deserialize<ContractInputPattern>(json, ContractJson.Options)!;
    ContractPatternCodec.Validate(decoded);
    Assert.Throws<JsonException>(() => JsonSerializer.Deserialize<ContractInputPattern>(
      json.Replace("\"minSize\":0", "\"minSize\":0,\"expression\":\"{}\"", StringComparison.Ordinal),
      ContractJson.Options));
  }

  // The SHA-256 stream is repeatable, gives every complete pattern an initial turn and resolves aliases independent of map order.
  [Fact]
  public void SamplerIsDeterministicFairAndSupportsBindingReuse() {
    var bound = new ContractInputPattern(ContractInputPatternKind.Bind, Name: "shared",
      Pattern: new(ContractInputPatternKind.IntegerRange,
        MinValue: "0", MaxValue: "100", BoundaryValues: ["0", "100"]));
    var first = new ContractCompleteInputPattern("first", 100,
      new Dictionary<string, ContractInputPattern> {
        ["y"] = new(ContractInputPatternKind.Reuse, Name: "shared"),
        ["x"] = bound
      });
    var second = new ContractCompleteInputPattern("second", 1,
      new Dictionary<string, ContractInputPattern> {
        ["y"] = Literal(Integer("9")),
        ["x"] = Literal(Integer("9"))
      });
    var campaign = Campaign(4, first, second);

    var sample = ContractPatternSampler.Sample(campaign, 0);
    var replay = ContractPatternSampler.Sample(campaign, 0);
    var fairSecond = ContractPatternSampler.Sample(campaign, 1);
    Assert.Equal(JsonSerializer.Serialize(sample, ContractJson.Options),
      JsonSerializer.Serialize(replay, ContractJson.Options));
    Assert.Equal(sample.Inputs["x"], sample.Inputs["y"]);
    Assert.Equal("first", sample.Provenance.PatternId);
    Assert.Equal("second", fairSecond.Provenance.PatternId);
    Assert.Equal(64, sample.Provenance.PatternSetSha256.Length);
    Assert.NotNull(sample.Provenance.InputSha256);
    Assert.Equal(64, sample.Provenance.InputSha256!.Length);
  }

  // Recursive data patterns materialize strings, finite sequences, datatypes and a single aliased reference graph.
  [Fact]
  public void SamplerMaterializesRecursiveValuesAndReferences() {
    var reference = new ContractInputPattern(ContractInputPatternKind.Bind, Name: "cell",
      Pattern: new(ContractInputPatternKind.Reference, Type: "Cell", ObjectId: "chosen-cell",
        Fields: new Dictionary<string, ContractInputPattern> {
          ["value"] = Literal(Integer("7"))
        }));
    var pattern = new ContractCompleteInputPattern("recursive", 1,
      new Dictionary<string, ContractInputPattern> {
        ["alias"] = new(ContractInputPatternKind.Reuse, Name: "cell"),
        ["cell"] = reference,
        ["text"] = new(ContractInputPatternKind.String, Alphabet: "ab", MinLength: 1, MaxLength: 3),
        ["items"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 2,
          Element: new(ContractInputPatternKind.Boolean)),
        ["pair"] = new(ContractInputPatternKind.Datatype, Constructor: "Pair.Pair",
          Fields: new Dictionary<string, ContractInputPattern> {
            ["left"] = Literal(Integer("1")),
            ["right"] = Literal(Integer("2"))
          })
      });

    var sample = ContractPatternSampler.Sample(Campaign(1, pattern), 0);
    Assert.Equal(sample.Inputs["cell"], sample.Inputs["alias"]);
    Assert.Equal(ContractValueKind.Sequence, sample.Inputs["text"].Kind);
    Assert.All(sample.Inputs["text"].Items!, item => Assert.Equal(ContractValueKind.Character, item.Kind));
    Assert.InRange(sample.Inputs["items"].Items!.Count, 1, 2);
    Assert.Equal(ContractValueKind.Datatype, sample.Inputs["pair"].Kind);
    Assert.Equal("object0", Assert.Single(sample.Heap).Id);
  }

  // SHA-256 sampling deterministically retries colliding keys and rejects an impossible distinct-key count.
  [Fact]
  public void MapSamplerIsDeterministicAndHandlesDuplicateKeys() {
    var distinct = MapPattern(2, 2,
      new(ContractInputPatternKind.IntegerRange, MinValue: "0", MaxValue: "1", BoundaryValues: []),
      new(ContractInputPatternKind.Boolean));
    var campaign = Campaign(1, new ContractCompleteInputPattern("map", 1,
      new Dictionary<string, ContractInputPattern> { ["m"] = distinct }));

    var sample = ContractPatternSampler.Sample(campaign, 0);
    var replay = ContractPatternSampler.Sample(campaign, 0);
    Assert.Equal(JsonSerializer.Serialize(sample, ContractJson.Options),
      JsonSerializer.Serialize(replay, ContractJson.Options));
    var entries = sample.Inputs["m"].Entries!;
    Assert.Equal(2, entries.Count);
    Assert.NotEqual(entries[0].Key, entries[1].Key);

    var impossible = MapPattern(2, 2, Literal(Integer("0")), Literal(Integer("1")));
    Assert.Throws<ArgumentException>(() => ContractPatternSampler.Sample(
      Campaign(1, new ContractCompleteInputPattern("duplicate", 1,
        new Dictionary<string, ContractInputPattern> { ["m"] = impossible })), 0));
  }

  // SHA-256 sampling retries duplicate set elements and fails when the requested cardinality is impossible.
  [Fact]
  public void SetSamplerIsDeterministicAndRequiresDistinctElements() {
    var pattern = CollectionPattern(ContractInputPatternKind.Set, 2, 2,
      new(ContractInputPatternKind.IntegerRange, MinValue: "0", MaxValue: "1", BoundaryValues: []));
    var campaign = Campaign(1, new ContractCompleteInputPattern("set", 1,
      new Dictionary<string, ContractInputPattern> { ["s"] = pattern }));

    var sample = ContractPatternSampler.Sample(campaign, 0);
    var replay = ContractPatternSampler.Sample(campaign, 0);
    Assert.Equal(JsonSerializer.Serialize(sample, ContractJson.Options),
      JsonSerializer.Serialize(replay, ContractJson.Options));
    Assert.Equal(2, sample.Inputs["s"].Items!.Count);
    Assert.Throws<ArgumentException>(() => ContractPatternSampler.Sample(Campaign(1,
      new ContractCompleteInputPattern("impossible", 1, new Dictionary<string, ContractInputPattern> {
        ["s"] = CollectionPattern(ContractInputPatternKind.Set, 2, 2, Literal(Integer("0")))
      })), 0));
  }

  // Multiset sampling keeps repeated elements as multiplicity-bearing items.
  [Fact]
  public void MultisetSamplerPreservesMultiplicity() {
    var pattern = CollectionPattern(ContractInputPatternKind.Multiset, 2, 2, Literal(Integer("7")));

    var sample = ContractPatternSampler.Sample(Campaign(1, new ContractCompleteInputPattern("multiset", 1,
      new Dictionary<string, ContractInputPattern> { ["m"] = pattern })), 0);

    Assert.Equal(new[] { "7", "7" }, sample.Inputs["m"].Items!.Select(item => item.Value));
  }

  // Bitvector sampling uses the same SHA-256 stream and records the exact source width.
  [Fact]
  public void BitvectorSamplerIsDeterministic() {
    var campaign = Campaign(1, new ContractCompleteInputPattern("bits", 1,
      new Dictionary<string, ContractInputPattern> { ["bits"] = BitvectorPattern(32, "0", "4294967295") }));

    var sample = ContractPatternSampler.Sample(campaign, 0);
    var replay = ContractPatternSampler.Sample(campaign, 0);

    Assert.Equal(JsonSerializer.Serialize(sample, ContractJson.Options),
      JsonSerializer.Serialize(replay, ContractJson.Options));
    Assert.Equal(32, sample.Inputs["bits"].Width);
  }

  // Pattern candidates that falsify P are filtered while a later candidate satisfying the original P is retained.
  [Fact]
  public async Task CampaignFiltersCandidatesWithOriginalPrecondition() {
    var request = ContractInputTests.Request(
      "method Entry(x:int) requires x == 7 { assert x == 7; }", count: 2) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(3,
        new ContractCompleteInputPattern("outside-p", 1, new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("1")) }),
        new ContractCompleteInputPattern("inside-p", 1, new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("7")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);
    var generated = Assert.Single(result.Inputs);
    Assert.Equal("7", generated.Request.Inputs["x"].Value);
    Assert.Equal("inside-p", generated.PatternProvenance!.PatternId);
    Assert.Equal(3, result.Counts.PatternSamples);
    Assert.Equal(2, result.Counts.PatternPreconditionFalse);
    Assert.All(generated.Queries, query => Assert.Contains(query.Outcome,
      new[] { ContractQueryOutcome.Sat, ContractQueryOutcome.Unsat }));
  }

  // A resolved generic baseline is sampled first, before each submitted pattern's first fair sample.
  [Fact]
  public async Task CampaignAddsExecutorOwnedBaselinePattern() {
    var request = ContractInputTests.Request(
      "datatype Choice = Empty | Pair(n:int, ok:bool) method Entry(x:int, s:seq<bool>, c:Choice) { }",
      count: 2) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("model", 1,
        new Dictionary<string, ContractInputPattern> {
          ["x"] = Literal(Integer("7")),
          ["s"] = Literal(new(ContractValueKind.Sequence, Items: [])),
          ["c"] = Literal(new(ContractValueKind.Datatype, Constructor: "Choice.Empty",
            Fields: new Dictionary<string, ContractValue>()))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.True(result.Inputs.Count == 2, JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.StartsWith("__executor_baseline", result.Inputs[0].PatternProvenance!.PatternId);
    Assert.Equal(0, result.Inputs[0].PatternProvenance!.SampleOrdinal);
    Assert.Equal("model", result.Inputs[1].PatternProvenance!.PatternId);
  }

  // The executor baseline owns only global ordinal zero and never enters submitted weighted sampling.
  [Fact]
  public async Task CampaignSamplesExecutorBaselineExactlyOnce() {
    var request = ContractInputTests.Request("method Entry(x:int) { }",
      count: 100) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(24,
        new ContractCompleteInputPattern("first", 1,
          new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("1")) }),
        new ContractCompleteInputPattern("weighted", 100,
          new Dictionary<string, ContractInputPattern> {
            ["x"] = new(ContractInputPatternKind.IntegerRange,
              MinValue: "2", MaxValue: "1000000", BoundaryValues: [])
          }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Equal(24, result.Counts.PatternSamples);
    Assert.Equal("pattern:__executor_baseline:0",
      Assert.Single(result.Goals.Where(goal => goal.Id.Contains("__executor_baseline", StringComparison.Ordinal))).Id);
    Assert.Contains(result.Goals, goal => goal.Id == "pattern:first:1");
    Assert.Contains(result.Goals, goal => goal.Id == "pattern:weighted:2");
    Assert.DoesNotContain(result.Goals, goal => goal.Id.StartsWith("pattern:__executor_baseline:",
      StringComparison.Ordinal) && goal.Id != "pattern:__executor_baseline:0");
  }

  // A submitted reserved-prefix id remains distinct from the exact generated one-shot baseline id.
  [Fact]
  public async Task CampaignTracksGeneratedBaselineByExactId() {
    var request = ContractInputTests.Request("method Entry(x:int) { }", count: 10) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(4,
        new ContractCompleteInputPattern("__executor_baseline", 1,
          new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("1")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Contains(result.Goals, goal => goal.Id == "pattern:__executor_baseline-1:0");
    Assert.Contains(result.Goals, goal => goal.Id == "pattern:__executor_baseline:1");
    Assert.All(result.Goals.Where(goal => goal.Id.EndsWith(":2", StringComparison.Ordinal) ||
      goal.Id.EndsWith(":3", StringComparison.Ordinal)),
      goal => Assert.StartsWith("pattern:__executor_baseline:", goal.Id));
  }

  // A feedback offset resumes submitted weighted sampling without replaying the ordinal-zero baseline.
  [Fact]
  public async Task CampaignFeedbackOffsetDoesNotReplayExecutorBaseline() {
    var request = ContractInputTests.Request("method Entry(x:int) { }",
      count: 100) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(6,
        new ContractCompleteInputPattern("positive", 1,
          new Dictionary<string, ContractInputPattern> {
            ["x"] = new(ContractInputPatternKind.IntegerRange,
              MinValue: "1", MaxValue: "1000000", BoundaryValues: [])
          })),
      CampaignFeedback = new(1, [], [], [], 6, 60000, 17)
    };

    var first = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);
    var replay = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Equal(6, first.Counts.PatternSamples);
    Assert.DoesNotContain(first.Goals, goal => goal.Id.Contains("__executor_baseline", StringComparison.Ordinal));
    Assert.Equal(Enumerable.Range(17, 6), first.Inputs.Select(input => input.PatternProvenance!.SampleOrdinal));
    Assert.Equal(first.Inputs.Select(input => input.PatternProvenance!.PatternId),
      replay.Inputs.Select(input => input.PatternProvenance!.PatternId));
    Assert.Equal(first.Inputs.Select(input => input.PatternProvenance!.InputSha256),
      replay.Inputs.Select(input => input.PatternProvenance!.InputSha256));
  }

  // Feedback skips hashes already executed and advances the reproducible global ordinal for the next round.
  [Fact]
  public async Task CampaignFeedbackSkipsSeenInputsAndAdvancesRound() {
    var campaign = Campaign(3,
      new ContractCompleteInputPattern("one", 1,
        new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("1")) }),
      new ContractCompleteInputPattern("two", 1,
        new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("2")) }));
    var firstSample = ContractPatternSampler.Sample(campaign, 0);
    var request = ContractInputTests.Request("method Entry(x:int) requires x == 2 { }", count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = campaign,
      CampaignFeedback = new(0, [ContractPatternSampler.SampleSha256(firstSample.Inputs, firstSample.Heap)], [], [], 3, 60000)
    };

    var filtered = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);
    Assert.Equal("2", Assert.Single(filtered.Inputs).Request.Inputs["x"].Value);
    Assert.Equal(1, filtered.Counts.DuplicateInputs);
    Assert.Equal(2, Assert.Single(filtered.Inputs).PatternProvenance!.SampleOrdinal);

    var nextRound = await ContractInputGenerator.GenerateAsync(request with {
      PatternCampaign = campaign with { MaxSamples = 1 },
      CampaignFeedback = new(1, [], [], [], 1, 60000, 2)
    }, ContractInputTests.Options(), CancellationToken.None);
    var next = Assert.Single(nextRound.Inputs);
    Assert.Equal("2", next.Request.Inputs["x"].Value);
    Assert.Equal(2, next.PatternProvenance!.SampleOrdinal);
  }

  // A reference pattern is resolved against the general Dafny class type and rechecked with its concrete heap fields.
  [Fact]
  public async Task ReferencePatternPassesResolvedHeapPrecondition() {
    var request = ContractInputTests.Request(
      "class Cell { var value:int } method Entry(c:Cell) requires c != null && c.value == 7 { }",
      count: 1, bounds: new(MaxInputs: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("cell", 1,
        new Dictionary<string, ContractInputPattern> {
          ["c"] = new(ContractInputPatternKind.Reference, Type: "Cell", ObjectId: "cell",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["value"] = Literal(Integer("7"))
            })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);
    var generated = Assert.Single(result.Inputs).Request;
    Assert.Equal("object0", generated.Inputs["c"].Value);
    Assert.Equal("7", Assert.Single(generated.Heap!).Fields["value"].Value);
  }

  // A reference pattern's ghost field participates in the exact P recheck through the logical heap shape.
  [Fact]
  public async Task ReferencePatternRechecksLogicalGhostHeapState() {
    var request = ContractInputTests.Request(
      "class Box { ghost var proof:int } method Entry(box:Box) requires box != null && box.proof == 7 { }",
      count: 1, bounds: new(MaxInputs: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("box", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["proof"] = Literal(Integer("7"))
            })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs).Request;
    Assert.Equal("object0", generated.Inputs["box"].Value);
    Assert.Equal("7", Assert.Single(generated.Heap!).Fields["proof"].Value);
  }

  // A general finite-map pattern is materialized and checked against the original resolved entry precondition.
  [Fact]
  public async Task MapPatternPassesOriginalPreconditionRecheck() {
    var request = ContractInputTests.Request(
      "method Entry(m:map<int,bool>) requires |m| == 1 && 7 in m && m[7] { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("single-entry", 1,
        new Dictionary<string, ContractInputPattern> {
          ["m"] = MapPattern(1, 1, Literal(Integer("7")),
            Literal(new(ContractValueKind.Boolean, "true")))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    var entry = Assert.Single(generated.Request.Inputs["m"].Entries!);
    Assert.Equal("7", entry.Key.Value);
    Assert.Equal("true", entry.Value.Value);
    Assert.Equal(ContractQueryOutcome.Sat, generated.Queries[0].Outcome);
    Assert.Equal(ContractQueryOutcome.Unsat, generated.Queries[1].Outcome);
  }

  // General finite set and multiset patterns are checked against the original resolved entry precondition.
  [Fact]
  public async Task CollectionPatternsPassOriginalPreconditionRecheck() {
    var request = ContractInputTests.Request(
      "method Entry(s:set<int>, m:multiset<int>) requires s == {7} && m == multiset{7, 7} { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 2)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("collections", 1,
        new Dictionary<string, ContractInputPattern> {
          ["s"] = CollectionPattern(ContractInputPatternKind.Set, 1, 1, Literal(Integer("7"))),
          ["m"] = CollectionPattern(ContractInputPatternKind.Multiset, 2, 2, Literal(Integer("7")))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(ContractValueKind.Set, generated.Request.Inputs["s"].Kind);
    Assert.Equal(ContractValueKind.Multiset, generated.Request.Inputs["m"].Kind);
    Assert.Equal(ContractQueryOutcome.Unsat, generated.Queries[1].Outcome);
  }

  // Map-valued heap fields use the same typed concrete renderer during the original P recheck.
  [Fact]
  public async Task MapPatternRechecksHeapFieldPrecondition() {
    var request = ContractInputTests.Request(
      "class Box { var values:map<int,bool> } method Entry(box:Box) requires box != null && 7 in box.values && box.values[7] { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("map-field", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["values"] = MapPattern(1, 1, Literal(Integer("7")),
                Literal(new(ContractValueKind.Boolean, "true")))
            })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs).Request;
    var map = Assert.Single(generated.Heap!).Fields["values"];
    Assert.Equal(ContractValueKind.Map, map.Kind);
    Assert.Single(map.Entries!);
  }

  // Set and multiset heap fields use typed rendering and preserve collection semantics in the original P recheck.
  [Fact]
  public async Task CollectionPatternsRecheckHeapFieldPrecondition() {
    var request = ContractInputTests.Request(
      "class Box { var values:set<int> var counts:multiset<int> } " +
      "method Entry(box:Box) requires box != null && box.values == {7} && box.counts == multiset{7, 7} { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 2, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("collection-fields", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["values"] = CollectionPattern(ContractInputPatternKind.Set, 1, 1, Literal(Integer("7"))),
              ["counts"] = CollectionPattern(ContractInputPatternKind.Multiset, 2, 2, Literal(Integer("7")))
            })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var heapObject = Assert.Single(Assert.Single(result.Inputs).Request.Heap!);
    Assert.Equal(ContractValueKind.Set, heapObject.Fields["values"].Kind);
    Assert.Equal(2, heapObject.Fields["counts"].Items!.Count);
  }

  // Pattern generation avoids global heap-layout enumeration even when an unused datatype branch reaches many classes.
  [Fact]
  public async Task PatternGenerationSkipsIrrelevantAutomaticLayouts() {
    var classes = string.Join(" ", Enumerable.Range(0, 16).Select(index =>
      $"class C{index} {{ var next:C{index}? }}"));
    var heavyFields = string.Join(", ", Enumerable.Range(0, 16).Select(index => $"c{index}:C{index}?"));
    var source = classes + $" datatype Choice = Empty | Heavy({heavyFields}) " +
      "method Entry(choice:Choice) requires choice.Empty? { }";
    var request = ContractInputTests.Request(source, count: 1,
      bounds: new(MaxInputs: 1, MaxHeapObjects: 8, MaxGoals: 1_000_000)) with {
      TimeoutMilliseconds = 10000,
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(1, new ContractCompleteInputPattern("empty", 1,
        new Dictionary<string, ContractInputPattern> {
          ["choice"] = new(ContractInputPatternKind.Datatype, Constructor: "Choice.Empty",
            Fields: new Dictionary<string, ContractInputPattern>())
        }))
    };
    var stopwatch = Stopwatch.StartNew();

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Equal(ContractTestStatus.Passed, result.Status);
    Assert.Single(result.Inputs);
    Assert.True(stopwatch.Elapsed < TimeSpan.FromSeconds(10));
  }

  // Each complete pattern gets an exact heap shape that preserves aliases, nested datatypes and collection lengths.
  [Fact]
  public async Task CompletePatternsRecheckDifferentAliasedHeaps() {
    ContractCompleteInputPattern Pattern(string id, string bits) {
      var payload = new ContractInputPattern(ContractInputPatternKind.Datatype, Constructor: "Payload.Pack",
        Fields: new Dictionary<string, ContractInputPattern> { ["bits"] = Literal(Bitvector(bits, 7)) });
      return new(id, 1, new Dictionary<string, ContractInputPattern> {
        ["first"] = new(ContractInputPatternKind.Bind, Name: "shared",
          Pattern: new ContractInputPattern(ContractInputPatternKind.Reference, Type: "Box", ObjectId: id,
            Fields: new Dictionary<string, ContractInputPattern> {
              ["payloads"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1,
                Element: payload)
            })),
        ["alias"] = new(ContractInputPatternKind.Reuse, Name: "shared"),
        ["items"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1, Element: payload)
      });
    }
    var request = ContractInputTests.Request("""
      datatype Payload = Pack(bits:bv7)
      class Box { var payloads:seq<Payload> }
      method Entry(first:Box, alias:Box, items:seq<Payload>)
        requires first == alias && first != null && |first.payloads| == 1 && |items| == 1
        requires first.payloads[0].bits == items[0].bits
        requires first.payloads[0].bits == 7 || first.payloads[0].bits == 9 { }
      """, count: 2, bounds: new(MaxInputs: 2, MaxSequenceLength: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(3, Pattern("seven", "7"), Pattern("nine", "9"))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.True(result.Inputs.Count == 2, JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.All(result.Inputs, generated =>
      Assert.Equal(generated.Request.Inputs["first"], generated.Request.Inputs["alias"]));
    Assert.Equal(new[] { "7", "9" }, result.Inputs.Select(generated => generated.Request.Heap![0]
      .Fields["payloads"].Items![0].Fields!["bits"].Value));
  }

  // A concrete array heap supplies its resolved element structure directly to the pattern precondition recheck.
  [Fact]
  public async Task PatternRechecksExactArrayElementShape() {
    var request = ContractInputTests.Request(
      "method Entry(values:array<seq<bv7>>) requires values != null && values.Length == 1 && values[0] == [7] { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("array", 1,
        new Dictionary<string, ContractInputPattern> {
          ["values"] = Literal(new(ContractValueKind.Reference, "values"))
        }, [new("values", "array<seq<bv7>>", new Dictionary<string, ContractValue>(), [1],
          [new(ContractValueKind.Sequence, Items: [Bitvector("7", 7)])])]))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var heap = Assert.Single(Assert.Single(result.Inputs).Request.Heap!);
    Assert.Equal(7, Assert.Single(Assert.Single(heap.Elements!).Items!).Width);
  }

  // Structurally validated samples without explicit or implicit refinement obligations skip SMT entirely.
  [Fact]
  public async Task NoRequiresPatternsUseZeroQueryFastPath() {
    var item = new ContractInputPattern(ContractInputPatternKind.Datatype, Constructor: "Item.Item",
      Fields: new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("7")) });
    var request = ContractInputTests.Request("""
      datatype Item = Item(value:int)
      class Box { var items:seq<Item> }
      method Entry(box:Box?, values:map<int,seq<Item>>) { }
      """, count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(1, new ContractCompleteInputPattern("structured", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["items"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1, Element: item)
            }),
          ["values"] = MapPattern(1, 1, Literal(Integer("1")),
            new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1, Element: item))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Single(result.Inputs);
    Assert.All(result.Inputs, generated => Assert.Empty(generated.Queries));
    Assert.All(result.Goals, outcome => Assert.Contains("SMT recheck was unnecessary", outcome.Reason));
  }

  // A refined collection element keeps the no-requires pattern path on SMT and rejects an invalid base value.
  [Fact]
  public async Task NoRequiresCompositeRefinementStillRejectsInvalidValue() {
    var request = ContractInputTests.Request("""
      type Positive = x:int | x > 0 witness 1
      method Entry(values:seq<Positive>) { }
      """, count: 2, bounds: new(MaxInputs: 2, MaxSequenceLength: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("invalid-composite", 1,
        new Dictionary<string, ContractInputPattern> {
          ["values"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1,
            Element: Literal(Integer("-1")))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.DoesNotContain(result.Inputs,
      generated => generated.PatternProvenance?.PatternId == "invalid-composite");
    Assert.True(result.Counts.PatternRejected >= 1, JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Goals, goal => goal.Id.Contains("invalid-composite", StringComparison.Ordinal) &&
      goal.Reason.Contains("ran 0 SMT queries", StringComparison.Ordinal));
  }

  // A refinement nested in a datatype inside a heap field also prevents the zero-query fast path.
  [Fact]
  public async Task NoRequiresNestedHeapRefinementStillRejectsInvalidValue() {
    var payload = new ContractInputPattern(ContractInputPatternKind.Datatype, Constructor: "Payload.Pack",
      Fields: new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("-1")) });
    var request = ContractInputTests.Request("""
      type Positive = x:int | x > 0 witness 1
      datatype Payload = Pack(value:Positive)
      class Box { var payload:Payload }
      method Entry(box:Box?) { }
      """, count: 2, bounds: new(MaxInputs: 2, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("invalid-heap", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> { ["payload"] = payload })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.DoesNotContain(result.Inputs,
      generated => generated.PatternProvenance?.PatternId == "invalid-heap");
    Assert.True(result.Counts.PatternRejected >= 1, JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Contains(result.Goals, goal => goal.Id.Contains("invalid-heap", StringComparison.Ordinal) &&
      goal.Reason.Contains("ran 0 SMT queries", StringComparison.Ordinal));
  }

  // A reference-free refined map with a nested datatype and nat reduces all concrete memberships without SMT.
  [Fact]
  public async Task NoRequiresComplexRefinementUsesDirectMembershipQueries() {
    var tree = new ContractInputPattern(ContractInputPatternKind.Datatype, Constructor: "Tree.Leaf",
      Fields: new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("7")) });
    var request = ContractInputTests.Request("""
      datatype Tree = Leaf(value:nat) | Branch(children:seq<Tree>)
      type FileSystem = value:map<int,Tree> | |value| <= 2 witness map[]
      method Entry(fileSystem:FileSystem) { }
      """, count: 2, bounds: new(MaxInputs: 2, MaxSequenceLength: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("valid-complex", 1,
        new Dictionary<string, ContractInputPattern> {
          ["fileSystem"] = MapPattern(1, 1, Literal(Integer("1")), tree)
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId == "valid-complex"));
    Assert.Empty(generated.Queries);
    Assert.Contains("direct refinement memberships were verified",
      result.Goals.Single(goal => goal.Id.Contains("valid-complex", StringComparison.Ordinal)).Reason);
  }

  // Repeated concrete membership obligations are verified once while unrelated pattern inputs still vary.
  [Fact]
  public async Task NoRequiresRefinementMembershipQueriesAreCached() {
    ContractCompleteInputPattern Pattern(string id, string noise) => new(id, 1,
      new Dictionary<string, ContractInputPattern> {
        ["value"] = Literal(Integer("7")),
        ["noise"] = Literal(Integer(noise))
      });
    var request = ContractInputTests.Request("""
      type Positive = value:int | value > 0 witness 1
      method Entry(value:Positive, noise:int) { }
      """, count: 3, bounds: new(MaxInputs: 3)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(3, Pattern("first", "1"), Pattern("second", "2"))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var submitted = result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId is "first" or "second").ToList();
    Assert.True(submitted.Count == 2, JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(0, submitted.Sum(input => input.Queries.Count));
    Assert.Contains(result.Goals, goal => goal.Id.Contains("second", StringComparison.Ordinal) &&
      goal.Reason.Contains("reused 1 cached SHA-256 obligations", StringComparison.Ordinal));
  }

  // An explicit method precondition keeps the established premise and property two-query recheck.
  [Fact]
  public async Task ExplicitPreconditionDoesNotUseDirectRefinementFastPath() {
    var request = ContractInputTests.Request("""
      type Positive = value:int | value > 0 witness 1
      method Entry(value:Positive) requires value == 7 { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("explicit", 1,
        new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("7")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId == "explicit"));
    Assert.Equal(2, generated.Queries.Count);
    Assert.Contains("original entry precondition recheck",
      result.Goals.Single(goal => goal.Id.Contains("explicit", StringComparison.Ordinal)).Reason);
  }

  // Generic subset applications substitute their concrete type arguments before reducing the resolved constraint.
  [Fact]
  public async Task GenericSubsetMembershipUsesResolvedTypeArgumentSubstitution() {
    var request = ContractInputTests.Request("""
      type Singleton<T(==)> = items:seq<T> |
        |items| == 1 && items[0] == items[0]
        witness *
      method Entry(items:Singleton<int>) { }
      """, count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("generic", 1,
        new Dictionary<string, ContractInputPattern> {
          ["items"] = new(ContractInputPatternKind.Sequence, MinLength: 1, MaxLength: 1,
            Element: Literal(Integer("7")))
        }))
    };
    var originalContent = request.Sources[0].Content;
    var originalSha256 = request.Sources[0].Sha256;

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId == "generic"));
    Assert.Empty(generated.Queries);
    Assert.Contains("resolved reduction",
      result.Goals.Single(goal => goal.Id.Contains("generic", StringComparison.Ordinal)).Reason);
    Assert.Equal(originalContent, request.Sources[0].Content);
    Assert.Equal(originalSha256, request.Sources[0].Sha256);
  }

  // Newtype membership reduces against its concrete base value and filters an invalid candidate locally.
  [Fact]
  public async Task NewtypeMembershipRejectsInvalidConcreteBaseValue() {
    var request = ContractInputTests.Request("""
      newtype Small = value:int | 0 <= value < 10 witness 0
      method Entry(value:Small) { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("invalid-newtype", 1,
        new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("12")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.DoesNotContain(result.Inputs,
      generated => generated.PatternProvenance?.PatternId == "invalid-newtype");
    Assert.True(result.Counts.PatternPreconditionFalse >= 1,
      JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // An uninhabited subset cannot make its parse-only carrier an assumption; its concrete membership reduces to false.
  [Fact]
  public async Task EmptySubsetMembershipRejectsConcreteCandidateLocally() {
    var request = ContractInputTests.Request("""
      type Empty = value:int | false witness *
      method Entry(value:Empty) { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("empty", 1,
        new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("0")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Empty(result.Inputs);
    Assert.Contains(result.Goals, goal => goal.Id.Contains("empty", StringComparison.Ordinal) &&
      goal.Reason.Contains("ran 0 SMT queries", StringComparison.Ordinal));
  }

  // An unbounded residual constraint is rendered only after resolved AST substitution and discharged by SMT.
  [Fact]
  public async Task ResidualRefinementMembershipFallsBackToSolver() {
    var request = ContractInputTests.Request("""
      type AdditiveZero = value:int | forall i:int :: value + i == i witness 0
      method Entry(value:AdditiveZero) { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("residual", 1,
        new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("0")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId == "residual"));
    Assert.Equal(ContractQueryOutcome.Unsat, Assert.Single(generated.Queries).Outcome);
  }

  // Quantifier reduction exhaustion preserves the residual membership and sends it to SMT.
  [Fact]
  public async Task ExhaustedRefinementReductionFallsBackToSolver() {
    var request = ContractInputTests.Request("""
      type NonNegativeByRange = value:int |
        forall i | 0 <= i < 200 :: value + i >= i
        witness 0
      method Entry(value:NonNegativeByRange) { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("exhausted", 1,
        new Dictionary<string, ContractInputPattern> { ["value"] = Literal(Integer("0")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs.Where(input =>
      input.PatternProvenance?.PatternId == "exhausted"));
    Assert.Equal(ContractQueryOutcome.Unsat, Assert.Single(generated.Queries).Outcome);
  }

  // Solver-goal generation uses bounded map shapes without changing the default strategy.
  [Fact]
  public async Task SolverGenerationMaterializesFiniteMap() {
    var result = await ContractInputGenerator.GenerateAsync(ContractInputTests.Request(
      "method Entry(m:map<int,bool>) requires |m| == 1 && 7 in m && m[7] { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1)), ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Null(generated.PatternProvenance);
    var entry = Assert.Single(generated.Request.Inputs["m"].Entries!);
    Assert.Equal("7", entry.Key.Value);
    Assert.Equal("true", entry.Value.Value);
  }

  // Solver-goal generation materializes bounded finite set shapes with distinct symbolic elements.
  [Fact]
  public async Task SolverGenerationMaterializesFiniteSet() {
    var result = await ContractInputGenerator.GenerateAsync(ContractInputTests.Request(
      "method Entry(s:set<int>) requires s == {7} { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 1)), ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(ContractValueKind.Set, generated.Request.Inputs["s"].Kind);
    Assert.Equal("7", Assert.Single(generated.Request.Inputs["s"].Items!).Value);
  }

  // Solver-goal generation materializes bounded multisets while retaining repeated elements.
  [Fact]
  public async Task SolverGenerationMaterializesFiniteMultiset() {
    var result = await ContractInputGenerator.GenerateAsync(ContractInputTests.Request(
      "method Entry(m:multiset<int>) requires m == multiset{7, 7} { }",
      count: 1, bounds: new(MaxInputs: 1, MaxSequenceLength: 2, MaxGoals: 16)), ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(ContractValueKind.Multiset, generated.Request.Inputs["m"].Kind);
    Assert.Equal(new[] { "7", "7" }, generated.Request.Inputs["m"].Items!.Select(item => item.Value));
  }

  // A bv32 pattern is resolved by exact width and checked against the original entry precondition.
  [Fact]
  public async Task BitvectorPatternPassesOriginalPreconditionRecheck() {
    var request = ContractInputTests.Request(
      "method Entry(bits:bv32) requires bits == 4294967295 { }", count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("bits", 1,
        new Dictionary<string, ContractInputPattern> {
          ["bits"] = new(ContractInputPatternKind.Literal, Value: Bitvector("4294967295", 32))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(ContractValueKind.Bitvector, generated.Request.Inputs["bits"].Kind);
    Assert.Equal(32, generated.Request.Inputs["bits"].Width);
  }

  // Automatic solver shapes preserve bv32 width while materializing a concrete unsigned value.
  [Fact]
  public async Task SolverGenerationMaterializesBitvector() {
    var result = await ContractInputGenerator.GenerateAsync(ContractInputTests.Request(
      "method Entry(bits:bv32) requires bits == 4294967295 { }", count: 1),
      ContractInputTests.Options(), CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(Bitvector("4294967295", 32), generated.Request.Inputs["bits"]);
  }

  // Subset and newtype inputs use base values while their resolved constraints remain in the original premise.
  [Fact]
  public async Task RefinedTypesUseBasePatternsAndPreserveConstraints() {
    var request = ContractInputTests.Request("""
      type Positive = x:int | x > 0 witness 1
      newtype Small = x:int | 0 <= x < 10 witness 0
      method Entry(x:Positive, y:Small) requires x == 7 && y == 8 { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("refined", 1,
        new Dictionary<string, ContractInputPattern> {
          ["x"] = Literal(Integer("7")),
          ["y"] = Literal(Integer("8"))
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var generated = Assert.Single(result.Inputs);
    Assert.Equal(Integer("7"), generated.Request.Inputs["x"]);
    Assert.Equal(Integer("8"), generated.Request.Inputs["y"]);
  }

  // A base value outside a subset constraint is rejected by the unchanged resolved input premise.
  [Fact]
  public async Task RefinedTypeConstraintRejectsInvalidBaseValue() {
    var request = ContractInputTests.Request("""
      type Positive = x:int | x > 0 witness 1
      method Entry(x:Positive) { }
      """, count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("invalid", 1,
        new Dictionary<string, ContractInputPattern> { ["x"] = Literal(Integer("-1")) }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.PatternRejected >= 1, JsonSerializer.Serialize(result, ContractJson.Options));
  }

  // Bitvector and subset heap fields are rendered by their resolved base representations during P recheck.
  [Fact]
  public async Task RefinedAndBitvectorHeapFieldsPassPreconditionRecheck() {
    var request = ContractInputTests.Request("""
      type Positive = x:int | x > 0 witness 1
      class Box { var bits:bv32 var count:Positive }
      method Entry(box:Box) requires box != null && box.bits == 7 && box.count == 8 { }
      """, count: 1, bounds: new(MaxInputs: 1, MaxHeapObjects: 1)) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(2, new ContractCompleteInputPattern("heap", 1,
        new Dictionary<string, ContractInputPattern> {
          ["box"] = new(ContractInputPatternKind.Reference, Type: "Box", ObjectId: "box",
            Fields: new Dictionary<string, ContractInputPattern> {
              ["bits"] = Literal(Bitvector("7", 32)),
              ["count"] = Literal(Integer("8"))
            })
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);

    var fields = Assert.Single(Assert.Single(result.Inputs).Request.Heap!).Fields;
    Assert.Equal(Bitvector("7", 32), fields["bits"]);
    Assert.Equal(Integer("8"), fields["count"]);
  }

  // Resolved type checking rejects a generator node whose output type cannot inhabit the formal.
  [Fact]
  public async Task CampaignRejectsPatternWithWrongResolvedType() {
    var request = ContractInputTests.Request("method Entry(flag:bool) { }", count: 1) with {
      GenerationStrategy = ContractGenerationStrategy.InputPatterns,
      PatternCampaign = Campaign(1, new ContractCompleteInputPattern("wrong", 1,
        new Dictionary<string, ContractInputPattern> {
          ["flag"] = new(ContractInputPatternKind.IntegerRange,
            MinValue: "0", MaxValue: "1", BoundaryValues: [])
        }))
    };

    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(),
      CancellationToken.None);
    Assert.Equal(ContractTestStatus.InvalidInput, result.Status);
    Assert.Empty(result.Inputs);
    Assert.Contains("does not produce resolved Dafny type", result.Reason);
  }

  // Existing generation keeps the solver strategy and produces no pattern provenance or pattern counts.
  [Fact]
  public async Task SolverGenerationRemainsTheDefault() {
    var result = await ContractInputGenerator.GenerateAsync(
      ContractInputTests.Request("method Entry(x:int) requires x == 11 { }", count: 1),
      ContractInputTests.Options(), CancellationToken.None);
    var generated = Assert.Single(result.Inputs);
    Assert.Null(generated.PatternProvenance);
    Assert.NotEmpty(generated.Queries);
    Assert.Equal(0, result.Counts.PatternSamples);
    Assert.Equal("11", generated.Request.Inputs["x"].Value);
  }
}
