#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>
/// One runtime campaign request. Scenarios that share a campaign are selected by
/// <c>PbtRandom.Source.Size()</c> (= 2 + ordinal / 4), so bucket <c>b</c> owns ordinals 4b..4b+3.
/// </summary>
public sealed record CampaignSpec(IReadOnlyList<ContractSource> Sources, string Entry, ContractSource? Generator,
  IReadOnlyList<ContractRuntimeDraft>? Drafts = null, int SampleCount = 1, int MaxClosedQueries = 0,
  int SampleTimeout = 5000, int ClosedQueryTimeout = 10000, int MaxViolationsPerObligation = 3,
  int? ReplayOrdinal = null, int Timeout = 300000, IReadOnlyList<ContractDependency>? Dependencies = null) {
  public const int BucketSize = 4;

  /// <summary>Builds a request from one source file and an optional generator.</summary>
  public static CampaignSpec Of(string source, string? generator, string entry = "M.Goal",
    string sourcePath = "M.dfy", string generatorPath = "G.dfy") =>
    new([Campaign.Source(sourcePath, source)], entry, generator == null ? null : Campaign.Source(generatorPath, generator));

  /// <summary>Builds a request from one named section pair of a fixture file.</summary>
  public static CampaignSpec Fixture(string file, string section, string entry = "M.Goal", string sourcePath = "M.dfy",
    string generatorPath = "G.dfy") {
    var sections = Campaign.Sections(file);
    return Of(sections["source " + section], sections.GetValueOrDefault("generator " + section), entry, sourcePath, generatorPath);
  }

  /// <summary>Runs <paramref name="count"/> buckets and keeps every violation so each bucket stays observable.</summary>
  public CampaignSpec Buckets(int count) =>
    this with { SampleCount = BucketSize * count, MaxViolationsPerObligation = BucketSize * count };

  /// <summary>Adds drafts for the named symbols.</summary>
  public CampaignSpec WithDrafts(params (string Symbol, string Content)[] drafts) => this with {
    Drafts = drafts.Select(draft => Campaign.Draft(draft.Symbol, draft.Content)).ToList()
  };
}

/// <summary>A finished campaign and its artifact directory, with slice helpers for bucketed scenarios.</summary>
public sealed class CampaignRun {
  public CampaignRun(CampaignSpec spec, ContractRuntimeCampaignResult result, string directory) {
    Spec = spec;
    Result = result;
    Directory = directory;
  }

  public CampaignSpec Spec { get; }
  public ContractRuntimeCampaignResult Result { get; }
  public string Directory { get; }
  public ContractRuntimePopulation Population => Result.Population;

  /// <summary>The ordinals that belong to one scenario bucket.</summary>
  public static IReadOnlyList<int> Ordinals(int bucket) =>
    Enumerable.Range(CampaignSpec.BucketSize * bucket, CampaignSpec.BucketSize).ToList();

  /// <summary>The obligations whose rendered clause contains <paramref name="clause"/>.</summary>
  public IReadOnlyList<ContractRuntimeObligation> Obligations(string clause) =>
    Result.Obligations.Where(obligation => obligation.Clause.Contains(clause, StringComparison.Ordinal)).ToList();

  /// <summary>The single obligation of <paramref name="kind"/> whose clause contains <paramref name="clause"/>.</summary>
  public ContractRuntimeObligation Obligation(string clause, ContractRuntimeObligationKind? kind = null) =>
    Assert.Single(Obligations(clause).Where(obligation => kind == null || obligation.Kind == kind));

  /// <summary>Goal violations recorded for one bucket, optionally restricted to a clause and kind.</summary>
  public IReadOnlyList<ContractRuntimeViolation> Violations(int bucket, string? clause = null,
    ContractRuntimeObligationKind? kind = null) =>
    Result.Violations.Where(violation => Ordinals(bucket).Contains(violation.SampleOrdinal) &&
      (kind == null || violation.Kind == kind) &&
      (clause == null || Obligations(clause).Any(obligation => obligation.Id == violation.ObligationId))).ToList();

  /// <summary>Callee contract violations recorded for one bucket.</summary>
  public IReadOnlyList<ContractRuntimeCalleeViolation> CalleeViolations(int bucket) =>
    Result.CalleeViolations.Where(violation => Ordinals(bucket).Contains(violation.SampleOrdinal)).ToList();

  /// <summary>Runtime errors recorded for one bucket.</summary>
  public IReadOnlyList<ContractRuntimeError> Errors(int bucket) =>
    Result.RuntimeErrors.Where(error => Ordinals(bucket).Contains(error.SampleOrdinal)).ToList();

  /// <summary>The raw observation records written by one sample process.</summary>
  public IReadOnlyList<JsonElement> Records(int ordinal) =>
    File.ReadAllLines(Path.Combine(Directory, "sample-" + ordinal + ".jsonl")).Where(line => line.Length > 0)
      .Select(line => JsonDocument.Parse(line).RootElement.Clone()).ToList();

  /// <summary>
  /// Asserts that every sample of the bucket violates the clause exactly <paramref name="perSample"/> times and, when
  /// <paramref name="exclusive"/>, that no sample outside the bucket violates it; returns its obligation and violations.
  /// </summary>
  public (ContractRuntimeObligation Obligation, IReadOnlyList<ContractRuntimeViolation> Violations) AssertViolated(
    int bucket, string clause, ContractRuntimeObligationKind? kind = null, int perSample = 1, bool exclusive = true) {
    var obligation = Obligation(clause, kind);
    var violations = Violations(bucket, clause, kind);
    Assert.True(violations.GroupBy(violation => violation.SampleOrdinal).OrderBy(sample => sample.Key)
      .Select(sample => (sample.Key, sample.Count())).SequenceEqual(Ordinals(bucket).Select(ordinal => (ordinal, perSample))),
      Detail());
    if (exclusive) {
      Assert.True(Result.Violations.Where(violation => violation.ObligationId == obligation.Id)
        .All(violation => Ordinals(bucket).Contains(violation.SampleOrdinal)), Detail());
      Assert.Equal(CampaignSpec.BucketSize * perSample, obligation.Violations);
    } else {
      Assert.True(obligation.Violations >= CampaignSpec.BucketSize * perSample, Detail());
    }
    return (obligation, violations);
  }

  /// <summary>Asserts that the clause was decided at runtime, never left unchecked, and violated nowhere.</summary>
  public ContractRuntimeObligation AssertHolds(int bucket, string clause, ContractRuntimeObligationKind? kind = null) {
    var obligation = Obligation(clause, kind);
    Assert.True(obligation.Evaluations is { Runtime: >= CampaignSpec.BucketSize, ClosedSmt: 0, Unchecked: 0 }, Detail());
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
    Assert.Equal(0, obligation.Violations);
    Assert.Empty(Violations(bucket));
    return obligation;
  }

  /// <summary>Asserts that every sample of the bucket is excluded by a callee contract violation and indicts no goal clause.</summary>
  public IReadOnlyList<ContractRuntimeCalleeViolation> AssertCalleeViolated(int bucket) {
    var violations = CalleeViolations(bucket);
    Assert.True(violations.Select(violation => violation.SampleOrdinal).Distinct().Order().SequenceEqual(Ordinals(bucket)),
      Detail());
    Assert.Empty(Violations(bucket));
    return violations;
  }

  /// <summary>Artifact paths matching a file pattern.</summary>
  public string[] Artifacts(string pattern) => System.IO.Directory.GetFiles(Directory, pattern);

  /// <summary>Parses one JSON artifact.</summary>
  public static JsonElement Json(string path) => JsonDocument.Parse(File.ReadAllText(path)).RootElement.Clone();

  /// <summary>The serialized result, used as an assertion message.</summary>
  public string Detail() => "Artifacts: " + Directory + "\n" + JsonSerializer.Serialize(Result, ContractJson.Options);
}

/// <summary>Deletes test artifact directories unless <c>DAFNY_CONTRACT_TEST_KEEP_ARTIFACTS=1</c> asks to keep them.</summary>
public static class ContractArtifacts {
  public const string KeepVariable = "DAFNY_CONTRACT_TEST_KEEP_ARTIFACTS";

  public static bool Keep => Environment.GetEnvironmentVariable(KeepVariable) == "1";

  /// <summary>Recursively deletes a directory created by a test, tolerating one that is already gone.</summary>
  public static void Delete(string directory) {
    if (Keep) {
      return;
    }
    try {
      System.IO.Directory.Delete(directory, recursive: true);
    } catch (DirectoryNotFoundException) {
      // Already removed.
    }
  }
}

/// <summary>Runs campaigns once per distinct request and throttles concurrent compilations.</summary>
public static class Campaign {
  private static readonly Dictionary<string, Task<CampaignRun>> Cache = new();
  private static readonly SemaphoreSlim Throttle = new(Math.Max(2, Environment.ProcessorCount / 4));
  private static readonly Dictionary<string, int> Users = new();

  /// <summary>A source snapshot with its content hash.</summary>
  public static ContractSource Source(string path, string content) => new(path, content, Hash(content));

  /// <summary>A draft snapshot with its content hash.</summary>
  public static ContractRuntimeDraft Draft(string symbol, string content, string? path = null) =>
    new(symbol, path ?? symbol.Split('.')[^1] + ".dfy", content, Hash(content));

  /// <summary>The content hash used by campaign requests.</summary>
  public static string Hash(string content) => ContractHarnessBuilder.Hash(content);

  /// <summary>
  /// Splits a fixture file into sections introduced by <c>// == source NAME ==</c> or
  /// <c>// == generator NAME ==</c> lines; each section starts at its own line 1.
  /// </summary>
  public static IReadOnlyDictionary<string, string> Sections(string file) {
    var lines = File.ReadAllText(Path.Combine(AppContext.BaseDirectory, "ContractRuntime", "Fixtures", file + ".dfy"))
      .Replace("\r\n", "\n").Split('\n');
    var sections = new Dictionary<string, string>();
    string? name = null;
    var body = new List<string>();
    foreach (var line in lines.Append("// == end ==")) {
      if (!line.StartsWith("// == ", StringComparison.Ordinal) || !line.EndsWith(" ==", StringComparison.Ordinal)) {
        body.Add(line);
        continue;
      }
      if (name != null) { sections.Add(name, string.Join("\n", body).TrimEnd() + "\n"); }
      name = line["// == ".Length..^" ==".Length];
      body.Clear();
    }
    return sections;
  }

  private static string Key(CampaignSpec spec) => Hash(JsonSerializer.Serialize(spec, ContractJson.Options));

  /// <summary>Registers one fixture as a user of the campaign and starts it if no fixture has yet.</summary>
  public static Task<CampaignRun> AcquireAsync(CampaignSpec spec) {
    lock (Cache) {
      var key = Key(spec);
      Users[key] = Users.GetValueOrDefault(key) + 1;
    }
    return RunAsync(spec);
  }

  /// <summary>
  /// Drops one fixture's use of the campaign. The last user removes the cached run and deletes its directory, so a
  /// directory is never deleted while a fixture that acquired it can still read it; a later request reruns it.
  /// </summary>
  public static async Task ReleaseAsync(CampaignSpec spec) {
    Task<CampaignRun>? finished;
    var key = Key(spec);
    lock (Cache) {
      Users[key]--;
      if (Users[key] > 0) {
        return;
      }
      Users.Remove(key);
      Cache.Remove(key, out finished);
    }
    // Campaign processes are reaped before the run completes, so nothing writes into the directory afterwards.
    var directory = (await finished!.ContinueWith(task => task.IsCompletedSuccessfully ? task.Result.Directory : null,
      TaskScheduler.Default));
    if (directory != null) {
      ContractArtifacts.Delete(directory);
    }
  }

  /// <summary>Returns the cached run of an identical request, starting it on first use.</summary>
  public static Task<CampaignRun> RunAsync(CampaignSpec spec) {
    var key = Key(spec);
    lock (Cache) {
      if (!Cache.TryGetValue(key, out var run)) {
        run = Start(spec, key);
        Cache.Add(key, run);
      }
      return run;
    }
  }

  private static async Task<CampaignRun> Start(CampaignSpec spec, string key) {
    await Throttle.WaitAsync();
    try {
      var directory = Path.Combine("/workspace/tmp", "contract-campaign-" + key[..12] + "-" + Guid.NewGuid().ToString("N"));
      System.IO.Directory.CreateDirectory(directory);
      var completed = false;
      try {
        var request = new ContractRuntimeCampaignRequest(1, spec.Sources, new(spec.Entry), "17", spec.Dependencies,
          spec.Drafts, spec.Generator, spec.SampleCount, spec.SampleTimeout, spec.Timeout, spec.MaxClosedQueries,
          spec.ClosedQueryTimeout, spec.MaxViolationsPerObligation, spec.ReplayOrdinal);
        var options = new DafnyOptions(DafnyOptions.Default);
        options.ApplyDefaultOptionsWithoutSettingsDefault();
        using var timeout = new CancellationTokenSource(TimeSpan.FromMilliseconds(spec.Timeout + 30000));
        var result = await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token);
        // Kept next to the campaign artifacts for diagnosing a failing slice.
        await File.WriteAllTextAsync(Path.Combine(directory, "campaign-result.json"), JsonSerializer.Serialize(result, ContractJson.Options));
        completed = true;
        return new CampaignRun(spec, result, directory);
      }
      finally {
        // A failed or cancelled campaign has no owner to release it.
        if (!completed) {
          ContractArtifacts.Delete(directory);
        }
      }
    }
    finally {
      Throttle.Release();
    }
  }
}

/// <summary>Starts every campaign of one fixture class concurrently; each test awaits its cached run.</summary>
public abstract class CampaignFixture : IAsyncLifetime {
  /// <summary>The campaigns used by the fixture's tests.</summary>
  protected abstract IEnumerable<CampaignSpec> Campaigns();

  // A failing campaign is reported by the tests that await it, not by fixture construction.
  public Task InitializeAsync() => Task.WhenAll(Campaigns().Select(spec =>
    Campaign.AcquireAsync(spec).ContinueWith(_ => { }, TaskScheduler.Default)));

  // Campaigns() yields the same specs on every call; the last fixture using a campaign deletes its directory.
  public Task DisposeAsync() => Task.WhenAll(Campaigns().Select(Campaign.ReleaseAsync));
}
