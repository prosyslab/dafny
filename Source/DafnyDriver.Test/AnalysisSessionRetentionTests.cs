using System.Text.Json;
using System.Text.Json.Nodes;
using DafnyDriver.Commands;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>
/// Drives the native session in memory with supplied source snapshots. Verification runs the real solver on
/// tiny programs; nothing is read from or written to disk.
/// </summary>
[Collection("Proof input translation")]
public class AnalysisSessionRetentionTests {
  private const string Cwd = "/workspace/session-retention";
  private const string Path = Cwd + "/Retention.dfy";
  private const string Source = """
    module Retention {
      lemma Sound(x: int)
        ensures x + 1 > x
      {
        assert x + 1 > x;
      }
      method Count(n: nat) returns (r: nat)
        ensures r == n
      {
        r := 0;
        while r < n
          invariant r <= n
        {
          r := r + 1;
        }
      }
    }
    """;
  private static readonly string[] Analyze = ["definition-analysis", "--include-semantic-facts", Path];
  private static readonly string[] AnalyzeExternal = ["definition-analysis", "--include-semantic-facts", "--allow-external-contracts", Path];
  private static readonly string[] Verify = ["verify", "--log-format:json", Path];
  private static readonly string[] VerifyExternal = ["verify", "--log-format:json", "--allow-external-contracts", Path];

  private sealed record Reply(int Code, string Stdout, string Stderr, JsonElement Evidence) {
    public int Count(string name) => Evidence.GetProperty(name).GetInt32();
  }

  private static async Task<Reply> Run(AnalysisSessionCommand.Session session, string[] arguments, string id,
    string context = "default", string source = Source) {
    var response = await session.Execute(new AnalysisSessionCommand.Request(id, arguments, Cwd, context,
      new Dictionary<string, string> { [Path] = source }), CancellationToken.None);
    return new Reply(response.Returncode, response.Stdout, response.Stderr,
      JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions));
  }

  // Alternating option contexts keep each context's resolved modules and analysis facts.
  [Fact]
  public async Task AlternatingAnalysisContextsStayWarm() {
    using var session = new AnalysisSessionCommand.Session();
    var first = await Run(session, Analyze, "s1");
    var other = await Run(session, AnalyzeExternal, "a1");
    Assert.Equal(0, first.Code);
    Assert.Equal(0, other.Code);
    Assert.True(first.Count("analysisModuleMisses") > 0);
    for (var round = 0; round < 2; round++) {
      var again = await Run(session, Analyze, "s" + (round + 2));
      var otherAgain = await Run(session, AnalyzeExternal, "a" + (round + 2));
      foreach (var reply in new[] { again, otherAgain }) {
        Assert.Equal(0, reply.Code);
        Assert.True(reply.Count("analysisModuleHits") > 0, reply.Evidence.ToString());
        Assert.True(reply.Count("analysisModuleMisses") <= 1, reply.Evidence.ToString());
      }
      Assert.Equal(first.Stdout, again.Stdout);
      Assert.Equal(other.Stdout, otherAgain.Stdout);
    }
    Assert.Equal(2, session.RetainedResolverContexts);
    Assert.Equal(2, session.RetainedResultContexts);
  }

  // An analysis request in another context no longer discards verification results.
  [Fact]
  public async Task InterleavedAnalysisKeepsVerificationResults() {
    using var session = new AnalysisSessionCommand.Session();
    var cold = await Run(session, VerifyExternal, "v1");
    Assert.Equal(0, cold.Code);
    Assert.True(cold.Count("solverRunCount") > 0);
    Assert.Equal(0, cold.Count("cacheHitCount"));
    for (var round = 0; round < 2; round++) {
      Assert.Equal(0, (await Run(session, Analyze, "s" + round)).Code);
      var warm = await Run(session, VerifyExternal, "v" + (round + 2));
      Assert.Equal(0, warm.Code);
      Assert.Equal(cold.Count("taskCount"), warm.Count("taskCount"));
      Assert.Equal(warm.Count("taskCount"), warm.Count("cacheHitCount"));
      Assert.Equal(0, warm.Count("solverRunCount"));
      Assert.Equal(0, warm.Count("resultCacheClears"));
    }
  }

  // Two verification contexts retain separate results and neither clears the other.
  [Fact]
  public async Task AlternatingVerificationContextsKeepSeparateResults() {
    using var session = new AnalysisSessionCommand.Session();
    Assert.True((await Run(session, Verify, "a1")).Count("solverRunCount") > 0);
    Assert.True((await Run(session, VerifyExternal, "b1")).Count("solverRunCount") > 0);
    foreach (var arguments in new[] { Verify, VerifyExternal, Verify }) {
      var warm = await Run(session, arguments, "again");
      Assert.Equal(0, warm.Count("solverRunCount"));
      Assert.Equal(warm.Count("taskCount"), warm.Count("cacheHitCount"));
    }
  }

  // Retained contexts are capped: the least recently used context is evicted and cleared.
  [Fact]
  public async Task LeastRecentlyUsedContextsAreEvicted() {
    using var session = new AnalysisSessionCommand.Session();
    for (var index = 0; index < 5; index++) {
      Assert.True((await Run(session, Verify, "v" + index, "context" + index)).Count("solverRunCount") > 0);
    }
    var evidence = await Run(session, Verify, "probe", "context4");
    Assert.Equal(AnalysisSessionCommand.Session.ResultContextCapacity, session.RetainedResultContexts);
    Assert.Equal(AnalysisSessionCommand.Session.ResolverContextCapacity, session.RetainedResolverContexts);
    Assert.Equal(1, evidence.Count("resultCacheEvictions"));
    Assert.Equal(3, evidence.Count("resolverEvictions"));
    // Context 1 is the oldest retained one; context 0 was evicted and must solve again.
    var retained = await Run(session, Verify, "retained", "context1");
    Assert.Equal(0, retained.Count("solverRunCount"));
    var evicted = await Run(session, Verify, "evicted", "context0");
    Assert.True(evicted.Count("solverRunCount") > 0);
    Assert.Equal(AnalysisSessionCommand.Session.ResultContextCapacity, session.RetainedResultContexts);
  }

  // The per-context window is a memory bound that clears only the context that reached it.
  [Fact]
  public async Task CompilationWindowClearsOnlyItsOwnContext() {
    const int window = 3;
    using var session = new AnalysisSessionCommand.Session(window);
    Assert.True((await Run(session, Verify, "cold", "bounded")).Count("solverRunCount") > 0);
    Assert.True((await Run(session, Verify, "other", "other")).Count("solverRunCount") > 0);
    // Alternating contexts replaces the state each time, so every request is a new compilation.
    for (var index = 1; index < window; index++) {
      Assert.Equal(0, (await Run(session, Verify, "r" + index, "bounded")).Count("solverRunCount"));
      Assert.Equal(0, (await Run(session, Verify, "s" + index, "other")).Count("solverRunCount"));
    }
    var kept = await Run(session, Verify, "kept", "bounded");
    Assert.Equal(1, kept.Count("resultCacheClears"));
    Assert.True(kept.Count("solverRunCount") > 0);
    // The other context reached the same count; it clears at its own next compilation, not earlier.
    var sibling = await Run(session, Verify, "sibling", "other");
    Assert.Equal(2, sibling.Count("resultCacheClears"));
    Assert.True(sibling.Count("solverRunCount") > 0);
    var untouched = await Run(session, Verify, "untouched", "bounded");
    Assert.Equal(0, untouched.Count("solverRunCount"));
    Assert.Equal(2, untouched.Count("resultCacheClears"));
  }

  // A reused result is reported against the current source lines, equal to a cold run of that source.
  [Theory]
  [InlineData("shift-above")]
  [InlineData("whitespace-inside")]
  public async Task ReusedResultsReportCurrentAssertionLines(string change) {
    var edited = change == "shift-above" ? "\n\n// moved down\n" + Source
      : Source.Replace("    assert x + 1 > x;", "\n\n    assert   x + 1 > x;");
    Assert.NotEqual(Source, edited);
    using var warm = new AnalysisSessionCommand.Session();
    var original = await Run(warm, Verify, "original");
    var reused = await Run(warm, Verify, "reused", source: edited);
    using var coldSession = new AnalysisSessionCommand.Session();
    var cold = await Run(coldSession, Verify, "cold", source: edited);

    Assert.Equal(0, reused.Code);
    Assert.Equal(reused.Count("taskCount"), reused.Count("cacheHitCount"));
    Assert.Equal(0, reused.Count("solverRunCount"));
    Assert.True(cold.Count("solverRunCount") > 0);
    var lines = Assertions(reused.Stdout);
    Assert.Equal(Assertions(cold.Stdout), lines);
    Assert.NotEqual(Assertions(original.Stdout), lines);
    Assert.Equal(Normalize(cold.Stdout), Normalize(reused.Stdout));
    Assert.Equal(cold.Stderr, reused.Stderr);
  }

  // Changed assertions, contracts and bodies still miss.
  [Theory]
  [InlineData("assertion")]
  [InlineData("contract")]
  [InlineData("invariant")]
  public async Task SemanticChangesStillMiss(string change) {
    var edited = change switch {
      "assertion" => Source.Replace("assert x + 1 > x;", "assert x + 2 > x;"),
      "contract" => Source.Replace("ensures r == n", "ensures r >= n"),
      _ => Source.Replace("invariant r <= n", "invariant r <= n + 1")
    };
    using var session = new AnalysisSessionCommand.Session();
    await Run(session, Verify, "original");
    var changed = await Run(session, Verify, "changed", source: edited);
    Assert.True(changed.Count("solverRunCount") > 0);
    Assert.True(changed.Count("cacheHitCount") < changed.Count("taskCount"));
  }

  private static string Assertions(string stdout) => string.Join("|", Json(stdout)["verificationResults"]!.AsArray()
    .SelectMany(scope => scope!["vcResults"]!.AsArray())
    .SelectMany(result => result!["assertions"]!.AsArray())
    .Select(assertion => $"{assertion!["line"]}:{assertion["col"]}:{assertion["description"]}"));

  // Timing fields differ between a cold run and a replayed one; every other logged field must not.
  private static string Normalize(string stdout) {
    var document = Json(stdout);
    Strip(document);
    return document.ToJsonString();
  }

  private static void Strip(JsonNode? node) {
    if (node is JsonObject target) {
      foreach (var timing in target.Where(property => property.Key is "runTime" or "startTime" or "endTime" or "duration").ToList()) {
        target.Remove(timing.Key);
      }
      foreach (var property in target) {
        Strip(property.Value);
      }
    } else if (node is JsonArray array) {
      foreach (var item in array) {
        Strip(item);
      }
    }
  }

  private static JsonNode Json(string stdout) {
    // The logger writes its document on its own line; the verifier summary line follows it.
    var line = stdout.Split('\n').FirstOrDefault(line => line.StartsWith('{'));
    Assert.True(line != null, stdout);
    return JsonNode.Parse(line)!;
  }
}
