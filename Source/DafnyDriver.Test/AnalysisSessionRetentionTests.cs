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

  // An edit confined to one method keeps the other target's modular key, so its result is reused across
  // compilations while the edited method is proved again.
  [Fact]
  public async Task UnrelatedEditKeepsOtherTargetsReusable() {
    var edited = Source.Replace("invariant r <= n", "invariant r <= n && r >= 0");
    Assert.NotEqual(Source, edited);
    using var session = new AnalysisSessionCommand.Session();
    var cold = await Run(session, Verify, "cold");
    Assert.Equal(0, cold.Code);
    var warm = await Run(session, Verify, "edited", source: edited);
    Assert.Equal(0, warm.Code);
    Assert.Equal(cold.Count("taskCount"), warm.Count("taskCount"));
    Assert.True(warm.Count("cacheHitCount") > 0, warm.Evidence.ToString());
    Assert.True(warm.Count("solverRunCount") > 0, warm.Evidence.ToString());
    Assert.True(warm.Count("cacheHitCount") < warm.Count("taskCount"), warm.Evidence.ToString());
  }

  private const string ReusePath = Cwd + "/Reuse.dfy";
  // Target's live set does not reach Helper, but Boogie's dependency collector reaches it through the datatype's
  // constructor functions (the Cat shape: a discriminator, constructors, a predicate over a constructor, a helper).
  private const string ReuseSource = """
    module Reuse {
      datatype Mode = Help | Run(n: nat)
      function Helper(x: int): int { x + 1 }
      ghost predicate Witness(m: Mode, x: int) { m == Help ==> Helper(x) > x }
      lemma Target(m: Mode) ensures m.Help? || m.Run? { }
      lemma Other(x: int) ensures Witness(Help, x) { }
    }
    """;

  private static async Task<Reply> RunReuse(AnalysisSessionCommand.Session session, string target, string id,
    string source, params string[] extra) {
    var arguments = new[] { "verify", "--log-format:json", $"--filter-symbol={target}" }.Concat(extra).Append(ReusePath).ToArray();
    var response = await session.Execute(new AnalysisSessionCommand.Request(id, arguments, Cwd, "default",
      new Dictionary<string, string> { [ReusePath] = source }), CancellationToken.None);
    return new Reply(response.Returncode, response.Stdout, response.Stderr,
      JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions));
  }

  // The native cache reuses a result when the modular key matches, whatever Boogie's own dependency checksum says:
  // an edit outside the target's live set hits, an edit inside another target's live set misses there.
  [Fact]
  public async Task NativeLookupFollowsTheModularKey() {
    var edited = ReuseSource.Replace("x + 1 }", "x + 2 }");
    Assert.NotEqual(ReuseSource, edited);
    using var session = new AnalysisSessionCommand.Session();
    var target = await RunReuse(session, "Reuse.Target", "t1", ReuseSource);
    var other = await RunReuse(session, "Reuse.Other", "o1", ReuseSource);
    Assert.True(target.Code == 0, target.Stdout + target.Stderr);
    Assert.True(other.Code == 0, other.Stdout + other.Stderr);
    Assert.True(target.Count("solverRunCount") > 0);
    var targetAgain = await RunReuse(session, "Reuse.Target", "t2", edited);
    var otherAgain = await RunReuse(session, "Reuse.Other", "o2", edited);
    Assert.Equal(0, targetAgain.Code);
    Assert.Equal(targetAgain.Count("taskCount"), targetAgain.Count("cacheHitCount"));
    Assert.True(targetAgain.Count("solverRunCount") == 0, targetAgain.Evidence.ToString());
    Assert.Equal(0, otherAgain.Code);
    Assert.True(otherAgain.Count("solverRunCount") > 0, otherAgain.Evidence.ToString());
  }

  // Session proof inputs are schema 3 and certify a target without proof obligations.
  [Fact]
  public async Task SessionProofInputsCertifyZeroObligationTargets() {
    var source = Source.Replace("module Retention {", "module Retention {\n  function Id(x: int): int { x }");
    using var session = new AnalysisSessionCommand.Session();
    var reply = await Run(session, ["definition-analysis", "--include-proof-inputs", Path], "inputs", source: source);
    Assert.True(reply.Code == 0, reply.Stdout + reply.Stderr);
    var inputs = Json(reply.Stdout)["sourceFacts"]!["proofInputs"]!;
    Assert.Equal(3, inputs["schemaVersion"]!.GetValue<int>());
    var rows = inputs["definitions"]!.AsArray().ToDictionary(row => row!["fullName"]!.GetValue<string>(), row => row!);
    Assert.Equal(0, rows["Retention.Id"]["implementations"]!.GetValue<int>());
    Assert.True(rows["Retention.Sound"]["implementations"]!.GetValue<int>() > 0);
    Assert.NotNull(rows["Retention.Count"]["closureOrigins"]);
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

  // A context keeps its results however many compilations it sees: memory is bounded by the native cache's
  // entry bound, and only eviction of the context or shutdown clears it. 33 compilations exceed the former
  // 32-compilation window, which cleared the cache.
  [Fact]
  public async Task ResultsSurviveManyCompilationsOfOneContext() {
    using var session = new AnalysisSessionCommand.Session();
    Assert.True((await Run(session, Verify, "cold", "bounded")).Count("solverRunCount") > 0);
    for (var index = 1; index <= 33; index++) {
      // Different bytes each time, so every request is a new compilation and asks the native cache.
      var reply = await Run(session, Verify, "r" + index, "bounded", $"// compilation {index}\n" + Source);
      Assert.True(reply.Code == 0, reply.Stdout + reply.Stderr);
      Assert.True(reply.Count("solverRunCount") == 0, $"compilation {index}: {reply.Evidence}");
      Assert.Equal(reply.Count("taskCount"), reply.Count("cacheHitCount"));
    }
    Assert.Equal(1, session.RetainedResultContexts);
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

  // The verifier's fake-solver case: a request naming another solver path never reuses the state whose engine starts
  // the first path, even when both files have equal content (injected; the two bundled Z3 builds stand in for byte
  // copies). The proof options stay path-free, and the same path reuses its state.
  [Fact]
  public async Task AnotherSolverPathNeverReusesTheState() {
    var directory = System.IO.Path.Combine(System.IO.Path.GetDirectoryName(typeof(DafnyOptions).Assembly.Location)!, "z3", "bin");
    var first = System.IO.Path.Combine(directory, $"z3-{DafnyOptions.DefaultZ3Version}");
    var second = System.IO.Path.Combine(directory, "z3-4.12.1");
    Assert.True(File.Exists(first) && File.Exists(second) && first != second);
    using var session = new AnalysisSessionCommand.Session { ToolFileHash = _ => "equal-bytes" };
    string[] Analyze(string solver) => ["definition-analysis", "--include-proof-inputs", "--solver-path", solver, Path];
    var a = await Run(session, Analyze(first), "a");
    var b = await Run(session, Analyze(second), "b");
    var again = await Run(session, Analyze(second), "again");
    foreach (var reply in new[] { a, b, again }) {
      Assert.True(reply.Code == 0, reply.Stderr);
    }
    string Identity(Reply reply) => reply.Evidence.GetProperty("optionsIdentity").GetString()!;
    Assert.NotEqual(Identity(a), Identity(b));
    Assert.True(b.Count("generation") > a.Count("generation"), b.Evidence.ToString());
    Assert.Equal(Identity(b), Identity(again));
    Assert.Equal(b.Count("generation"), again.Count("generation"));
    string OptionsSha(Reply reply) => Json(reply.Stdout)["sourceFacts"]!["proofInputs"]!["optionsSha256"]!.GetValue<string>();
    Assert.Equal(OptionsSha(a), OptionsSha(b));
  }

  // The session refuses a relative or unnormalized solver path instead of hashing one file while starting another.
  [Theory]
  [InlineData("z3/bin/z3-4.16.0")]
  [InlineData("/workspace/session-retention/link/../z3")]
  public async Task InexactSolverPathIsUnsupported(string solver) {
    using var session = new AnalysisSessionCommand.Session();
    var reply = await Run(session, ["verify", "--solver-option", "PROVER_PATH=" + solver, Path], "inexact");
    Assert.Equal(7, reply.Code);
    Assert.Contains("DAFNY_SESSION_UNSUPPORTED", reply.Stderr);
  }

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
