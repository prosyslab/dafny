using System.Reactive.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Microsoft.Dafny;
using VC;
using Xunit;
using Transfer = Microsoft.Dafny.NativeSessionTransfer;

namespace DafnyDriver.Test;

/// <summary>
/// Cross-process transfer in memory: a parent session exports, a fresh session imports, and the child must
/// reach the same cache hits as an in-process clone. Sources are supplied snapshots; verification uses the real
/// solver on a tiny program, like the retention tests, and the cache-level case uses a fake solver task.
/// </summary>
[Collection("Proof input translation")]
public class AnalysisSessionTransferTests {
  private const string Cwd = "/workspace/session-transfer";
  private const string Path = Cwd + "/Transfer.dfy";
  private const string Source = """
    module Transfer {
      lemma Sound(x: int)
        ensures x + 1 > x
      {
        assert x + 1 > x;
      }
    }
    """;
  private static readonly string[] Verify = ["verify", "--log-format:json", Path];
  private static readonly string[] VerifyExternal = ["verify", "--log-format:json", "--allow-external-contracts", Path];
  private static readonly string Toolchain = DefinitionAnalysis.ContextToolchainIdentity()!;

  private sealed record Reply(int Code, string Stdout, string Stderr, JsonElement Evidence) {
    public int Count(string name) => Evidence.GetProperty(name).GetInt32();
  }

  private static async Task<Reply> Run(AnalysisSessionCommand.Session session, string[] arguments, string id = "run") {
    var response = await session.Execute(new AnalysisSessionCommand.Request(id, arguments, Cwd, "role",
      new Dictionary<string, string> { [Path] = Source }), CancellationToken.None);
    return new Reply(response.Returncode, response.Stdout, response.Stderr,
      JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions));
  }

  private static async Task<Transfer.TransferDocument> Export(AnalysisSessionCommand.Session session, string toolchain) {
    var (resolvers, results) = await session.ExportTransfer(CancellationToken.None);
    return new Transfer.TransferDocument(1, Guid.NewGuid().ToString("N"), "default", session.Epoch, toolchain, resolvers, results);
  }

  private static string Contexts(Transfer.TransferDocument document) =>
    JsonSerializer.Serialize(new { document.Resolvers, document.Results }, AnalysisSessionCommand.JsonOptions);

  private static async Task<AnalysisSessionCommand.Session> WarmParent() {
    var parent = new AnalysisSessionCommand.Session();
    var cold = await Run(parent, Verify);
    Assert.Equal(0, cold.Code);
    Assert.True(cold.Count("solverRunCount") > 0);
    return parent;
  }

  private static Transfer.TransferDocument Parse(string payload) => Transfer.Parse(payload, Toolchain, 2, 4);

  // An imported fresh session hits the same entries as an in-process clone of the same parent.
  [Fact]
  public async Task ImportedChildReachesTheCacheHitsOfAnInProcessClone() {
    using var parent = await WarmParent();
    var clone = await parent.Clone(CancellationToken.None);
    using var cloned = clone.Child;
    var payload = Transfer.Serialize(await Export(parent, Toolchain));
    using var imported = new AnalysisSessionCommand.Session();
    var (parsed, verification) = await imported.Import(Parse(payload), CancellationToken.None);
    Assert.Equal(clone.ParsedEntries, parsed);
    Assert.Equal(clone.VerificationEntries, verification);
    Assert.True(verification > 0);
    Assert.True(parsed > 0);
    Assert.Equal(Contexts(Parse(payload)), Contexts(await Export(imported, Toolchain)));

    var fromClone = await Run(cloned, Verify);
    var fromImport = await Run(imported, Verify);
    Assert.Equal(0, fromImport.Code);
    Assert.Equal(fromClone.Count("taskCount"), fromImport.Count("taskCount"));
    Assert.Equal(fromClone.Count("cacheHitCount"), fromImport.Count("cacheHitCount"));
    Assert.Equal(fromImport.Count("taskCount"), fromImport.Count("cacheHitCount"));
    Assert.Equal(0, fromClone.Count("solverRunCount"));
    Assert.Equal(0, fromImport.Count("solverRunCount"));
    Assert.Equal(fromClone.Stdout, fromImport.Stdout);
    Assert.Equal(parsed, imported.ImportedSeedsBound);
    Assert.Equal(0, imported.ImportedSeedsDiscarded);
    // Parser reuse: both children now retain the same parsed sources.
    var afterClone = await Export(cloned, Toolchain);
    var afterImport = await Export(imported, Toolchain);
    Assert.Equal(afterClone.Resolvers.Select(r => r.Entries.Length), afterImport.Resolvers.Select(r => r.Entries.Length));
    Assert.Equal(afterClone.Resolvers.Select(r => r.Key), afterImport.Resolvers.Select(r => r.Key));
  }

  // Export reads the parent only: its documents, epoch and cache hits are unchanged, however often it exports.
  [Fact]
  public async Task ExportLeavesTheParentUnchanged() {
    using var parent = await WarmParent();
    var epoch = parent.Epoch;
    var contexts = (parent.RetainedResolverContexts, parent.RetainedResultContexts);
    var first = Contexts(await Export(parent, Toolchain));
    var second = Contexts(await Export(parent, Toolchain));
    Assert.Equal(first, second);
    Assert.Equal(epoch, parent.Epoch);
    Assert.Equal(contexts, (parent.RetainedResolverContexts, parent.RetainedResultContexts));
    var warm = await Run(parent, Verify);
    Assert.Equal(0, warm.Count("solverRunCount"));
    Assert.Equal(warm.Count("taskCount"), warm.Count("cacheHitCount"));
    Assert.Equal(first, Contexts(await Export(parent, Toolchain)));
  }

  // Parked sources only seed a resolver context created for exactly the exported options identity.
  [Fact]
  public async Task OptionIdentityMismatchDiscardsParsedSourcesAndOtherOptionsNeverUseThem() {
    using var parent = await WarmParent();
    var document = await Export(parent, Toolchain);
    var tampered = document with {
      Resolvers = document.Resolvers.Select(r => r with { OptionsIdentity = new string('a', 64) }).ToArray()
    };
    using var mismatched = new AnalysisSessionCommand.Session();
    await mismatched.Import(Parse(Transfer.Serialize(tampered)), CancellationToken.None);
    var reply = await Run(mismatched, Verify);
    Assert.Equal(0, reply.Code);
    Assert.Equal(0, mismatched.ImportedSeedsBound);
    Assert.Equal(document.Resolvers.Sum(r => r.Entries.Length), mismatched.ImportedSeedsDiscarded);
    // The result caches are still authoritative through native checksums, so they still hit.
    Assert.Equal(0, reply.Count("solverRunCount"));

    using var other = new AnalysisSessionCommand.Session();
    await other.Import(Parse(Transfer.Serialize(document)), CancellationToken.None);
    var different = await Run(other, VerifyExternal);
    Assert.Equal(0, different.Code);
    Assert.Equal(0, other.ImportedSeedsBound);
    Assert.True(different.Count("solverRunCount") > 0);
  }

  // A child exported before it served a request still carries the parked parser sources and result entries.
  [Fact]
  public async Task UnboundImportCanBeExportedAndClonedAgain() {
    using var parent = await WarmParent();
    var document = await Export(parent, Toolchain);
    using var imported = new AnalysisSessionCommand.Session();
    await imported.Import(Parse(Transfer.Serialize(document)), CancellationToken.None);
    Assert.Equal(Contexts(document), Contexts(await Export(imported, Toolchain)));
    var clone = await imported.Clone(CancellationToken.None);
    using var child = clone.Child;
    Assert.Equal(document.Resolvers.Sum(r => r.Entries.Length), clone.ParsedEntries);
    var reply = await Run(child, Verify);
    Assert.Equal(0, reply.Count("solverRunCount"));
    Assert.Equal(clone.ParsedEntries, child.ImportedSeedsBound);
  }

  // A session that already served a request, or already imported, cannot import.
  [Fact]
  public async Task OnlyAFreshSessionImportsAndOnlyOnce() {
    using var parent = await WarmParent();
    var document = Parse(Transfer.Serialize(await Export(parent, Toolchain)));
    await Assert.ThrowsAsync<Transfer.TransferRejectedException>(() => parent.Import(document, CancellationToken.None));
    using var served = new AnalysisSessionCommand.Session();
    Assert.Equal(0, (await Run(served, Verify)).Code);
    await Assert.ThrowsAsync<Transfer.TransferRejectedException>(() => served.Import(document, CancellationToken.None));
    using var fresh = new AnalysisSessionCommand.Session();
    await fresh.Import(document, CancellationToken.None);
    await Assert.ThrowsAsync<Transfer.TransferRejectedException>(() => fresh.Import(document, CancellationToken.None));
    Assert.Equal(parent.RetainedResultContexts, fresh.RetainedResultContexts);
  }

  private static AnalysisSessionCommand.Request ExportRequest(string session = "default") =>
    new("export", Operation: "export-session", SessionId: session);

  private static AnalysisSessionCommand.Request ImportRequest(string? payload, string session = "default") =>
    new("import", Operation: "import-session", SessionId: session, Payload: payload);

  private static async Task<AnalysisSessionCommand.Response> RegistryRun(AnalysisSessionCommand.SessionRegistry registry,
    string[] arguments, string id = "run") => await registry.Execute(new AnalysisSessionCommand.Request(id, arguments, Cwd, "role",
    new Dictionary<string, string> { [Path] = Source }), CancellationToken.None);

  // The protocol round trip: strict export document, receipt, then a warm verify with no solver start.
  [Fact]
  public async Task RegistryExportsADocumentAndImportsItIntoAFreshProcess() {
    await using var parent = new AnalysisSessionCommand.SessionRegistry();
    var cold = await RegistryRun(parent, Verify);
    Assert.Equal(0, cold.Returncode);
    var exported = await parent.Execute(ExportRequest(), CancellationToken.None);
    Assert.True(exported.Returncode == 0, exported.Stderr);
    Assert.Null(exported.NativeEvidence);
    Assert.Equal("", exported.Stderr);
    var document = JsonNode.Parse(exported.Stdout)!.AsObject();
    Assert.Equal(1, (int)document["schemaVersion"]!);
    Assert.Equal(Toolchain, (string)document["toolchain"]!);
    Assert.Equal("default", (string)document["sessionId"]!);
    Assert.NotEmpty(document["resolvers"]!.AsArray());
    Assert.NotEmpty(document["results"]!.AsArray()[0]!["entries"]!.AsArray());
    Assert.Equal(["uri", "text"], document["resolvers"]![0]!["entries"]![0]!.AsObject().Select(p => p.Key).ToArray());
    var evidence = JsonSerializer.SerializeToElement((await RegistryRun(parent, Verify, "again")).NativeEvidence,
      AnalysisSessionCommand.JsonOptions);
    Assert.Equal(0, evidence.GetProperty("solverRunCount").GetInt32());

    await using var child = new AnalysisSessionCommand.SessionRegistry();
    var imported = await child.Execute(ImportRequest(exported.Stdout), CancellationToken.None);
    Assert.True(imported.Returncode == 0, imported.Stderr);
    Assert.Null(imported.NativeEvidence);
    var receipt = JsonSerializer.Deserialize<Transfer.ImportReceipt>(imported.Stdout, AnalysisSessionCommand.JsonOptions)!;
    Assert.Equal(1, receipt.SchemaVersion);
    Assert.Equal("default", receipt.SessionId);
    Assert.True(receipt.ParsedEntries > 0);
    Assert.True(receipt.VerificationEntries > 0);
    Assert.NotEqual((string)document["sessionEpoch"]!, receipt.SessionEpoch);
    Assert.NotEqual((string)document["daemonEpoch"]!, receipt.DaemonEpoch);
    var warm = await RegistryRun(child, Verify, "warm");
    var warmEvidence = JsonSerializer.SerializeToElement(warm.NativeEvidence, AnalysisSessionCommand.JsonOptions);
    Assert.Equal(0, warm.Returncode);
    Assert.Equal(warmEvidence.GetProperty("taskCount").GetInt32(), warmEvidence.GetProperty("cacheHitCount").GetInt32());
    Assert.Equal(0, warmEvidence.GetProperty("solverRunCount").GetInt32());
    Assert.Equal(receipt.SessionEpoch, warmEvidence.GetProperty("sessionEpoch").GetString());
  }

  // A payload over the frame limit is refused with a clear error, never truncated, and costs the parent nothing.
  [Fact]
  public async Task ExportOverTheFrameLimitFailsWithoutTruncationOrParentChange() {
    await using var parent = new AnalysisSessionCommand.SessionRegistry(transferFrameLimit: 4600);
    Assert.Equal(0, (await RegistryRun(parent, Verify)).Returncode);
    var refused = await parent.Execute(ExportRequest(), CancellationToken.None);
    Assert.Equal(6, refused.Returncode);
    Assert.Equal("", refused.Stdout);
    Assert.Contains("DAFNY_SESSION_TRANSFER_TOO_LARGE", refused.Stderr);
    Assert.Contains("4600", refused.Stderr);
    Assert.Null(refused.NativeEvidence);
    var warm = JsonSerializer.SerializeToElement((await RegistryRun(parent, Verify, "warm")).NativeEvidence,
      AnalysisSessionCommand.JsonOptions);
    Assert.Equal(0, warm.GetProperty("solverRunCount").GetInt32());
  }

  // Request frames count the client's unescaped-quote JSON string; responses count this process's stricter escaping.
  [Fact]
  public void FrameAccountingCoversBothFramesAndIsExactAtTheLimit() {
    var payload = new string('x', 1000) + "\"\n";
    var bytes = Transfer.RequestFrameBytes(payload);
    Assert.Equal(1000 + 2 + 2 + 2 + Transfer.FrameReserve, bytes);
    Assert.Equal(1000 + 2 + 6 + 2 + Transfer.FrameReserve, Transfer.ResponseFrameBytes(payload));
    Transfer.CheckFrame(payload, (int)bytes);
    Assert.Throws<Transfer.TransferTooLargeException>(() => Transfer.CheckFrame(payload, (int)bytes - 1));
    var oversized = new string('x', AnalysisSessionCommand.RequestLimit);
    Assert.Throws<Transfer.TransferTooLargeException>(() => Transfer.CheckFrame(oversized));
    Assert.Throws<Transfer.TransferRejectedException>(() => Transfer.Parse(oversized, Toolchain, 2, 4));
    // Quotes grow threefold when the response escapes them: the 8 MiB request frame stays binding, so a
    // payload that fits it fits the 128 MiB response frame; a small injected response limit checks that side.
    var quotes = new string('"', 3_000_000);
    Assert.True(Transfer.RequestFrameBytes(quotes) < AnalysisSessionCommand.RequestLimit);
    Transfer.CheckFrame(quotes);
    Assert.Throws<Transfer.TransferTooLargeException>(() => Transfer.CheckFrame(quotes, responseLimit: 16 * 1024 * 1024));
    var worst = new string('"', (AnalysisSessionCommand.RequestLimit - Transfer.FrameReserve) / 2);
    Assert.True(Transfer.ResponseFrameBytes(worst) < AnalysisSessionCommand.ResponseLimit);
  }

  // Rejections install nothing: the same fresh process still accepts a valid document afterwards.
  [Fact]
  public async Task RejectedImportsInstallNothing() {
    await using var parent = new AnalysisSessionCommand.SessionRegistry();
    Assert.Equal(0, (await RegistryRun(parent, Verify)).Returncode);
    var good = (await parent.Execute(ExportRequest(), CancellationToken.None)).Stdout;
    var foreign = JsonNode.Parse(good)!;
    foreign["toolchain"] = new string('b', 64);
    await using var child = new AnalysisSessionCommand.SessionRegistry();
    foreach (var bad in new[] { foreign.ToJsonString(), "{", "", good[..^5] }) {
      var rejected = await child.Execute(ImportRequest(bad), CancellationToken.None);
      Assert.Equal(2, rejected.Returncode);
      Assert.Contains("DAFNY_SESSION_TRANSFER_REJECTED", rejected.Stderr);
      Assert.Null(rejected.NativeEvidence);
    }
    Assert.Equal(2, (await child.Execute(ImportRequest(null), CancellationToken.None)).Returncode);
    var mismatch = await child.Execute(ImportRequest(foreign.ToJsonString()), CancellationToken.None);
    Assert.Contains("toolchain", mismatch.Stderr);
    var cold = await RegistryRun(child, Verify, "cold");
    Assert.True(JsonSerializer.SerializeToElement(cold.NativeEvidence, AnalysisSessionCommand.JsonOptions)
      .GetProperty("solverRunCount").GetInt32() > 0);
  }

  [Fact]
  public async Task ImportAfterARequestAndAnUnknownBranchAreRejected() {
    await using var parent = new AnalysisSessionCommand.SessionRegistry();
    Assert.Equal(0, (await RegistryRun(parent, Verify)).Returncode);
    var good = (await parent.Execute(ExportRequest(), CancellationToken.None)).Stdout;
    var served = await parent.Execute(ImportRequest(good), CancellationToken.None);
    Assert.Equal(2, served.Returncode);
    Assert.Contains("fresh session", served.Stderr);
    var missing = await parent.Execute(ImportRequest(good, "nobody"), CancellationToken.None);
    Assert.Equal(2, missing.Returncode);
    var exportMissing = await parent.Execute(ExportRequest("nobody"), CancellationToken.None);
    Assert.Equal(2, exportMissing.Returncode);
  }

  [Fact]
  public async Task CancelledTransfersReturnCancelledAndLeaveTheParentUsable() {
    await using var parent = new AnalysisSessionCommand.SessionRegistry();
    Assert.Equal(0, (await RegistryRun(parent, Verify)).Returncode);
    using var cancelled = new CancellationTokenSource();
    await cancelled.CancelAsync();
    Assert.Equal(130, (await parent.Execute(ExportRequest(), cancelled.Token)).Returncode);
    var good = await parent.Execute(ExportRequest(), CancellationToken.None);
    Assert.Equal(0, good.Returncode);
    await using var child = new AnalysisSessionCommand.SessionRegistry();
    Assert.Equal(130, (await child.Execute(ImportRequest(good.Stdout), cancelled.Token)).Returncode);
    Assert.Equal(0, (await child.Execute(ImportRequest(good.Stdout), CancellationToken.None)).Returncode);
  }

  private static (string Payload, JsonObject Document) ValidDocument() {
    using var cache = new NativeVerificationCache();
    var identity = Identity();
    cache.PublishSuccessful(identity, Success(identity));
    var document = new Transfer.TransferDocument(1, Guid.NewGuid().ToString("N"), "default", Guid.NewGuid().ToString("N"), Toolchain,
      [new Transfer.ResolverTransfer(new string('1', 64), new string('2', 64),
        [new Transfer.TransferEntry("file:///a/b.dfy", "module B {}")])],
      [new Transfer.ResultTransfer(new string('3', 64), 4, cache.ExportSnapshots().ToArray())]);
    var payload = Transfer.Serialize(document);
    return (payload, JsonNode.Parse(payload)!.AsObject());
  }

  private static void AddFourResults(JsonObject document) {
    for (var i = 0; i < 4; i++) {
      var more = document["results"]![0]!.DeepClone();
      more["key"] = new string((char)('4' + i), 64);
      document["results"]!.AsArray().Add(more);
    }
  }

  [Fact]
  public void AValidHandBuiltDocumentParses() {
    var (payload, _) = ValidDocument();
    var document = Parse(payload);
    Assert.Single(document.Resolvers);
    Assert.Single(document.Results[0].Entries);
    Assert.Equal("module B {}", document.Resolvers[0].Entries[0].Text);
  }

  [Fact]
  public void ToolchainMismatchRejectsTheDocument() {
    var (payload, _) = ValidDocument();
    var error = Assert.Throws<Transfer.TransferRejectedException>(() => Transfer.Parse(payload, new string('c', 64), 2, 4));
    Assert.Contains("toolchain", error.Message);
    Assert.Throws<Transfer.TransferRejectedException>(() => Transfer.Parse(payload, null, 2, 4));
  }

  [Theory]
  [InlineData("schema version")]
  [InlineData("unknown member")]
  [InlineData("missing member")]
  [InlineData("null member")]
  [InlineData("epoch")]
  [InlineData("empty session id")]
  [InlineData("resolver key")]
  [InlineData("resolver identity")]
  [InlineData("result key")]
  [InlineData("duplicate resolver")]
  [InlineData("too many results")]
  [InlineData("relative uri")]
  [InlineData("non canonical uri")]
  [InlineData("missing text")]
  [InlineData("duplicate entry")]
  [InlineData("negative compilations")]
  [InlineData("fractional count")]
  [InlineData("empty checksum")]
  [InlineData("empty dependencies")]
  [InlineData("bad base64")]
  [InlineData("long dependencies")]
  [InlineData("negative resources")]
  [InlineData("no splits")]
  [InlineData("null split")]
  [InlineData("integer solver")]
  [InlineData("unknown solver")]
  [InlineData("bad time")]
  [InlineData("negative run time")]
  [InlineData("null assertion")]
  [InlineData("missing assertion type")]
  [InlineData("duplicate id")]
  [InlineData("null entry")]
  public void MalformedDocumentsAreRejected(string name) {
    var (_, document) = ValidDocument();
    Action<JsonObject> mutate = (name switch {
      "schema version" => d => d["schemaVersion"] = 2,
      "unknown member" => d => d["extra"] = 1,
      "missing member" => d => d.Remove("results"),
      "null member" => d => d["resolvers"] = null,
      "epoch" => d => d["daemonEpoch"] = "not-an-epoch",
      "empty session id" => d => d["sessionId"] = " ",
      "resolver key" => d => d["resolvers"]![0]!["key"] = "ABC",
      "resolver identity" => d => d["resolvers"]![0]!["optionsIdentity"] = "short",
      "result key" => d => d["results"]![0]!["key"] = new string('G', 64),
      "duplicate resolver" => d => d["resolvers"]!.AsArray().Add(d["resolvers"]![0]!.DeepClone()),
      "too many results" => AddFourResults,
      "relative uri" => d => d["resolvers"]![0]!["entries"]![0]!["uri"] = "a/b.dfy",
      "non canonical uri" => d => d["resolvers"]![0]!["entries"]![0]!["uri"] = "file:///a/x y.dfy",
      "missing text" => d => d["resolvers"]![0]!["entries"]![0]!.AsObject().Remove("text"),
      "duplicate entry" => d => d["resolvers"]![0]!["entries"]!.AsArray().Add(d["resolvers"]![0]!["entries"]![0]!.DeepClone()),
      "negative compilations" => d => d["results"]![0]!["compilations"] = -1,
      "fractional count" => d => d["results"]![0]!["compilations"] = 1.5,
      "empty checksum" => d => d["results"]![0]!["entries"]![0]!["checksum"] = "",
      "empty dependencies" => d => d["results"]![0]!["entries"]![0]!["dependencies"] = "",
      "bad base64" => d => d["results"]![0]!["entries"]![0]!["dependencies"] = "!!",
      "long dependencies" => d => d["results"]![0]!["entries"]![0]!["dependencies"] = Convert.ToBase64String(new byte[65]),
      "negative resources" => d => d["results"]![0]!["entries"]![0]!["resources"] = -1,
      "no splits" => d => d["results"]![0]!["entries"]![0]!["splits"] = new JsonArray(),
      "null split" => d => d["results"]![0]!["entries"]![0]!["splits"] = new JsonArray((JsonNode?)null),
      "integer solver" => d => d["results"]![0]!["entries"]![0]!["splits"]![0]!["solverUsed"] = 1,
      "unknown solver" => d => d["results"]![0]!["entries"]![0]!["splits"]![0]!["solverUsed"] = "nothing",
      "bad time" => d => d["results"]![0]!["entries"]![0]!["start"] = "yesterday",
      "negative run time" => d => d["results"]![0]!["entries"]![0]!["splits"]![0]!["runTime"] = "-00:00:01",
      "null assertion" => d => d["results"]![0]!["entries"]![0]!["splits"]![0]!["assertions"] = new JsonArray((JsonNode?)null),
      "missing assertion type" => d => d["results"]![0]!["entries"]![0]!["splits"]![0]!["assertions"]![0]!.AsObject().Remove("type"),
      "duplicate id" => d => d["results"]![0]!["entries"]!.AsArray().Add(d["results"]![0]!["entries"]![0]!.DeepClone()),
      "null entry" => d => d["results"]![0]!["entries"]!.AsArray().Add(null),
      _ => throw new ArgumentException(name)
    });
    mutate(document);
    Assert.Throws<Transfer.TransferRejectedException>(() => Parse(document.ToJsonString()));
  }

  private static Implementation Identity(string checksum = "body", byte dependency = 1) =>
    new(Microsoft.Boogie.Token.NoToken, "method", [], [], [], [], new List<Block>(),
      new QKeyValue(Microsoft.Boogie.Token.NoToken, "id", ["stable-id"],
        new QKeyValue(Microsoft.Boogie.Token.NoToken, "checksum", [checksum], null))) {
      DependenciesCollected = true,
      MD5DependencyChecksum_ = [dependency]
    };

  private static AssertCmd Assertion(int line) => new(new Microsoft.Boogie.Token(line, 1), Expr.True, null);

  private static ImplementationRunResult Success(Implementation implementation) => new(implementation) {
    VcOutcome = VcOutcome.Correct,
    Start = DateTime.UnixEpoch,
    End = DateTime.UnixEpoch.AddSeconds(2),
    Elapsed = TimeSpan.FromSeconds(1),
    ResourceCount = 13,
    ProofObligationCountAfter = 1,
    RunResults = [new VerificationRunResult(1, 0, DateTime.UnixEpoch, SolverOutcome.Valid,
      TimeSpan.FromSeconds(1), 1, [], [Assertion(3)], Array.Empty<TrackedNodeComponent>(), 13, SolverKind.Z3,
      Array.Empty<Microsoft.Boogie.Declaration>())]
  };

  // A fake solver's roster, transferred through the wire document, warms a child like an in-process clone does.
  [Fact]
  public async Task WireRoundTripKeepsNativeReuseAuthorityWithoutSolverStarts() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    var sourceResult = Success(identity).RunResults[0];
    var coldTask = new FakeTask(sourceResult, cached: false);
    var completion = new AnalysisSessionCommand.NativeImplementationCompletion(parent.PublishSuccessful);
    completion.Register(identity, new Dictionary<IVerificationTask, int> { [coldTask] = 0 });
    var cold = await new AnalysisSessionCommand.NativeTaskEntry(coldTask, () => sourceResult.Asserts)
      .Wait(CancellationToken.None, () => { });
    completion.Complete(identity, coldTask, cold.Result);
    Assert.Equal(1, coldTask.SolverStarts);

    using var cloned = parent.Clone(out var cloneCount);
    var document = new Transfer.TransferDocument(1, Guid.NewGuid().ToString("N"), "default", Guid.NewGuid().ToString("N"), Toolchain,
      [], [new Transfer.ResultTransfer(new string('3', 64), 1, parent.ExportSnapshots().ToArray())]);
    var received = Parse(Transfer.Serialize(document));
    using var imported = NativeVerificationCache.Restore(received.Results[0].Entries, out var importCount);
    Assert.Equal(cloneCount, importCount);
    Assert.Equal(1, importCount);

    foreach (var (cache, line) in new[] { (cloned, 13), (imported, 13) }) {
      var native = cache.Lookup(Identity(), false, out var priority)!;
      Assert.Equal(NativeVerificationCache.ReusePriority, priority);
      var task = new FakeTask(native.RunResults[0], cached: true);
      var current = Assertion(line);
      var reused = await new AnalysisSessionCommand.NativeTaskEntry(task, () => [current]).Wait(CancellationToken.None, () => { });
      Assert.True(reused.Reused);
      Assert.False(reused.Started);
      Assert.Equal(0, task.SolverStarts);
      Assert.Same(current, Assert.Single(reused.Result.Asserts));
      Assert.Equal(cold.Result.ResourceCount, reused.Result.ResourceCount);
      Assert.Equal(cold.Result.RunTime, reused.Result.RunTime);
      Assert.Equal(cold.Result.SolverUsed, reused.Result.SolverUsed);
    }
    // Native lookup stays authoritative: changed checksum or dependency bytes still miss.
    foreach (var changed in new[] { Identity("changed"), Identity("body", 2) }) {
      imported.Lookup(changed, false, out var priority);
      Assert.NotEqual(NativeVerificationCache.ReusePriority, priority);
    }
    // The parent is untouched by exporting it.
    Assert.NotNull(parent.Lookup(Identity(), false, out var parentPriority));
    Assert.Equal(NativeVerificationCache.ReusePriority, parentPriority);
    Assert.Equal(1, parent.ExportSnapshots().Count);
  }

  private sealed class FakeTask(VerificationRunResult result, bool cached) : IVerificationTask {
    public int SolverStarts { get; private set; }
    public IVerificationStatus CacheStatus => cached ? new Completed(result) : new Stale();
    public ManualSplit Split => null!;
    public IToken ScopeToken => Microsoft.Boogie.Token.NoToken;
    public string ScopeId => "stable-id";
    public IToken Token => Microsoft.Boogie.Token.NoToken;
    public bool IsIdle => true;
    public IVerificationTask FromSeed(int seed) => this;
    public void Cancel() => throw new InvalidOperationException("The synchronous fake solver never needs cancellation.");
    public IObservable<IVerificationStatus> TryRun() {
      if (!cached) {
        SolverStarts++;
      }
      return Observable.Return<IVerificationStatus>(new Completed(result));
    }
  }
}
