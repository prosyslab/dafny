using System.Reactive.Subjects;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Xunit;

namespace DafnyDriver.Test;

public class NativeTaskEntryTests {
  private static readonly TimeSpan Timeout = TimeSpan.FromSeconds(5);
  private static VerificationRunResult Result(SolverOutcome outcome = SolverOutcome.Valid) => LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult(
    new VerificationRunResultPartialCopy(1, DateTime.UnixEpoch, TimeSpan.Zero, outcome,
      [], Array.Empty<TrackedNodeComponent>(), Array.Empty<Axiom>(), 0)).Result;

  // Timing evidence is opt-in even when a request fails before compilation.
  [Fact]
  public async Task TimingEvidenceRequiresRequestOptIn() {
    using var session = new AnalysisSessionCommand.Session();
    var plain = await session.Execute(new AnalysisSessionCommand.Request("plain"), CancellationToken.None);
    var profiled = await session.Execute(new AnalysisSessionCommand.Request("profiled", ProfileTimings: true), CancellationToken.None);
    var normal = System.Text.Json.JsonSerializer.SerializeToElement(plain.NativeEvidence, AnalysisSessionCommand.JsonOptions);
    var timed = System.Text.Json.JsonSerializer.SerializeToElement(profiled.NativeEvidence, AnalysisSessionCommand.JsonOptions);
    Assert.False(normal.TryGetProperty("timings", out _));
    var timings = timed.GetProperty("timings");
    Assert.Equal(1, timings.GetProperty("schemaVersion").GetInt32());
    Assert.Equal(System.Text.Json.JsonValueKind.Null, timings.GetProperty("compilationReused").ValueKind);
    Assert.True(timings.GetProperty("durationsSeconds").GetProperty("admission_wait").GetDouble() >= 0);
  }

  // Fresh snapshot parsing and resolution are measured only for the request that performs them.
  [Fact]
  public async Task SnapshotResolutionTimingsDoNotReplayOnReuse() {
    const string cwd = "/workspace/session-profiling";
    const string path = cwd + "/Snapshot.dfy";
    var snapshots = new Dictionary<string, string> { [path] = "method M() {}" };
    using var session = new AnalysisSessionCommand.Session();
    async Task<(AnalysisSessionCommand.Response Response, System.Text.Json.JsonElement Timings)> Resolve(string id) {
      var response = await session.Execute(new AnalysisSessionCommand.Request(id, ["resolve", path], cwd,
        SourceSnapshots: snapshots, ProfileTimings: true), CancellationToken.None);
      var evidence = System.Text.Json.JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions);
      return (response, evidence.GetProperty("timings"));
    }
    var cold = await Resolve("cold");
    Assert.True(cold.Response.Returncode == 0, cold.Response.Stderr);
    Assert.False(cold.Timings.GetProperty("compilationReused").GetBoolean());
    var phases = cold.Timings.GetProperty("durationsSeconds");
    Assert.True(phases.GetProperty("parse").GetDouble() >= 0);
    Assert.True(phases.GetProperty("resolve").GetDouble() >= 0);

    var warm = await Resolve("warm");
    Assert.True(warm.Response.Returncode == 0, warm.Response.Stderr);
    Assert.True(warm.Timings.GetProperty("compilationReused").GetBoolean());
    phases = warm.Timings.GetProperty("durationsSeconds");
    Assert.False(phases.TryGetProperty("parse", out _));
    Assert.False(phases.TryGetProperty("resolve", out _));
  }

  // A cancelled subscriber detaches without cancelling another subscriber's native task.
  [Fact]
  public async Task OneSubscriberCancellationPreservesOtherSubscriber() {
    var native = new FakeTask();
    var entry = new AnalysisSessionCommand.NativeTaskEntry(native);
    using var cancellation = new CancellationTokenSource();
    var retired = 0;
    var first = entry.Wait(cancellation.Token, () => retired++);
    var second = entry.Wait(CancellationToken.None, () => retired++);

    await cancellation.CancelAsync();
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first.WaitAsync(Timeout));
    Assert.Equal(0, native.CancelCount);
    Assert.Equal(0, retired);
    native.Complete(Result());
    var completed = await second.WaitAsync(Timeout);

    Assert.Equal(SolverOutcome.Valid, completed.Result.Outcome);
    Assert.Equal(1, native.RunCount);
  }

  // Last-subscriber cancellation waits for native termination before releasing ownership.
  [Fact]
  public async Task LastCancellationWaitsForNativeDrainAndRejectsNewJoins() {
    var native = new FakeTask();
    var entry = new AnalysisSessionCommand.NativeTaskEntry(native);
    using var cancellation = new CancellationTokenSource();
    var retired = 0;
    var waiting = entry.Wait(cancellation.Token, () => retired++);

    await cancellation.CancelAsync();
    await native.CancelRequested.Task.WaitAsync(Timeout);
    Assert.False(waiting.IsCompleted);
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => entry.Wait(CancellationToken.None, () => retired++).WaitAsync(Timeout));
    native.AcknowledgeCancellation();
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => waiting.WaitAsync(Timeout));

    Assert.Equal(1, retired);
    Assert.Equal(1, native.CancelCount);
  }

  // Completed native work is replayed without claiming another physical solver start.
  [Fact]
  public async Task CompletedFutureReplayReportsReuse() {
    var native = new FakeTask();
    var entry = new AnalysisSessionCommand.NativeTaskEntry(native);
    var first = entry.Wait(CancellationToken.None, () => { });
    native.Complete(Result());
    var cold = await first.WaitAsync(Timeout);
    var warm = await entry.Wait(CancellationToken.None, () => { }).WaitAsync(Timeout);

    Assert.True(cold.Started);
    Assert.True(cold.Fresh);
    Assert.False(cold.Reused);
    Assert.False(warm.Started);
    Assert.True(warm.Reused);
    Assert.Equal(1, native.RunCount);
  }

  // A completed status without terminal stream completion cannot win a later cancellation.
  [Fact]
  public async Task CancellationBeforeTerminalStreamDoesNotPublishSuccess() {
    var native = new FakeTask();
    var entry = new AnalysisSessionCommand.NativeTaskEntry(native);
    using var cancellation = new CancellationTokenSource();
    var waiting = entry.Wait(cancellation.Token, () => { });
    native.EmitCompleted(Result());
    await cancellation.CancelAsync();
    await native.CancelRequested.Task.WaitAsync(Timeout);
    native.AcknowledgeCancellation();

    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => waiting.WaitAsync(Timeout));
  }

  [Fact]
  public void NativeCachePublicationRequiresEveryPreparedSplit() {
    var implementation = Implementation();
    var first = new FakeTask();
    var second = new FakeTask();
    var published = new List<ImplementationRunResult>();
    var completion = new AnalysisSessionCommand.NativeImplementationCompletion((_, result) => published.Add(result));
    completion.Register(implementation, new Dictionary<IVerificationTask, int> { [first] = 0, [second] = 1 });
    var later = Result();
    completion.Complete(implementation, second, later);
    Assert.Empty(published);
    var earlier = Result();
    completion.Complete(implementation, first, earlier);
    var aggregate = Assert.Single(published);
    Assert.Equal(new[] { earlier, later }, aggregate.RunResults);
    completion.Complete(implementation, second, later);
    Assert.Single(published);
  }

  [Theory]
  [InlineData(SolverOutcome.Invalid)]
  [InlineData(SolverOutcome.Undetermined)]
  [InlineData(SolverOutcome.TimeOut)]
  [InlineData(SolverOutcome.Bounded)]
  public void NativeCacheDoesNotPublishIncompleteProofOutcomes(SolverOutcome outcome) {
    var implementation = Implementation();
    var task = new FakeTask();
    var published = false;
    var completion = new AnalysisSessionCommand.NativeImplementationCompletion((_, _) => published = true);
    completion.Register(implementation, new Dictionary<IVerificationTask, int> { [task] = 0 });
    completion.Complete(implementation, task, Result(outcome));
    Assert.False(published);
  }

  [Fact]
  public void NativeCacheRejectsChangedRosterAndUnownedCompletion() {
    var implementation = Implementation();
    var task = new FakeTask();
    var other = new FakeTask();
    var completion = new AnalysisSessionCommand.NativeImplementationCompletion((_, _) => { });
    Assert.Throws<InvalidOperationException>(() => completion.Register(implementation,
      new Dictionary<IVerificationTask, int> { [task] = 1 }));
    completion.Register(implementation, new Dictionary<IVerificationTask, int> { [task] = 0 });
    Assert.Throws<InvalidOperationException>(() => completion.Register(implementation,
      new Dictionary<IVerificationTask, int> { [other] = 0 }));
    Assert.Throws<InvalidOperationException>(() => completion.Complete(implementation, other, Result()));
  }

  private static AssertCmd Assertion(int line, Microsoft.Boogie.ProofObligationDescription? description = null) =>
    description == null
      ? new AssertCmd(new Microsoft.Boogie.Token(line, 1), Expr.True, null)
      : new AssertCmd(new Microsoft.Boogie.Token(line, 1), Expr.True, description, null);

  private static Microsoft.Boogie.ProofObligationDescription Other() => new SubrangeCheck("", "int", "nat", true, true, null, null);

  private static VerificationRunResult Reused(params AssertCmd[] assertions) {
    return Result() with { Asserts = assertions.ToList(), ResourceCount = 7 };
  }

  // A reused result reports the current assertions and keeps every other cached field.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task ReusedResultIsRebasedOntoCurrentAssertions(bool nullStream) {
    var old = Reused(Assertion(3), Assertion(5, Other()));
    var current = new List<AssertCmd> { Assertion(13), Assertion(15, Other()) };
    var native = new FakeTask(old, nullStream);
    var entry = new AnalysisSessionCommand.NativeTaskEntry(native, () => current);
    var wait = entry.Wait(CancellationToken.None, () => { });
    if (!nullStream) {
      native.Complete(old);
    }
    var reused = await wait.WaitAsync(Timeout);

    Assert.True(reused.Reused);
    Assert.False(reused.Started);
    Assert.False(reused.Fresh);
    Assert.Equal(current, reused.Result.Asserts);
    Assert.Equal(new[] { 13, 15 }, reused.Result.Asserts.Select(assertion => assertion.tok.line));
    Assert.Equal(7, reused.Result.ResourceCount);
    Assert.Equal(old.Outcome, reused.Result.Outcome);
    Assert.Equal(old.StartTime, reused.Result.StartTime);
    // The cached object is not mutated; another reader of the cache still sees its own assertions.
    Assert.Equal(new[] { 3, 5 }, old.Asserts.Select(assertion => assertion.tok.line));
  }

  // A reused result that disagrees with the current split fails the task instead of reporting old tokens.
  [Theory]
  [InlineData("count")]
  [InlineData("description")]
  [InlineData("order")]
  public async Task ReusedResultMismatchFailsTheTask(string mismatch) {
    var old = Reused(Assertion(3), Assertion(5, Other()));
    var current = mismatch switch {
      "count" => new List<AssertCmd> { Assertion(13) },
      "description" => new List<AssertCmd> { Assertion(13), Assertion(15) },
      _ => new List<AssertCmd> { Assertion(15, Other()), Assertion(13) }
    };
    var entry = new AnalysisSessionCommand.NativeTaskEntry(new FakeTask(old, true), () => current);
    await Assert.ThrowsAsync<InvalidOperationException>(() => entry.Wait(CancellationToken.None, () => { }).WaitAsync(Timeout));
    // The failure is the task's result; a later subscriber sees the same error, never the old tokens.
    await Assert.ThrowsAsync<InvalidOperationException>(() => entry.Wait(CancellationToken.None, () => { }).WaitAsync(Timeout));
  }

  private static Implementation Implementation() => new(Microsoft.Boogie.Token.NoToken, "synthetic",
    [], [], [], [], new List<Block>(), new QKeyValue(Microsoft.Boogie.Token.NoToken, "checksum", ["synthetic"], null)) {
    DependenciesCollected = true
  };

  private sealed class FakeTask(VerificationRunResult? cached = null, bool cachedHasNoStream = false) : IVerificationTask {
    private readonly Subject<IVerificationStatus> updates = new();
    public TaskCompletionSource CancelRequested { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);
    public int CancelCount { get; private set; }
    public int RunCount { get; private set; }
    public IVerificationTask FromSeed(int seed) => this;
    public IVerificationStatus CacheStatus => cached == null ? new Stale() : new Completed(cached);
    public ManualSplit Split => null!;
    public IToken ScopeToken => Microsoft.Boogie.Token.NoToken;
    public string ScopeId => "synthetic";
    public IToken Token => Microsoft.Boogie.Token.NoToken;
    public bool IsIdle => false;
    public IObservable<IVerificationStatus> TryRun() { RunCount++; return cachedHasNoStream ? null! : updates; }
    public void Cancel() { CancelCount++; CancelRequested.TrySetResult(); }
    public void EmitCompleted(VerificationRunResult result) => updates.OnNext(new Completed(result));
    public void Complete(VerificationRunResult result) { EmitCompleted(result); updates.OnCompleted(); }
    public void AcknowledgeCancellation() => updates.OnError(new OperationCanceledException());
  }
}
