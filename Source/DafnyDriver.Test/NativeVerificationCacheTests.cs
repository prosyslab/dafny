using Microsoft.Boogie;
using Microsoft.Dafny;
using System.Reactive.Linq;
using VC;
using Xunit;

namespace DafnyDriver.Test;

public class NativeVerificationCacheTests {
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
      TimeSpan.FromSeconds(1), 1, [], [Assertion(3)], Array.Empty<TrackedNodeComponent>(), 13, null,
      Array.Empty<Microsoft.Boogie.Declaration>())]
  };

  // Two inherited caches preserve the original native identity and clear independently.
  [Fact]
  public void TwoChildrenKeepNativeSkipAuthorityAndIndependentOwnership() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    using var first = parent.Clone(out var firstCount);
    using var second = parent.Clone(out var secondCount);
    Assert.Equal(1, firstCount);
    Assert.Equal(1, secondCount);
    first.Clear();
    Assert.Null(first.Lookup(Identity(), false, out var firstPriority));
    Assert.NotEqual(NativeVerificationCache.ReusePriority, firstPriority);
    Assert.NotNull(parent.Lookup(Identity(), false, out var parentPriority));
    Assert.NotNull(second.Lookup(Identity(), false, out var secondPriority));
    Assert.Equal(NativeVerificationCache.ReusePriority, parentPriority);
    Assert.Equal(NativeVerificationCache.ReusePriority, secondPriority);
    parent.Dispose();
    first.Dispose();
    second.Dispose();
  }

  // A requesting child's changed checksum or dependency bytes cannot rewrite the stored identity.
  [Theory]
  [InlineData("changed", (byte)1)]
  [InlineData("body", (byte)2)]
  public void ChangedNativeInputsMissAfterTransfer(string checksum, byte dependency) {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    using var child = parent.Clone(out _);
    var result = child.Lookup(Identity(checksum, dependency), false, out var priority);
    Assert.NotNull(result);
    Assert.NotEqual(NativeVerificationCache.ReusePriority, priority);
    Assert.Equal("body", result.Checksum);
    Assert.Equal("01", result.DependenciesChecksum);
    Assert.NotNull(child.Lookup(Identity(), false, out var unchanged));
    Assert.Equal(NativeVerificationCache.ReusePriority, unchanged);
    parent.Dispose();
    child.Dispose();
  }

  // Detached results hold scalar shapes and rebind only to the current child's assertion objects.
  [Fact]
  public void TransferDropsParentAstAndRebasesCurrentLocations() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    var original = Success(identity);
    parent.PublishSuccessful(identity, original);
    using var child = parent.Clone(out _);
    var transferred = child.Lookup(Identity(), false, out var priority)!;
    Assert.Equal(NativeVerificationCache.ReusePriority, priority);
    var split = Assert.Single(transferred.RunResults);
    Assert.Empty(split.Asserts);
    Assert.Empty(split.CoveredElements);
    Assert.Empty(split.DeclarationsAfterPruning);
    Assert.Empty(split.CounterExamples);
    var current = Assertion(23);
    var rebound = AnalysisSessionCommand.NativeTaskEntry.RebaseCachedResult(split, [current]);
    Assert.Same(current, Assert.Single(rebound.Asserts));
    Assert.Equal(23, rebound.Asserts[0].tok.line);
    Assert.Same(original.RunResults[0].Asserts[0], Assert.Single(original.RunResults[0].Asserts));
    Assert.Equal(original.RunResults[0].RunTime, rebound.RunTime);
    Assert.Equal(13, rebound.ResourceCount);
    parent.Dispose();
    child.Dispose();
  }

  // Transferred shapes still reject assertion roster or description mismatches.
  [Fact]
  public void DetachedRebaseRejectsMismatchedAssertions() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    using var child = parent.Clone(out _);
    var split = child.Lookup(Identity(), false, out _)!.RunResults[0];
    Assert.Throws<InvalidOperationException>(() => AnalysisSessionCommand.NativeTaskEntry.RebaseCachedResult(split, []));
    var described = new AssertCmd(Microsoft.Boogie.Token.NoToken, Expr.True,
      new SubrangeCheck("", "int", "nat", true, true, null, null), null);
    Assert.Throws<InvalidOperationException>(() => AnalysisSessionCommand.NativeTaskEntry.RebaseCachedResult(split, [described]));
    parent.Dispose();
    child.Dispose();
  }

  // Native inserts retain their normal lookup behavior without becoming trusted export evidence.
  [Fact]
  public void OrdinaryInsertIsNotTransferable() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.Insert(identity, Success(identity));
    Assert.NotNull(parent.Lookup(Identity(), false, out var priority));
    Assert.Equal(NativeVerificationCache.ReusePriority, priority);
    using var child = parent.Clone(out var count);
    Assert.Equal(0, count);
    Assert.Null(child.Lookup(Identity(), false, out _));
    parent.Dispose();
    child.Dispose();
  }

  // Failed or partial proof results cannot enter the detached successful-result journal.
  [Theory]
  [InlineData(SolverOutcome.Invalid)]
  [InlineData(SolverOutcome.TimeOut)]
  [InlineData(SolverOutcome.Undetermined)]
  public void FailedProofCannotBePublished(SolverOutcome outcome) {
    using var cache = new NativeVerificationCache();
    var identity = Identity();
    var result = Success(identity);
    result.RunResults[0] = result.RunResults[0] with { Outcome = outcome };
    Assert.Throws<InvalidOperationException>(() => cache.PublishSuccessful(identity, result));
    cache.Clone(out var count).Dispose();
    Assert.Equal(0, count);
    cache.Dispose();
  }

  // The export journal expires conservatively with the native cache's ten-minute retention window.
  [Fact]
  public void ExpiredJournalDoesNotResurrectNativeResults() {
    var now = DateTime.UtcNow;
    using var parent = new NativeVerificationCache(() => now);
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    now = now.AddMinutes(10);
    using var child = parent.Clone(out var count);
    Assert.Equal(0, count);
    Assert.Null(child.Lookup(Identity(), false, out _));
    parent.Dispose();
    child.Dispose();
  }

  // The copied dependency checksum bytes cannot be changed by mutating a parent's implementation later.
  [Fact]
  public void CopiedOriginalDependencyBytesAreDetached() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    using var child = parent.Clone(out _);
    identity.MD5DependencyChecksum_[0] = 8;
    Assert.NotNull(child.Lookup(Identity(), false, out var priority));
    Assert.Equal(NativeVerificationCache.ReusePriority, priority);
    using var grandchild = child.Clone(out var count);
    Assert.Equal(1, count);
    Assert.NotNull(grandchild.Lookup(Identity(), false, out var inheritedPriority));
    Assert.Equal(NativeVerificationCache.ReusePriority, inheritedPriority);
    parent.Dispose();
    child.Dispose();
    grandchild.Dispose();
  }

  // Cancelled snapshot construction leaves the parent's successful native entry reusable.
  [Fact]
  public void CancelledTransferPreservesParent() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    Assert.ThrowsAny<OperationCanceledException>(() => parent.Clone(out _, new CancellationToken(true)));
    Assert.NotNull(parent.Lookup(Identity(), false, out var priority));
    Assert.Equal(NativeVerificationCache.ReusePriority, priority);
    parent.Dispose();
  }

  // Repeated clone/close cycles allocate cache timer owners only up to the concurrent owner count.
  [Fact]
  public void RepeatedCloneDisposalReusesNativeTimerOwners() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    parent.PublishSuccessful(identity, Success(identity));
    var before = NativeVerificationCache.AllocatedCaches;
    for (var index = 0; index < 16; index++) {
      using var child = parent.Clone(out var count);
      Assert.Equal(1, count);
      Assert.NotNull(child.Lookup(Identity(), false, out var priority));
      Assert.Equal(NativeVerificationCache.ReusePriority, priority);
    }
    Assert.InRange(NativeVerificationCache.AllocatedCaches, before, before + 1);
  }

  // An idempotent return cannot give two live wrappers the same cache or leak a prior owner's result.
  [Fact]
  public void DoubleDisposalCannotAliasAnotherLiveOwner() {
    var returned = new NativeVerificationCache();
    var identity = Identity();
    returned.PublishSuccessful(identity, Success(identity));
    returned.Dispose();
    returned.Dispose();
    Assert.Throws<ObjectDisposedException>(() => returned.Lookup(Identity(), false, out _));
    using var first = new NativeVerificationCache();
    using var second = new NativeVerificationCache();
    Assert.Null(first.Lookup(Identity(), false, out _));
    first.PublishSuccessful(identity, Success(identity));
    Assert.Null(second.Lookup(Identity(), false, out _));
    Assert.NotNull(first.Lookup(Identity(), false, out var priority));
    Assert.Equal(NativeVerificationCache.ReusePriority, priority);
  }

  // The session-only cache rejects the unsupported native program-snapshot mode before retaining ASTs.
  [Fact]
  public void ProgramSnapshotsCannotEnterTheReusableOwnerPool() {
    using var cache = new NativeVerificationCache();
    Assert.Throws<NotSupportedException>(() => cache.SetProgram("program", new Microsoft.Boogie.Program(),
      new System.Runtime.Caching.CacheItemPolicy()));
    Assert.Null(cache.CachedProgram("program"));
  }

  // A fake solver's complete native roster warms two children without starting another solver task.
  [Fact]
  public async Task CompleteNativeRosterTransfersReusableResultsToTwoChildren() {
    using var parent = new NativeVerificationCache();
    var identity = Identity();
    var sourceResult = Success(identity).RunResults[0];
    var coldTask = new FakeTask(sourceResult, cached: false);
    var completion = new AnalysisSessionCommand.NativeImplementationCompletion(parent.PublishSuccessful);
    completion.Register(identity, new Dictionary<IVerificationTask, int> { [coldTask] = 0 });
    var cold = await new AnalysisSessionCommand.NativeTaskEntry(coldTask, () => sourceResult.Asserts)
      .Wait(CancellationToken.None, () => { });
    completion.Complete(identity, coldTask, cold.Result);
    Assert.True(cold.Started);
    Assert.False(cold.Reused);
    Assert.Equal(1, coldTask.SolverStarts);

    foreach (var line in new[] { 13, 23 }) {
      using var child = parent.Clone(out var count);
      Assert.Equal(1, count);
      var native = child.Lookup(Identity(), false, out var priority)!;
      Assert.Equal(NativeVerificationCache.ReusePriority, priority);
      var task = new FakeTask(native.RunResults[0], cached: true);
      var current = Assertion(line);
      var reused = await new AnalysisSessionCommand.NativeTaskEntry(task, () => [current])
        .Wait(CancellationToken.None, () => { });
      Assert.True(reused.Reused);
      Assert.False(reused.Started);
      Assert.Equal(0, task.SolverStarts);
      Assert.Same(current, Assert.Single(reused.Result.Asserts));
      Assert.Equal(cold.Result.ResourceCount, reused.Result.ResourceCount);
      Assert.Equal(cold.Result.Outcome, reused.Result.Outcome);
      Assert.Equal(cold.Result.RunTime, reused.Result.RunTime);
      child.Dispose();
    }
    Assert.NotNull(parent.Lookup(Identity(), false, out var stillWarm));
    Assert.Equal(NativeVerificationCache.ReusePriority, stillWarm);
    parent.Dispose();
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
