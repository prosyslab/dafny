#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Caching;
using System.Runtime.CompilerServices;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using VC;

namespace Microsoft.Dafny;

/// <summary>
/// The native cache remains the only reuse authority. This journal contains detached copies of
/// complete successful results published by the session's native completion bookkeeping.
/// </summary>
internal sealed class NativeVerificationCache : IVerificationResultCache, IDisposable {
  // Boogie 3.5.5's internal Priority.SKIP (also used by ExecutionEngine.GetCachedVerificationResult).
  internal const int ReusePriority = int.MaxValue;
  internal sealed record AssertionShape(string Type, string? Success, string? Failure) {
    internal static AssertionShape Capture(AssertCmd assertion) => new(
      assertion.GetType().FullName!, assertion.Description?.SuccessDescription, assertion.Description?.FailureDescription);
  }

  private sealed record Split(int VcNum, int Iteration, DateTime StartTime, TimeSpan RunTime,
    int MaxCounterExamples, int ResourceCount, SolverKind? SolverUsed, AssertionShape[] Assertions) {
    public VerificationRunResult Restore() {
      var result = new VerificationRunResult(VcNum, Iteration, StartTime, SolverOutcome.Valid, RunTime,
        MaxCounterExamples, [], [], Array.Empty<TrackedNodeComponent>(), ResourceCount, SolverUsed,
        Array.Empty<Microsoft.Boogie.Declaration>());
      DetachedAssertions.Add(result, Assertions);
      return result;
    }
  }

  private sealed record Snapshot(string Id, string Name, string Checksum, byte[] Dependencies,
    string? ProgramId, DateTime Start, DateTime End, TimeSpan Elapsed, int Resources,
    int ObligationsBefore, int ObligationsAfter, Split[] Splits) {
    public Implementation Identity() => new(Token.NoToken, Name, [], [], [], [], new List<Block>(),
      new QKeyValue(Token.NoToken, "id", [Id], new QKeyValue(Token.NoToken, "checksum", [Checksum], null))) {
      DependenciesCollected = true,
      MD5DependencyChecksum_ = Dependencies.ToArray()
    };

    public ImplementationRunResult Restore(Implementation identity) => new(identity, ProgramId) {
      VcOutcome = VcOutcome.Correct,
      Start = Start,
      End = End,
      Elapsed = Elapsed,
      ResourceCount = Resources,
      ProofObligationCountBefore = ObligationsBefore,
      ProofObligationCountAfter = ObligationsAfter,
      RunResults = Splits.Select(split => split.Restore()).ToList()
    };
  }

  // Keys are transferred run records, never a parent AST. Values contain scalar shape data only.
  private static readonly ConditionalWeakTable<VerificationRunResult, AssertionShape[]> DetachedAssertions = new();
  private static readonly TimeSpan NativeSlidingExpiration = TimeSpan.FromMinutes(10);
  private static readonly Regex AllResultKeys = new(".*", RegexOptions.CultureInvariant);
  // Boogie's sealed cache has no disposal API, but owns MemoryCache timers. Reuse drained owners
  // so historical clone/close cycles do not allocate an unbounded number of timer owners.
  private static readonly object PoolGate = new();
  private static readonly Stack<VerificationResultCache> Pool = new();
  private static int allocatedCaches;
  private readonly VerificationResultCache inner;
  private readonly Dictionary<string, (Snapshot Snapshot, DateTime Access)> journal = new(StringComparer.Ordinal);
  private readonly object gate = new();
  private readonly Func<DateTime> utcNow;
  private bool disposed;

  public NativeVerificationCache(Func<DateTime>? utcNow = null) {
    this.utcNow = utcNow ?? (() => DateTime.UtcNow);
    lock (PoolGate) {
      if (Pool.TryPop(out var cached)) {
        inner = cached;
      } else {
        inner = new VerificationResultCache();
        allocatedCaches++;
      }
    }
  }

  internal static int AllocatedCaches {
    get {
      lock (PoolGate) {
        return allocatedCaches;
      }
    }
  }

  private void CheckOwner() => ObjectDisposedException.ThrowIf(disposed, this);

  internal static IReadOnlyList<AssertionShape> Shapes(VerificationRunResult result) =>
    DetachedAssertions.TryGetValue(result, out var shapes) ? shapes : result.Asserts.Select(AssertionShape.Capture).ToArray();

  public Microsoft.Boogie.Program? CachedProgram(string programId) {
    lock (gate) {
      CheckOwner();
      return inner.CachedProgram(programId);
    }
  }
  public void SetProgram(string programId, Microsoft.Boogie.Program program, CacheItemPolicy policy) {
    // Session engines pin VerifySnapshots=1. Boogie only uses its program cache above that mode;
    // its public Clear cannot empty that cache, so it must never receive branch-owned AST graphs.
    throw new NotSupportedException("Native analysis sessions support result-cache snapshots only.");
  }
  public int VerificationPriority(Implementation implementation, bool runDiagnosticsOnTimeout) {
    Lookup(implementation, runDiagnosticsOnTimeout, out var priority);
    return priority;
  }
  public ImplementationRunResult? Lookup(Implementation implementation, bool runDiagnosticsOnTimeout, out int priority) {
    lock (gate) {
      CheckOwner();
      var result = inner.Lookup(implementation, runDiagnosticsOnTimeout, out priority);
      if (result != null && journal.TryGetValue(implementation.Id, out var entry)) {
        journal[implementation.Id] = (entry.Snapshot, utcNow());
      }
      return result;
    }
  }

  // Ordinary native inserts retain their native behavior but cannot manufacture transferable evidence.
  public void Insert(Implementation implementation, ImplementationRunResult result) {
    lock (gate) {
      CheckOwner();
      journal.Remove(implementation.Id);
      inner.Insert(implementation, result);
    }
  }

  internal void PublishSuccessful(Implementation implementation, ImplementationRunResult result) {
    if (result.VcOutcome != VcOutcome.Correct || result.ErrorBeforeVerification != null || result.Errors.Count != 0 ||
        result.RunResults is not { Count: > 0 } runs ||
        runs.Any(run => run.Outcome != SolverOutcome.Valid || run.CounterExamples.Count != 0) ||
        string.IsNullOrEmpty(implementation.Checksum) || implementation.MD5DependencyChecksum == null) {
      throw new InvalidOperationException("Only complete successful native results can be transferred.");
    }
    var snapshot = new Snapshot(implementation.Id, implementation.Name, implementation.Checksum,
      implementation.MD5DependencyChecksum.ToArray(), result.ProgramId, result.Start, result.End, result.Elapsed,
      result.ResourceCount, result.ProofObligationCountBefore, result.ProofObligationCountAfter,
      runs.Select(run => new Split(run.VcNum, run.Iteration, run.StartTime, run.RunTime, run.MaxCounterExamples,
        run.ResourceCount, run.SolverUsed, Shapes(run).ToArray())).ToArray());
    lock (gate) {
      CheckOwner();
      inner.Insert(implementation, result);
      journal[implementation.Id] = (snapshot, utcNow());
      PruneExpired();
    }
  }

  private void PruneExpired() {
    var now = utcNow();
    foreach (var id in journal.Where(entry => now - entry.Value.Access >= NativeSlidingExpiration)
               .Select(entry => entry.Key).ToArray()) {
      journal.Remove(id);
    }
  }

  internal NativeVerificationCache Clone(out int copiedEntries, CancellationToken cancellationToken = default) {
    cancellationToken.ThrowIfCancellationRequested();
    var clone = new NativeVerificationCache(utcNow);
    try {
      cancellationToken.ThrowIfCancellationRequested();
      lock (gate) {
        CheckOwner();
        PruneExpired();
        foreach (var entry in journal.Values) {
          cancellationToken.ThrowIfCancellationRequested();
          var snapshot = entry.Snapshot;
          var identity = snapshot.Identity();
          // Check the real native cache, including expiration, before exporting the journal entry.
          var current = inner.Lookup(identity, false, out var priority);
          if (current == null || priority != ReusePriority || current.VcOutcome != VcOutcome.Correct) {
            continue;
          }
          var copied = snapshot with {
            Dependencies = snapshot.Dependencies.ToArray(),
            Splits = snapshot.Splits.Select(split => {
              cancellationToken.ThrowIfCancellationRequested();
              return split with { Assertions = split.Assertions.ToArray() };
            }).ToArray()
          };
          var childIdentity = copied.Identity();
          clone.inner.Insert(childIdentity, copied.Restore(childIdentity));
          clone.journal.Add(copied.Id, (copied, utcNow()));
        }
      }
      cancellationToken.ThrowIfCancellationRequested();
      copiedEntries = clone.journal.Count;
      return clone;
    } catch {
      clone.Dispose();
      throw;
    }
  }

  public void Clear() {
    lock (gate) {
      CheckOwner();
      inner.RemoveMatchingKeys(AllResultKeys);
      journal.Clear();
    }
  }

  public void Dispose() {
    lock (gate) {
      if (disposed) {
        return;
      }
      // MemoryCache.Trim can decline a concurrent flush; explicit removals under this exclusive
      // wrapper owner are required before another branch rents the native instance.
      inner.RemoveMatchingKeys(AllResultKeys);
      journal.Clear();
      disposed = true;
      lock (PoolGate) {
        Pool.Push(inner);
      }
    }
  }
}
