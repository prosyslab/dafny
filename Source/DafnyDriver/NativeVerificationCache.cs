#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Caching;
using System.Runtime.CompilerServices;
using System.Text.Json.Serialization;
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
  internal sealed record AssertionShape([property: JsonRequired] string Type, [property: JsonRequired] string? Success,
    [property: JsonRequired] string? Failure) {
    internal static AssertionShape Capture(AssertCmd assertion) => new(
      assertion.GetType().FullName!, assertion.Description?.SuccessDescription, assertion.Description?.FailureDescription);
  }

  internal sealed record Split([property: JsonRequired] int VcNum, [property: JsonRequired] int Iteration,
    [property: JsonRequired] DateTime StartTime, [property: JsonRequired] TimeSpan RunTime,
    [property: JsonRequired] int MaxCounterExamples, [property: JsonRequired] int ResourceCount,
    [property: JsonRequired] SolverKind? SolverUsed, [property: JsonRequired] AssertionShape[] Assertions) {
    public VerificationRunResult Restore() {
      var result = new VerificationRunResult(VcNum, Iteration, StartTime, SolverOutcome.Valid, RunTime,
        MaxCounterExamples, [], [], Array.Empty<TrackedNodeComponent>(), ResourceCount, SolverUsed,
        Array.Empty<Microsoft.Boogie.Declaration>());
      DetachedAssertions.Add(result, Assertions);
      return result;
    }
  }

  internal sealed record Snapshot([property: JsonRequired] string Id, [property: JsonRequired] string Name,
    [property: JsonRequired] string Checksum, [property: JsonRequired] byte[] Dependencies,
    [property: JsonRequired] string? ProgramId, [property: JsonRequired] DateTime Start, [property: JsonRequired] DateTime End,
    [property: JsonRequired] TimeSpan Elapsed, [property: JsonRequired] int Resources,
    [property: JsonRequired] int ObligationsBefore, [property: JsonRequired] int ObligationsAfter,
    [property: JsonRequired] Split[] Splits) {
    internal const int MaximumDependencyBytes = 64;
    internal const int MaximumTextLength = 8192;

    /// <summary>Checks the shape of a snapshot that came from outside this process. Throws FormatException.</summary>
    public void Validate() {
      static void Text(string? value, string name, bool required = true) {
        if (value == null ? required : value.Length > MaximumTextLength || required && value.Length == 0) {
          throw new FormatException($"{name} must be a{(required ? " nonempty" : "")} string of at most {MaximumTextLength} characters.");
        }
      }
      Text(Id, "id");
      Text(Name, "name");
      Text(Checksum, "checksum");
      Text(ProgramId, "programId", false);
      if (Dependencies == null || Dependencies.Length is < 1 or > MaximumDependencyBytes) {
        throw new FormatException($"dependencies must hold 1 to {MaximumDependencyBytes} bytes.");
      }
      if (Resources < 0 || ObligationsBefore < 0 || ObligationsAfter < 0 || Elapsed < TimeSpan.Zero) {
        throw new FormatException("A snapshot count or duration is negative.");
      }
      if (Splits == null || Splits.Length == 0 || Splits.Any(split => split == null)) {
        throw new FormatException("A snapshot needs at least one split.");
      }
      foreach (var split in Splits) {
        if (split.VcNum < 0 || split.Iteration < 0 || split.MaxCounterExamples < 0 || split.ResourceCount < 0 ||
            split.RunTime < TimeSpan.Zero) {
          throw new FormatException("A split count or duration is negative.");
        }
        if (split.SolverUsed is { } solver && !Enum.IsDefined(solver)) {
          throw new FormatException("A split names an unknown solver kind.");
        }
        if (split.Assertions == null || split.Assertions.Any(shape => shape == null)) {
          throw new FormatException("A split needs an assertion roster.");
        }
        foreach (var shape in split.Assertions) {
          Text(shape.Type, "assertion type");
          Text(shape.Success, "assertion success description", false);
          Text(shape.Failure, "assertion failure description", false);
        }
      }
    }

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
  /// <summary>Default bound on retained results per cache (one per implementation id).</summary>
  internal const int DefaultCapacity = 4096;
  // Boogie's own priorities (internal class Priority in Boogie 3.5.5).
  internal const int MissingPriority = 3;
  internal const int ChangedPriority = 2;
  internal const int DependencyChangedPriority = 1;

  /// <summary>
  /// Results keyed by implementation id, bounded by entry count with least-recently-used eviction. Boogie's
  /// <see cref="VerificationResultCache"/> stores them in a <c>MemoryCache</c> with a fixed 10-minute sliding
  /// expiration, so results of a long cold run, or of a session idle during a long model turn, were dropped by
  /// idle time alone. Lookup and insert reproduce Boogie's semantics exactly; only retention differs.
  /// </summary>
  private sealed class ResultStore(int capacity) {
    private readonly Dictionary<string, LinkedListNode<(string Id, ImplementationRunResult Result)>> entries =
      new(StringComparer.Ordinal);
    private readonly LinkedList<(string Id, ImplementationRunResult Result)> recency = new();
    public int Count => entries.Count;

    public ImplementationRunResult? Get(string id) {
      if (!entries.TryGetValue(id, out var node)) {
        return null;
      }
      recency.Remove(node);
      recency.AddFirst(node);
      return node.Value.Result;
    }

    /// <summary>Stores a result and returns the ids evicted to stay within the bound.</summary>
    public IReadOnlyList<string> Set(string id, ImplementationRunResult result) {
      if (entries.Remove(id, out var existing)) {
        recency.Remove(existing);
      }
      entries[id] = recency.AddFirst((id, result));
      var evicted = new List<string>();
      while (entries.Count > capacity) {
        var oldest = recency.Last!;
        recency.RemoveLast();
        entries.Remove(oldest.Value.Id);
        evicted.Add(oldest.Value.Id);
      }
      return evicted;
    }

    public bool Contains(string id) => entries.ContainsKey(id);

    public void Clear() {
      entries.Clear();
      recency.Clear();
    }
  }

  private readonly int capacity;
  private readonly ResultStore inner;
  private readonly Dictionary<string, Snapshot> journal = new(StringComparer.Ordinal);
  private readonly object gate = new();
  private bool disposed;

  public NativeVerificationCache(int capacity = DefaultCapacity) {
    ArgumentOutOfRangeException.ThrowIfLessThan(capacity, 1);
    this.capacity = capacity;
    inner = new ResultStore(capacity);
  }

  internal int Count {
    get {
      lock (gate) {
        return inner.Count;
      }
    }
  }

  /// <summary>Transfer journal size and whether every journal entry is still in the store (test seam).</summary>
  internal (int Entries, bool WithinStore) Journal {
    get {
      lock (gate) {
        return (journal.Count, journal.Keys.All(inner.Contains));
      }
    }
  }

  private void CheckOwner() => ObjectDisposedException.ThrowIf(disposed, this);

  internal static IReadOnlyList<AssertionShape> Shapes(VerificationRunResult result) =>
    DetachedAssertions.TryGetValue(result, out var shapes) ? shapes : result.Asserts.Select(AssertionShape.Capture).ToArray();

  // Session engines pin VerifySnapshots=1, so Boogie never reads or writes a program snapshot.
  public Microsoft.Boogie.Program? CachedProgram(string programId) {
    lock (gate) {
      CheckOwner();
      return null;
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
      return LookupCore(implementation, runDiagnosticsOnTimeout, out priority);
    }
  }

  // Ordinary native inserts retain their native behavior but cannot manufacture transferable evidence.
  public void Insert(Implementation implementation, ImplementationRunResult result) {
    lock (gate) {
      CheckOwner();
      journal.Remove(implementation.Id);
      Store(implementation.Id, result);
    }
  }

  /// <summary>Boogie 3.5.5 <c>VerificationResultCache.Lookup</c>, over the bounded store.</summary>
  private ImplementationRunResult? LookupCore(Implementation implementation, bool runDiagnosticsOnTimeout, out int priority) {
    var result = inner.Get(implementation.Id);
    if (result == null) {
      priority = MissingPriority;
    } else if (result.Checksum != implementation.Checksum) {
      priority = ChangedPriority;
    } else if (implementation.DependencyChecksum == null || result.DependenciesChecksum != implementation.DependencyChecksum) {
      priority = DependencyChangedPriority;
    } else if (result.VcOutcome == VcOutcome.TimedOut && runDiagnosticsOnTimeout) {
      priority = ChangedPriority;
    } else {
      priority = ReusePriority;
    }
    return result;
  }

  private void Store(string id, ImplementationRunResult result) {
    foreach (var evicted in inner.Set(id, result)) {
      journal.Remove(evicted);
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
      Store(implementation.Id, result);
      journal[implementation.Id] = snapshot;
    }
  }

  /// <summary>
  /// Detached copies of every complete successful entry the native cache would still reuse. Reads the
  /// native store without changing any entry.
  /// </summary>
  internal IReadOnlyList<Snapshot> ExportSnapshots(CancellationToken cancellationToken = default) {
    cancellationToken.ThrowIfCancellationRequested();
    var copies = new List<Snapshot>();
    lock (gate) {
      CheckOwner();
      foreach (var snapshot in journal.Values) {
        cancellationToken.ThrowIfCancellationRequested();
        var identity = snapshot.Identity();
        // Check the native store before exporting the journal entry.
        var current = LookupCore(identity, false, out var priority);
        if (current == null || priority != ReusePriority || current.VcOutcome != VcOutcome.Correct) {
          continue;
        }
        copies.Add(snapshot with {
          Dependencies = snapshot.Dependencies.ToArray(),
          Splits = snapshot.Splits.Select(split => {
            cancellationToken.ThrowIfCancellationRequested();
            return split with { Assertions = split.Assertions.ToArray() };
          }).ToArray()
        });
      }
    }
    cancellationToken.ThrowIfCancellationRequested();
    return copies;
  }

  /// <summary>
  /// Builds an independently owned cache from detached snapshots. The snapshots must not be shared with
  /// another owner. Clone, session export and session import all create their child this way.
  /// </summary>
  internal static NativeVerificationCache Restore(IEnumerable<Snapshot> snapshots, out int copiedEntries,
    CancellationToken cancellationToken = default, int capacity = DefaultCapacity) {
    cancellationToken.ThrowIfCancellationRequested();
    var restored = new NativeVerificationCache(capacity);
    try {
      lock (restored.gate) {
        foreach (var copied in snapshots) {
          cancellationToken.ThrowIfCancellationRequested();
          var childIdentity = copied.Identity();
          restored.Store(childIdentity.Id, copied.Restore(childIdentity));
          restored.journal[copied.Id] = copied;
        }
      }
      cancellationToken.ThrowIfCancellationRequested();
      copiedEntries = restored.journal.Count;
      return restored;
    } catch {
      restored.Dispose();
      throw;
    }
  }

  internal NativeVerificationCache Clone(out int copiedEntries, CancellationToken cancellationToken = default) =>
    Restore(ExportSnapshots(cancellationToken), out copiedEntries, cancellationToken, capacity);

  public void Clear() {
    lock (gate) {
      CheckOwner();
      inner.Clear();
      journal.Clear();
    }
  }

  public void Dispose() {
    lock (gate) {
      if (disposed) {
        return;
      }
      inner.Clear();
      journal.Clear();
      disposed = true;
    }
  }
}
