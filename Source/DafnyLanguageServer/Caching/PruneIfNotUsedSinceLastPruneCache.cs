using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny;

public record PruneResult<T>(T Result, int Pruned, int Hits, int Total);

public class PruneIfNotUsedSinceLastPruneCache<TKey, TValue>
  where TValue : class
  where TKey : notnull {
  private SemaphoreSlim semaphoreSlim = new(1);


  class Item {
    public Item(TValue value) {
      Value = value;
      Accessed = true;
    }

    public bool Accessed { get; set; }
    public TValue Value { get; }
  }

  private readonly ConcurrentDictionary<TKey, Item> items;

  public IEnumerable<TValue> Values => items.Select(i => i.Value.Value);
  public int Count => items.Count;

  public PruneIfNotUsedSinceLastPruneCache(IEqualityComparer<TKey> comparer) {
    items = new(comparer);
  }

  /// <summary>
  /// Copies membership and pruning state into an independently owned cache. Callers must prevent
  /// concurrent Set/TryGet calls; a running UseAndPrune operation is rejected rather than waited on.
  /// The supplied functions determine key/value ownership; this cache never assumes they are immutable.
  /// </summary>
  public PruneIfNotUsedSinceLastPruneCache<TKey, TValue> Clone(
    Func<TKey, TKey> cloneKey, Func<TValue, TValue> cloneValue, CancellationToken cancellationToken = default) {
    if (!semaphoreSlim.Wait(0, cancellationToken)) {
      throw new InvalidOperationException("Cannot clone a cache while it is in use.");
    }

    try {
      var clone = new PruneIfNotUsedSinceLastPruneCache<TKey, TValue>(items.Comparer);
      foreach (var (key, item) in items) {
        cancellationToken.ThrowIfCancellationRequested();
        clone.items.TryAdd(cloneKey(key), new Item(cloneValue(item.Value)) { Accessed = item.Accessed });
      }

      cancellationToken.ThrowIfCancellationRequested();
      return clone;
    }
    finally {
      semaphoreSlim.Release();
    }
  }

  /// <summary>
  /// Reads every entry through <paramref name="select"/> without changing the cache. Like Clone, it
  /// rejects a cache that is in use, so the entries are a consistent drained snapshot.
  /// </summary>
  public IReadOnlyList<TResult> Export<TResult>(Func<TKey, TValue, TResult> select,
    CancellationToken cancellationToken = default) {
    if (!semaphoreSlim.Wait(0, cancellationToken)) {
      throw new InvalidOperationException("Cannot export a cache while it is in use.");
    }

    try {
      var exported = new List<TResult>(items.Count);
      foreach (var (key, item) in items) {
        cancellationToken.ThrowIfCancellationRequested();
        exported.Add(select(key, item.Value));
      }

      return exported;
    }
    finally {
      semaphoreSlim.Release();
    }
  }

  /// <summary>
  /// Adds an entry that no prune cycle has used yet. This is the state every entry of a drained
  /// cache is in, because each pruning pass clears the access marker of the entries it keeps.
  /// </summary>
  public void Seed(TKey key, TValue value) {
    items.TryAdd(key, new Item(value) { Accessed = false });
  }

  public async Task<PruneResult<T>> UseAndPrune<T>(Func<Task<T>> use, CancellationToken cancellationToken) {
    await semaphoreSlim.WaitAsync(cancellationToken);
    try {
      var before = Count;
      var result = await use();
      var pruned = Prune();
      var hits = before - pruned;

      return new PruneResult<T>(result, pruned, hits, Count);
    }
    finally {
      semaphoreSlim.Release();
    }
  }

  private int Prune() {
    var keys = items.Keys.ToList();
    var removedCount = 0;
    foreach (var key in keys) {
      var item = items[key];
      if (!item.Accessed) {
        items.TryRemove(key, out _);
        removedCount++;
      }

      item.Accessed = false;
    }

    return removedCount;
  }

  public void Set(TKey key, TValue value) {
    items.TryAdd(key, new Item(value));
  }

  public bool TryGet(TKey key, out TValue? value) {
    var result = items.TryGetValue(key, out var item);
    if (result) {
      value = item!.Value;
      item.Accessed = true;
    } else {
      value = null;
    }

    return result;
  }
}
