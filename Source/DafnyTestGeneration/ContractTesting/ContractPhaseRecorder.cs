using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Immediately persists diagnostic phase boundaries independently of query completion.</summary>
public sealed class ContractPhaseRecorder {
  private readonly string path;
  private readonly Stopwatch clock = Stopwatch.StartNew();

  public ContractPhaseRecorder(string path) {
    this.path = path;
    Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
  }

  /// <summary>Observes a synchronous phase without changing its result or suppressing failures.</summary>
  public static T Measure<T>(Action<string, string>? observer, string phase,
    CancellationToken cancellationToken, Func<T> operation) {
    observer?.Invoke(phase, "started");
    var completed = false;
    try {
      var result = operation();
      completed = true;
      return result;
    }
    finally {
      observer?.Invoke(phase, completed ? "completed" : cancellationToken.IsCancellationRequested ? "cancelled" : "failed");
    }
  }

  /// <summary>Observes an asynchronous phase even when cancellation interrupts its result.</summary>
  public static async Task<T> MeasureAsync<T>(Action<string, string>? observer, string phase,
    CancellationToken cancellationToken, Func<Task<T>> operation) {
    observer?.Invoke(phase, "started");
    var completed = false;
    try {
      var result = await operation();
      completed = true;
      return result;
    }
    finally {
      observer?.Invoke(phase, completed ? "completed" : cancellationToken.IsCancellationRequested ? "cancelled" : "failed");
    }
  }

  /// <summary>Observes a phase that completes without a returned value.</summary>
  public static Task MeasureAsync(Action<string, string>? observer, string phase,
    CancellationToken cancellationToken, Func<Task> operation) =>
    MeasureAsync(observer, phase, cancellationToken, async () => {
      await operation();
      return true;
    });

  /// <summary>Appends a complete timing record so cancellation preserves the last phase boundary.</summary>
  public void Record(string phase, string state) {
    File.AppendAllText(path, JsonSerializer.Serialize(new {
      Phase = phase,
      State = state,
      ElapsedMilliseconds = clock.Elapsed.TotalMilliseconds
    }, ContractJson.Options) + "\n");
  }
}

/// <summary>Aggregates diagnostic operation counts and elapsed monotonic time into a sidecar snapshot.</summary>
public sealed class ContractProfileRecorder {
  private sealed record MutableMetric(long Count, long ElapsedTicks);

  private readonly string path;
  private readonly object profileLock = new();
  private readonly Dictionary<string, MutableMetric> metrics = new(StringComparer.Ordinal);
  private long temporaryOrdinal;

  public ContractProfileRecorder(string path) {
    this.path = path;
    Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
  }

  /// <summary>Measures an operation, including time ending in an exception, without changing its result.</summary>
  public T Measure<T>(string metric, Func<T> operation) {
    ArgumentException.ThrowIfNullOrEmpty(metric);
    ArgumentNullException.ThrowIfNull(operation);
    var started = Stopwatch.GetTimestamp();
    try {
      return operation();
    }
    finally {
      Record(metric, started);
    }
  }

  /// <summary>Measures an asynchronous operation, including cancellation or failure, without changing its result.</summary>
  public async Task<T> MeasureAsync<T>(string metric, Func<Task<T>> operation) {
    ArgumentException.ThrowIfNullOrEmpty(metric);
    ArgumentNullException.ThrowIfNull(operation);
    var started = Stopwatch.GetTimestamp();
    try {
      return await operation();
    }
    finally {
      Record(metric, started);
    }
  }

  /// <summary>Measures an asynchronous operation that has no returned value.</summary>
  public Task MeasureAsync(string metric, Func<Task> operation) =>
    MeasureAsync(metric, async () => {
      await operation();
      return true;
    });

  /// <summary>Adds one completed or failed operation measured from the supplied monotonic timestamp.</summary>
  public void Record(string metric, long startedTimestamp) {
    ArgumentException.ThrowIfNullOrEmpty(metric);
    var elapsed = Math.Max(0, Stopwatch.GetTimestamp() - startedTimestamp);
    lock (profileLock) {
      metrics.TryGetValue(metric, out var current);
      metrics[metric] = new((current?.Count ?? 0) + 1, (current?.ElapsedTicks ?? 0) + elapsed);
    }
  }

  /// <summary>Atomically replaces the profile sidecar with a deterministic aggregate snapshot.</summary>
  public void Flush() {
    lock (profileLock) {
      var profile = new ContractProfile(ContractJson.SchemaVersion, "Stopwatch", metrics
        .OrderBy(pair => pair.Key, StringComparer.Ordinal)
        .Select(pair => new ContractProfileMetric(pair.Key, pair.Value.Count,
          pair.Value.ElapsedTicks * 1000.0 / Stopwatch.Frequency)).ToList());
      var temporaryPath = path + ".tmp." + Environment.ProcessId + "." + temporaryOrdinal++;
      File.WriteAllText(temporaryPath, JsonSerializer.Serialize(profile, ContractJson.Options));
      File.Move(temporaryPath, path, overwrite: true);
    }
  }
}

/// <summary>Describes one aggregate diagnostic timing category.</summary>
public sealed record ContractProfileMetric(string Name, long Count, double ElapsedMilliseconds);

/// <summary>Defines the versioned diagnostic profile sidecar schema.</summary>
public sealed record ContractProfile(int SchemaVersion, string Clock, IReadOnlyList<ContractProfileMetric> Metrics);
