using System;
using System.Diagnostics;
using System.IO;
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
