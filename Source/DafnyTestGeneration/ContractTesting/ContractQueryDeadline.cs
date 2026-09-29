using System;
using System.Diagnostics;
using System.Threading;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Monotonic wall-clock deadlines independent of delayed cancellation callbacks.</summary>
public static class ContractQueryDeadline {
  /// <summary>Creates an absolute timestamp for a query whose complete construction and checking fit this budget.</summary>
  public static long AfterMilliseconds(long milliseconds) => checked(Stopwatch.GetTimestamp() +
    (long)Math.Ceiling(milliseconds * (double)Stopwatch.Frequency / 1000));

  /// <summary>Rejects expired work even when the cancellation timer has not had a chance to run.</summary>
  public static void Check(long? deadlineTimestamp, CancellationToken cancellationToken) {
    cancellationToken.ThrowIfCancellationRequested();
    if (deadlineTimestamp is { } deadline && Stopwatch.GetTimestamp() >= deadline) {
      throw new OperationCanceledException("The contract query exceeded its monotonic wall-clock deadline.");
    }
  }
}
