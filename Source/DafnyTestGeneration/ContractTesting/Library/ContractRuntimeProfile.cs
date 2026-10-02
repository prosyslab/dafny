namespace DafnyContractRuntime {
  /// <summary>Counts and times contract checks and record encoding/IO, and writes them to the profile file when enabled by configuration.</summary>
  internal static class ContractRuntimeProfile {
    private const bool Enabled = ContractRuntimeConfiguration.ProfileRuntime;
    private static readonly object profileLock = new();
    private static long actualContractCheckCount;
    private static long actualContractCheckTicks;
    private static long valueEncodingCount;
    private static long valueEncodingTicks;
    private static long recordEncodingCount;
    private static long recordEncodingTicks;
    private static long recordIoCount;
    private static long recordIoTicks;
    private static long temporaryOrdinal;
    [System.ThreadStatic]
    private static int contractCheckDepth;
    [System.ThreadStatic]
    private static long outerContractCheckStarted;
    internal static long Start() => Enabled ? System.Diagnostics.Stopwatch.GetTimestamp() : 0;
    internal static bool BeginContractCheck() {
      if (Enabled && contractCheckDepth++ == 0) {
        outerContractCheckStarted = System.Diagnostics.Stopwatch.GetTimestamp();
      }
      return true;
    }
    internal static bool EndContractCheck(bool passed) {
      if (Enabled && contractCheckDepth > 0) {
        System.Threading.Interlocked.Increment(ref actualContractCheckCount);
        if (--contractCheckDepth == 0) {
          System.Threading.Interlocked.Add(ref actualContractCheckTicks,
            System.Math.Max(0, System.Diagnostics.Stopwatch.GetTimestamp() - outerContractCheckStarted));
        }
      }
      return passed;
    }
    internal static void RecordValueEncoding(long started) =>
      Record(ref valueEncodingCount, ref valueEncodingTicks, started);
    internal static void RecordRecordEncoding(long started) =>
      Record(ref recordEncodingCount, ref recordEncodingTicks, started);
    internal static void RecordRecordIo(long started) =>
      Record(ref recordIoCount, ref recordIoTicks, started);
    private static void Record(ref long count, ref long ticks, long started) {
      if (!Enabled) { return; }
      System.Threading.Interlocked.Increment(ref count);
      System.Threading.Interlocked.Add(ref ticks,
        System.Math.Max(0, System.Diagnostics.Stopwatch.GetTimestamp() - started));
    }
    private static object Metric(string name, long count, long ticks) => new {
      name,
      count,
      elapsedMilliseconds = ticks * 1000.0 / System.Diagnostics.Stopwatch.Frequency
    };
    internal static void Flush(string path) {
      if (!Enabled) { return; }
      lock (profileLock) {
        var profile = new {
          schemaVersion = 1,
          clock = "Stopwatch",
          metrics = new[] {
          Metric("actual_contract_check", System.Threading.Interlocked.Read(ref actualContractCheckCount),
            System.Threading.Interlocked.Read(ref actualContractCheckTicks)),
          Metric("record_encoding", System.Threading.Interlocked.Read(ref recordEncodingCount),
            System.Threading.Interlocked.Read(ref recordEncodingTicks)),
          Metric("record_io", System.Threading.Interlocked.Read(ref recordIoCount),
            System.Threading.Interlocked.Read(ref recordIoTicks)),
          Metric("value_encoding", System.Threading.Interlocked.Read(ref valueEncodingCount),
            System.Threading.Interlocked.Read(ref valueEncodingTicks))
        }
        };
        var temporaryPath = path + ".tmp." + System.Environment.ProcessId + "." +
          System.Threading.Interlocked.Increment(ref temporaryOrdinal);
        System.IO.File.WriteAllText(temporaryPath, System.Text.Json.JsonSerializer.Serialize(profile));
        System.IO.File.Move(temporaryPath, path, overwrite: true);
      }
    }
  }
}
