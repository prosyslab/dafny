namespace DafnyPbtRuntime {
  /// <summary>Records runtime check results, contract calls and heap captures as observation JSONL for the parent process.</summary>
  public static class Checks {
    private static string currentLocation;
    private static int nextInvocation;
    private static readonly System.Collections.Generic.Stack<int> Calls = new();
    private static int? CurrentInvocation => Calls.Count == 0 ? null : Calls.Peek();
    private static readonly System.Collections.Generic.HashSet<(string, object)> PendingContracts = new();
    private static readonly object OutputLock = new();
    private static readonly System.Lazy<string> OutputPath = new(() => {
      var args = System.Environment.GetCommandLineArgs();
      return args[System.Array.IndexOf(args, "--pbt-out") + 1];
    });
    private static System.IO.StreamWriter output;
    public static bool EnterContract<T>(Dafny.ISequence<Dafny.Rune> id, T values) {
      return PendingContracts.Add((Text(id), values));
    }
    public static bool ExitContract<T>(Dafny.ISequence<Dafny.Rune> id, T values) {
      return PendingContracts.Remove((Text(id), values));
    }
    static Checks() {
      System.AppDomain.CurrentDomain.UnhandledException += (_, args) => {
        var message = args.ExceptionObject is System.Exception exception ? exception.Message : args.ExceptionObject.ToString();
        Write(new { kind = "runtime_error", message, location = currentLocation });
        FlushProfile();
      };
      System.AppDomain.CurrentDomain.ProcessExit += (_, _) => {
        lock (OutputLock) {
          output?.Dispose();
          FlushProfile();
        }
      };
    }
    private static string Text(Dafny.ISequence<Dafny.Rune> value) { return Observation.Text(value); }
    private static void FlushProfile() => DafnyContractRuntime.ContractRuntimeProfile.Flush(OutputPath.Value + ".profile.json");
    public static bool BeginCheck() => DafnyContractRuntime.ContractRuntimeProfile.BeginContractCheck();
    public static bool Evaluated(bool passed) => DafnyContractRuntime.ContractRuntimeProfile.EndContractCheck(passed);
    private static void Write(object value) {
      var encodingStarted = DafnyContractRuntime.ContractRuntimeProfile.Start();
      var json = System.Text.Json.JsonSerializer.Serialize(value);
      DafnyContractRuntime.ContractRuntimeProfile.RecordRecordEncoding(encodingStarted);
      var ioStarted = DafnyContractRuntime.ContractRuntimeProfile.Start();
      try {
        lock (OutputLock) {
          output ??= new System.IO.StreamWriter(OutputPath.Value, append: true);
          output.Write(json + "\n");
          // Completed records remain visible even when the parent kills this sample.
          output.Flush();
        }
      }
      finally {
        DafnyContractRuntime.ContractRuntimeProfile.RecordRecordIo(ioStarted);
      }
    }
    public static bool Check(Dafny.ISequence<Dafny.Rune> id, System.Numerics.BigInteger iteration, bool passed,
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fragments) {
      var values = Observation.PrepareValues(fragments);
      if (CurrentInvocation is { } invocation) {
        Write(new { kind = "check", id = Text(id), iteration = (int)iteration, passed, values, call_invocation = invocation });
      } else {
        Write(new { kind = "check", id = Text(id), iteration = (int)iteration, passed, values });
      }
      if (!passed && Text(id).StartsWith("call_precondition:", System.StringComparison.Ordinal)) {
        Complete(); System.Environment.Exit(0);
      }
      return passed;
    }
    public static bool Require(bool passed) {
      if (!passed) { throw new System.InvalidOperationException("callee implementation invoked a helper outside its precondition"); }
      return true;
    }
    public static bool RequireInSpec(bool passed) {
      if (!passed) { throw new System.InvalidOperationException("obligation evaluation called a function outside its precondition"); }
      return true;
    }
    public static bool Checkpoint(Dafny.ISequence<Dafny.Rune> id, System.Numerics.BigInteger iteration,
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fragments) {
      var values = Observation.PrepareValues(fragments);
      if (CurrentInvocation is { } invocation) {
        Write(new { kind = "checkpoint", id = Text(id), iteration = (int)iteration, values, call_invocation = invocation });
      } else {
        Write(new { kind = "checkpoint", id = Text(id), iteration = (int)iteration, values });
      }
      return true;
    }
    public static void Input(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> value) {
      Write(new { kind = "input", name = Text(name), value = System.Text.Json.JsonDocument.Parse(Text(value)).RootElement });
    }
    public static void InputValues(Dafny.ISequence<Dafny.Rune> values) {
      foreach (var value in System.Text.Json.JsonDocument.Parse(Text(values)).RootElement.EnumerateObject()) {
        Write(new { kind = "input", name = value.Name, value = value.Value });
      }
    }
    public static void CaptureHeap(Dafny.ISequence<Dafny.Rune> phase, Dafny.ISequence<Dafny.Rune> outputs) {
      Write(new {
        kind = "heap_capture",
        phase = Text(phase),
        outputs = System.Text.Json.JsonDocument.Parse(Text(outputs)).RootElement,
        heap = System.Text.Json.JsonDocument.Parse(Observation.RuntimeHeap()).RootElement
      });
    }
    public static System.Numerics.BigInteger BeginCall(Dafny.ISequence<Dafny.Rune> scope, Dafny.ISequence<Dafny.Rune> inputs) {
      var invocation = checked(++nextInvocation);
      Calls.Push(invocation);
      Write(new {
        kind = "heap_capture",
        phase = "call_entry",
        scope = Text(scope),
        invocation,
        inputs = System.Text.Json.JsonDocument.Parse(Text(inputs)).RootElement,
        heap = System.Text.Json.JsonDocument.Parse(Observation.RuntimeHeap()).RootElement
      });
      return invocation;
    }
    public static void EndCall(Dafny.ISequence<Dafny.Rune> scope, System.Numerics.BigInteger invocation,
        Dafny.ISequence<Dafny.Rune> outputs) {
      if (CurrentInvocation != (int)invocation) { throw new System.InvalidOperationException("Mismatched call return."); }
      Write(new {
        kind = "heap_capture",
        phase = "call_return",
        scope = Text(scope),
        invocation = (int)invocation,
        outputs = System.Text.Json.JsonDocument.Parse(Text(outputs)).RootElement,
        heap = System.Text.Json.JsonDocument.Parse(Observation.RuntimeHeap()).RootElement
      });
    }
    public static void LeaveCall(System.Numerics.BigInteger invocation) {
      if (CurrentInvocation != (int)invocation) { throw new System.InvalidOperationException("Mismatched call exit."); }
      Calls.Pop();
    }
    public static void Generated() { Write(new { kind = "generated" }); }
    public static void Executed() { Write(new { kind = "executed" }); }
    public static void Complete() { Write(new { kind = "complete" }); FlushProfile(); }
    public static bool Location(Dafny.ISequence<Dafny.Rune> location) { currentLocation = Text(location); return true; }
    public static void Stop() { Write(new { kind = "rejected" }); FlushProfile(); System.Environment.Exit(0); }
    public static void Unreachable() { throw new System.InvalidOperationException("unreachable scaffold executed"); }
    public static void UnreachableBody() { throw new System.InvalidOperationException("statically unreachable diagnostic body executed"); }
    public static T UnreachableValue<T>() { throw new System.InvalidOperationException("statically unreachable diagnostic body executed"); }
  }
}
