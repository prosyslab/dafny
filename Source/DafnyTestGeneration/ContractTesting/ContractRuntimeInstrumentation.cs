using System;
using System.Text.Json;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Supplies the diagnostic-only random stream and append-only observation bridge.</summary>
public static class ContractRuntimeInstrumentation {
  public const string DafnySource = """
    module {:extern "DafnyPbtBridgeRuntime"} PbtRuntime {
      class {:extern "DafnyPbtBridgeRuntime", "Bridge"} PbtBridge {
        static function {:extern} Check(id: string, iteration: int, passed: bool, values: string): bool
        static function {:extern} Require(passed: bool): bool
        static function {:extern} RequireInSpec(passed: bool): bool
        static function {:extern} EnterContract<T>(id: string, values: T): bool
        static function {:extern} ExitContract<T>(id: string, values: T): bool
        static function {:extern} Checkpoint(id: string, iteration: int, values: string): bool
        static function {:extern "DafnyContractRuntime.ContractDiagnosticBridge", "Serialize"} Serialize<T>(value: T, shape: string): string
        static function {:extern "DafnyContractRuntime.ContractDiagnosticBridge", "SerializeNamed"} SerializeNamed<T>(name: string, value: T, shape: string): string
        static function {:extern} Location(location: string): bool
        static method {:extern} Input(name: string, value: string)
        static method {:extern} InputValues(values: string)
        static method {:extern} Generated()
        static method {:extern} Executed()
        static method {:extern} Complete()
        static method {:extern} Stop()
        static method {:extern} Unreachable()
        static method {:extern} UnreachableBody()
        static function {:extern} UnreachableValue<T>(): T
      }
    }
    module {:extern "DafnyPbtRuntime"} PbtRandom {
      class {:extern "DafnyPbtRuntime", "Source"} Source {
        method {:extern} {:axiom} Int(lo: int, hi: int) returns (v: int) requires lo <= hi ensures lo <= v <= hi
        method {:extern} {:axiom} Nat(bound: nat) returns (v: nat) ensures v <= bound
        method {:extern} Bool() returns (b: bool)
        method {:extern} {:axiom} Char(lo: char, hi: char) returns (c: char) requires lo <= hi ensures lo <= c <= hi
        method {:extern} {:axiom} Index(n: nat) returns (i: nat) requires n > 0 ensures i < n
        method {:extern} {:axiom} Size() returns (s: nat)
      }
      method {:extern "DafnyPbtRuntime.Source", "New"} {:axiom} New() returns (r: Source)
    }
    """;

  public static string BridgeSource(string observationPath, ContractRuntimeTransformation transformation) =>
    ContractStubRuntime.BridgeSource(observationPath + ".legacy", transformation.Prepared, runtimeReferences: true,
      transformation.CompiledGhostFields) + "\n" + RuntimeSource;

  private const string RuntimeSource = """
    namespace DafnyPbtRuntime {
      public sealed class Source {
        private readonly ulong seed;
        private readonly int ordinal;
        private ulong counter;
        public Source() {
          var args = System.Environment.GetCommandLineArgs();
          seed = ulong.Parse(args[System.Array.IndexOf(args, "--pbt-seed") + 1], System.Globalization.CultureInfo.InvariantCulture);
          ordinal = int.Parse(args[System.Array.IndexOf(args, "--pbt-ordinal") + 1], System.Globalization.CultureInfo.InvariantCulture);
        }
        public static Source New() { return new Source(); }
        private byte[] Block() {
          var bytes = new byte[34];
          System.Buffers.Binary.BinaryPrimitives.WriteUInt64BigEndian(bytes.AsSpan(0, 8), seed);
          System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian(bytes.AsSpan(8, 4), ordinal);
          System.Buffers.Binary.BinaryPrimitives.WriteUInt64BigEndian(bytes.AsSpan(12, 8), counter++);
          System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian(bytes.AsSpan(20, 4), 10);
          System.Text.Encoding.UTF8.GetBytes("pbt-random").CopyTo(bytes, 24);
          return System.Security.Cryptography.SHA256.HashData(bytes);
        }
        private System.Numerics.BigInteger Next(System.Numerics.BigInteger bound) {
          if (bound <= 0) { throw new System.ArgumentOutOfRangeException(nameof(bound)); }
          var bytes = new byte[bound.GetByteCount(isUnsigned: true)];
          for (var offset = 0; offset < bytes.Length; offset += 32) {
            var block = Block();
            System.Array.Copy(block, 0, bytes, offset, System.Math.Min(32, bytes.Length - offset));
          }
          return new System.Numerics.BigInteger(bytes, isUnsigned: true, isBigEndian: true) % bound;
        }
        public System.Numerics.BigInteger Int(System.Numerics.BigInteger lo, System.Numerics.BigInteger hi) { return lo + Next(hi - lo + 1); }
        public System.Numerics.BigInteger Nat(System.Numerics.BigInteger bound) { return Next(bound + 1); }
        public bool Bool() { return Next(2) == 1; }
        public Dafny.Rune Char(Dafny.Rune lo, Dafny.Rune hi) { return new Dafny.Rune((int)Int(lo.Value, hi.Value)); }
        public System.Numerics.BigInteger Index(System.Numerics.BigInteger n) { return Next(n); }
        public System.Numerics.BigInteger Size() { return System.Math.Min(2 + ordinal / 4, 32); }
      }
    }
    namespace DafnyPbtBridgeRuntime {
      public static class Bridge {
        private static string currentLocation;
        private static readonly System.Collections.Generic.HashSet<(string, object)> PendingContracts = new();
        public static bool EnterContract<T>(Dafny.ISequence<Dafny.Rune> id, T values) {
          return PendingContracts.Add((Text(id), values));
        }
        public static bool ExitContract<T>(Dafny.ISequence<Dafny.Rune> id, T values) {
          return PendingContracts.Remove((Text(id), values));
        }
        static Bridge() {
          System.AppDomain.CurrentDomain.UnhandledException += (_, args) => {
            var message = args.ExceptionObject is System.Exception exception ? exception.Message : args.ExceptionObject.ToString();
            Write(new { kind = "runtime_error", message, location = currentLocation });
          };
        }
        private static string Text(Dafny.ISequence<Dafny.Rune> value) { return value.ToVerbatimString(false); }
        private static string Path {
          get { var args = System.Environment.GetCommandLineArgs(); return args[System.Array.IndexOf(args, "--pbt-out") + 1]; }
        }
        private static void Write(object value) { System.IO.File.AppendAllText(Path, System.Text.Json.JsonSerializer.Serialize(value) + "\n"); }
        public static bool Check(Dafny.ISequence<Dafny.Rune> id, System.Numerics.BigInteger iteration, bool passed, Dafny.ISequence<Dafny.Rune> values) {
          Write(new { kind = "check", id = Text(id), iteration = (int)iteration, passed, values = System.Text.Json.JsonDocument.Parse(Text(values)).RootElement });
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
        public static bool Checkpoint(Dafny.ISequence<Dafny.Rune> id, System.Numerics.BigInteger iteration, Dafny.ISequence<Dafny.Rune> values) {
          Write(new { kind = "checkpoint", id = Text(id), iteration = (int)iteration, values = System.Text.Json.JsonDocument.Parse(Text(values)).RootElement }); return true;
        }
        public static void Input(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> value) {
          Write(new { kind = "input", name = Text(name), value = System.Text.Json.JsonDocument.Parse(Text(value)).RootElement });
        }
        public static void InputValues(Dafny.ISequence<Dafny.Rune> values) {
          foreach (var value in System.Text.Json.JsonDocument.Parse(Text(values)).RootElement.EnumerateObject()) {
            Write(new { kind = "input", name = value.Name, value = value.Value });
          }
        }
        public static void Generated() { Write(new { kind = "generated" }); }
        public static void Executed() { Write(new { kind = "executed" }); }
        public static void Complete() { Write(new { kind = "complete" }); }
        public static bool Location(Dafny.ISequence<Dafny.Rune> location) { currentLocation = Text(location); return true; }
        public static void Stop() { Write(new { kind = "rejected" }); System.Environment.Exit(0); }
        public static void Unreachable() { throw new System.InvalidOperationException("unreachable scaffold executed"); }
        public static void UnreachableBody() { throw new System.InvalidOperationException("statically unreachable diagnostic body executed"); }
        public static T UnreachableValue<T>() { throw new System.InvalidOperationException("statically unreachable diagnostic body executed"); }
      }
    }
    """;
}
