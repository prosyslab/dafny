namespace DafnyPbtSmt {
  using Observation = DafnyPbtRuntime.Observation;
  /// <summary>Sends SMT realization, choice and precondition requests to the parent process through request and response files.</summary>
  public static class Oracle {
    private static string currentCall = "";
    private static readonly System.Collections.Generic.Dictionary<string, object> currentInputs = new();
    private static readonly System.Collections.Generic.Dictionary<string, System.Text.Json.JsonElement> pureChoices = new();
    private static System.Numerics.BigInteger targetCallCount;
    private static string targetSymbol;
    private static int targetInvocation;
    public static void Begin(Dafny.ISequence<Dafny.Rune> name) {
      currentCall = Observation.Text(name);
      currentInputs.Clear();
    }
    public static void Input<T>(Dafny.ISequence<Dafny.Rune> name, T value,
        Dafny.ISequence<Dafny.Rune> shape) {
      currentInputs.Add(Observation.Text(name), Observation.Encode(value, Observation.Shape(shape)));
    }
    public static void End() {
      Request(currentCall, System.Text.Json.JsonSerializer.Serialize(currentInputs), "precondition");
    }
    public static bool CheckPrecondition(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> arguments) {
      Request(Observation.Text(name), Observation.Text(arguments), "precondition");
      return true;
    }
    private static System.Text.Json.JsonElement Request(string symbol, string inputs, string operation, int? invocation = null, string outputs = null) {
      var prefix = DafnyContractRuntime.ContractRuntimeConfiguration.ObservationPath + ".rpc." + System.Guid.NewGuid().ToString("N");
      var formalInputs = System.Text.Json.JsonSerializer.Deserialize<System.Collections.Generic.Dictionary<string, System.Text.Json.JsonElement>>(inputs);
      System.Text.Json.JsonElement? receiver = formalInputs.Remove("$this", out var receiverValue) ? receiverValue : null;
      System.IO.File.WriteAllText(prefix + ".tmp", System.Text.Json.JsonSerializer.Serialize(new {
        symbol,
        inputs = formalInputs,
        operation,
        receiver,
        typeArguments = Observation.ConcreteTypes.TryGetValue(symbol, out var types) ? types : System.Array.Empty<string>(),
        heap = Observation.SnapshotHeap(),
        invocation,
        outputs = outputs == null ? null : System.Text.Json.JsonSerializer.Deserialize<System.Collections.Generic.Dictionary<string, System.Text.Json.JsonElement>>(outputs)
      }));
      System.IO.File.Move(prefix + ".tmp", prefix + ".request");
      while (!System.IO.File.Exists(prefix + ".response")) { System.Threading.Thread.Sleep(5); }
      var response = System.Text.Json.JsonDocument.Parse(System.IO.File.ReadAllText(prefix + ".response")).RootElement.Clone();
      if (response.GetProperty("status").GetString() != "realized") {
        throw new System.InvalidOperationException("contract_rpc_" + response.GetProperty("status").GetString());
      }
      if (operation == "realize" && response.TryGetProperty("postHeap", out var postHeap)) { Observation.ApplyHeap(postHeap); }
      return response;
    }
    public static System.Numerics.BigInteger StartTarget(Dafny.ISequence<Dafny.Rune> symbol, Dafny.ISequence<Dafny.Rune> arguments, System.Numerics.BigInteger invocation) {
      var current = targetCallCount++;
      if (current != invocation) { return System.Numerics.BigInteger.Zero; }
      targetSymbol = Observation.Text(symbol);
      targetInvocation = checked((int)current);
      Request(targetSymbol, Observation.Text(arguments), "entry_start", targetInvocation);
      return current + System.Numerics.BigInteger.One;
    }
    public static void EndTarget(System.Numerics.BigInteger token, Dafny.ISequence<Dafny.Rune> outputs) {
      if (token.IsZero) { return; }
      if (token != new System.Numerics.BigInteger(targetInvocation) + System.Numerics.BigInteger.One) { throw new System.InvalidOperationException("Mismatched target invocation."); }
      Request(targetSymbol, "{}", "entry_end", targetInvocation, Observation.Text(outputs));
      System.Environment.Exit(0);
    }
    public static T EndTargetValue<T>(System.Numerics.BigInteger token, Dafny.ISequence<Dafny.Rune> outputName, T value,
        Dafny.ISequence<Dafny.Rune> shape) {
      EndTarget(token, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(System.Text.Json.JsonSerializer.Serialize(
        new System.Collections.Generic.Dictionary<string, object> {
          [Observation.Text(outputName)] =
          Observation.Encode(value, Observation.Shape(shape))
        })));
      return value;
    }
    public static Dafny.ISequence<Dafny.Rune> Realize(Dafny.ISequence<Dafny.Rune> name,
        Dafny.ISequence<Dafny.Rune> arguments, bool pure) {
      var symbol = Observation.Text(name);
      var inputs = Observation.Text(arguments);
      var key = symbol + ":" + inputs + ":" + System.Text.Json.JsonSerializer.Serialize(Observation.SnapshotHeap());
      System.Text.Json.JsonElement response;
      if (!pure || !pureChoices.TryGetValue(key, out response)) {
        response = Request(symbol, inputs, "realize");
        if (pure) { pureChoices.Add(key, response); }
      }
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(response.GetRawText());
    }
    public static T Choose<T>(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> arguments,
        Dafny.ISequence<Dafny.Rune> outputName, bool pure) {
      return Output<T>(Realize(name, arguments, pure), outputName);
    }
    public static T Output<T>(Dafny.ISequence<Dafny.Rune> realization, Dafny.ISequence<Dafny.Rune> outputName) {
      var observation = System.Text.Json.JsonDocument.Parse(Observation.Text(realization)).RootElement.GetProperty("outputs").GetProperty(Observation.Text(outputName));
      return (T)Observation.Decode(observation, typeof(T));
    }
  }
}
