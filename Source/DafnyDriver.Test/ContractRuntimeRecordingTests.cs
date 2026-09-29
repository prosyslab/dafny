#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractRuntimeRecordingTests : IClassFixture<ContractRuntimeRecordingTests.RuntimeFixture> {
  private readonly RuntimeFixture fixture;

  public ContractRuntimeRecordingTests(RuntimeFixture fixture) {
    this.fixture = fixture;
  }

  // Repeated metadata never suppresses records or freezes mutable values, Unicode or reference identity.
  [Fact]
  public async Task RecordsEveryChangingValueAndKeepsProcessPathsSeparate() {
    foreach (var ordinal in Enumerable.Range(0, 2)) {
      var path = fixture.ObservationPath("values-" + ordinal);
      await File.WriteAllTextAsync(path, "{\"kind\":\"existing\"}\n");
      var process = await fixture.Run("values", path);
      Assert.Equal(0, process.ExitCode);
      Assert.False(process.Cancelled);
      Assert.Empty(process.StandardError);
      var lines = await File.ReadAllLinesAsync(path);
      Assert.Equal(5, lines.Length);
      Assert.Equal("{\"kind\":\"existing\"}", lines[0]);
      Assert.Equal(lines[1], lines[2]);
      Assert.NotEqual(lines[2], lines[3]);
      for (var index = 0; index < 3; index++) {
        using var record = JsonDocument.Parse(lines[index + 1]);
        Assert.Equal("check", record.RootElement.GetProperty("kind").GetString());
        var values = record.RootElement.GetProperty("values");
        Assert.Equal("pbt-reference-0", values.GetProperty("items").GetProperty("value").GetString());
        Assert.Equal(index == 2 ? "9" : "7", values.GetProperty("items[0]").GetProperty("value").GetString());
        Assert.Equal("🙂", values.GetProperty("character").GetProperty("value").GetString());
      }
      Assert.Equal("{\"kind\":\"complete\"}", lines[4]);
      var bytes = await File.ReadAllBytesAsync(path);
      Assert.Equal(Encoding.UTF8.GetBytes(string.Join("\n", lines) + "\n"), bytes);
    }
  }

  // Fully instantiated shape tokens distinguish equal CLR values with different Dafny generic widths.
  [Fact]
  public async Task KeepsCompleteGenericShapeIdentity() {
    var path = fixture.ObservationPath("shapes");
    var process = await fixture.Run("shapes", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(4, lines.Length);
    Assert.Equal(lines[0], lines[2]);
    for (var index = 0; index < 3; index++) {
      using var record = JsonDocument.Parse(lines[index]);
      var value = record.RootElement.GetProperty("values").GetProperty("result").GetProperty("items")[0];
      Assert.Equal("bitvector", value.GetProperty("kind").GetString());
      Assert.Equal(index == 1 ? 8 : 7, value.GetProperty("width").GetInt32());
      Assert.Equal("7", value.GetProperty("value").GetString());
    }
  }

  // Cached closed CLR metadata preserves constructor fields across changing values and Dafny widths.
  [Fact]
  public async Task RecordsFreshGenericDatatypeAndMapValues() {
    var path = fixture.ObservationPath("datatypes");
    var process = await fixture.Run("datatypes", path);
    Assert.Equal(0, process.ExitCode);
    Assert.Empty(process.StandardError);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(5, lines.Length);
    Assert.Equal(lines[0], lines[3]);
    for (var index = 0; index < 4; index++) {
      using var record = JsonDocument.Parse(lines[index]);
      var datatype = record.RootElement.GetProperty("values").GetProperty("result");
      Assert.Equal("Fixture.Box.Box", datatype.GetProperty("constructor").GetString());
      var entries = datatype.GetProperty("fields").GetProperty("value").GetProperty("entries");
      Assert.Equal(1, entries.GetArrayLength());
      var value = entries[0].GetProperty("value");
      Assert.Equal(index == 2 ? "9" : "7", value.GetProperty("value").GetString());
      Assert.Equal(index == 1 ? 8 : 7, value.GetProperty("width").GetInt32());
    }
  }

  // A readonly datatype containing an externally mutable collection is observed anew each time.
  [Fact]
  public async Task DoesNotReuseMutableCollectionInsideDatatype() {
    var path = fixture.ObservationPath("mutable-datatype");
    var process = await fixture.Run("mutable-datatype", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(4, lines.Length);
    Assert.Equal(lines[0], lines[2]);
    for (var index = 0; index < 3; index++) {
      using var record = JsonDocument.Parse(lines[index]);
      var items = record.RootElement.GetProperty("values").GetProperty("result").GetProperty("fields").GetProperty("value").GetProperty("items");
      Assert.Equal(index == 1 ? "9" : "7", items[0].GetProperty("value").GetString());
    }
  }

  // A repeated class reference retains identity while each record captures its current mutable field.
  [Fact]
  public async Task DoesNotReuseMutableClassFields() {
    var path = fixture.ObservationPath("classes");
    var process = await fixture.Run("classes", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(4, lines.Length);
    for (var index = 0; index < 3; index++) {
      using var record = JsonDocument.Parse(lines[index]);
      var values = record.RootElement.GetProperty("values");
      Assert.Equal(index == 2 ? "pbt-reference-1" : "pbt-reference-0", values.GetProperty("cell").GetProperty("value").GetString());
      Assert.Equal(index == 0 ? "7" : "9", values.GetProperty("cell.value").GetProperty("value").GetString());
    }
  }

  // Explicit child registration invalidates an already observed parent's structural encoding.
  [Fact]
  public async Task RegistrationInvalidatesParentEncodingAfterCaughtMetadataFailure() {
    var path = fixture.ObservationPath("register-child");
    var process = await fixture.Run("register-child", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(3, lines.Length);
    using var first = JsonDocument.Parse(lines[0]);
    using var second = JsonDocument.Parse(lines[1]);
    var firstChild = first.RootElement.GetProperty("values").GetProperty("parent").GetProperty("fields").GetProperty("value");
    var secondChild = second.RootElement.GetProperty("values").GetProperty("parent").GetProperty("fields").GetProperty("value");
    Assert.Equal("datatype", firstChild.GetProperty("kind").GetString());
    Assert.Equal("reference", secondChild.GetProperty("kind").GetString());
    Assert.Equal("registered-child", secondChild.GetProperty("value").GetString());
  }

  // The same immutable value retains the exact requested Unicode field label on every observation.
  [Fact]
  public async Task NamedImmutableFragmentsKeepDistinctLabels() {
    var path = fixture.ObservationPath("named-fragments");
    var process = await fixture.Run("named-fragments", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(4, lines.Length);
    Assert.Equal(lines[0], lines[2]);
    for (var index = 0; index < 3; index++) {
      using var record = JsonDocument.Parse(lines[index]);
      var property = Assert.Single(record.RootElement.GetProperty("values").EnumerateObject());
      Assert.Equal(index == 1 ? "right🙂" : "left", property.Name);
      Assert.Equal("1", property.Value.GetProperty("fields").GetProperty("value").GetProperty("value").GetString());
    }
  }

  // Structured fragments retain exact empty, ordered, Unicode and duplicate-property JSON bytes.
  [Fact]
  public async Task WritesExactOrderedFragmentBytes() {
    var path = fixture.ObservationPath("fragment-bytes");
    var process = await fixture.Run("fragment-bytes", path);
    Assert.Equal(0, process.ExitCode);
    Assert.Empty(process.StandardError);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(4, lines.Length);
    Assert.Equal("{\"kind\":\"check\",\"id\":\"empty\",\"iteration\":0,\"passed\":true,\"values\":{}}", lines[0]);
    Assert.Equal("{\"kind\":\"check\",\"id\":\"one\",\"iteration\":1,\"passed\":true,\"values\":{\"one\":{\"kind\":\"integer\",\"value\":\"1\"}}}", lines[1]);
    Assert.Equal("{\"kind\":\"checkpoint\",\"id\":\"many\",\"iteration\":2,\"values\":{\"right\\uD83D\\uDE42\":{\"kind\":\"character\",\"value\":\"\\uD83D\\uDE42\"},\"same\":{\"kind\":\"integer\",\"value\":\"1\"},\"same\":{\"kind\":\"integer\",\"value\":\"2\"}}}", lines[2]);
    Assert.Equal("{\"kind\":\"complete\"}", lines[3]);
    Assert.Equal(Encoding.UTF8.GetBytes(string.Join("\n", lines) + "\n"), await File.ReadAllBytesAsync(path));
  }

  // Unassociated external fragments use the complete legacy object grammar and preserve duplicates.
  [Fact]
  public async Task ParsesCompleteExternalFragmentObject() {
    var path = fixture.ObservationPath("external-fragments");
    var process = await fixture.Run("external-fragments", path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(2, lines.Length);
    Assert.Equal("{\"kind\":\"check\",\"id\":\"external\",\"iteration\":0,\"passed\":true,\"values\":{\"first\":1,\"duplicate\":2,\"duplicate\":3}}", lines[0]);
    Assert.Equal("{\"kind\":\"complete\"}", lines[1]);
  }

  // Immutable reuse requires exact value identity, label and full shape while mutable values stay fresh.
  [Fact]
  public async Task ReusesOnlyExactImmutableNamedFragmentIdentity() {
    var process = await fixture.Run("fragment-identity", fixture.ObservationPath("fragment-identity"));
    Assert.Equal(0, process.ExitCode);
    using var output = JsonDocument.Parse(process.StandardOutput);
    Assert.True(output.RootElement.GetProperty("same").GetBoolean());
    Assert.False(output.RootElement.GetProperty("label").GetBoolean());
    Assert.False(output.RootElement.GetProperty("shape").GetBoolean());
    Assert.False(output.RootElement.GetProperty("array").GetBoolean());
    Assert.False(output.RootElement.GetProperty("external").GetBoolean());
    Assert.False(output.RootElement.GetProperty("reference").GetBoolean());
  }

  // Concrete array and concatenated strings preserve controls and both Unicode scalar boundaries.
  [Fact]
  public async Task DecodesCompleteUnicodeScalarRange() {
    var process = await fixture.Run("text-scalars", fixture.ObservationPath("text-scalars"));
    Assert.Equal(0, process.ExitCode);
    using var output = JsonDocument.Parse(process.StandardOutput);
    const string expected = "\0\t\n\ud7ff\ue000\uffff\U00010000\U0010ffff";
    Assert.Equal(expected, output.RootElement.GetProperty("array").GetString());
    Assert.Equal(expected + expected, output.RootElement.GetProperty("concat").GetString());
  }

  // An external string implementation keeps its own observable conversion rather than being enumerated.
  [Fact]
  public async Task PreservesExternalStringConversion() {
    var process = await fixture.Run("text-external", fixture.ObservationPath("text-external"));
    Assert.Equal(0, process.ExitCode);
    Assert.Equal("custom🙂", JsonSerializer.Deserialize<string>(process.StandardOutput));
  }

  // A completed record is readable before process exit and survives an abrupt parent kill.
  [Fact]
  public async Task FlushesCompletedRecordBeforeCancellation() {
    var path = fixture.ObservationPath("hold");
    using var process = new Process { StartInfo = fixture.StartInfo("hold", path) };
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(30));
    process.Start();
    var stderr = process.StandardError.ReadToEndAsync();
    try {
      Assert.Equal("ready", await process.StandardOutput.ReadLineAsync(timeout.Token));
      Assert.False(process.HasExited);
      byte[] beforeKill;
      await using (var input = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite)) {
        using var copy = new MemoryStream();
        await input.CopyToAsync(copy, timeout.Token);
        beforeKill = copy.ToArray();
      }
      Assert.Equal(Encoding.UTF8.GetBytes("{\"kind\":\"generated\"}\n"), beforeKill);
      process.Kill(entireProcessTree: true);
      await process.WaitForExitAsync(timeout.Token);
      Assert.Equal(beforeKill, await File.ReadAllBytesAsync(path, timeout.Token));
      Assert.Empty(await stderr);
    }
    finally {
      if (!process.HasExited) {
        process.Kill(entireProcessTree: true);
        await process.WaitForExitAsync(CancellationToken.None);
      }
    }
  }

  // Explicit rejection and failed call preconditions flush their final records before Environment.Exit.
  [Theory]
  [InlineData("stop", "rejected")]
  [InlineData("precondition", "complete")]
  public async Task FlushesExplicitEarlyExit(string scenario, string finalKind) {
    var path = fixture.ObservationPath(scenario);
    var process = await fixture.Run(scenario, path);
    Assert.Equal(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(scenario == "stop" ? 2 : 3, lines.Length);
    using var last = JsonDocument.Parse(lines[^1]);
    Assert.Equal(finalKind, last.RootElement.GetProperty("kind").GetString());
    if (scenario == "precondition") {
      using var failed = JsonDocument.Parse(lines[1]);
      Assert.Equal("check", failed.RootElement.GetProperty("kind").GetString());
      Assert.Equal("call_precondition:fixture", failed.RootElement.GetProperty("id").GetString());
      Assert.False(failed.RootElement.GetProperty("passed").GetBoolean());
      Assert.Equal("7", failed.RootElement.GetProperty("values").GetProperty("nested").GetProperty("value").GetString());
    }
    Assert.DoesNotContain("unreachable", process.StandardOutput);
  }

  // Unknown malformed fragments fail before a check record and retain the direct JsonDocument parse error.
  [Theory]
  [InlineData("bad-fragment", 10)]
  [InlineData("bad-mixed-fragment", 49)]
  public async Task RejectsMalformedExternalFragmentsBeforeWrite(string scenario, int bytePosition) {
    var path = fixture.ObservationPath(scenario);
    var process = await fixture.Run(scenario, path);
    Assert.NotEqual(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    using var record = JsonDocument.Parse(Assert.Single(lines));
    Assert.Equal("runtime_error", record.RootElement.GetProperty("kind").GetString());
    Assert.Equal($"'}}' is an invalid start of a value. LineNumber: 0 | BytePositionInLine: {bytePosition}.",
      record.RootElement.GetProperty("message").GetString());
  }

  // Completing a trace does not prevent a subsequent unhandled failure from being recorded.
  [Fact]
  public async Task RecordsUnhandledErrorAfterComplete() {
    var path = fixture.ObservationPath("error");
    var process = await fixture.Run("error", path);
    Assert.NotEqual(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(2, lines.Length);
    Assert.Equal("{\"kind\":\"complete\"}", lines[0]);
    using var record = JsonDocument.Parse(lines[1]);
    Assert.Equal("runtime_error", record.RootElement.GetProperty("kind").GetString());
    Assert.Equal("fixture failure", record.RootElement.GetProperty("message").GetString());
    Assert.Equal("fixture:1", record.RootElement.GetProperty("location").GetString());
  }

  // Invalid encoded metadata still fails after a valid shape has populated the cache.
  [Theory]
  [InlineData("bad-base64")]
  [InlineData("bad-json")]
  [InlineData("unsupported")]
  public async Task RejectsMalformedOrUnsupportedShapes(string scenario) {
    var path = fixture.ObservationPath(scenario);
    var process = await fixture.Run(scenario, path);
    Assert.NotEqual(0, process.ExitCode);
    var lines = await File.ReadAllLinesAsync(path);
    Assert.Equal(2, lines.Length);
    Assert.Equal("{\"kind\":\"generated\"}", lines[0]);
    using var record = JsonDocument.Parse(lines[1]);
    Assert.Equal("runtime_error", record.RootElement.GetProperty("kind").GetString());
    Assert.NotEmpty(record.RootElement.GetProperty("message").GetString()!);
  }

  /// <summary>Compiles the production-generated bridge once and executes each scenario in its own process.</summary>
  public sealed class RuntimeFixture : IAsyncLifetime {
    private readonly string directory = Path.Combine("/workspace/tmp", "contract-runtime-recording-" + Guid.NewGuid().ToString("N"));
    private string assemblyPath = null!;

    public async Task InitializeAsync() {
      Directory.CreateDirectory(directory);
      var dependencyPath = Path.Combine(directory, "RecordingFixture.cs");
      await File.WriteAllTextAsync(dependencyPath, FixtureSource);
      const string source = "module Fixture { datatype Box<T> = Box(value:T) class Cell { var value:int } method {:extern \"RecordingFixture\", \"Run\"} Native() method Main() { Native(); } }";
      var snapshot = new ContractSource("Fixture.dfy", source, ContractHarnessBuilder.Hash(source));
      var options = new DafnyOptions(DafnyOptions.Default);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
      var prepared = await ContractCompilerWorker.ParseAsync(new(1, [snapshot], new("Fixture.Main"),
        new Dictionary<string, ContractValue>()), options, timeout.Token);
      var transformation = new ContractRuntimeTransformation([snapshot], [], [], "Fixture.Main", prepared, new HashSet<Field>());
      var request = new ContractRuntimeCampaignRequest(1, [snapshot], new("Fixture.Main"), "17",
        Dependencies: [new(dependencyPath, ContractHarnessBuilder.Hash(FixtureSource))]);
      var compiled = await ContractCompilerWorker.CompileRuntimeAsync(transformation, request,
        Path.Combine(directory, "compiled"), options, timeout.Token);
      Assert.True(compiled.Status == ContractTestStatus.Passed, compiled.Reason);
      assemblyPath = compiled.AssemblyPath!;
    }

    public Task DisposeAsync() => Task.CompletedTask;

    public string ObservationPath(string scenario) => Path.Combine(directory, scenario + ".jsonl");

    public ProcessStartInfo StartInfo(string scenario, string path) {
      var start = new ProcessStartInfo("dotnet") {
        WorkingDirectory = directory,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true
      };
      foreach (var argument in Arguments(scenario, path)) { start.ArgumentList.Add(argument); }
      return start;
    }

    public async Task<ContractProcessResult> Run(string scenario, string path) {
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(30));
      return await ContractExecutionProcess.RunAsync("dotnet", Arguments(scenario, path), directory, timeout.Token);
    }

    private string[] Arguments(string scenario, string path) => [assemblyPath, "--scenario", scenario, "--pbt-out", path];
  }

  private const string FixtureSource = """
    using System;
    using System.Numerics;
    using System.Text;
    using System.Threading;
    using DafnyContractRuntime;
    using DafnyPbtBridgeRuntime;
    public static class RecordingFixture {
      private static Dafny.ISequence<Dafny.Rune> Text(string value) => Dafny.Sequence<Dafny.Rune>.UnicodeFromString(value);
      private static Dafny.ISequence<Dafny.Rune> Shape(string json) => Text(Convert.ToBase64String(Encoding.UTF8.GetBytes(json)));
      private static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> Fragments(params Dafny.ISequence<Dafny.Rune>[] values) =>
        Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(values);
      public static void Run() {
        var args = Environment.GetCommandLineArgs();
        var scenario = args[Array.IndexOf(args, "--scenario") + 1];
        if (scenario == "text-scalars") {
          var text = Dafny.Sequence<Dafny.Rune>.FromElements(new Dafny.Rune(0), new Dafny.Rune(9), new Dafny.Rune(10), new Dafny.Rune(0xd7ff), new Dafny.Rune(0xe000), new Dafny.Rune(0xffff), new Dafny.Rune(0x10000), new Dafny.Rune(0x10ffff));
          Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(new { array = ContractDiagnosticBridge.Text(text), concat = ContractDiagnosticBridge.Text(Dafny.Sequence<Dafny.Rune>.Concat(text, text)) }));
          Bridge.Complete();
          return;
        }
        if (scenario == "text-external") {
          var text = System.Reflection.DispatchProxy.Create<Dafny.ISequence<Dafny.Rune>, TextProxy>();
          Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(ContractDiagnosticBridge.Text(text)));
          Bridge.Complete();
          return;
        }
        if (scenario == "values") {
          var items = new BigInteger[1];
          var shape = Shape("{\"kind\":\"array\",\"type\":\"array<int>\",\"element\":{\"kind\":\"integer\"}}");
          foreach (var value in new[] { 7, 7, 9 }) {
            items[0] = value;
            var values = ContractDiagnosticBridge.SerializeNamed(Text("items"), items, shape);
            var character = ContractDiagnosticBridge.SerializeNamed(Text("character"), new Dafny.Rune(0x1f642), Shape("{\"kind\":\"other\"}"));
            Bridge.Check(Text("state"), BigInteger.Zero, true, Fragments(values, character));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "shapes") {
          var template = Shape("{\"kind\":\"sequence\",\"element\":{\"kind\":\"parameter\",\"index\":0}}");
          foreach (var width in new[] { 7, 8, 7 }) {
            var parameter = Shape("{\"kind\":\"bitvector\",\"width\":" + width + "}");
            var concrete = ContractDiagnosticBridge.InstantiateShape(template, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(parameter));
            var values = ContractDiagnosticBridge.SerializeNamed(Text("result"), Dafny.Sequence<byte>.FromElements(7), concrete);
            Bridge.Check(Text("shape"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "datatypes") {
          var shared = Fixture.Box<Dafny.IMap<BigInteger, byte>>.create_Box(Dafny.Map<BigInteger, byte>.FromElements(new Dafny.Pair<BigInteger, byte>(BigInteger.One, 7)));
          foreach (var item in new[] { (Value: (byte)7, Width: 7), (Value: (byte)7, Width: 8), (Value: (byte)9, Width: 7), (Value: (byte)7, Width: 7) }) {
            var map = Dafny.Map<BigInteger, byte>.FromElements(new Dafny.Pair<BigInteger, byte>(BigInteger.One, item.Value));
            var value = item.Value == 7 ? shared : Fixture.Box<Dafny.IMap<BigInteger, byte>>.create_Box(map);
            var shape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"map\",\"key\":{\"kind\":\"integer\"},\"value\":{\"kind\":\"bitvector\",\"width\":" + item.Width + "}}]}");
            var values = ContractDiagnosticBridge.SerializeNamed(Text("result"), value, shape);
            Bridge.Check(Text("datatype"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "mutable-datatype") {
          var items = new System.Collections.Generic.List<BigInteger> { 7 };
          var value = Fixture.Box<System.Collections.Generic.List<BigInteger>>.create_Box(items);
          var shape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"sequence\",\"element\":{\"kind\":\"integer\"}}]}");
          foreach (var number in new[] { 7, 9, 7 }) {
            items[0] = number;
            var values = ContractDiagnosticBridge.SerializeNamed(Text("result"), value, shape);
            Bridge.Check(Text("datatype"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "classes") {
          var cell = new Fixture.Cell();
          for (var index = 0; index < 3; index++) {
            if (index == 2) { cell = new Fixture.Cell(); }
            cell.@value = index == 0 ? 7 : 9;
            var values = ContractDiagnosticBridge.SerializeNamed(Text("cell"), cell, Shape("{\"kind\":\"other\"}"));
            Bridge.Check(Text("class"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "register-child") {
          var child = Fixture.Box<BigInteger>.create_Box(BigInteger.One);
          var parent = Fixture.Box<Fixture._IBox<BigInteger>>.create_Box(child);
          var shape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"integer\"}]}]}");
          for (var index = 0; index < 2; index++) {
            if (index == 1) {
              try { ContractDiagnosticBridge.Register(Text("registered-child"), Text("Fixture.Box"), child, Text(Convert.ToBase64String(Encoding.UTF8.GetBytes("{}")))); }
              catch (NotSupportedException) { }
            }
            var values = ContractDiagnosticBridge.SerializeNamed(Text("parent"), parent, shape);
            Bridge.Check(Text("registration"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "named-fragments") {
          var value = Fixture.Box<BigInteger>.create_Box(BigInteger.One);
          var shape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"integer\"}]}");
          foreach (var name in new[] { "left", "right🙂", "left" }) {
            var values = ContractDiagnosticBridge.SerializeNamed(Text(name), value, shape);
            Bridge.Check(Text("names"), BigInteger.Zero, true, Fragments(values));
          }
          Bridge.Complete();
          return;
        }
        if (scenario == "fragment-bytes") {
          var integer = Shape("{\"kind\":\"integer\"}");
          Bridge.Check(Text("empty"), BigInteger.Zero, true, Fragments());
          Bridge.Check(Text("one"), BigInteger.One, true,
            Fragments(ContractDiagnosticBridge.SerializeNamed(Text("one"), BigInteger.One, integer)));
          var unicode = ContractDiagnosticBridge.SerializeNamed(Text("right🙂"), new Dafny.Rune(0x1f642), Shape("{\"kind\":\"other\"}"));
          var first = ContractDiagnosticBridge.SerializeNamed(Text("same"), BigInteger.One, integer);
          var second = ContractDiagnosticBridge.SerializeNamed(Text("same"), new BigInteger(2), integer);
          Bridge.Checkpoint(Text("many"), new BigInteger(2), Fragments(unicode, first, second));
          Bridge.Complete();
          return;
        }
        if (scenario == "external-fragments") {
          Bridge.Check(Text("external"), BigInteger.Zero, true,
            Fragments(Text("\"first\":1,\"duplicate\":2"), Text("\"duplicate\":3")));
          Bridge.Complete();
          return;
        }
        if (scenario == "fragment-identity") {
          var value = Fixture.Box<BigInteger>.create_Box(BigInteger.One);
          var integerShape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"integer\"}]}");
          var bitvectorShape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"bitvector\",\"width\":8}]}");
          var first = ContractDiagnosticBridge.SerializeNamed(Text("value"), value, integerShape);
          var same = ContractDiagnosticBridge.SerializeNamed(Text("value"), value, integerShape);
          var label = ContractDiagnosticBridge.SerializeNamed(Text("other"), value, integerShape);
          var shape = ContractDiagnosticBridge.SerializeNamed(Text("value"), value, bitvectorShape);
          var array = new BigInteger[] { BigInteger.One };
          var arrayShape = Shape("{\"kind\":\"array\",\"type\":\"array<int>\",\"element\":{\"kind\":\"integer\"}}");
          var arrayFirst = ContractDiagnosticBridge.SerializeNamed(Text("array"), array, arrayShape);
          var arraySecond = ContractDiagnosticBridge.SerializeNamed(Text("array"), array, arrayShape);
          var items = new System.Collections.Generic.List<BigInteger> { BigInteger.One };
          var externalValue = Fixture.Box<System.Collections.Generic.List<BigInteger>>.create_Box(items);
          var externalShape = Shape("{\"kind\":\"datatype\",\"arguments\":[{\"kind\":\"sequence\",\"element\":{\"kind\":\"integer\"}}]}");
          var externalFirst = ContractDiagnosticBridge.SerializeNamed(Text("external"), externalValue, externalShape);
          var externalSecond = ContractDiagnosticBridge.SerializeNamed(Text("external"), externalValue, externalShape);
          var cell = new Fixture.Cell();
          var referenceFirst = ContractDiagnosticBridge.SerializeNamed(Text("cell"), cell, Shape("{\"kind\":\"other\"}"));
          var referenceSecond = ContractDiagnosticBridge.SerializeNamed(Text("cell"), cell, Shape("{\"kind\":\"other\"}"));
          Console.WriteLine(System.Text.Json.JsonSerializer.Serialize(new {
            same = Object.ReferenceEquals(first, same), label = Object.ReferenceEquals(first, label),
            shape = Object.ReferenceEquals(first, shape), array = Object.ReferenceEquals(arrayFirst, arraySecond),
            external = Object.ReferenceEquals(externalFirst, externalSecond), reference = Object.ReferenceEquals(referenceFirst, referenceSecond)
          }));
          Bridge.Complete();
          return;
        }
        if (scenario == "bad-fragment" || scenario == "bad-mixed-fragment") {
          var fragments = scenario == "bad-fragment"
            ? Fragments(Text("\"broken\":"))
            : Fragments(ContractDiagnosticBridge.SerializeNamed(Text("valid"), BigInteger.One, Shape("{\"kind\":\"integer\"}")), Text("\"broken\":"));
          Bridge.Check(Text("malformed"), BigInteger.Zero, true, fragments);
          return;
        }
        if (scenario == "error") {
          Bridge.Complete();
          Bridge.Location(Text("fixture:1"));
          throw new InvalidOperationException("fixture failure");
        }
        Bridge.Generated();
        if (scenario == "hold") {
          Console.WriteLine("ready");
          Console.Out.Flush();
          Thread.Sleep(Timeout.Infinite);
        } else if (scenario == "stop") {
          Bridge.Stop();
        } else if (scenario == "precondition") {
          Bridge.Check(Text("outer"), BigInteger.Zero,
            Bridge.Check(Text("call_precondition:fixture"), BigInteger.Zero, false,
              Fragments(ContractDiagnosticBridge.SerializeNamed(Text("nested"), new BigInteger(7), Shape("{\"kind\":\"integer\"}")))),
            Fragments(ContractDiagnosticBridge.SerializeNamed(Text("unreachable"), BigInteger.Zero, Shape("{\"kind\":\"integer\"}"))));
        } else {
          ContractDiagnosticBridge.Serialize(BigInteger.One, Shape("{\"kind\":\"integer\"}"));
          var bad = scenario == "bad-base64" ? Text("!") : scenario == "bad-json" ? Shape("{") : Shape("{\"kind\":\"parameter\",\"index\":0}");
          ContractDiagnosticBridge.Serialize(BigInteger.One, bad);
        }
        Console.WriteLine("unreachable");
        Bridge.Complete();
      }
    }
    public class TextProxy : System.Reflection.DispatchProxy {
      protected override object Invoke(System.Reflection.MethodInfo method, object[] arguments) {
        if (method.Name == "ToVerbatimString") { return "custom🙂"; }
        throw new InvalidOperationException("External string must use its own conversion.");
      }
    }
    """;
}
