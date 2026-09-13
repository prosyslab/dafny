#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractExternExecutionTests {
  // The compiler worker executes the contract model while a linked native extern remains observably uncalled.
  [Fact]
  public async Task DiagnosticExecutableDoesNotInvokeNativeExtern() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-extern-execution-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try {
      var markerPath = Path.Combine(directory, "native-marker.txt");
      var dependencyPath = Path.Combine(directory, "NativeDependency.cs");
      var dependencySource = $$"""
        using System.IO;
        using System.Numerics;
        public static class NativeDependency {
          public static BigInteger External(BigInteger x) {
            File.WriteAllText({{JsonSerializer.Serialize(markerPath)}}, "called");
            return -1;
          }
        }
        """;
      await File.WriteAllTextAsync(dependencyPath, dependencySource);
      const string source = "function {:extern \"NativeDependency\", \"External\"} External(x:int):(r:int) ensures r == x+1 method Entry(x:int) returns(r:int) ensures r == x+1 { r := External(x); }";
      var sourcePath = Path.Combine(directory, "program.dfy");
      var request = new ContractTestRequest(ContractJson.SchemaVersion,
        [new(sourcePath, source, ContractHarnessBuilder.Hash(source))], new("Entry"),
        new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "6") },
        Dependencies: [new(dependencyPath,
          Convert.ToHexString(SHA256.HashData(await File.ReadAllBytesAsync(dependencyPath))).ToLowerInvariant())],
        TimeoutMilliseconds: 60000);
      var options = new DafnyOptions(DafnyOptions.Default);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
      var prepared = await ContractCompilerWorker.ParseAsync(request, options, timeout.Token);
      var outputDirectory = Path.Combine(directory, "output");
      var result = await new ContractTestRunner(new DriverContractProgramCompiler())
        .RunAsync(prepared, request, outputDirectory, timeout.Token);
      Assert.True(result.Status == ContractTestStatus.Passed,
        $"{result.Status}: {result.Reason}\n{result.StandardError}");
      Assert.Equal(new ContractValue(ContractValueKind.Integer, "7"), result.Outputs!["r"]);
      Assert.True(result.UsedContractModels);
      Assert.False(File.Exists(markerPath));
    }
    finally {
      Directory.Delete(directory, true);
    }
  }

  // The generated runtime decodes modeled finite collections and encodes their multiplicities back to schema-1 values.
  [Fact]
  public async Task DiagnosticExecutableRoundTripsFiniteCollections() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-collection-execution-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try {
      const string source = "method {:extern} Missing() returns(s:set<int>, m:multiset<int>) " +
        "ensures s == {1, 7} && m == multiset{1, 7, 7} " +
        "method Entry() returns(s:set<int>, m:multiset<int>) " +
        "ensures s == {1, 7} && m == multiset{1, 7, 7} { s, m := Missing(); }";
      var sourcePath = Path.Combine(directory, "program.dfy");
      var request = new ContractTestRequest(ContractJson.SchemaVersion,
        [new(sourcePath, source, ContractHarnessBuilder.Hash(source))], new("Entry"),
        new Dictionary<string, ContractValue>(), TimeoutMilliseconds: 60000);
      var options = new DafnyOptions(DafnyOptions.Default);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
      var prepared = await ContractCompilerWorker.ParseAsync(request, options, timeout.Token);

      var result = await new ContractTestRunner(new DriverContractProgramCompiler())
        .RunAsync(prepared, request, Path.Combine(directory, "output"), timeout.Token);

      Assert.True(result.Status == ContractTestStatus.Passed,
        $"{result.Status}: {result.Reason}\n{result.StandardError}");
      Assert.Equal(2, result.Outputs!["s"].Items!.Count);
      Assert.Equal(3, result.Outputs["m"].Items!.Count);
      Assert.Equal(2, result.Outputs["m"].Items!.Count(item => item.Value == "7"));
    }
    finally {
      Directory.Delete(directory, true);
    }
  }

  // The generated runtime preserves non-native bitvector widths recursively alongside constrained scalar outputs.
  [Fact]
  public async Task DiagnosticExecutableRoundTripsBitvectorAndRefinedValues() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-scalar-execution-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try {
      const string source = "type Positive = x:int | x > 0 witness 1 " +
        "newtype Small = x:int | 0 <= x < 10 witness 0 " +
        "method {:extern} Missing() returns(small:bv7, wide:bv128, items:seq<bv7>, x:Positive, y:Small) " +
        "ensures small == 127 && wide == 1267650600228229401496703205376 && items == [1, 127] && x == 7 && y == 8 " +
        "method Entry() returns(small:bv7, wide:bv128, items:seq<bv7>, x:Positive, y:Small) " +
        "ensures small == 127 && wide == 1267650600228229401496703205376 && items == [1, 127] && x == 7 && y == 8 " +
        "{ small, wide, items, x, y := Missing(); }";
      var sourcePath = Path.Combine(directory, "program.dfy");
      var request = new ContractTestRequest(ContractJson.SchemaVersion,
        [new(sourcePath, source, ContractHarnessBuilder.Hash(source))], new("Entry"),
        new Dictionary<string, ContractValue>(), TimeoutMilliseconds: 60000);
      var options = new DafnyOptions(DafnyOptions.Default);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
      var prepared = await ContractCompilerWorker.ParseAsync(request, options, timeout.Token);

      var result = await new ContractTestRunner(new DriverContractProgramCompiler())
        .RunAsync(prepared, request, Path.Combine(directory, "output"), timeout.Token);

      Assert.True(result.Status == ContractTestStatus.Passed,
        $"{result.Status}: {result.Reason}\n{result.StandardError}");
      Assert.Equal(new ContractValue(ContractValueKind.Bitvector, "127", Width: 7), result.Outputs!["small"]);
      Assert.Equal(new ContractValue(ContractValueKind.Bitvector, "1267650600228229401496703205376", Width: 128),
        result.Outputs["wide"]);
      Assert.Equal([new ContractValue(ContractValueKind.Bitvector, "1", Width: 7),
        new ContractValue(ContractValueKind.Bitvector, "127", Width: 7)], result.Outputs["items"].Items);
      Assert.Equal(new ContractValue(ContractValueKind.Integer, "7"), result.Outputs["x"]);
      Assert.Equal(new ContractValue(ContractValueKind.Integer, "8"), result.Outputs["y"]);
    }
    finally {
      Directory.Delete(directory, true);
    }
  }
}
