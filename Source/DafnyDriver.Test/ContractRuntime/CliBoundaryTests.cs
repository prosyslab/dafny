#nullable enable
using System;
using System.IO;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>The public <c>test-contracts --runtime-check</c> command boundary.</summary>
public class CliBoundaryTests {
  private const string ConstantGenerator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }";

  // Runs the command on one request in a fresh directory and decodes its structured result.
  private static async Task<(ContractProcessResult Process, ContractRuntimeCampaignResult Result)> RunCli(
    Func<string, ContractRuntimeCampaignRequest> request, int seconds) {
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-cli-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try {
      var path = Path.Combine(directory, "request.json");
      await File.WriteAllTextAsync(path, JsonSerializer.Serialize(request(directory), ContractJson.Options));
      using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(seconds));
      var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
        "test-contracts",
        path,
        "--runtime-check"], directory, timeout.Token);
      return (process, JsonSerializer.Deserialize<ContractRuntimeCampaignResult>(process.StandardOutput, ContractJson.Options)!);
    }
    finally {
      ContractArtifacts.Delete(directory);
    }
  }

  // CLI validation failures keep the caller seed so the strict transport can decode the receipt.
  [Fact]
  public async Task CliPreservesSeedOnGeneratorFailure() {
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(x:bool) { x:=false; }";
    var (_, result) = await RunCli(_ => new(2, [Campaign.Source("M.dfy", "module M { method Goal(x:int) {} }")],
      new("M.Goal"), "17", Generator: Campaign.Source("G.dfy", generator)), 30);
    Assert.Equal("17", result.Seed);
    Assert.Equal(ContractRuntimeStatus.Unsupported, result.Status);
  }

  // A genuine backend error reaches the public structured result with its compiler code and offending symbol.
  [Fact]
  public async Task CliReportsBackendCompilationError() {
    const string dependency = "class BrokenDependency { static int Value() => MissingContractDiagnosticSymbol; }";
    var (process, result) = await RunCli(directory => {
      var dependencyPath = Path.Combine(directory, "BrokenDependency.cs");
      File.WriteAllText(dependencyPath, dependency);
      return new(2, [Campaign.Source("M.dfy", "module M { method Goal(x:int) ensures true {} }")], new("M.Goal"), "17",
        Dependencies: [new(dependencyPath, Campaign.Hash(dependency))],
        Generator: Campaign.Source("G.dfy", ConstantGenerator), SampleCount: 1);
    }, 60);
    Assert.Equal(0, process.ExitCode);
    Assert.Equal(ContractRuntimeStatus.Unsupported, result.Status);
    Assert.Equal(0, result.Population.Generated);
    Assert.Contains("CS0103", result.Reason);
    Assert.Contains("MissingContractDiagnosticSymbol", result.Reason);
  }
}
