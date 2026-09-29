#nullable enable
using System;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>Checks counterexamples from finite observations of nonterminating executions.</summary>
public class ContractRuntimePrefixTests {
  // A failed invariant remains a counterexample when the valid execution never returns.
  [Fact]
  public async Task ReportsInvariantFailureBeforeTimeout() {
    var (result, directory) = await Run("method Goal(x:int) requires x > 0 { var i := 0; while true invariant i == 0 { i := 1; } }");
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, JsonSerializer.Serialize(result.Population, ContractJson.Options));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.Timeouts);
    Assert.Single(result.Violations);
    var certificate = JsonDocument.Parse(await File.ReadAllTextAsync(
      Assert.Single(Directory.GetFiles(directory, "prefix-certificate-*.json")))).RootElement;
    Assert.True(certificate.GetProperty("originalTimeout").GetBoolean());
    Assert.False(certificate.GetProperty("originalComplete").GetBoolean());
    Assert.True(certificate.GetProperty("recordCount").GetInt32() < certificate.GetProperty("originalRecordCount").GetInt32());
    Assert.Equal(result.Violations[0].ObligationId, certificate.GetProperty("endpointId").GetString());
  }

  // An invalid entry cannot support a later invariant counterexample.
  [Fact]
  public async Task RejectsInvalidEntry() {
    var (result, directory) = await Run("method Goal(x:int) requires x < 0 { while true invariant false {} }");
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.PreconditionRejected);
    Assert.Empty(Directory.GetFiles(directory, "prefix-certificate-*.json"));
  }

  // A false helper contract before the invariant failure invalidates goal evidence.
  [Fact]
  public async Task ExcludesInvalidEarlierCallee() {
    var (result, directory) = await Run("method Help() returns (r:int) ensures r == 0 { r := 1; } method Goal(x:int) { var r := Help(); while true invariant false {} }");
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractViolations);
    Assert.Empty(Directory.GetFiles(directory, "prefix-certificate-*.json"));
  }

  // An undecidable helper contract before the invariant failure cannot be skipped.
  [Fact]
  public async Task ExcludesUncheckedEarlierCallee() {
    var (result, directory) = await Run("method Help() ensures forall i:int :: i * i >= 0 {} method Goal(x:int) { Help(); while true invariant false {} }");
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractUnchecked);
    Assert.Empty(Directory.GetFiles(directory, "prefix-certificate-*.json"));
  }

  // A helper failure after the invariant endpoint cannot invalidate an earlier valid counterexample.
  [Fact]
  public async Task IgnoresCalleeFailureAfterEndpoint() {
    var (result, _) = await Run("method Help() ensures false {} method Goal(x:int) { while true invariant false { Help(); } }");
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, JsonSerializer.Serialize(result.Population, ContractJson.Options));
    Assert.Equal(0, result.Population.CalleeContractViolations);
    Assert.Empty(result.CalleeViolations);
  }

  // An infinite run without a failed goal check remains a timeout.
  [Fact]
  public async Task KeepsTimeoutWithoutInvariantFailure() {
    var (result, directory) = await Run("method Goal(x:int) { while true {} }");
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Equal(1, result.Population.Timeouts);
    Assert.Empty(result.Violations);
    Assert.Empty(Directory.GetFiles(directory, "prefix-certificate-*.json"));
  }

  private static async Task<(ContractRuntimeCampaignResult Result, string Directory)> Run(string declarations) {
    var source = "module M { " + declarations + " }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(x:int) { x := 1; }";
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-prefix-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var request = new ContractRuntimeCampaignRequest(1, [new("M.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("M.Goal"), "17", Generator: new("G.dfy", generator, ContractHarnessBuilder.Hash(generator)),
      SampleCount: 1, TimeoutMilliseconds: 60000, MaxClosedQueries: 0, SampleTimeoutMilliseconds: 1000);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
    return (await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token), directory);
  }
}
