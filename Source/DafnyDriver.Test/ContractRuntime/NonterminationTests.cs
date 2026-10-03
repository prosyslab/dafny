#nullable enable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Counterexamples from finite observations of nonterminating executions.</summary>
public class NonterminationTests : IClassFixture<NonterminationTests.Fixture> {
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("Nontermination", "Main").Buckets(6) with { SampleTimeout = 1000 };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public NonterminationTests(Fixture fixture) { }

  private static IEnumerable<string> Certificates(CampaignRun run, int bucket) =>
    CampaignRun.Ordinals(bucket).Select(ordinal => Path.Combine(run.Directory, "prefix-certificate-" + ordinal + ".json"))
      .Where(File.Exists);

  // Every sample is generated and classified by its own bucket, including those killed at the sample timeout.
  [Fact]
  public async Task ClassifiesEveryBucket() {
    var run = await Campaign.RunAsync(Main);
    const int size = CampaignSpec.BucketSize;
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, PreconditionRejected: size,
      Executed: Main.SampleCount - size, Valid: 2 * size, CalleeContractViolations: size, CalleeContractUnchecked: size,
      Timeouts: size, ViolatingSamples: 2 * size), run.Detail());
  }

  // A failed invariant remains a counterexample when the valid execution never returns.
  [Fact]
  public async Task ReportsInvariantFailureBeforeTimeout() {
    var run = await Campaign.RunAsync(Main);
    var (_, violations) = run.AssertViolated(0, "i == 0", ContractRuntimeObligationKind.LoopInvariantMaintenance);
    Assert.Empty(run.Errors(0));
    foreach (var violation in violations) {
      var certificate = CampaignRun.Json(Path.Combine(run.Directory, "prefix-certificate-" + violation.SampleOrdinal + ".json"));
      Assert.True(certificate.GetProperty("originalTimeout").GetBoolean());
      Assert.False(certificate.GetProperty("originalComplete").GetBoolean());
      Assert.True(certificate.GetProperty("recordCount").GetInt32() < certificate.GetProperty("originalRecordCount").GetInt32());
      Assert.Equal(violation.ObligationId, certificate.GetProperty("endpointId").GetString());
    }
  }

  // Rejected entry inputs are excluded from the denominators and cannot support a later invariant counterexample.
  [Fact]
  public async Task RejectsInvalidEntry() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(1));
    Assert.All(CampaignRun.Ordinals(1), ordinal =>
      Assert.Contains(run.Records(ordinal), record => record.GetProperty("kind").GetString() == "rejected"));
    Assert.Empty(Certificates(run, 1));
  }

  // A false helper contract before the invariant failure invalidates goal evidence.
  [Fact]
  public async Task ExcludesInvalidEarlierCallee() {
    var run = await Campaign.RunAsync(Main);
    run.AssertCalleeViolated(2);
    Assert.Empty(Certificates(run, 2));
  }

  // An undecidable helper contract before the invariant failure cannot be skipped.
  [Fact]
  public async Task ExcludesUncheckedEarlierCallee() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(3));
    Assert.Empty(run.CalleeViolations(3));
    Assert.Empty(run.Errors(3));
    Assert.Empty(Certificates(run, 3));
  }

  // A helper failure after the invariant endpoint cannot invalidate an earlier valid counterexample.
  [Fact]
  public async Task IgnoresCalleeFailureAfterEndpoint() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(4, "tag != 4", ContractRuntimeObligationKind.LoopInvariantEntry);
    Assert.Empty(run.CalleeViolations(4));
  }

  // An infinite run without a failed goal check is killed as a timeout before the next ordinal starts.
  [Fact]
  public async Task KeepsTimeoutWithoutInvariantFailure() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(5));
    Assert.True(run.Errors(5).Select(error => error.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(5)), run.Detail());
    Assert.All(run.Errors(5), error => Assert.Equal("sample_timeout", error.Message));
    Assert.Empty(Certificates(run, 5));
  }
}
