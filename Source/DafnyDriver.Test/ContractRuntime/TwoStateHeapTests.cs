#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Original two-state heap postconditions decided over captured entry and return heaps.</summary>
public class TwoStateHeapTests : IClassFixture<TwoStateHeapTests.Fixture> {
  private const string File = "TwoStateHeap";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture(File, "Main", "Client.Goal").Buckets(4) with {
    ClosedQueryTimeout = 3000
  };
  private static readonly CampaignSpec Observed = CampaignSpec.Fixture(File, "Observed", "Client.Goal").Buckets(3) with {
    ClosedQueryTimeout = 3000
  };
  private static readonly CampaignSpec CertifiedSpecification =
    CampaignSpec.Fixture(File, "CertifiedSpecification", "Client.Goal").Buckets(2) with {
      ClosedQueryTimeout = 3000
    };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main, Observed, CertifiedSpecification];
  }

  public TwoStateHeapTests(Fixture fixture) { }

  private const string Changed = "Changed(cell, amount)";

  // Every transition bucket is valid except the one excluded by its invalid callee, and no heap query faults.
  [Fact]
  public async Task ClassifiesEveryTransitionBucket() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount,
      Valid: 3 * CampaignSpec.BucketSize, CalleeContractViolations: CampaignSpec.BucketSize,
      ViolatingSamples: 2 * CampaignSpec.BucketSize), run.Detail());
  }

  // A fully captured ghost input decides both original old/current heap polarities without replacing either heap.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task CapturedGhostHeapDecidesOriginalTransition(int bucket, bool holds) {
    var run = await Campaign.RunAsync(Main);
    var obligation = run.Obligation(Changed, Postcondition);
    // Buckets 0-2 decide the shared clause by closed query; bucket 3 is excluded by its callee and leaves it unchecked.
    // Only buckets 0 and 2 violate it, so bucket 1 is decided and holds in every sample.
    Assert.Equal(new ContractRuntimeEvaluations(ClosedSmt: 3 * CampaignSpec.BucketSize, Unchecked: CampaignSpec.BucketSize),
      obligation.Evaluations);
    Assert.Equal(2 * CampaignSpec.BucketSize, obligation.Violations);
    if (holds) {
      Assert.Empty(run.Violations(bucket));
      return;
    }
    var (_, violations) = run.AssertViolated(bucket, Changed, Postcondition, exclusive: false);
    Assert.All(violations, violation => {
      Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, violation.DecisionMethod);
      Assert.Equal("2", violation.Inputs["amount"].Value);
      Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$initial/") && pair.Value.Value == "7");
      Assert.Contains(violation.Values, pair => pair.Key.StartsWith("$final/") && pair.Value.Value == "8");
    });
  }

  // Actual captured transitions retain native original Q after a checked heap-projection equivalence.
  [Fact]
  public async Task HeapProjectionKeepsOriginalRuntimeTransition() {
    var run = await Campaign.RunAsync(Main);
    Assert.Equal(0, run.Population.RuntimeErrors);
    Assert.Contains(run.Artifacts("heap-query-*.result.json"), path =>
      System.IO.File.ReadAllText(path).Contains("addedCheckedEquivalences=1", StringComparison.Ordinal));
  }

  // Synthetic entry and call wrappers retain the original declarations' nontermination permission.
  [Fact]
  public async Task PreservesNonterminationPermission() {
    (await Campaign.RunAsync(Main)).AssertViolated(2, Changed, Postcondition, exclusive: false);
  }

  // A violated executed callee contract excludes the sample before final heap evidence is considered.
  [Fact]
  public async Task InvalidCalleeExcludesHeapDecision() {
    var run = await Campaign.RunAsync(Main);
    Assert.All(run.AssertCalleeViolated(3), violation => Assert.Equal("Client.Bad", violation.Callee));
    var obligation = run.Obligation(Changed, Postcondition);
    Assert.Equal(CampaignSpec.BucketSize, obligation.Evaluations.Unchecked);
    Assert.Equal("callee_contract_unvalidated", obligation.UncheckedReason);
  }

  // Explicit initial construction and exact final memberships preserve both original two-state polarities.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task ObservedConstructionDecidesBothOriginalPolarities(int bucket, bool holds) {
    var run = await Campaign.RunAsync(Observed);
    if (holds) {
      Assert.Empty(run.Violations(bucket));
    } else {
      run.AssertViolated(bucket, "Changed(cell, result)", Postcondition);
    }
    Assert.True(run.Obligation("Changed(cell, result)", Postcondition).Evaluations.ClosedSmt >= 2 * CampaignSpec.BucketSize,
      run.Detail());
    // Identical later samples of the bucket reuse the cached decision, so the first ordinal holds the certificate.
    var certificate = CampaignRun.Json(Path.Combine(run.Directory, "observed-type-certificate-" + CampaignRun.Ordinals(bucket)[0] + ".json"));
    Assert.True(certificate.GetProperty("constructive").GetBoolean());
    Assert.True(certificate.GetProperty("passed").GetBoolean());
    Assert.False(certificate.GetProperty("requiresNativeProof").GetBoolean());
    Assert.NotEmpty(certificate.GetProperty("runtimeChecks").EnumerateArray());
  }

  // A rejected original P cannot be bypassed by valid captured type memberships in either heap.
  [Fact]
  public async Task ObservedConstructionKeepsInvalidEntryRejected() {
    var run = await Campaign.RunAsync(Observed);
    Assert.Empty(run.Violations(2));
    Assert.Equal(CampaignSpec.BucketSize, run.Population.PreconditionRejected);
    Assert.All(CampaignRun.Ordinals(2), ordinal =>
      Assert.False(System.IO.File.Exists(Path.Combine(run.Directory, "observed-type-certificate-" + ordinal + ".json"))));
  }

  // A certified requires-only specification supports either polarity of the unchanged captured-heap property.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task CertifiedSpecificationDecidesBothHeapPolarities(int bucket, bool holds) {
    var run = await Campaign.RunAsync(CertifiedSpecification);
    Assert.Equal(CertifiedSpecification.SampleCount, run.Population.Valid);
    Assert.Equal(CertifiedSpecification.SampleCount, run.Obligation("Changed(cell)", Postcondition).Evaluations.ClosedSmt);
    if (holds) {
      Assert.Empty(run.Violations(bucket));
    } else {
      run.AssertViolated(bucket, "Changed(cell)", Postcondition);
    }
  }
}
