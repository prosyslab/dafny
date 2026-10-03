#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Declared input and output type constraints; every scenario is one bucket of a single campaign.</summary>
public class InputValidityTests : IClassFixture<InputValidityTests.Fixture> {
  private const int Control = 10;
  private const string Marker = "tag < 0";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("InputValidity", "Main").Buckets(14);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public InputValidityTests(Fixture fixture) { }

  // Exactly the ten invalid-input buckets are rejected; the control and output buckets are valid.
  [Fact]
  public async Task RejectsOnlyInvalidInputBuckets() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount,
      PreconditionRejected: 10 * CampaignSpec.BucketSize, Executed: 4 * CampaignSpec.BucketSize,
      Valid: 4 * CampaignSpec.BucketSize, ViolatingSamples: 4 * CampaignSpec.BucketSize), run.Detail());
  }

  // A generated input outside a declared constraint, at any supported nesting, is rejected like a failed precondition.
  [Theory]
  [InlineData(0, "nat formal")]
  [InlineData(1, "newtype in a sequence")]
  [InlineData(2, "nat datatype field")]
  [InlineData(3, "nat sequence in a datatype field")]
  [InlineData(4, "nat sequence in a map range")]
  [InlineData(5, "nat in five nested sequences")]
  [InlineData(6, "null non-null formal")]
  [InlineData(7, "null non-null datatype field")]
  [InlineData(8, "nat in a recursive list")]
  [InlineData(9, "nat in a recursive map child")]
  public async Task RejectsInvalidInput(int bucket, string constraint) {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(bucket));
    Assert.All(CampaignRun.Ordinals(bucket), ordinal => Assert.True(
      run.Records(ordinal).Any(record => record.GetProperty("kind").GetString() == "rejected"), constraint));
  }

  // Valid values of every constrained input shape admit the sample as goal evidence.
  [Fact]
  public async Task AcceptsValidInputs() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(Control, Marker, exclusive: false);
    Assert.All(run.Violations(Control), violation => Assert.Equal(Marker, run.Result.Obligations
      .Single(obligation => obligation.Id == violation.ObligationId).Clause));
  }

  // Multiple method outputs retain executable structural constraints without capturing C# out parameters in lambdas.
  [Theory]
  [InlineData(11, "outBox")]
  [InlineData(12, "outSeq")]
  [InlineData(13, "outMap")]
  public async Task ChecksMultipleStructuralOutputs(int bucket, string output) {
    var run = await Campaign.RunAsync(Main);
    var markerId = run.Obligation(Marker).Id;
    var violations = run.Violations(bucket).Where(violation => violation.ObligationId != markerId).ToList();
    Assert.True(violations.Select(violation => violation.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(bucket)),
      run.Detail());
    Assert.All(violations, violation => {
      Assert.Equal(ContractRuntimeObligationKind.Postcondition, violation.Kind);
      Assert.True(violation.Values.ContainsKey(output));
    });
  }
}
