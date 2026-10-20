#nullable enable
using System.Text.Json;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

// These checks use JSON values and pure result helpers, never campaign execution or staging.
public sealed class GeneratorProofResultTests {
  // An early opt-in failure reports its distinct result schema and an evidence-free proof outcome.
  [Fact]
  public void OptInFailureUsesProvedInputSchema() {
    var legacy = ContractRuntimeCampaignRunner.Failure(ContractRuntimeStatus.Error, "early", "1");
    var optedIn = ContractRuntimeCampaignRunner.Failure(ContractRuntimeStatus.Error, "early", "1", true);
    using var legacyJson = JsonDocument.Parse(JsonSerializer.Serialize(legacy, ContractJson.Options));
    using var proofJson = JsonDocument.Parse(JsonSerializer.Serialize(optedIn, ContractJson.Options));

    Assert.Equal(1, legacy.SchemaVersion);
    Assert.False(legacyJson.RootElement.TryGetProperty("generatorProof", out _));
    Assert.Equal(3, optedIn.SchemaVersion);
    Assert.Equal("not_attempted", proofJson.RootElement.GetProperty("generatorProof").GetProperty("status").GetString());
    Assert.False(optedIn.GeneratorProof!.EntryRequiresOmitted);
  }

  // The optional request field remains absent from legacy JSON and selects request schema four when true.
  [Fact]
  public void LegacyRequestKeepsOmittedProofField() {
    var request = new ContractRuntimeCampaignRequest(2, [], new("M.Goal"), "1");
    using var legacy = JsonDocument.Parse(JsonSerializer.Serialize(request, ContractJson.Options));
    using var proof = JsonDocument.Parse(JsonSerializer.Serialize(request with {
      SchemaVersion = 4,
      ProveGeneratorPreconditions = true
    }, ContractJson.Options));

    Assert.False(legacy.RootElement.TryGetProperty("proveGeneratorPreconditions", out _));
    Assert.True(proof.RootElement.GetProperty("proveGeneratorPreconditions").GetBoolean());
    Assert.Equal(4, ContractRuntimeCampaignSchema.RequestVersion(true));
  }

  // The proof budget leaves half the remaining campaign time and never exceeds ten seconds.
  [Theory]
  [InlineData(240000, 0, 10000)]
  [InlineData(12000, 2000, 5000)]
  [InlineData(10000, 9999, 0)]
  [InlineData(10000, 10000, 0)]
  public void ProofBudgetLeavesCampaignTime(int timeout, long elapsed, int expected) {
    Assert.Equal(expected, ContractRuntimeCampaignRunner.GeneratorProofBudgetMilliseconds(timeout, elapsed));
  }

  // Complete public status metadata cannot report successful omission when the internal certificate gate rejected it.
  [Fact]
  public void VerifiedMetadataWithoutOmissionIsUnsupported() {
    var report = new ContractGeneratorProofReport(ContractGeneratorProofStatus.Verified, "fake", ["check"], ["check"]);
    var result = ContractRuntimeCampaignRunner.GeneratorProofResult(report, false, 1);

    Assert.Equal(ContractRuntimeGeneratorProofStatus.Unsupported, result.Status);
    Assert.False(result.EntryRequiresOmitted);
  }

  // A nominally verified attempt with missing coverage remains unsupported even if omission was reported.
  [Fact]
  public void IncompleteVerifiedCoverageIsUnsupported() {
    var report = new ContractGeneratorProofReport(ContractGeneratorProofStatus.Verified, "fake", ["first", "second"], ["first"]);
    var result = ContractRuntimeCampaignRunner.GeneratorProofResult(report, true, 1);

    Assert.Equal(ContractRuntimeGeneratorProofStatus.Unsupported, result.Status);
    Assert.False(result.EntryRequiresOmitted);
  }
}
