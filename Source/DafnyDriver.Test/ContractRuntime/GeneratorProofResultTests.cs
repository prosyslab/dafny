#nullable enable
using System.Text.Json;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

// These checks use JSON values, pure result helpers, and pre-artifact request validation; they never stage sources or execute a campaign.
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
    Assert.False(legacyJson.RootElement.TryGetProperty("terminalStage", out _));
    Assert.False(legacyJson.RootElement.TryGetProperty("noValidSampleReasons", out _));
    Assert.Equal(3, optedIn.SchemaVersion);
    Assert.Equal("not_attempted", proofJson.RootElement.GetProperty("generatorProof").GetProperty("status").GetString());
    Assert.False(proofJson.RootElement.TryGetProperty("terminalStage", out _));
    Assert.False(proofJson.RootElement.TryGetProperty("noValidSampleReasons", out _));
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
    Assert.False(legacy.RootElement.TryGetProperty("externExecution", out _));
    Assert.True(proof.RootElement.GetProperty("proveGeneratorPreconditions").GetBoolean());
    Assert.Equal(4, ContractRuntimeCampaignSchema.RequestVersion(true));
  }

  // Native extern requests use distinct strict schemas while legacy requests retain their exact omitted mode field.
  [Fact]
  public void NativeExternRequestsUseExplicitVersionedMode() {
    var request = new ContractRuntimeCampaignRequest(ContractRuntimeCampaignSchema.NativeRequestVersion,
      [], new("M.Goal"), "1", ExternExecution: ContractRuntimeExternExecution.Native);
    var proved = request with {
      SchemaVersion = ContractRuntimeCampaignSchema.ProvedNativeRequestVersion,
      ProveGeneratorPreconditions = true
    };
    using var nativeJson = JsonDocument.Parse(JsonSerializer.Serialize(request, ContractJson.Options));
    using var provedJson = JsonDocument.Parse(JsonSerializer.Serialize(proved, ContractJson.Options));
    var nativeResult = ContractRuntimeCampaignRunner.Failure(request, ContractRuntimeStatus.Error, "early",
      ContractRuntimeTerminalStage.Input, ContractRuntimeNoValidSampleReason.PipelineNotReached);
    var provedResult = ContractRuntimeCampaignRunner.Failure(proved, ContractRuntimeStatus.Error, "early",
      ContractRuntimeTerminalStage.Input, ContractRuntimeNoValidSampleReason.PipelineNotReached);

    Assert.Equal("native", nativeJson.RootElement.GetProperty("externExecution").GetString());
    Assert.Equal("native", provedJson.RootElement.GetProperty("externExecution").GetString());
    Assert.True(provedJson.RootElement.GetProperty("proveGeneratorPreconditions").GetBoolean());
    Assert.Equal(5, ContractRuntimeCampaignSchema.RequestVersion(false, ContractRuntimeExternExecution.Native));
    Assert.Equal(6, ContractRuntimeCampaignSchema.RequestVersion(true, ContractRuntimeExternExecution.Native));
    Assert.Equal(ContractRuntimeCampaignSchema.LegacyResultVersion, nativeResult.SchemaVersion);
    Assert.Equal(ContractRuntimeCampaignSchema.ProvedInputResultVersion, provedResult.SchemaVersion);
    Assert.True(ContractRuntimeCampaignSchema.IsCompatibleResult(request, nativeResult));
    Assert.True(ContractRuntimeCampaignSchema.IsCompatibleResult(proved, provedResult));
  }

  // Every request version rejects an absent, explicit-draft or proof mode that belongs to another wire schema.
  [Fact]
  public void RejectsMismatchedExternExecutionSchemasBeforeArtifacts() {
    const string content = "method Goal() {}";
    var source = new ContractSource("M.dfy", content, ContractHarnessBuilder.Hash(content));
    ContractRuntimeCampaignRequest[] invalid = [
      new(2, [source], new("Goal"), "1", ExternExecution: ContractRuntimeExternExecution.Draft),
      new(2, [source], new("Goal"), "1", ExternExecution: ContractRuntimeExternExecution.Native),
      new(5, [source], new("Goal"), "1"),
      new(5, [source], new("Goal"), "1", ProveGeneratorPreconditions: true,
        ExternExecution: ContractRuntimeExternExecution.Native),
      new(6, [source], new("Goal"), "1", ExternExecution: ContractRuntimeExternExecution.Native)
    ];

    foreach (var request in invalid) {
      Assert.Throws<ArgumentException>(() => ContractRuntimeCampaignRunner.ValidateRequest(request));
    }
  }

  // Structured requests accept every explicit proof and extern policy pairing and require result schema four.
  [Fact]
  public void StructuredRequestSupportsAllExplicitPolicies() {
    foreach (var prove in new[] { false, true }) {
      foreach (var externExecution in new[] { ContractRuntimeExternExecution.Draft, ContractRuntimeExternExecution.Native }) {
        var request = StructuredRequest(prove, externExecution);

        ContractRuntimeCampaignRunner.ValidateRequest(request);
        var result = ContractRuntimeCampaignRunner.Failure(request, ContractRuntimeStatus.Error, "early",
          ContractRuntimeTerminalStage.Input, ContractRuntimeNoValidSampleReason.PipelineNotReached);

        Assert.Equal(ContractRuntimeCampaignSchema.StructuredResultVersion, result.SchemaVersion);
        Assert.Equal(prove, result.GeneratorProof != null);
        Assert.True(ContractRuntimeCampaignSchema.IsCompatibleResult(request, result));
      }
    }
  }

  // Structured requests reject an omitted extern policy before campaign artifacts can be created.
  [Fact]
  public void StructuredRequestRequiresExplicitExternPolicy() {
    var request = StructuredRequest(false, ContractRuntimeExternExecution.Draft) with { ExternExecution = null };

    Assert.Throws<ArgumentException>(() => ContractRuntimeCampaignRunner.ValidateRequest(request));
  }

  // A decoded malformed legacy request keeps the result pairing selected by its request schema.
  [Fact]
  public void DecodedLegacySchemaControlsFailurePairing() {
    var nativeWithProof = new ContractRuntimeCampaignRequest(ContractRuntimeCampaignSchema.NativeRequestVersion,
      [], new("Goal"), "1", ProveGeneratorPreconditions: true,
      ExternExecution: ContractRuntimeExternExecution.Native);
    var provedWithoutProof = nativeWithProof with {
      SchemaVersion = ContractRuntimeCampaignSchema.ProvedInputRequestVersion,
      ProveGeneratorPreconditions = false,
      ExternExecution = null
    };

    var nativeResult = ContractRuntimeCampaignRunner.Failure(nativeWithProof, ContractRuntimeStatus.Error, "invalid",
      ContractRuntimeTerminalStage.Input, ContractRuntimeNoValidSampleReason.PipelineNotReached);
    var provedResult = ContractRuntimeCampaignRunner.Failure(provedWithoutProof, ContractRuntimeStatus.Error, "invalid",
      ContractRuntimeTerminalStage.Input, ContractRuntimeNoValidSampleReason.PipelineNotReached);

    Assert.Equal(ContractRuntimeCampaignSchema.LegacyResultVersion, nativeResult.SchemaVersion);
    Assert.Null(nativeResult.GeneratorProof);
    Assert.Equal(ContractRuntimeCampaignSchema.ProvedInputResultVersion, provedResult.SchemaVersion);
    Assert.NotNull(provedResult.GeneratorProof);
  }

  // Structured failures serialize typed terminal metadata while preserving the ordinary diagnostic reason.
  [Fact]
  public void StructuredFailureSerializesTerminalMetadata() {
    var request = StructuredRequest(false, ContractRuntimeExternExecution.Draft);
    var result = ContractRuntimeCampaignRunner.Failure(request, ContractRuntimeStatus.Error, "worker failed",
      ContractRuntimeTerminalStage.Supervision, ContractRuntimeNoValidSampleReason.WorkerResultUnavailable);
    using var json = JsonDocument.Parse(JsonSerializer.Serialize(result, ContractJson.Options));

    Assert.Equal("supervision", json.RootElement.GetProperty("terminalStage").GetString());
    Assert.Equal("worker_result_unavailable",
      json.RootElement.GetProperty("noValidSampleReasons")[0].GetString());
    Assert.Equal("worker failed", result.Reason);
  }

  // A worker receipt using result schema four without its required metadata is incompatible with request seven.
  [Fact]
  public void StructuredRequestRejectsIncompleteWorkerReceipt() {
    var request = StructuredRequest(false, ContractRuntimeExternExecution.Draft);
    var incomplete = ContractRuntimeCampaignRunner.Failure(ContractRuntimeStatus.Error, "old") with {
      SchemaVersion = ContractRuntimeCampaignSchema.StructuredResultVersion
    };

    Assert.False(ContractRuntimeCampaignSchema.IsCompatibleResult(request, incomplete));
  }

  // Mixed rejected, unchecked, failed, and timed-out samples produce every applicable reason in stable order.
  [Fact]
  public void NoValidSampleReasonsAreDeterministic() {
    var population = new ContractRuntimePopulation(PreconditionRejected: 1, PreconditionUnchecked: 1,
      CalleeContractViolations: 1, CalleeContractUnchecked: 1, RuntimeErrors: 1, Timeouts: 1);

    Assert.Equal(new[] {
      ContractRuntimeNoValidSampleReason.RequiresRejected,
      ContractRuntimeNoValidSampleReason.RequiresUnchecked,
      ContractRuntimeNoValidSampleReason.CalleeContractRejected,
      ContractRuntimeNoValidSampleReason.CalleeContractUnchecked,
      ContractRuntimeNoValidSampleReason.RuntimeError,
      ContractRuntimeNoValidSampleReason.SampleTimeout
    }, ContractRuntimeCampaignRunner.NoValidSampleReasons(population, false));
  }

  // A sampling deadline reached before the first process starts has one direct typed cause.
  [Fact]
  public void ZeroScheduledSamplesReportSamplingBudget() {
    Assert.Equal(new[] { ContractRuntimeNoValidSampleReason.SamplingBudgetExpired },
      ContractRuntimeCampaignRunner.NoValidSampleReasons(new(), true));
  }

  // A partial sampling run retains both the exhausted campaign allowance and the observed invalid-sample cause.
  [Fact]
  public void PartialSamplingBudgetRetainsObservedCause() {
    var population = new ContractRuntimePopulation(PreconditionRejected: 1);

    Assert.Equal(new[] {
      ContractRuntimeNoValidSampleReason.SamplingBudgetExpired,
      ContractRuntimeNoValidSampleReason.RequiresRejected
    }, ContractRuntimeCampaignRunner.NoValidSampleReasons(population, true));
  }

  // Any valid observation makes the no-valid-sample reason list empty even when other samples were rejected.
  [Fact]
  public void ValidPopulationHasNoInvalidSampleSummary() {
    var population = new ContractRuntimePopulation(PreconditionRejected: 1, Valid: 1);

    Assert.Empty(ContractRuntimeCampaignRunner.NoValidSampleReasons(population, false));
  }

  // A null draft is rejected at the request boundary before campaign recorders or disk paths are constructed.
  [Fact]
  public async Task NullDraftIsRejectedBeforeCampaignArtifacts() {
    const string content = "method Goal() {}";
    var source = new ContractSource("M.dfy", content, ContractHarnessBuilder.Hash(content));
    var request = new ContractRuntimeCampaignRequest(2, [source], new("Goal"), "1", Drafts: [null!]);

    await Assert.ThrowsAsync<ArgumentException>(() => ContractRuntimeCampaignRunner.RunAsync(
      request, null!, "/workspace/unused-null-draft-campaign", CancellationToken.None));
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

  private static ContractRuntimeCampaignRequest StructuredRequest(bool proveGeneratorPreconditions,
    ContractRuntimeExternExecution externExecution) {
    const string content = "method Goal() {}";
    return new(ContractRuntimeCampaignSchema.StructuredRequestVersion,
      [new("M.dfy", content, ContractHarnessBuilder.Hash(content))], new("Goal"), "1",
      ProveGeneratorPreconditions: proveGeneratorPreconditions, ExternExecution: externExecution);
  }
}
