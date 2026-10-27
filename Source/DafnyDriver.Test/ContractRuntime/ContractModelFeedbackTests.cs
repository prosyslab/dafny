#nullable enable
using System;
using System.Linq;
using System.Text.Json;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

// These tests exercise only pure JSON/population helpers; no campaign, file, process, or solver is invoked.
public sealed class ContractModelFeedbackTests {
  private static JsonElement[] Records(string json) {
    using var document = JsonDocument.Parse(json);
    return document.RootElement.EnumerateArray().Select(record => record.Clone()).ToArray();
  }

  // An exhausted initial search supplies no valid input or counterexample evidence.
  [Fact]
  public void InitialExhaustionIsUnchecked() {
    var result = ContractRuntimeCampaignRunner.ExcludeExhaustedModelSample(new(), Records("""
      [{"kind":"model_exhausted","phase":"initial","symbol":"M.Goal"}]
      """));
    Assert.Equal(new ContractRuntimePopulation(PreconditionUnchecked: 1), result.Population);
    Assert.Contains("configured domain", result.Reason);
  }

  // A failed check before transition exhaustion cannot become a validated safety prefix.
  [Fact]
  public void TransitionExhaustionRetainsOnlyObservedCounts() {
    var result = ContractRuntimeCampaignRunner.ExcludeExhaustedModelSample(new(), Records("""
      [{"kind":"generated"},{"kind":"executed"},
       {"kind":"check","id":"assertion:fake","passed":false},
       {"kind":"model_exhausted","phase":"transition","symbol":"M.IO.Step"}]
      """));
    Assert.Equal(new ContractRuntimePopulation(Generated: 1, Executed: 1, CalleeContractUnchecked: 1), result.Population);
    Assert.NotNull(result.Reason);
  }

  // Ordinary records continue through existing classification unchanged.
  [Fact]
  public void OrdinarySampleIsNotExcluded() {
    var previous = new ContractRuntimePopulation(Generated: 2, Executed: 2, Valid: 2);
    var result = ContractRuntimeCampaignRunner.ExcludeExhaustedModelSample(previous, Records("""
      [{"kind":"generated"},{"kind":"executed"},{"kind":"complete"}]
      """));
    Assert.Same(previous, result.Population);
    Assert.Null(result.Reason);
  }

  // Exhaustion remains visible even when other completed samples found no violation.
  [Fact]
  public void ExhaustedCampaignIsInconclusive() {
    var status = ContractRuntimeCampaignRunner.CampaignStatus(new(Generated: 2, Executed: 2, Valid: 1), 3, true);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, status);
  }

  // A separately accepted complete counterexample remains reportable despite another exhausted sample.
  [Fact]
  public void ExistingViolationSurvivesExhaustion() {
    var status = ContractRuntimeCampaignRunner.CampaignStatus(new(Valid: 1, ViolatingSamples: 1), 1, true);
    Assert.Equal(ContractRuntimeStatus.ViolationFound, status);
  }

  // Unmarked complete valid samples retain their prior campaign outcome.
  [Fact]
  public void OrdinarySuccessfulCampaignRemainsSuccessful() {
    Assert.Equal(ContractRuntimeStatus.NoViolationFound,
      ContractRuntimeCampaignRunner.CampaignStatus(new(Valid: 1), 1, false));
  }

  // Unknown exhaustion phases cannot silently become valid evidence.
  [Fact]
  public void MalformedExhaustionIsRejected() {
    Assert.Throws<ArgumentException>(() => ContractRuntimeCampaignRunner.ExcludeExhaustedModelSample(new(), Records("""
      [{"kind":"model_exhausted","phase":"unknown","symbol":"M.Goal"}]
      """)));
  }
}
