#nullable enable
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

public class SamplingBudgetTests {
  // Preparation beyond half the original timeout still leaves half of the remaining campaign time for sampling.
  [Fact]
  public void LatePreparationRetainsSamplingTime() {
    Assert.Equal(194_203L,
      ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(231_782, 156_624));
  }

  // The caller's one computed deadline shrinks normally instead of moving when later samples start.
  [Fact]
  public void SamplingDeadlineRemainsFixedAcrossSamples() {
    var deadline = ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(100, 20);

    Assert.Equal(60L, deadline);
    Assert.Equal(20L, deadline - 40);
    Assert.Equal(70L, ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(100, 40));
  }

  // Preparation at or beyond the aggregate deadline grants no sampling time.
  [Theory]
  [InlineData(100, 100)]
  [InlineData(100, 101)]
  public void ExpiredCampaignGrantsNoSamplingTime(int timeout, long elapsed) {
    var deadline = ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(timeout, elapsed);

    Assert.Equal(0L, deadline - elapsed);
  }

  // Odd and tiny remaining budgets round sampling down so classification retains at least half.
  [Theory]
  [InlineData(5, 0, 2)]
  [InlineData(2, 0, 1)]
  [InlineData(1, 0, 0)]
  [InlineData(5, 2, 1)]
  public void SamplingRoundsDownRemainingTime(int timeout, long elapsed, long expectedBudget) {
    var deadline = ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(timeout, elapsed);

    Assert.Equal(expectedBudget, deadline - elapsed);
  }

  // The largest request timeout uses long arithmetic without overflowing the fixed deadline.
  [Fact]
  public void MaximumTimeoutDoesNotOverflow() {
    var deadline = ContractRuntimeCampaignRunner.SamplingDeadlineMilliseconds(int.MaxValue, int.MaxValue - 2L);

    Assert.Equal(int.MaxValue - 1L, deadline);
  }
}
