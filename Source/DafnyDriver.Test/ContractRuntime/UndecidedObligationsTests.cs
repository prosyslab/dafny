#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Goal obligations that stay undecided in valid samples, and the inconclusive status they yield.</summary>
public class UndecidedObligationsTests : IClassFixture<UndecidedObligationsTests.Fixture> {
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("UndecidedObligations", "Main").Buckets(5);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public UndecidedObligationsTests(Fixture fixture) { }

  // Valid samples that decide no goal obligation are inconclusive rather than violation-free.
  [Fact]
  public async Task ValidSamplesWithoutDecisionsAreInconclusive() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Result is { Status: ContractRuntimeStatus.Inconclusive, Reason: "No goal obligation was decided in a valid sample." },
      run.Detail());
    Assert.Equal(Main.SampleCount, run.Population.Valid);
    Assert.Empty(run.Result.Violations);
  }

  // A ghost-method-produced local stays unavailable; the executed samples are valid but decide no goal obligation.
  [Fact]
  public async Task ExecutesWithUnavailableGhostLocal() {
    var run = await Campaign.RunAsync(Main);
    var obligation = run.Obligation("y == x", ContractRuntimeObligationKind.LoopInvariantEntry);
    Assert.Equal("value_unavailable", obligation.UncheckedReason);
    Assert.Equal(new ContractRuntimeEvaluations(Unchecked: CampaignSpec.BucketSize), obligation.Evaluations);
  }

  // An unavailable ghost output records an unchecked checkpoint, which cannot support a no-violation status.
  [Fact]
  public async Task ReportsUnavailableGhostOutput() {
    var run = await Campaign.RunAsync(Main);
    var obligation = run.Obligation("gy == x", ContractRuntimeObligationKind.Postcondition);
    Assert.Equal(ContractRuntimeDecisionMethod.Unchecked, obligation.DecisionMethod);
    Assert.Equal("value_unavailable", obligation.UncheckedReason);
    Assert.Equal(new ContractRuntimeEvaluations(Unchecked: Main.SampleCount), obligation.Evaluations);
  }

  // A resolver-rejected ghost compiled copy leaves its exclusion visible in the result.
  [Fact]
  public async Task ReportsResolverExclusion() {
    var run = await Campaign.RunAsync(Main);
    Assert.Contains(run.Result.DeghostExclusions, exclusion => exclusion.Symbol == "M.Choose");
  }

  // Without a closed-query budget an erased check leaves valid samples undecided rather than violation-free.
  [Fact]
  public async Task ErasedCheckWithoutBudgetIsUndecided() {
    var run = await Campaign.RunAsync(Main);
    var obligation = run.Obligation("d != C && d != A");
    Assert.Equal(0, obligation.Evaluations.Runtime);
    Assert.Equal(Main.SampleCount, obligation.Evaluations.Unchecked);
  }

  // An unbounded quantified clause remains unchecked when the closed-query budget is zero.
  [Fact]
  public async Task ReportsClosedQueryBudget() {
    var obligation = (await Campaign.RunAsync(Main)).Obligation("forall n: int :: n <= x");
    Assert.Equal("closed_query_budget_exhausted", obligation.UncheckedReason);
    Assert.Equal(Main.SampleCount, obligation.Evaluations.Unchecked);
  }
}
