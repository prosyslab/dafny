#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Callee heap postconditions decided over each internal invocation's own captured heaps.</summary>
public class InternalCallsTests : IClassFixture<InternalCallsTests.Fixture> {
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("InternalCalls", "Main", "Client.Goal").Buckets(6) with {
    MaxClosedQueries = 96,
    ClosedQueryTimeout = 3000,
    SampleTimeout = 2000
  };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public InternalCallsTests(Fixture fixture) { }

  // Each bucket lands in exactly the classification its internal call owns.
  [Fact]
  public async Task ClassifiesEveryBucket() {
    var run = await Campaign.RunAsync(Main);
    const int size = CampaignSpec.BucketSize;
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount,
      Valid: size, CalleeContractViolations: 2 * size, CalleeContractUnchecked: 2 * size, Timeouts: size,
      ViolatingSamples: size), run.Detail());
  }

  // Each nested call proves its own old/current transition after the goal has already changed the aliased receiver.
  [Theory]
  [InlineData(0, true)]
  [InlineData(1, false)]
  public async Task InternalHeapCallsUseTheirOwnEntryState(int bucket, bool validCallee) {
    var run = await Campaign.RunAsync(Main);
    if (validCallee) {
      run.AssertViolated(bucket, "false", ContractRuntimeObligationKind.Postcondition);
      Assert.Empty(run.CalleeViolations(bucket));
    } else {
      run.AssertCalleeViolated(bucket);
    }
    Assert.Contains(run.Result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition &&
      obligation.Clause.Contains("Moved(2)") && obligation.Evaluations.ClosedSmt > 0);
    var entries = run.Records(CampaignRun.Ordinals(bucket)[0]).Where(record => record.GetProperty("kind").GetString() == "heap_capture" &&
      record.GetProperty("phase").GetString() == "call_entry").ToList();
    Assert.Equal(3, entries.Count);
    Assert.Equal(3, entries.Select(record => record.GetProperty("invocation").GetInt32()).Distinct().Count());
    Assert.All(entries, record => Assert.Equal(record.GetProperty("inputs").GetProperty("receiver").GetRawText(),
      record.GetProperty("inputs").GetProperty("alias").GetRawText()));
  }

  // A proved first invocation cannot authorize a later invocation whose different heap violates the same clause.
  [Fact]
  public async Task InternalHeapFactDoesNotCrossChangedCallState() {
    var run = await Campaign.RunAsync(Main);
    Assert.All(run.AssertCalleeViolated(2), violation => Assert.Contains(violation.Values, pair =>
      pair.Key.StartsWith("$initial/") && pair.Value.Value == "9"));
  }

  // A killed invocation with no return snapshot cannot establish a callee contract or a goal violation.
  [Fact]
  public async Task InternalHeapCallWithoutReturnRemainsIncomplete() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(3));
    Assert.Empty(run.CalleeViolations(3));
    Assert.True(run.Errors(3).Select(error => error.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(3)), run.Detail());
    Assert.All(run.Errors(3), error => Assert.Equal("sample_timeout", error.Message));
  }

  // A callee missing its own frame, or reaching an invalid specification contract, stays unchecked despite a successful call.
  [Theory]
  [InlineData(4, "missing callee frame")]
  [InlineData(5, "invalid specification dependency")]
  public async Task InternalHeapCallStaysUnchecked(int bucket, string reason) {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Violations(bucket).Count == 0, reason);
    Assert.Empty(run.CalleeViolations(bucket));
    Assert.Empty(run.Errors(bucket));
  }
}
