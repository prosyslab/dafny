#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Contracts of functions evaluated by type constraints, callee outputs and specification formals.</summary>
public class CalleeTypeContractsTests : IClassFixture<CalleeTypeContractsTests.Fixture> {
  private const string Marker = "tag < 0";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("CalleeTypeContracts", "Main").Buckets(20);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public CalleeTypeContractsTests(Fixture fixture) { }

  // Each bucket lands in exactly the classification its scenario owns.
  [Fact]
  public async Task ClassifiesEveryBucket() {
    var run = await Campaign.RunAsync(Main);
    const int size = CampaignSpec.BucketSize;
    // The faulting constraint function of bucket 0 runs while the input is validated, before execution.
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount - size,
      Valid: 8 * size, CalleeContractViolations: 9 * size, CalleeContractUnchecked: 2 * size,
      RuntimeErrors: size, ViolatingSamples: 8 * size), run.Detail());
  }

  // A predicate evaluated by a subset constraint cannot run outside its declared domain and admit the goal input.
  [Fact]
  public async Task RejectsTypeConstraintFunctionDomainViolation() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(0));
    Assert.True(run.Errors(0).Select(error => error.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(0)), run.Detail());
  }

  // A non-runtime predicate domain in a type constraint stays excluded when closed-query evidence is unavailable.
  [Fact]
  public async Task ExcludesUncheckedTypeConstraintFunctionDomain() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(1));
    Assert.Empty(run.CalleeViolations(1));
    Assert.Empty(run.Errors(1));
  }

  // Membership predicates admit a goal counterexample only when their own postcondition holds, across supported type shapes.
  [Theory]
  [InlineData(2, true)]
  [InlineData(3, false)]
  [InlineData(4, true)]
  [InlineData(5, false)]
  [InlineData(6, true)]
  [InlineData(7, false)]
  [InlineData(8, true)]
  [InlineData(9, false)]
  [InlineData(10, true)]
  [InlineData(11, false)]
  public async Task ChecksTypeConstraintFunctionPostconditions(int bucket, bool validCallee) {
    var run = await Campaign.RunAsync(Main);
    if (validCallee) {
      run.AssertViolated(bucket, Marker, exclusive: false);
      Assert.Empty(run.CalleeViolations(bucket));
    } else {
      Assert.All(run.AssertCalleeViolated(bucket), violation => Assert.Equal("M.AcceptInvalid", violation.Callee));
    }
  }

  // Invalid structured callee outputs stay outside valid goal evidence, while their normal counterparts remain usable.
  [Theory]
  [InlineData(12, false)]
  [InlineData(13, true)]
  [InlineData(14, false)]
  [InlineData(15, true)]
  public async Task ChecksMultipleCalleeStructuralOutputs(int bucket, bool validOutput) {
    var run = await Campaign.RunAsync(Main);
    if (validOutput) {
      run.AssertViolated(bucket, Marker, exclusive: false);
      Assert.Empty(run.CalleeViolations(bucket));
    } else {
      run.AssertCalleeViolated(bucket);
    }
  }

  // A spec function's declared non-null input is a validity condition even without explicit requires or ensures.
  [Theory]
  [InlineData(16, true)]
  [InlineData(17, false)]
  public async Task ChecksSpecNonnullStructuralTypeConstraint(int bucket, bool validCallee) {
    var run = await Campaign.RunAsync(Main);
    if (validCallee) {
      run.AssertViolated(bucket, "!AcceptC(cn)");
    } else {
      Assert.All(run.AssertCalleeViolated(bucket), violation => Assert.Equal("M.AcceptC", violation.Callee));
    }
  }

  // A nested helper's declared input type is checked before its result can count as valid goal evidence.
  [Fact]
  public async Task ChecksNestedStructuralTypeConstraint() {
    (await Campaign.RunAsync(Main)).AssertCalleeViolated(18);
  }

  // An unbounded spec-function domain stays unchecked when no closed-query budget is available.
  [Fact]
  public async Task ExcludesUncheckedSpecFunctionDomain() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(19));
    Assert.Empty(run.CalleeViolations(19));
    Assert.Contains(run.Result.Obligations, obligation => obligation.Callee == "M.HelperQ" &&
      obligation.Evaluations is { Unchecked: CampaignSpec.BucketSize, Runtime: 0, ClosedSmt: 0 });
  }
}
