#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Sample classification by callee and specification-function contracts, and the campaign status it yields.</summary>
public class SampleClassificationTests : IClassFixture<SampleClassificationTests.Fixture> {
  private const string File = "SampleClassification";
  private static readonly CampaignSpec Excluded = CampaignSpec.Fixture(File, "Excluded").Buckets(13).WithDrafts(
    ("M.Extern", "method {:pbt_draft \"M.Extern\"} Extern(x: int) returns (y: int) { y := x; }"),
    ("M.Natural", "method {:pbt_draft \"M.Natural\"} Natural(x: int) returns (y: nat) { y := x - 5; }"));
  private static readonly CampaignSpec Accepted = CampaignSpec.Fixture(File, "Accepted").Buckets(4);
  private static readonly CampaignSpec Mixed = CampaignSpec.Fixture(File, "Mixed").Buckets(2);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Excluded, Accepted, Mixed];
  }

  public SampleClassificationTests(Fixture fixture) { }

  // A campaign whose samples are all excluded is inconclusive because no valid sample completed.
  [Fact]
  public async Task ExcludedSamplesYieldNoValidSampleStatus() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.True(run.Result is { Status: ContractRuntimeStatus.Inconclusive, Reason: "No valid sample completed." }, run.Detail());
    Assert.Empty(run.Result.Violations);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Excluded.SampleCount, Executed: Excluded.SampleCount,
      CalleeContractViolations: 11 * CampaignSpec.BucketSize, CalleeContractUnchecked: CampaignSpec.BucketSize,
      RuntimeErrors: CampaignSpec.BucketSize), run.Detail());
  }

  // A failing draft postcondition invalidates its sample instead of indicting the goal.
  [Fact]
  public async Task SeparatesDraftContractViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(0), violation => Assert.True(violation.Draft));
  }

  // A nested helper contract violation invalidates the sample even when the direct callee contract is true.
  [Fact]
  public async Task SeparatesNestedCalleeViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(1), violation => Assert.Equal("M.Inner", violation.Callee));
  }

  // A nested ordinary function must satisfy its own callee domain before goal evidence is valid.
  [Fact]
  public async Task RejectsNestedFunctionDomainViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.Empty(run.Violations(2));
    var errors = run.Errors(2);
    Assert.True(errors.Select(error => error.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(2)), run.Detail());
    Assert.All(errors, error => Assert.Contains("outside its precondition", error.Message));
  }

  // A contract-violating function evaluated only by the goal postcondition invalidates the sample for ordinary and ghost functions.
  [Theory]
  [InlineData(3, "M.Bad")]
  [InlineData(4, "M.GhostBad")]
  public async Task SeparatesSpecFunctionContractViolation(int bucket, string function) {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(bucket), violation => Assert.Equal(function, violation.Callee));
    var callee = Assert.Single(run.Result.Obligations, obligation => obligation.Kind == CalleePostcondition && obligation.Callee == function);
    Assert.Equal("b", callee.Clause);
  }

  // A callee's by-method body must agree with its defining expression even without explicit ensures.
  [Fact]
  public async Task RejectsFunctionByMethodCalleeDefinitionMismatch() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(5), violation => Assert.Equal("M.Mismatch", violation.Callee));
    Assert.Equal(0, run.Obligation("tag == 5 ==> y == 0", Postcondition).Violations);
  }

  // A function called only from a callee's postcondition must satisfy its own contract.
  [Fact]
  public async Task RejectsNestedSpecFunctionContractViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.Contains(run.AssertCalleeViolated(6), violation => violation.Callee == "M.BadNullary");
  }

  // Entry-state function captures validate the function before its result can indict the goal.
  [Fact]
  public async Task RejectsOldStateSpecFunctionContractViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(7), violation => Assert.Equal("M.BadRead", violation.Callee));
  }

  // An unverified by-method may change the heap while a mutual contract is pending, so reference cycles stay unchecked.
  [Fact]
  public async Task ExcludesReentrantMutableSpecContracts() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.Empty(run.Violations(8));
    Assert.Empty(run.CalleeViolations(8));
    Assert.Contains(run.Result.Obligations, obligation => obligation.UncheckedReason == "recursive_heap_contract" &&
      obligation.Evaluations.Unchecked >= CampaignSpec.BucketSize);
  }

  // A callee postcondition in a conjunctive quantified shape still invalidates the sample instead of indicting the goal.
  [Fact]
  public async Task ChecksConjunctiveQuantifiedCalleePostcondition() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(9), violation => Assert.Equal("M.Evens", violation.Callee));
  }

  // A generic function used by the goal postcondition must satisfy its own contract before goal evidence is valid.
  [Fact]
  public async Task SeparatesGenericSpecFunctionViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(10), violation => Assert.Equal("M.Pick", violation.Callee));
  }

  // A draft result outside its declared subset type is a callee contract violation, not goal evidence.
  [Fact]
  public async Task SeparatesDraftResultSubsetViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.All(run.AssertCalleeViolated(11), violation => Assert.True(violation.Draft));
  }

  // Nested generic specification wrappers preserve shape bindings while excluding the invalid inner callee.
  [Fact]
  public async Task SeparatesNestedGenericSpecFunctionViolation() {
    var run = await Campaign.RunAsync(Excluded);
    Assert.Contains(run.AssertCalleeViolated(12), violation => violation.Callee == "M.InnerPick");
    Assert.Empty(run.Errors(12));
  }

  // A campaign of valid, decided and violation-free samples reports no violation.
  [Fact]
  public async Task AcceptedSamplesYieldNoViolationStatus() {
    var run = await Campaign.RunAsync(Accepted);
    Assert.True(run.Result.Status == ContractRuntimeStatus.NoViolationFound, run.Detail());
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Accepted.SampleCount,
      Executed: Accepted.SampleCount, Valid: Accepted.SampleCount), run.Detail());
  }

  // Mutually referring contracts check all evaluated callees without repeating an identical pending obligation.
  [Fact]
  public async Task ChecksSpecFunctionContractsWithoutRecursiveWrapping() {
    var run = await Campaign.RunAsync(Accepted);
    run.AssertHolds(0, "b == Pos(x) && !Neg(x)", Postcondition);
    var callees = run.Result.Obligations.Where(obligation => obligation.Kind == CalleePostcondition &&
      obligation.Callee is "M.Pos" or "M.Neg").ToList();
    Assert.Equal(3, callees.Count);
    Assert.All(callees, obligation => Assert.True(obligation.Evaluations.Runtime >= CampaignSpec.BucketSize, run.Detail()));
  }

  // Recursive callee definitions evaluate the definition while validating the actual by-method results.
  [Fact]
  public async Task AcceptsRecursiveFunctionByMethodCallee() {
    var run = await Campaign.RunAsync(Accepted);
    run.AssertHolds(1, "tag == 1 ==> y == x", Postcondition);
    Assert.Contains(run.Result.Obligations, obligation => obligation.Callee == "M.Recursive" &&
      obligation.Evaluations.Runtime >= CampaignSpec.BucketSize);
  }

  // Distinct decreasing arguments inside contracts retain their own validity checks.
  [Fact]
  public async Task AcceptsDescendingSpecFunctionContracts() {
    var run = await Campaign.RunAsync(Accepted);
    run.AssertHolds(2, "Count(x) == x", Postcondition);
    Assert.Contains(run.Result.Obligations, obligation => obligation.Callee == "M.Count" &&
      obligation.Evaluations.Runtime >= CampaignSpec.BucketSize);
  }

  // Valid transitive contracts inside old use the entry heap even when the goal later mutates it.
  [Fact]
  public async Task AcceptsOldStateTransitiveSpecContracts() {
    (await Campaign.RunAsync(Accepted)).AssertHolds(3, "Outer(o) == 0", Postcondition);
  }

  // Any valid violating sample makes the campaign report a violation, whatever the excluded samples show.
  [Fact]
  public async Task ValidViolatingSampleYieldsViolationStatus() {
    var run = await Campaign.RunAsync(Mixed);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(CampaignSpec.BucketSize, run.Population.ViolatingSamples);
  }

  // Obligation violation counts include only failures from samples classified by that obligation.
  [Fact]
  public async Task CountsObligationViolationsByClassification() {
    var run = await Campaign.RunAsync(Mixed);
    run.AssertCalleeViolated(0);
    run.AssertViolated(1, "r > 100", Postcondition);
    var goal = run.Obligation("r > 100", Postcondition);
    var callee = run.Obligation("y >= 0", CalleePostcondition);
    Assert.Equal(Mixed.SampleCount, goal.Evaluations.Runtime);
    Assert.Equal(CampaignSpec.BucketSize, run.Population.Valid);
    Assert.Equal(run.Population.Valid, goal.Violations);
    Assert.Equal(run.Population.CalleeContractViolations, callee.Violations);
  }
}
