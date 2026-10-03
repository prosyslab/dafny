#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Goal obligation kinds decided at runtime; every scenario is one bucket of a single campaign.</summary>
public class ObligationKindsTests : IClassFixture<ObligationKindsTests.Fixture> {
  private const int Buckets = 18;
  private const int ReplayOrdinal = 1;
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("ObligationKinds", "Main").Buckets(Buckets);
  private static readonly CampaignSpec Replay = Main with { ReplayOrdinal = ReplayOrdinal };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main, Replay];
  }

  public ObligationKindsTests(Fixture fixture) { }

  private static async Task<(CampaignRun Run, ContractRuntimeObligation Obligation, IReadOnlyList<ContractRuntimeViolation> Violations)>
    Violated(int bucket, string clause, ContractRuntimeObligationKind? kind = null, int perSample = 1) {
    var run = await Campaign.RunAsync(Main);
    var (obligation, violations) = run.AssertViolated(bucket, clause, kind, perSample);
    return (run, obligation, violations);
  }

  private static async Task Holds(int bucket, string clause, ContractRuntimeObligationKind kind) =>
    (await Campaign.RunAsync(Main)).AssertHolds(bucket, clause, kind);

  // Every scenario sample is valid, so each bucket's verdict is goal evidence rather than an exclusion.
  [Fact]
  public async Task EverySampleIsValid() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount,
      Valid: Main.SampleCount, ViolatingSamples: run.Population.ViolatingSamples), run.Detail());
  }

  // A concrete postcondition defect is reported once per failing sample under one postcondition obligation.
  [Fact]
  public async Task ReportsPostconditionViolation() {
    var (_, obligation, _) = await Violated(0, "y == random + 1");
    Assert.Equal(Postcondition, obligation.Kind);
  }

  // The same seed and ordinal reproduce the input and concrete violation exactly.
  [Fact]
  public async Task ReplaysOrdinal() {
    var (_, _, violations) = await Violated(0, "y == random + 1");
    var selected = violations.Single(violation => violation.SampleOrdinal == ReplayOrdinal);
    var replay = await Campaign.RunAsync(Replay);
    Assert.Equal(JsonSerializer.Serialize(selected, ContractJson.Options),
      JsonSerializer.Serialize(Assert.Single(replay.Result.Violations), ContractJson.Options));
  }

  // A bad invariant at the initial loop head is reported with iteration zero.
  [Fact]
  public async Task ReportsInvariantEntry() {
    var (_, _, violations) = await Violated(1, "e == 0", LoopInvariantEntry);
    Assert.All(violations, violation => Assert.Equal(0, violation.Iteration));
  }

  // A later loop head records the exact iteration where the invariant becomes false.
  [Fact]
  public async Task ReportsInvariantMaintenance() {
    // Each sample fails at loop heads 2 and 3.
    var (_, _, violations) = await Violated(2, "m <= 1", LoopInvariantMaintenance, perSample: 2);
    Assert.All(violations.GroupBy(violation => violation.SampleOrdinal),
      sample => Assert.Equal(new int?[] { 2, 3 }, sample.Select(violation => violation.Iteration).Order().ToArray()));
  }

  // A break skips the final invariant check for precisely the loop it exits.
  [Fact]
  public async Task BreakDoesNotCheckExitInvariant() {
    await Holds(3, "b <= 1", LoopInvariantEntry);
  }

  // Runtime diagnostics do not turn a weak but true invariant into a proof-level counterexample.
  [Fact]
  public async Task WeakInvariantIsNotViolation() {
    await Holds(4, "w >= 0", LoopInvariantMaintenance);
  }

  // For-loop checks retain the index in scope at both entry and the final loop head.
  [Fact]
  public async Task ChecksForLoop() {
    var (_, _, violations) = await Violated(5, "f < 3", LoopInvariantMaintenance);
    Assert.All(violations, violation => Assert.Equal(3, violation.Iteration));
  }

  // A false call precondition is reported at its call site and stops the sample before the out-of-domain callee runs.
  [Fact]
  public async Task ReportsCallPreconditionWithoutExecutingCallee() {
    var (run, _, violations) = await Violated(6, "x > 5", CallPrecondition);
    Assert.All(violations, violation => Assert.Equal(CallPrecondition, violation.Kind));
    Assert.Empty(run.Errors(6));
    Assert.Empty(run.CalleeViolations(6));
  }

  // Function expressions check their callee requirements through an expression wrapper.
  [Fact]
  public async Task ChecksFunctionCallPrecondition() {
    await Violated(7, "x < 0", CallPrecondition);
  }

  // Old field values are captured before mutation and compared at return.
  [Fact]
  public async Task ChecksOldState() {
    var (_, obligation, _) = await Violated(8, "box.f == old(box.f) + 1", Postcondition);
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
  }

  // Unchanged compares the captured fields rather than object identity alone.
  [Fact]
  public async Task ChecksUnchangedFields() {
    await Violated(9, "unchanged(box)");
  }

  // Proof-only statements are removed while preserving the surrounding executable assignments.
  [Fact]
  public async Task RemovesProofStatements() {
    await Violated(10, "y == x + 1");
  }

  // A conjunctive quantified postcondition is checked in its written, compilable form instead of being erased.
  [Fact]
  public async Task ChecksConjunctiveQuantifiedPostcondition() {
    var (_, obligation, _) = await Violated(11, "e in s && e % 2 == 0");
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
    // Every sample that returns evaluates it; buckets 6 and 7 stop at their failed call precondition.
    Assert.Equal(Main.SampleCount - 2 * CampaignSpec.BucketSize, obligation.Evaluations.Runtime);
  }

  // A generic function call in the goal body gets a generic call-site wrapper.
  [Fact]
  public async Task WrapsGenericCallSite() {
    await Holds(12, "|s| > 0", CallPrecondition);
  }

  // Old heap fields through an immutable local alias are captured using the original input identity.
  [Fact]
  public async Task CapturesOldThroughLocalAlias() {
    await Holds(13, "alias.f == old(alias.f)", LoopInvariantEntry);
    Assert.All((await Campaign.RunAsync(Main)).Obligations("alias.f == old(alias.f)"),
      obligation => Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod));
  }

  // A compiled forall statement keeps its assignment-only body free of diagnostic markers.
  [Fact]
  public async Task ExecutesCompiledForallStatement() {
    await Violated(14, "a[i] == 1");
  }

  // An opaque finite predicate executes as ordinary diagnostic code after deghosting.
  [Fact]
  public async Task ExecutesOpaqueFinitePredicate() {
    var (_, obligation, _) = await Violated(15, "Good([x])");
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
  }

  // Ghost output values and recursive ghost functions are preserved by the diagnostic compile.
  [Fact]
  public async Task ExecutesGhostPostcondition() {
    var (_, obligation, _) = await Violated(16, "gy == Sum([x])");
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod);
  }

  // A call through a trait dispatches to the concrete override instead of requesting drafts for abstract members.
  [Fact]
  public async Task DispatchesTraitCallToOverride() {
    var (run, _, _) = await Violated(17, "scaled == k * shape.Area()");
    Assert.Empty(run.Result.MissingDrafts);
  }
}
