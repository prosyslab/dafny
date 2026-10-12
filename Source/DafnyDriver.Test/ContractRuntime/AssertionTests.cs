#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Target assertion instrumentation and exact-prefix sample classification.</summary>
public class AssertionTests : IClassFixture<AssertionTests.Fixture> {
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("Assertions", "Main").Buckets(7) with {
    ClosedQueryTimeout = 15000,
    Timeout = 240000
  };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public AssertionTests(Fixture fixture) { }

  // Samples with observed runtime safety failures run first while both partitions retain original ordinal order.
  [Fact]
  public async Task PrioritizesObservedRuntimeSafetyFailuresStably() {
    var run = await Campaign.RunAsync(Main);
    var startedOrdinals = File.ReadLines(Path.Combine(run.Directory, "campaign-phases.jsonl"))
      .Select(Json)
      .Where(record => record.GetProperty("state").GetString() == "started" &&
        record.GetProperty("phase").GetString()!.StartsWith("runtime_evidence:", StringComparison.Ordinal))
      .Select(record => int.Parse(record.GetProperty("phase").GetString()!["runtime_evidence:".Length..]))
      .ToList();
    var expected = Enumerable.Range(4, 4).Concat(Enumerable.Range(12, 4))
      .Concat(Enumerable.Range(0, 4)).Concat(Enumerable.Range(8, 4)).Concat(Enumerable.Range(16, 12));
    Assert.Equal(expected, startedOrdinals);
  }

  // A false compiled assertion before the malformed-record boundary identifies its exact finite prefix.
  [Fact]
  public void FindsRuntimeSafetyFailureBeforeMalformedBoundary() {
    var records = new[] { Json("""{"kind":"executed"}"""), RuntimeFailureRecord() };
    Assert.Equal(2, ContractRuntimeCampaignRunner.RuntimeSafetyFailurePrefixLength(
      records, 2, RuntimeObligations()));
  }

  // A false compiled assertion at the malformed-record boundary cannot schedule or terminate a prefix.
  [Fact]
  public void IgnoresRuntimeSafetyFailureAtMalformedBoundary() {
    var records = new[] { Json("""{"kind":"executed"}"""), RuntimeFailureRecord() };
    Assert.Equal(0, ContractRuntimeCampaignRunner.RuntimeSafetyFailurePrefixLength(
      records, 1, RuntimeObligations()));
  }

  // Executed target assertions are distinct goal obligations; callee and proof-block assertions are ignored.
  [Fact]
  public async Task InstrumentsOnlyTargetExecutableAssertions() {
    var run = await Campaign.RunAsync(Main);
    var assertions = run.Result.Obligations.Where(obligation => obligation.Kind == Assertion).ToList();
    Assert.Equal(7, assertions.Count);
    Assert.Single(assertions, obligation => obligation.Clause == "true");
    Assert.DoesNotContain(assertions, obligation => obligation.Path != "M.dfy");
  }

  // Generic assertion rendering supplies its own type shape and erases every proof-block descendant.
  [Fact]
  public async Task RendersGenericAssertionWithoutProofInstrumentation() {
    var run = await Campaign.RunAsync(Main);
    run.AssertHolds(0, "Identity<int>(x) == x", Assertion);
    run.AssertHolds(2, "true", Assertion);
    Assert.DoesNotContain(run.Result.Obligations, obligation => obligation.Clause.Contains("0 <= i <= 1"));
  }

  // A true assertion holds while a false runtime assertion becomes a target violation.
  [Fact]
  public async Task ChecksRuntimeAssertionVerdicts() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(1, "x > 0", Assertion);
    Assert.All(run.Result.Obligations.Where(obligation => obligation.Kind == Assertion && obligation.Clause == "true"),
      obligation => Assert.Equal(0, obligation.Violations));
  }

  // An invalid entry never reaches or indicts the target assertion.
  [Fact]
  public async Task RejectsInvalidEntryBeforeAssertion() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(4));
    Assert.Equal(CampaignSpec.BucketSize, run.Population.PreconditionRejected);
  }

  // A prior callee failure excludes the sample even though a target assertion later fails.
  [Fact]
  public async Task PriorCalleeViolationSuppressesAssertion() {
    var run = await Campaign.RunAsync(Main);
    run.AssertCalleeViolated(3);
    Assert.Empty(run.Violations(3));
  }

  // A closed assertion counterexample uses its completed trace prefix, so a later bad callee cannot mask it.
  [Fact]
  public async Task LaterCalleeCannotMaskClosedAssertionPrefix() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(5, "forall i: int :: false", Assertion);
    Assert.Empty(run.CalleeViolations(5));
    foreach (var ordinal in CampaignRun.Ordinals(5)) {
      Assert.Contains(run.Records(ordinal), record => record.GetProperty("kind").GetString() == "complete");
      var certificate = CampaignRun.Json(Path.Combine(run.Directory, "prefix-certificate-" + ordinal + ".json"));
      Assert.True(certificate.GetProperty("originalComplete").GetBoolean());
      Assert.True(certificate.GetProperty("recordCount").GetInt32() < certificate.GetProperty("originalRecordCount").GetInt32());
    }
  }

  // An assertion over a ghost value with no executable witness remains explicitly unchecked.
  [Fact]
  public async Task UnavailableGhostAssertionRemainsUnchecked() {
    var run = await Campaign.RunAsync(Main);
    var obligation = run.Obligation("y == x", Assertion);
    Assert.Equal("value_unavailable", obligation.UncheckedReason);
    Assert.Equal(CampaignSpec.BucketSize, obligation.Evaluations.Unchecked);
    Assert.Empty(run.Violations(6));
  }

  private static JsonElement RuntimeFailureRecord() =>
    Json("""{"kind":"check","id":"assertion","passed":false}""");

  private static IReadOnlyDictionary<string, ContractRuntimeObligation> RuntimeObligations() =>
    new Dictionary<string, ContractRuntimeObligation> {
      ["assertion"] = new("assertion", Assertion, "M.dfy", 1, 1, "false", null,
        ContractRuntimeDecisionMethod.Runtime, null, new())
    };

  private static JsonElement Json(string text) => JsonDocument.Parse(text).RootElement.Clone();
}
