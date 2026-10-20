#nullable enable

using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public sealed class ContractRuntimeGeneratorProofTests {
  private const string SourceText = "module M { import PbtRandom type Positive = x: nat | x > 0 witness 1 " +
    "method Goal(x: Positive) requires x > 1 decreases x { if x > 0 { Goal(x - 1); } } " +
    "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: Positive) { x := 2; } }";

  private static async Task<ContractRuntimeTransformation> TransformAsync(ContractGeneratorProofReport? proof = null) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] sources = [
      new("M.dfy", SourceText, ContractHarnessBuilder.Hash(SourceText)),
      new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))
    ];
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal, generatorProof: proof).Transform();
  }

  // Ordinary transformation keeps the selected entry condition, declared type check, heap capture and recursive call precondition.
  [Fact]
  public async Task KeepsEveryRuntimeBoundaryWithoutAProof() {
    var transformation = await TransformAsync();

    Assert.False(transformation.EntryRequiresOmitted);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition && !clause.TypeConstraint);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition && clause.TypeConstraint);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.CallPrecondition &&
      clause.Owner.FullDafnyName == "M.Goal");
    Assert.Contains(transformation.Sources, source => source.Content.Contains("PbtChecks.CaptureHeap(\"entry\"", System.StringComparison.Ordinal));
  }

  // A fabricated public verified report has no internal certificate and cannot omit the entry condition.
  [Fact]
  public async Task ForgedVerifiedReportCannotOmitTheEntryCondition() {
    var forged = new ContractGeneratorProofReport(ContractGeneratorProofStatus.Verified, "forged",
      ["native-check"], ["native-check"]);
    var transformation = await TransformAsync(forged);

    Assert.False(transformation.EntryRequiresOmitted);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition && !clause.TypeConstraint);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition && clause.TypeConstraint);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.CallPrecondition &&
      clause.Owner.FullDafnyName == "M.Goal");
  }
}
