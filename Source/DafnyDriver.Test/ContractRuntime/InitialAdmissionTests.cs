#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Admission of captured and constructed initial heaps before runtime goal evidence.</summary>
public class InitialAdmissionTests : IClassFixture<InitialAdmissionTests.Fixture> {
  private const string File = "InitialAdmission";

  private static CampaignSpec Heap(string section, int queries, int buckets = 0) {
    var spec = CampaignSpec.Fixture(File, section, "Client.Goal") with { MaxClosedQueries = queries, ClosedQueryTimeout = 3000 };
    return buckets == 0 ? spec : spec.Buckets(buckets);
  }

  private static string ReadDraft(string method, string body) =>
    "method {:pbt_draft \"Store.Cell." + method + "\"} " + method + "() returns (result: int) { result := " + body + "; }";

  private static readonly CampaignSpec Store = Heap("Store", 32, 4).WithDrafts(
    ("Store.Cell.ReadValue", ReadDraft("ReadValue", "Read()")),
    ("Store.Cell.ReadWrong", ReadDraft("ReadWrong", "Read() + 2")),
    ("Store.Cell.ReadEven", ReadDraft("ReadEven", "Read() + 0")),
    ("Store.Cell.ReadOdd", ReadDraft("ReadOdd", "Read() + 1")));
  private static readonly CampaignSpec OmittedByDraft = Heap("OmittedByDraft", 6)
    .WithDrafts(("Store.Cell.ReadValue", ReadDraft("ReadValue", "Read() + unused")));
  private static readonly CampaignSpec UncallableConstructor = CampaignSpec.Fixture(File, "UncallableConstructor").Buckets(2);
  private static readonly CampaignSpec EmptyGlobal = Heap("EmptyGlobal", 10);
  private static readonly CampaignSpec EmptyGlobalInitializer = Heap("EmptyGlobalInitializer", 10);
  private static readonly CampaignSpec DatatypeConstant = Heap("DatatypeConstant", 0);
  private static readonly CampaignSpec PlainDatatype = Heap("PlainDatatype", 0);
  private static readonly CampaignSpec NegativeConstant = Heap("NegativeConstant", 6);
  private static readonly CampaignSpec UndefinedConstant = Heap("UndefinedConstant", 6);
  private static readonly CampaignSpec ValidConstant = Heap("ValidConstant", 6);
  private static readonly CampaignSpec TypedGhostField = Heap("TypedGhostField", 0, 3);
  private static readonly CampaignSpec CyclicTree = Heap("CyclicTree", 0, 2);
  private static readonly CampaignSpec NegativeResidual = Heap("NegativeResidual", 2);
  private static readonly CampaignSpec UnbudgetedResidual = HeapProofReuseTests.PositiveCell with { MaxClosedQueries = 0 };
  private static readonly CampaignSpec RefinedRoot = Heap("RefinedRoot", 2, 2);
  private static readonly CampaignSpec PlainFunctionWellDefinedness = Heap("PlainFunctionWellDefinedness", 2);
  private static readonly CampaignSpec ConstraintCallee = Heap("ConstraintCallee", 6);
  private static readonly CampaignSpec HigherOrderConstraintCallee = Heap("HigherOrderConstraintCallee", 6);
  private static readonly CampaignSpec EmptyOmittedField = Heap("EmptyOmittedField", 2);
  private static readonly CampaignSpec PositiveOmittedField = Heap("PositiveOmittedField", 2);
  private static readonly CampaignSpec UnbudgetedOmittedField = Heap("PositiveOmittedField", 0);
  private static readonly CampaignSpec OrdinaryArrowOmission = Heap("OrdinaryArrowOmission", 0);
  private static readonly CampaignSpec RefinedArrowOmission = Heap("RefinedArrowOmission", 0);
  private static readonly CampaignSpec ValidWitness = Heap("ValidWitness", 1);
  private static readonly CampaignSpec InvalidWitness = Heap("InvalidWitness", 1);
  private static readonly CampaignSpec NestedEmptyOmission = Heap("NestedEmptyOmission", 6);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Store,
      OmittedByDraft,
      UncallableConstructor,
      EmptyGlobal,
      EmptyGlobalInitializer,
      DatatypeConstant,
      PlainDatatype,
      NegativeConstant,
      UndefinedConstant,
      ValidConstant,
      TypedGhostField,
      CyclicTree,
      NegativeResidual,
      UnbudgetedResidual,
      HeapProofReuseTests.PositiveCell,
      RefinedRoot,
      PlainFunctionWellDefinedness,
      ConstraintCallee,
      HigherOrderConstraintCallee,
      EmptyOmittedField,
      PositiveOmittedField,
      UnbudgetedOmittedField,
      OrdinaryArrowOmission,
      RefinedArrowOmission,
      ValidWitness,
      InvalidWitness,
      NestedEmptyOmission];
  }

  public InitialAdmissionTests(Fixture fixture) { }

  // Asserts the verdict of a single-sample admission campaign: a valid sample violates its `ensures false`.
  private static async Task AssertAdmission(CampaignSpec spec, bool valid) {
    var run = await Campaign.RunAsync(spec);
    Assert.True(run.Result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), run.Detail());
    Assert.Equal(valid ? spec.SampleCount : 0, run.Population.Valid);
    if (!valid) { Assert.Empty(run.Result.Violations); }
  }

  // A cross-module ghost-backed draft runs over an explicitly supplied partial logical heap.
  [Fact]
  public async Task ConstructsPartialHeapAndExecutesGhostDraft() {
    var run = await Campaign.RunAsync(Store);
    run.AssertViolated(0, "result == cell.Read() + 1", Postcondition);
    Assert.Empty(run.CalleeViolations(0));
  }

  // A wrong draft return is excluded instead of being blamed on the entry implementation.
  [Fact]
  public async Task InvalidGhostDraftExcludesSample() {
    var run = await Campaign.RunAsync(Store);
    Assert.All(run.AssertCalleeViolated(1), violation => Assert.Equal("Store.Cell.ReadWrong", violation.Callee));
  }

  // Scalar callee checks use original sources even when another module contains a ghost-backed draft.
  [Theory]
  [InlineData(2, false)]
  [InlineData(3, true)]
  public async Task ScalarClosedCalleeUsesOriginalSources(int bucket, bool invalidCallee) {
    var run = await Campaign.RunAsync(Store);
    if (invalidCallee) {
      Assert.All(run.AssertCalleeViolated(bucket), violation => Assert.Equal("Store.Cell.ReadOdd", violation.Callee));
    } else {
      run.AssertViolated(bucket, "tag >= 2 ==> false", Postcondition);
      Assert.Empty(run.CalleeViolations(bucket));
    }
    Assert.Contains(run.Result.Obligations, obligation => obligation.Kind == CalleePostcondition &&
      obligation.Callee == (invalidCallee ? "Store.Cell.ReadOdd" : "Store.Cell.ReadEven") && obligation.Evaluations.ClosedSmt > 0);
  }

  // A draft cannot make a ghost field relevant after the initial omission audit accepted it.
  [Fact]
  public async Task RejectsOmittedStateReadOnlyByDraft() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Campaign.RunAsync(OmittedByDraft));
    Assert.Contains("Store.Cell.unused", error.Message);
  }

  // The original false-precondition constructor is never redirected to diagnostic construction.
  [Theory]
  [InlineData(0)]
  [InlineData(1)]
  public async Task OriginalConstructorRemainsUncallable(int bucket) {
    var run = await Campaign.RunAsync(UncallableConstructor);
    Assert.Equal(0, run.Population.Executed);
    Assert.True(run.Errors(bucket).Select(error => error.SampleOrdinal).Order().SequenceEqual(CampaignRun.Ordinals(bucket)), run.Detail());
    Assert.Empty(run.Violations(bucket));
  }

  // An inconsistent unused global cannot turn a real captured transition into a valid sample or entry violation.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task GlobalInconsistencyCannotAuthorizeCapturedSample(bool initializer) {
    var run = await Campaign.RunAsync(initializer ? EmptyGlobalInitializer : EmptyGlobal);
    Assert.Equal(1, run.Population.Executed);
    Assert.True(run.Population.Valid == 0, run.Detail());
    Assert.Empty(run.Result.Violations);
  }

  // Unused datatype constants cannot make an empty-heap scalar execution count as valid; ordinary datatypes remain usable.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task ScalarAdmissionChecksUnusedDatatypeConstants(bool constant) {
    var run = await Campaign.RunAsync(constant ? DatatypeConstant : PlainDatatype);
    Assert.Equal(1, run.Population.Executed);
    Assert.True(run.Population.Valid == (constant ? 0 : 1), run.Detail());
    Assert.Equal(constant ? 0 : 1, run.Result.Violations.Count);
  }

  // Initialized ghost slots need original WD and unpruned consistency independently of their ordinary field types.
  [Theory]
  [InlineData("negative nat initializer", false)]
  [InlineData("initializer outside its function domain", false)]
  [InlineData("valid nat initializer", true)]
  public async Task InitialConstantEquationsRequireValidation(string initializer, bool valid) {
    var spec = initializer.StartsWith("negative") ? NegativeConstant : initializer.StartsWith("initializer") ? UndefinedConstant : ValidConstant;
    var run = await Campaign.RunAsync(spec);
    Assert.Equal(1, run.Population.Executed);
    Assert.True(run.Population.Valid == (valid ? 1 : 0), run.Detail());
    Assert.Equal(valid ? 1 : 0, run.Result.Violations.Count);
  }

  // Runtime-only postconditions cannot indict a goal reached with an invalid typed initial field.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  [InlineData(2, false)]
  public async Task ValidatesInitialFieldsBeforeRuntimeGoalEvidence(int bucket, bool valid) {
    var run = await Campaign.RunAsync(TypedGhostField);
    if (valid) {
      run.AssertViolated(bucket, "false", Postcondition);
    } else {
      Assert.Empty(run.Violations(bucket));
    }
    Assert.Equal(2 * CampaignSpec.BucketSize, run.Population.PreconditionRejected);
  }

  // A nullable reference cycle does not hide invalid nested datatype fields or consume solver budget.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task ValidatesNestedFieldsInCyclicInitialHeap(int bucket, bool valid) {
    var run = await Campaign.RunAsync(CyclicTree);
    if (valid) {
      run.AssertViolated(bucket, "false", Postcondition);
    } else {
      Assert.Empty(run.Violations(bucket));
    }
    Assert.Equal(CampaignSpec.BucketSize, run.Population.Valid);
  }

  // Residual refinement constraints require a satisfiable typed initial state before runtime evidence.
  [Theory]
  [InlineData("negative value", false)]
  [InlineData("positive value", true)]
  [InlineData("positive value without budget", false)]
  public async Task ValidatesResidualInitialFieldConstraint(string row, bool valid) {
    var spec = row.StartsWith("negative") ? NegativeResidual : row.EndsWith("budget") ? UnbudgetedResidual : HeapProofReuseTests.PositiveCell;
    await AssertAdmission(spec, valid);
  }

  // Exact initial construction includes refined root arguments even when the captured heap is valid.
  [Theory]
  [InlineData(0, true)]
  [InlineData(1, false)]
  public async Task NativeConstructionIncludesRefinedRootInput(int bucket, bool valid) {
    var run = await Campaign.RunAsync(RefinedRoot);
    if (valid) {
      run.AssertViolated(bucket, "false", Postcondition);
    } else {
      Assert.Empty(run.Violations(bucket));
    }
    Assert.Equal(CampaignSpec.BucketSize, run.Population.Valid);
  }

  // A plain ill-defined function cannot supply a type certificate merely because it has no explicit contracts.
  [Fact]
  public async Task NativeConstructionRequiresPlainFunctionWellDefinedness() {
    await AssertAdmission(PlainFunctionWellDefinedness, false);
  }

  // Type-constraint dependencies cannot admit a heap using an unvalidated function contract, even behind a higher-order binding.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task InitialFieldConstraintCalleeRemainsUnchecked(bool higherOrder) {
    await AssertAdmission(higherOrder ? HigherOrderConstraintCallee : ConstraintCallee, false);
  }

  // Omitted refined ghost fields still require a satisfiable original typed heap.
  [Theory]
  [InlineData("empty refinement", false)]
  [InlineData("positive refinement", true)]
  [InlineData("positive refinement without budget", false)]
  public async Task ValidatesOmittedRefinedGhostField(string row, bool valid) {
    var spec = row.StartsWith("empty") ? EmptyOmittedField : row.EndsWith("budget") ? UnbudgetedOmittedField : PositiveOmittedField;
    await AssertAdmission(spec, valid);
  }

  // Unconstrained ordinary function fields can remain omitted without a solver query.
  [Fact]
  public async Task KeepsSafeOrdinaryArrowOmission() {
    await AssertAdmission(OrdinaryArrowOmission, true);
  }

  // An omitted ghost function returning an empty refined sequence has a valid constant-function inhabitant.
  [Fact]
  public async Task RunsWithConstructibleRefinedArrowOmission() {
    await AssertAdmission(RefinedArrowOmission, true);
    Assert.Equal(0, (await Campaign.RunAsync(RefinedArrowOmission)).Population.PreconditionUnchecked);
  }

  // An original declared witness can admit omitted state only after its native dependency and witness proofs succeed.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task CertifiesOriginalOmittedWitness(bool valid) {
    await AssertAdmission(valid ? ValidWitness : InvalidWitness, valid);
  }

  // An empty refinement nested in an omitted datatype must not be hidden by partial capture.
  [Fact]
  public async Task RejectsOmittedNestedEmptyRefinement() {
    await AssertAdmission(NestedEmptyOmission, false);
  }
}
