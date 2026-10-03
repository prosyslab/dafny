#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Declarations reached across module, export and import boundaries.</summary>
public class ModuleBoundaryTests : IClassFixture<ModuleBoundaryTests.Fixture> {
  private const string File = "ModuleBoundary";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture(File, "Main").Buckets(10).WithDrafts(
    ("Lib.Store.ReadState", "method {:pbt_draft \"Lib.Store.ReadState\"} ReadState() returns (r: int) { r := state; }"),
    ("Lib.Store.ReadZero", "method {:pbt_draft \"Lib.Store.ReadZero\"} ReadZero() returns (r: int) { r := 0; }"),
    ("Shapes.Shape.Scale", "method {:pbt_draft \"Shapes.Shape.Scale\"} Scale(k: int) returns (a: int) { a := k * Area(); }"),
    ("Shapes.Shape.Area", "function {:pbt_draft \"Shapes.Shape.Area\"} Area(): int reads this { 0 }"));
  private static readonly CampaignSpec Host = CampaignSpec.Fixture(File, "Host").Buckets(1);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main, Host];
  }

  public ModuleBoundaryTests(Fixture fixture) { }

  // Only the invalid by-method bucket is excluded; every other cross-module scenario yields valid goal evidence.
  [Fact]
  public async Task OnlyInvalidImplementationBucketIsExcluded() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount,
      Valid: Main.SampleCount - CampaignSpec.BucketSize, CalleeContractViolations: CampaignSpec.BucketSize,
      ViolatingSamples: run.Population.ViolatingSamples), run.Detail());
  }

  // Cross-module specification wrappers keep their imported qualification and validate the callee at runtime.
  [Fact]
  public async Task ImportedSpecificationWrapperKeepsCompiledCheck() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(0, "result == 2");
    var callee = run.Obligation("N.Width(x)", CalleePostcondition);
    Assert.Equal(ContractRuntimeDecisionMethod.Runtime, callee.DecisionMethod);
    Assert.True(callee.Evaluations is { Runtime: >= CampaignSpec.BucketSize, ClosedSmt: 0, Unchecked: 0 }, run.Detail());
  }

  // Recursive by-method definition equality evaluates imported constructors in the declaring module.
  [Fact]
  public async Task ImportedRecursiveDefinitionKeepsCompiledCheck() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(1, "result == |values| + 1");
    var callees = run.Result.Obligations.Where(obligation => obligation.Callee == "Operations.Encode").ToList();
    Assert.Contains(callees, obligation => obligation.Evaluations.Runtime >= CampaignSpec.BucketSize);
    Assert.All(callees, obligation => Assert.True(obligation.Evaluations is { ClosedSmt: 0, Unchecked: 0 }, run.Detail()));
  }

  // Fixing recursive definition rendering must still exclude an implementation whose returned datatype sequence is wrong.
  [Fact]
  public async Task ImportedRecursiveDefinitionRejectsInvalidImplementation() {
    var run = await Campaign.RunAsync(Main);
    Assert.All(run.AssertCalleeViolated(2), violation => Assert.Equal("Operations.EncodeWrong", violation.Callee));
  }

  // A diagnostic generator may construct a region through an otherwise hidden ghost constructor.
  [Fact]
  public async Task ConstructsHiddenGhostRegion() {
    (await Campaign.RunAsync(Main)).AssertViolated(3, "S.Read(box) == 2");
  }

  // A subset-type test on a type from another module keeps its constraint function executable.
  [Fact]
  public async Task ExecutesCrossModuleSubsetTypeTest() {
    var run = await Campaign.RunAsync(Main);
    run.AssertHolds(4, "e in s && e % 2 == 0", Postcondition);
    Assert.Empty(run.Errors(4));
  }

  // A cross-module subset witness used as an array default value remains executable.
  [Fact]
  public async Task ExecutesCrossModuleSubsetWitness() {
    var run = await Campaign.RunAsync(Main);
    run.AssertHolds(5, "result >= 3", Postcondition);
    Assert.Empty(run.Errors(5));
  }

  // An export too short to rewrite in place no longer prevents the diagnostic from revealing its declarations.
  [Fact]
  public async Task ToleratesShortExportDeclaration() {
    (await Campaign.RunAsync(Main)).AssertViolated(6, "Short.F() + 1");
  }

  // A class-member draft can use ghost state after diagnostic preparation while retaining the original contract.
  [Fact]
  public async Task ExecutesGhostStateDraftForExternMember() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(7, "store.state + 1");
    Assert.Empty(run.CalleeViolations(7));
  }

  // A compilable class-member draft for an extern method executes and is checked against the original contract.
  [Fact]
  public async Task ExecutesCompilableDraftForExternMember() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(8, "store.state + 2");
    Assert.Empty(run.CalleeViolations(8));
  }

  // Drafts supplied for abstract trait members are ignored because the overrides implement them.
  [Fact]
  public async Task IgnoresDraftsForAbstractTraitMembers() {
    (await Campaign.RunAsync(Main)).AssertViolated(9, "3 * shape.Area()");
  }

  // A pure goal runs although unrelated modules keep logical ghost initialization and native-only dependencies.
  [Fact]
  public async Task IsolatesUnrelatedNativeHostState() {
    var run = await Campaign.RunAsync(Host);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(Host.SampleCount, run.Population.Valid);
    Assert.Equal(0, run.Population.RuntimeErrors);
  }
}
