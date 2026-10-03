#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Function-by-method goals: their implementation runs and the original function contract is checked.</summary>
public class FunctionByMethodGoalTests : IClassFixture<FunctionByMethodGoalTests.Fixture> {
  private const string File = "FunctionByMethodGoal";
  private const string Definition = "if tag == 1 then n + 1 else";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture(File, "Main").Buckets(3);
  private static readonly CampaignSpec MissingHelper = CampaignSpec.Fixture(File, "Helper");
  private static readonly CampaignSpec DraftedHelper = MissingHelper.WithDrafts(
    ("M.Helper", "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; }")) with { SampleCount = 2 };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main, MissingHelper, DraftedHelper];
  }

  public FunctionByMethodGoalTests(Fixture fixture) { }

  // A function-by-method goal executes its implementation and checks the original function contract.
  [Fact]
  public async Task ExecutesFunctionByMethod() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(0, "Goal(tag, n) == n + 1", ContractRuntimeObligationKind.Postcondition);
    Assert.Empty(run.Violations(0, Definition));
  }

  // A function-by-method result that differs from the original definition is reported at that definition.
  [Fact]
  public async Task ChecksFunctionByMethodDefinition() {
    var run = await Campaign.RunAsync(Main);
    var (obligation, violations) = run.AssertViolated(1, Definition, ContractRuntimeObligationKind.Postcondition);
    Assert.StartsWith(Definition, obligation.Clause);
    var line = Main.Sources[0].Content.Split('\n')[obligation.Line - 1];
    Assert.Equal(line.IndexOf(Definition, StringComparison.Ordinal) + 1, obligation.Column);
    Assert.All(violations, violation => {
      Assert.Equal("1", violation.Values["contractResult"].Value);
      Assert.Equal("2", violation.Values["Goal(tag, n)"].Value);
    });
  }

  // Obligations of a correct recursive function-by-method evaluate its definition instead of re-entering the implementation.
  [Fact]
  public async Task EvaluatesRecursiveDefinitionInObligations() {
    var run = await Campaign.RunAsync(Main);
    run.AssertHolds(2, "c == Goal(tag, i)", ContractRuntimeObligationKind.LoopInvariantMaintenance);
    Assert.Equal(Main.SampleCount, run.Population.Valid);
    Assert.All(run.Result.Obligations, obligation => Assert.Equal(ContractRuntimeDecisionMethod.Runtime, obligation.DecisionMethod));
  }

  // A bodyless method reached only through a function-by-method body is requested before any compilation.
  [Fact]
  public async Task RequiresDraftInsideFunctionByMethod() {
    var run = await Campaign.RunAsync(MissingHelper);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, run.Result.Status);
    var missing = Assert.Single(run.Result.MissingDrafts);
    Assert.Equal("M.Helper", missing.Symbol);
    Assert.Contains("ensures", missing.Contract);
  }

  // A drafted method call inside a function-by-method body executes and satisfies the original definition.
  [Fact]
  public async Task ExecutesDraftInsideFunctionByMethod() {
    var run = await Campaign.RunAsync(DraftedHelper);
    Assert.True(run.Result.Status == ContractRuntimeStatus.NoViolationFound, run.Detail());
    Assert.Equal(DraftedHelper.SampleCount, run.Population.Valid);
  }
}
