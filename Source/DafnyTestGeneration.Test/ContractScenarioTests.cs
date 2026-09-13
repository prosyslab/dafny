using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractScenarioTests {
  // A false conjunction covers its first false operand even when another operand can also falsify the guard.
  [Fact]
  public async Task ShortCircuitCasesCoverBothFalseOperandsWithinBudget() {
    const string source = "class Box { var spare:int } method Entry(box:Box,amount:int,enabled:bool) returns(r:int) requires amount >= 23 ensures if !enabled && amount == 23 then r == 0 else r == 1 { r := 0; if amount == 23 { r := 0; } else { r := 1; } }";
    var result = await ContractInputGenerator.GenerateAsync(ContractInputTests.Request(source, count: 4),
      ContractInputTests.Options(), CancellationToken.None);
    Assert.Contains(result.Inputs, input => input.GoalKind == ContractInputGoalKind.SpecificationCase &&
      input.Request.Inputs["enabled"].Value == "true" && input.Request.Inputs["amount"].Value == "23");
    Assert.Equal(ContractInputGoalKind.SpecificationCase, result.Inputs[1].GoalKind);
  }

  // Short-circuit false cases never demand an invalid right-hand sequence index.
  [Fact]
  public async Task ShortCircuitCasesPreserveRightOperandDefinedness() {
    const string source = "method Entry(s:seq<int>) returns(r:int) ensures if |s| > 0 && s[0] == 29 then r == 1 else r == 0 { r := 0; }";
    var request = ContractInputTests.Request(source, count: 1) with {
      RequiredGoalId = "spec1",
      CandidateInputs = new System.Collections.Generic.Dictionary<string, ContractValue> {
        ["s"] = new(ContractValueKind.Sequence, Items: [])
      }
    };
    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(), CancellationToken.None);
    Assert.Single(result.Inputs);
    Assert.Equal(0, result.Counts.Unknown);
  }

  // Conditional specifications over old fields create input cases independently of actual body branches.
  [Fact]
  public async Task OldHeapGuardCreatesInitialStateCases() {
    var options = ContractInputTests.Options();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter,
      "class Memory { var available:bool var container:bool } method Entry(io:Memory) returns(r:int) ensures if !old(io.available) || !old(io.container) then r == 1 else r == 0 { r := 0; }");
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var scenarios = new ContractScenarioExtractor(program, method).Extract();
    Assert.Equal(3, scenarios.Count(scenario => scenario.Projection == ContractScenarioProjection.Exact));
    Assert.All(scenarios.Where(scenario => scenario.Projection == ContractScenarioProjection.Exact),
      scenario => Assert.DoesNotContain("old(", scenario.InputConstraint));
  }

  // Nested else guards retain earlier branch negations when selecting an input case.
  [Fact]
  public async Task NestedBranchesPreservePriorNegation() {
    var source = "method Entry(x:int) returns(r:int) ensures if x < 10 then r == 0 else if x < 20 then r == 1 else r == 2 { r := 0; }";
    var request = ContractInputTests.Request(source, count: 1) with {
      RequiredGoalId = "spec3",
      CandidateInputs = new System.Collections.Generic.Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "5") }
    };
    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(), CancellationToken.None);
    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.BoundedUnsat > 0);
  }

  // Output-dependent guards remain residual instead of inventing an exact input projection.
  [Fact]
  public async Task OutputDependentGuardRemainsResidual() {
    var options = ContractInputTests.Options();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, "method Entry(x:int) returns(r:int) ensures if r > 0 then x > 0 else x <= 0 { r := x; }");
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var scenarios = new ContractScenarioExtractor(program, method).Extract();
    Assert.All(scenarios, scenario => Assert.Equal(ContractScenarioProjection.Residual, scenario.Projection));
  }
}
