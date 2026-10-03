#nullable enable
using System.Collections.Generic;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Specification dependencies of two-state heap postconditions.</summary>
public class SpecificationDependenciesTests : IClassFixture<SpecificationDependenciesTests.Fixture> {
  private const string File = "SpecificationDependencies";
  private static readonly CampaignSpec Unvalidated = CampaignSpec.Fixture(File, "Unvalidated", "Client.Goal").Buckets(8) with {
    MaxClosedQueries = 24,
    ClosedQueryTimeout = 3000
  };
  private static readonly CampaignSpec LogicalCertificates =
    CampaignSpec.Fixture(File, "LogicalCertificates", "Client.Goal").Buckets(3) with {
      MaxClosedQueries = 24,
      ClosedQueryTimeout = 3000
    };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Unvalidated, LogicalCertificates];
  }

  public SpecificationDependenciesTests(Fixture fixture) { }

  // A clause whose specification dependency closure reaches an unvalidated contract never decides the entry body.
  [Theory]
  [InlineData("ChangedDirect(cell)", "explicit contract on the two-state predicate, in both polarities")]
  [InlineData("ChangedTransitive(cell)", "contract hidden behind the two-state predicate")]
  [InlineData("ChangedTyped(cell)", "invalid predicate in a dependency's formal type")]
  [InlineData("ChangedRecursive(cell)", "recursive contract with a cycle guard")]
  [InlineData("ChangedHigherOrder(cell)", "function hidden behind a local higher-order binding")]
  [InlineData("ChangedGhost(cell, amount)", "contract applied to a captured ghost input")]
  [InlineData("ChangedMismatch(cell)", "false definition whose by-method matches the contract")]
  public async Task UnvalidatedDependencyKeepsClauseUnchecked(string clause, string dependency) {
    var run = await Campaign.RunAsync(Unvalidated);
    var obligation = run.Obligation(clause, Postcondition);
    Assert.True(obligation.UncheckedReason == "callee_contract_unvalidated", dependency);
    Assert.Equal(new ContractRuntimeEvaluations(Unchecked: Unvalidated.SampleCount), obligation.Evaluations);
  }

  // No unvalidated dependency becomes evidence against the entry body in any sample.
  [Fact]
  public async Task UnvalidatedDependenciesReportNoViolation() {
    var run = await Campaign.RunAsync(Unvalidated);
    Assert.True(run.Result.Status == ContractRuntimeStatus.Inconclusive, run.Detail());
    Assert.Equal(Unvalidated.SampleCount, run.Population.Valid);
    Assert.Empty(run.Result.Violations);
  }

  // Logical use needs the original definition; an unexecuted compiled by-method is not a proof of that definition.
  [Fact]
  public async Task LogicalHeapCertificateDoesNotRequireUnexecutedByMethod() {
    var run = await Campaign.RunAsync(LogicalCertificates);
    var (_, violations) = run.AssertViolated(0, "ChangedHidden(cell)", Postcondition);
    Assert.All(violations, violation => Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, violation.DecisionMethod));
    Assert.Empty(run.CalleeViolations(0));
  }

  // A logical certificate cannot rescue a sample whose actual by-method result disagrees with its definition.
  [Theory]
  [InlineData(1, true)]
  [InlineData(2, false)]
  public async Task LogicalHeapCertificateRetainsExecutedByMethodChecks(int bucket, bool valid) {
    var run = await Campaign.RunAsync(LogicalCertificates);
    if (valid) {
      var (_, violations) = run.AssertViolated(bucket, "ChangedGood(cell)", Postcondition);
      Assert.All(violations, violation => Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, violation.DecisionMethod));
      Assert.Empty(run.CalleeViolations(bucket));
    } else {
      Assert.All(run.AssertCalleeViolated(bucket), violation => Assert.Equal("Client.OffsetBad", violation.Callee));
    }
  }
}
