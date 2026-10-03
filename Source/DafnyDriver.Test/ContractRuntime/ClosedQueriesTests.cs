#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Clauses decided by closed queries over observed concrete values.</summary>
public class ClosedQueriesTests : IClassFixture<ClosedQueriesTests.Fixture> {
  private const string File = "ClosedQueries";
  private static readonly CampaignSpec Budget = CampaignSpec.Fixture(File, "Budget").Buckets(6) with {
    MaxClosedQueries = 64,
    ClosedQueryTimeout = 3000
  };
  private static readonly CampaignSpec ErasedEntry = CampaignSpec.Fixture(File, "ErasedEntry") with { SampleCount = 2 };
  private static readonly CampaignSpec Initializer = CampaignSpec.Fixture(File, "Initializer") with { SampleCount = 2 };
  private static readonly CampaignSpec CertifiedInitializer = Initializer with { MaxClosedQueries = 6 };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Budget, ErasedEntry, Initializer, CertifiedInitializer];
  }

  public ClosedQueriesTests(Fixture fixture) { }

  // Only the false closed-domain bucket is excluded; every other closed scenario is valid goal evidence.
  [Fact]
  public async Task OnlyFalseClosedDomainBucketIsExcluded() {
    var run = await Campaign.RunAsync(Budget);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Budget.SampleCount, Executed: Budget.SampleCount,
      Valid: Budget.SampleCount - CampaignSpec.BucketSize, CalleeContractViolations: CampaignSpec.BucketSize,
      ViolatingSamples: 2 * CampaignSpec.BucketSize), run.Detail());
  }

  // Closed SMT decides a quantified clause only after fixing the observed concrete inputs.
  [Fact]
  public async Task ChecksClosedQuantifier() {
    var run = await Campaign.RunAsync(Budget);
    var (obligation, _) = run.AssertViolated(0, "forall n: int :: n <= x");
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, obligation.DecisionMethod);
  }

  // A runtime check erased by ghost inference is decided by a closed query instead of passing unevaluated.
  [Fact]
  public async Task LowersErasedRuntimeCheckToClosedQuery() {
    var run = await Campaign.RunAsync(Budget);
    var (obligation, _) = run.AssertViolated(1, "d != C && d != A");
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, obligation.DecisionMethod);
    Assert.Equal(new ContractRuntimeEvaluations(ClosedSmt: Budget.SampleCount), obligation.Evaluations);
  }

  // A true clause that the solver cannot prove is left unchecked instead of being reported as violated.
  [Fact]
  public async Task ClosedQueryDoesNotReportUnprovenClause() {
    var run = await Campaign.RunAsync(Budget);
    Assert.Empty(run.Violations(2));
    var obligation = run.Obligation("Sum(k) >= 0", Postcondition);
    Assert.StartsWith("closed_query_", obligation.UncheckedReason);
    Assert.Equal(CampaignSpec.BucketSize, obligation.Evaluations.Unchecked);
  }

  // A closed-query clause that calls a contract-bearing function cannot indict the goal through that function.
  [Fact]
  public async Task ClosedClauseWithUnvalidatedCalleeIsUnchecked() {
    var run = await Campaign.RunAsync(Budget);
    Assert.Empty(run.Violations(3));
    var obligation = run.Obligation("Bad(x)", Postcondition);
    Assert.Equal("callee_contract_unvalidated", obligation.UncheckedReason);
    Assert.Equal(CampaignSpec.BucketSize, obligation.Evaluations.Unchecked);
  }

  // A false non-runtime domain decided from concrete inputs invalidates the callee instead of the goal.
  [Fact]
  public async Task RejectsClosedSpecFunctionDomain() {
    (await Campaign.RunAsync(Budget)).AssertCalleeViolated(4);
  }

  // A closed decision of an unbounded valid spec-function domain can admit the sample.
  [Fact]
  public async Task AcceptsClosedSpecFunctionDomain() {
    var run = await Campaign.RunAsync(Budget);
    run.AssertHolds(5, "HelperTrue(x)", Postcondition);
    Assert.Empty(run.CalleeViolations(5));
    Assert.Contains(run.Result.Obligations, obligation => obligation.Callee == "M.HelperTrue" &&
      obligation.Evaluations.ClosedSmt >= CampaignSpec.BucketSize);
  }

  // An erased entry precondition is never treated as satisfied, so its samples are discarded as unchecked.
  [Fact]
  public async Task ErasedEntryPreconditionDiscardsSamples() {
    var run = await Campaign.RunAsync(ErasedEntry);
    Assert.True(run.Result.Status == ContractRuntimeStatus.Inconclusive, run.Detail());
    Assert.Equal(ErasedEntry.SampleCount, run.Population.PreconditionUnchecked);
    Assert.Equal(0, run.Population.Valid);
  }

  // Capturing keeps the original initializer executable; accepting its readonly equation needs native validation.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task CapturesObjectWithConstantInitializer(bool certified) {
    var spec = certified ? CertifiedInitializer : Initializer;
    var run = await Campaign.RunAsync(spec);
    Assert.True(run.Result.Status == (certified ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive),
      run.Detail());
    Assert.Equal(spec.SampleCount, run.Population.Executed);
    Assert.Equal(certified ? spec.SampleCount : 0, run.Population.Valid);
    Assert.Equal(certified ? 0 : spec.SampleCount, run.Population.PreconditionUnchecked);
    Assert.Equal(0, run.Population.RuntimeErrors);
    var entry = Assert.Single(run.Records(0), record => record.GetProperty("kind").GetString() == "heap_capture" &&
      record.GetProperty("phase").GetString() == "entry");
    var box = entry.GetProperty("heap").EnumerateArray().Single(item => item.GetProperty("type").GetString() == "M.Box");
    Assert.Equal("7", box.GetProperty("fields").GetProperty("tag").GetProperty("value").GetString());
    if (certified) {
      Assert.Equal("7", run.Result.Violations.First().Values["b.tag"].Value);
    } else {
      Assert.Empty(run.Result.Violations);
    }
  }
}
