#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Checks original logical dependencies before admitting scalar runtime clause evidence.</summary>
public class ClauseDependenciesTests : IClassFixture<ClauseDependenciesTests.Fixture> {
  private const string File = "ClauseDependencies";
  private static readonly CampaignSpec Main = CampaignSpec.Fixture(File, "Main").Buckets(4) with {
    ClosedQueryTimeout = 15000,
    SampleTimeout = 3000,
    Timeout = 240000
  };
  private static readonly CampaignSpec Bodyless = CampaignSpec.Fixture(File, "Bodyless");

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main, Bodyless];
  }

  public ClauseDependenciesTests(Fixture fixture) { }

  private static IEnumerable<ContractSpecificationResult> Proofs(CampaignRun run) =>
    run.Artifacts("specification-query-*.result.json").Select(path =>
      JsonSerializer.Deserialize<ContractSpecificationResult>(System.IO.File.ReadAllText(path), ContractJson.Options)!);

  // Only the certified dependency bucket is valid; every other dependency leaves its callee clause unchecked.
  [Fact]
  public async Task ClassifiesEveryBucket() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Population == new ContractRuntimePopulation(Generated: Main.SampleCount, Executed: Main.SampleCount,
      Valid: CampaignSpec.BucketSize, CalleeContractUnchecked: 3 * CampaignSpec.BucketSize,
      ViolatingSamples: CampaignSpec.BucketSize), run.Detail());
  }

  // A proven original dependency admits a positive callee clause and exposes the actual goal failure.
  [Fact]
  public async Task CertifiesOriginalScalarCalleeDependencies() {
    var run = await Campaign.RunAsync(Main);
    run.AssertViolated(0, "r == x + 1", Postcondition);
    Assert.Equal(CampaignSpec.BucketSize, run.Obligation("IdentityValid(x) == x", CalleePostcondition).Evaluations.ClosedSmt);
    Assert.Contains(Proofs(run), proof => proof.Verified && proof.Role == ContractSpecificationRole.Logical &&
      proof.Implementations.Any(name => name.Contains("IdentityValid", StringComparison.Ordinal)));
  }

  // A dependency that is invalid, trusted or opaque never certifies its closed callee clause.
  [Theory]
  [InlineData(1, "IdentityInvalid(x) == x", "invalid original function contract")]
  [InlineData(2, "IdentityTrusted(x) == x", "trust assumption in the original definition")]
  [InlineData(3, "IdentityOpaque(x) == x", "hidden definition with an insufficient exported contract")]
  public async Task UncertifiedDependencyKeepsCalleeClauseUnchecked(int bucket, string clause, string dependency) {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Violations(bucket).Count == 0, dependency);
    Assert.Empty(run.CalleeViolations(bucket));
    var obligation = run.Obligation(clause, CalleePostcondition);
    Assert.Equal(0, obligation.Evaluations.ClosedSmt);
    Assert.Equal(CampaignSpec.BucketSize, obligation.Evaluations.Unchecked);
  }

  // A bodyless logical dependency cannot be certified from its declared contract alone; it is requested as a draft.
  [Fact]
  public async Task RejectsBodylessLogicalDefinition() {
    var run = await Campaign.RunAsync(Bodyless);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, run.Result.Status);
    Assert.Equal("M.Identity", Assert.Single(run.Result.MissingDrafts).Symbol);
    Assert.Empty(run.Result.Violations);
    Assert.Equal(0, run.Population.Valid);
  }

  // An invalid original function contract fails its native dependency proof.
  [Fact]
  public async Task RejectsInvalidOriginalFunctionContract() {
    var run = await Campaign.RunAsync(Main);
    Assert.Contains(Proofs(run), proof => !proof.Verified &&
      proof.Implementations.Any(name => name.Contains("IdentityInvalid", StringComparison.Ordinal)));
  }

  // Original clauses are recovered by immutable source identity, never by reusing a detached expression.
  [Fact]
  public async Task MapsOnlyExactOriginalDeclaredClause() {
    const string source = "// 한글\nmodule M { ghost function Identity(x:int):int { x } method Help(x:int) ensures Identity(x) == x {} }";
    ContractSource[] sources = [Campaign.Source("M.dfy", source)];
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var original = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var detached = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var owner = ContractRuntimeObligationTransformer.Members(detached).OfType<Method>().Single();
    var expression = owner.Ens.Single().E;
    var obligation = new ContractRuntimeObligation("clause", CalleePostcondition,
      "M.dfy", expression.Origin.line, expression.Origin.col, "Identity(x) == x", "M.Help",
      ContractRuntimeDecisionMethod.ClosedSmt, null, new());
    var clause = new ContractRuntimeClause(obligation, expression, [], owner, true,
      OriginalSourceHash: sources[0].Sha256, OriginalSourceSetHash: ContractRuntimeTypeEvidence.SourceSetHash(sources));
    var mapped = ContractRuntimeClauseDependencies.OriginalExpression(original, sources, clause);
    Assert.Same(ContractRuntimeObligationTransformer.Members(original).OfType<Method>().Single().Ens.Single().E, mapped);
    Assert.NotSame(expression, mapped);
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources, clause with { OriginalSourceHash = "wrong" }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources, clause with { OriginalSourceSetHash = "wrong" }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources, clause with { TypeConstraint = true }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Column = obligation.Column + 1 } }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Clause = "true" } }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Kind = LoopInvariantEntry } }));
  }

  // Original assertions are recovered only from the exact target source location, text and hashes.
  [Fact]
  public async Task MapsOnlyExactOriginalTargetAssertion() {
    const string source = "module M { method Goal(x:int) { assert x > 0; } }";
    ContractSource[] sources = [Campaign.Source("M.dfy", source)];
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var original = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var detached = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var owner = ContractRuntimeObligationTransformer.Members(detached).OfType<Method>().Single();
    var assertion = owner.Body!.Descendants().OfType<AssertStmt>().Single();
    var obligation = new ContractRuntimeObligation("clause", Assertion, "M.dfy", assertion.Expr.Origin.line,
      assertion.Expr.Origin.col, "x > 0", null, ContractRuntimeDecisionMethod.ClosedSmt, null, new());
    var clause = new ContractRuntimeClause(obligation, assertion.Expr, [], owner,
      OriginalSourceHash: sources[0].Sha256, OriginalSourceSetHash: ContractRuntimeTypeEvidence.SourceSetHash(sources));

    var mapped = ContractRuntimeClauseDependencies.OriginalExpression(original, sources, clause);

    Assert.Same(ContractRuntimeObligationTransformer.Members(original).OfType<Method>().Single()
      .Body!.Descendants().OfType<AssertStmt>().Single().Expr, mapped);
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { OriginalSourceHash = "wrong" }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Column = obligation.Column + 1 } }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Clause = "x >= 0" } }));
    Assert.Null(ContractRuntimeClauseDependencies.OriginalExpression(original, sources,
      clause with { Obligation = obligation with { Kind = Postcondition } }));
  }
}
