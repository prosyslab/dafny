#nullable enable
using System;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>Checks original logical dependencies before admitting scalar runtime clause evidence.</summary>
public class ContractRuntimeClauseDependencyTests {
  private const string Identity = "ghost function Identity(x:int):int ensures Identity(x) == x { x }";
  private const string Body = "method Help(x:int) ensures forall n:int :: n*n >= 0 && Identity(x) == x {} " +
    "method Goal(x:int) returns(r:int) ensures r == x+1 { Help(x); r := x; }";

  // A proven original dependency admits a positive callee clause and exposes the actual goal failure.
  [Fact]
  public async Task CertifiesOriginalScalarCalleeDependencies() {
    var (result, directory) = await Run(Identity);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Equal(0, result.Population.CalleeContractUnchecked);
    Assert.Contains(result.Obligations, obligation => obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition &&
      obligation.Evaluations.ClosedSmt == 1);
    Assert.Single(result.Violations);
    var proofs = Directory.GetFiles(directory, "specification-query-*.result.json").Select(File.ReadAllText)
      .Select(text => JsonSerializer.Deserialize<ContractSpecificationResult>(text, ContractJson.Options)!).ToList();
    Assert.Contains(proofs, proof => proof.Verified && proof.Role == ContractSpecificationRole.Logical &&
      proof.Implementations.Any(name => name.Contains("Identity", StringComparison.Ordinal)));
  }

  // An invalid original function contract cannot authorize a contradictory closed clause proof.
  [Fact]
  public async Task RejectsInvalidOriginalFunctionContract() {
    var (result, directory) = await Run(Identity.Replace("== x {", "== x+1 {"));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractUnchecked);
    Assert.Contains(Directory.GetFiles(directory, "specification-query-*.result.json"), path =>
      JsonSerializer.Deserialize<ContractSpecificationResult>(File.ReadAllText(path), ContractJson.Options) is { Verified: false });
  }

  // A trust assumption in the original definition never becomes a dependency certificate.
  [Fact]
  public async Task RejectsTrustedOriginalDefinition() {
    var (result, _) = await Run(Identity.Replace("{ x }", "{ assume false; x }"));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractUnchecked);
  }

  // Hidden definitions with insufficient exported contracts remain unproved despite their true bodies.
  [Fact]
  public async Task KeepsOpaqueDefinitionUnproved() {
    var (result, _) = await Run("opaque ghost function Identity(x:int):int ensures true { x }");
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractUnchecked);
  }

  // A bodyless logical dependency cannot be certified from its declared contract alone.
  [Fact]
  public async Task RejectsBodylessLogicalDefinition() {
    var (result, _) = await Run("ghost function {:axiom} Identity(x:int):int ensures Identity(x) == x");
    Assert.NotEqual(ContractRuntimeStatus.ViolationFound, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal(0, result.Population.Valid);
  }

  // A zero budget or one spent on the clause query cannot also certify its original dependencies.
  [Theory]
  [InlineData(0)]
  [InlineData(1)]
  public async Task RespectsSharedClosedQueryBudget(int budget) {
    var (result, directory) = await Run(Identity, budget);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, result.Status);
    Assert.Empty(result.Violations);
    Assert.Equal(1, result.Population.CalleeContractUnchecked);
    Assert.Empty(Directory.GetFiles(directory, "specification-query-*.result.json"));
  }

  // Original clauses are recovered by immutable source identity, never by reusing a detached expression.
  [Fact]
  public async Task MapsOnlyExactOriginalDeclaredClause() {
    const string source = "// 한글\nmodule M { ghost function Identity(x:int):int { x } method Help(x:int) ensures Identity(x) == x {} }";
    ContractSource[] sources = [new("M.dfy", source, ContractHarnessBuilder.Hash(source))];
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var original = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var detached = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var owner = ContractRuntimeObligationTransformer.Members(detached).OfType<Method>().Single();
    var expression = owner.Ens.Single().E;
    var obligation = new ContractRuntimeObligation("clause", ContractRuntimeObligationKind.CalleePostcondition,
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
      clause with { Obligation = obligation with { Kind = ContractRuntimeObligationKind.LoopInvariantEntry } }));
  }

  private static string Detail(ContractRuntimeCampaignResult result) => JsonSerializer.Serialize(result, ContractJson.Options);

  private static async Task<(ContractRuntimeCampaignResult Result, string Directory)> Run(string identity, int maxQueries = 8) {
    var source = "module M { " + identity + " " + Body + " }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r:PbtRandom.Source) returns(x:int) { x := 1; }";
    var directory = Path.Combine("/workspace/tmp", "contract-scalar-dependency-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var request = new ContractRuntimeCampaignRequest(1, [new("M.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("M.Goal"), "17", Generator: new("G.dfy", generator, ContractHarnessBuilder.Hash(generator)),
      SampleCount: 1, TimeoutMilliseconds: 90000, MaxClosedQueries: maxQueries, ClosedQueryTimeoutMilliseconds: 15000,
      SampleTimeoutMilliseconds: 3000);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(100));
    return (await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token), directory);
  }
}
