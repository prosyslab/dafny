#nullable enable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Reuse of native heap proofs, membership certificates and closed-query budget across samples and clauses.</summary>
public class HeapProofReuseTests : IClassFixture<HeapProofReuseTests.Fixture> {
  private const string File = "HeapProofReuse";

  private static CampaignSpec Heap(string section, int queries, int samples = 1, string entry = "Client.Goal") =>
    CampaignSpec.Fixture(File, section, entry) with { MaxClosedQueries = queries, ClosedQueryTimeout = 3000, SampleCount = samples };

  private static readonly CampaignSpec GlobalReuse = Heap("GlobalReuse", 3, 20);
  private static readonly CampaignSpec DistinctHeaps = Heap("DistinctHeaps", 2, 2);
  private static readonly CampaignSpec ChangedValue = Heap("ChangedValue", 3, 2);
  private static readonly CampaignSpec UnsuccessfulProof = Heap("UnsuccessfulProof", 3, 2);
  private static readonly CampaignSpec ObservedReuse = Heap("ObservedReuse", 4);
  private static readonly CampaignSpec InvalidLaterState = Heap("InvalidLaterState", 3);
  internal static readonly CampaignSpec PositiveCell = Heap("PositiveCell", 2);
  private static readonly CampaignSpec PositiveCellOtherView = PositiveCell with {
    Sources = [Campaign.Source(PositiveCell.Sources[0].Path, PositiveCell.Sources[0].Content + "\n// distinct supplied source view")]
  };
  private static readonly CampaignSpec NativeCertificateReuse = Heap("NativeCertificateReuse", 5);
  private static readonly CampaignSpec HeapFacts = Heap("HeapFacts", 4);
  private static readonly CampaignSpec RecursiveMembership = Heap("RecursiveMembership", 1, entry: "M.Goal");
  private static readonly CampaignSpec RecursiveMembershipDuplicate = RecursiveMembership with {
    Generator = Campaign.Source(RecursiveMembership.Generator!.Path, RecursiveMembership.Generator.Content.Replace("Node(1,map[])", "Node(0,map[])"))
  };
  private static readonly CampaignSpec RecursiveMembershipInvalidCallee = RecursiveMembership with {
    Sources = [Campaign.Source(RecursiveMembership.Sources[0].Path,
      RecursiveMembership.Sources[0].Content.Replace("reads cell { cell.value }", "reads cell ensures false { cell.value }"))]
  };

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [GlobalReuse,
      DistinctHeaps,
      ChangedValue,
      UnsuccessfulProof,
      ObservedReuse,
      InvalidLaterState,
      PositiveCell,
      PositiveCellOtherView,
      NativeCertificateReuse,
      HeapFacts,
      RecursiveMembership,
      RecursiveMembershipDuplicate,
      RecursiveMembershipInvalidCallee];
  }

  public HeapProofReuseTests(Fixture fixture) { }

  private static IEnumerable<JsonElement> AllRecords(CampaignRun run) =>
    Enumerable.Range(0, run.Spec.SampleCount).SelectMany(run.Records);

  // A single source-bound global certificate admits many distinct pure inputs despite an unused ghost output.
  [Fact]
  public async Task IndependentGlobalProofIsReusedAcrossPureSamples() {
    var run = await Campaign.RunAsync(GlobalReuse);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(20, run.Population.Valid);
    Assert.Equal(0, run.Population.PreconditionUnchecked);
    Assert.Equal(20, AllRecords(run).Where(record => record.GetProperty("kind").GetString() == "input")
      .Select(record => record.GetProperty("value").GetRawText()).Distinct().Count());
    Assert.Single(run.Artifacts("specification-query-*.result.json"));
    Assert.Empty(run.Artifacts("heap-query-*.result.json"));
    Assert.Empty(run.Artifacts("initial-type-query-*.result.json"));
    var certificates = run.Artifacts("initial-type-certificate-*.json");
    Assert.Equal(20, certificates.Length);
    foreach (var certificate in certificates.Select(CampaignRun.Json)) {
      Assert.True(certificate.GetProperty("passed").GetBoolean());
      Assert.True(certificate.GetProperty("hostMembershipChecks").GetInt32() > 0);
      Assert.NotEqual(JsonValueKind.Null, certificate.GetProperty("independentGlobals").ValueKind);
    }
  }

  // An exact successful membership proof admits a second distinct heap without consuming a closed-query slot.
  [Fact]
  public async Task MembershipReuseAdmitsDistinctHeapsAfterQueryCap() {
    var run = await Campaign.RunAsync(DistinctHeaps);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(2, run.Population.Valid);
    Assert.Equal(2, AllRecords(run).Where(record => record.GetProperty("kind").GetString() == "heap_capture" &&
      record.GetProperty("phase").GetString() == "entry").Select(record => record.GetProperty("heap").GetRawText()).Distinct().Count());
    Assert.Single(run.Artifacts("initial-type-query-*.result.json"));
    Assert.Equal(2, run.Artifacts("initial-type-certificate-*.json").Length);
    var receipt = CampaignRun.Json(Assert.Single(run.Artifacts("membership-proof-reuse-initial-*.json")));
    var original = receipt.GetProperty("originalProof");
    Assert.Equal("unsat", original.GetProperty("outcome").GetString());
    Assert.Equal(receipt.GetProperty("identitySha256").GetString(), original.GetProperty("identitySha256").GetString());
    foreach (var (artifact, hash) in new[] { ("queryArtifact", "querySha256"), ("resultArtifact", "resultSha256") }) {
      var path = Path.Combine(run.Directory, original.GetProperty(artifact).GetString()!);
      Assert.True(System.IO.File.Exists(path));
      Assert.Equal(original.GetProperty(hash).GetString(), Campaign.Hash(System.IO.File.ReadAllText(path)));
    }
  }

  // Different refined values produce distinct membership identities and native proofs.
  [Fact]
  public async Task MembershipReuseRejectsChangedValue() {
    var run = await Campaign.RunAsync(ChangedValue);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(2, run.Population.Valid);
    var queries = run.Artifacts("initial-type-query-*.dfy");
    Assert.Equal(2, queries.Length);
    Assert.Equal(2, queries.Select(System.IO.File.ReadAllText).Distinct().Count());
    Assert.Empty(run.Artifacts("membership-proof-reuse-*.json"));
  }

  // An identical unsuccessful membership query is retried and never authorizes either invalid heap.
  [Fact]
  public async Task MembershipReuseRejectsUnsuccessfulProof() {
    var run = await Campaign.RunAsync(UnsuccessfulProof);
    Assert.True(run.Result.Status == ContractRuntimeStatus.Inconclusive, run.Detail());
    Assert.Equal(0, run.Population.Valid);
    var queries = run.Artifacts("initial-type-query-*.dfy");
    Assert.Equal(2, queries.Length);
    Assert.Single(queries.Select(System.IO.File.ReadAllText).Distinct());
    Assert.All(run.Artifacts("initial-type-query-*.result.json"), path =>
      Assert.NotEqual("unsat", CampaignRun.Json(path).GetProperty("outcome").GetString()));
    Assert.Empty(run.Artifacts("membership-proof-reuse-*.json"));
  }

  // An exact observed-state membership can cite the initial proof while the original transition is checked separately.
  [Fact]
  public async Task MembershipReuseSharesExactInitialProofWithObservedState() {
    var run = await Campaign.RunAsync(ObservedReuse);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Single(run.Artifacts("initial-type-query-*.result.json"));
    Assert.Empty(run.Artifacts("observed-type-query-*.result.json"));
    var receipt = CampaignRun.Json(Assert.Single(run.Artifacts("membership-proof-reuse-observed-*.json")));
    Assert.Equal("observed", receipt.GetProperty("role").GetString());
    Assert.Equal("initial", receipt.GetProperty("originalProof").GetProperty("role").GetString());
    Assert.Equal(receipt.GetProperty("identitySha256").GetString(),
      receipt.GetProperty("originalProof").GetProperty("identitySha256").GetString());
  }

  // A valid initial proof cannot admit a changed invalid observed carrier.
  [Fact]
  public async Task MembershipReuseKeepsInvalidLaterStateUnchecked() {
    var run = await Campaign.RunAsync(InvalidLaterState);
    Assert.True(run.Result.Status == ContractRuntimeStatus.Inconclusive, run.Detail());
    Assert.Empty(run.Result.Violations);
    Assert.Single(run.Artifacts("initial-type-query-*.result.json"));
    var observed = CampaignRun.Json(Assert.Single(run.Artifacts("observed-type-query-*.result.json")));
    Assert.NotEqual("unsat", observed.GetProperty("outcome").GetString());
    Assert.Empty(run.Artifacts("membership-proof-reuse-*.json"));
  }

  // Exact proof state remains campaign-local when the supplied source view changes.
  [Fact]
  public async Task MembershipReuseDoesNotCrossCampaignOrSourceView() {
    var first = await Campaign.RunAsync(PositiveCell);
    var second = await Campaign.RunAsync(PositiveCellOtherView);
    Assert.True(first.Result.Status == ContractRuntimeStatus.ViolationFound, first.Detail());
    Assert.True(second.Result.Status == ContractRuntimeStatus.ViolationFound, second.Detail());
    Assert.NotEqual(System.IO.File.ReadAllText(Assert.Single(first.Artifacts("initial-type-query-*.dfy"))),
      System.IO.File.ReadAllText(Assert.Single(second.Artifacts("initial-type-query-*.dfy"))));
    Assert.Empty(first.Artifacts("membership-proof-reuse-*.json"));
    Assert.Empty(second.Artifacts("membership-proof-reuse-*.json"));
  }

  // Reusing the exact initial construction certificate leaves enough budget for the original observed-state decision.
  [Fact]
  public async Task ReusesExactNativeInitialCertificateForHeapDecision() {
    var run = await Campaign.RunAsync(NativeCertificateReuse);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(1, run.Population.Valid);
    Assert.Contains(run.Result.Violations, violation => violation.DecisionMethod == ContractRuntimeDecisionMethod.ClosedSmt);
  }

  // Two different clauses on the same observed state reuse a successful native premise rather than spending its budget twice.
  [Fact]
  public async Task ExactHeapFactsAreReusedAcrossClauses() {
    var run = await Campaign.RunAsync(HeapFacts);
    Assert.True(run.Population.Valid == 1, run.Detail());
    Assert.All(run.Result.Obligations.Where(item => item.Kind == ContractRuntimeObligationKind.Postcondition),
      item => Assert.Equal(1, item.Evaluations.ClosedSmt));
    Assert.NotEmpty(run.Artifacts("heap-fact-reuse-*.json"));
    var profile = JsonSerializer.Deserialize<ContractProfile>(
      System.IO.File.ReadAllText(Path.Combine(run.Directory, "campaign-profile.json")), ContractJson.Options)!;
    Assert.Equal(new[] { "result_classification", "sample_process" }, profile.Metrics.Select(metric => metric.Name));
    Assert.All(profile.Metrics, metric => { Assert.Equal(1, metric.Count); Assert.True(metric.ElapsedMilliseconds >= 0); });
    Assert.True(System.IO.File.Exists(Path.Combine(run.Directory, "sample-0.jsonl.profile.json")));
  }

  // Existing compiled recursive membership can admit exact captured carriers without an empty native proof query.
  [Theory]
  [InlineData("unique child id", true)]
  [InlineData("duplicate child id", false)]
  [InlineData("invalid callee contract", false)]
  public async Task ReusesCompiledRecursiveTypeCheckForCapturedHeap(string row, bool valid) {
    var spec = row.StartsWith("unique") ? RecursiveMembership : row.StartsWith("duplicate") ? RecursiveMembershipDuplicate : RecursiveMembershipInvalidCallee;
    var run = await Campaign.RunAsync(spec);
    Assert.True(run.Result.Status == (valid ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.Inconclusive), run.Detail());
    Assert.Equal(valid ? 1 : 0, run.Population.Valid);
    if (!valid) { return; }
    var certificate = CampaignRun.Json(Assert.Single(run.Artifacts("initial-type-certificate-*.json")));
    Assert.True(certificate.GetProperty("passed").GetBoolean());
    Assert.False(certificate.GetProperty("requiresNativeProof").GetBoolean());
    var reused = certificate.GetProperty("runtimeChecks").EnumerateArray().Select(item => item.GetString()).ToList();
    Assert.NotEmpty(reused);
    Assert.Contains(run.Result.Obligations, obligation => reused.Contains(obligation.Id) &&
      obligation.Callee == "M.Read" && obligation.Clause.Contains("contractResult"));
    Assert.Empty(run.Artifacts("initial-type-query-*.dfy"));
  }
}
