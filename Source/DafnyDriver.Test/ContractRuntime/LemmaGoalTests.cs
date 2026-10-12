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

/// <summary>Checks concrete lemma implications without executing or trusting the erased target proof.</summary>
public class LemmaGoalTests : IClassFixture<LemmaGoalTests.Fixture> {
  private static readonly CampaignSpec Main = Spec("Main").Buckets(3);
  private static readonly string[] Cases = ["Quantified",
    "Dependency",
    "Trusted",
    "PremiseDependency",
    "SelfDependency",
    "ValidSelfDependency",
    "BodylessDependency",
    "Hidden",
    "Undefined",
    "InvalidType",
    "BodylessRefinement",
    "TrustedRefinement",
    "VerifiedRefinement",
    "ProofOnlyInput",
    "SelfRefinement"];

  private static CampaignSpec Spec(string section) => CampaignSpec.Fixture("LemmaGoal", section);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => Cases.Select(Spec).Prepend(Main);
  }

  public LemmaGoalTests(Fixture fixture) { }

  // A true premise and false original conclusion produce a postcondition witness without running the impossible proof.
  [Fact]
  public async Task FindsFalseConclusion() {
    var run = await Campaign.RunAsync(Main);
    Assert.Equal(ContractRuntimeStatus.ViolationFound, run.Result.Status);
    var (obligation, violations) = run.AssertViolated(0, "x == 0", Postcondition);
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, obligation.DecisionMethod);
    Assert.All(violations, violation => Assert.Equal("1", violation.Inputs["x"].Value));
    Assert.DoesNotContain(run.Result.Obligations, item => item.Kind == Assertion);
    Assert.Empty(run.Result.MissingDrafts);
    Assert.Equal(2 * CampaignSpec.BucketSize, run.Population.Valid);
  }

  // A sampled input outside the original premise cannot become a lemma counterexample.
  [Fact]
  public async Task RejectsFalsePremise() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(2));
    Assert.Equal(CampaignSpec.BucketSize, run.Population.PreconditionRejected);
    Assert.Equal(CampaignSpec.BucketSize, run.Obligation("x >= 0", EntryPrecondition).Violations);
  }

  // A valid sample satisfying the conclusion remains decided without producing a violation.
  [Fact]
  public async Task AcceptsTrueConclusion() {
    var run = await Campaign.RunAsync(Main);
    Assert.Empty(run.Violations(1));
    Assert.Equal(Main.SampleCount, run.Obligation("x == 0", Postcondition).Evaluations.ClosedSmt);
    Assert.Equal(0, run.Obligation("x == 0", Postcondition).Evaluations.Unchecked);
  }

  // A bodyless target with typed datatype inputs can expose a quantified false conclusion through its original definition.
  [Fact]
  public async Task FindsQuantifiedValueCounterexample() {
    var run = await Campaign.RunAsync(Spec("Quantified"));
    Assert.Equal(ContractRuntimeStatus.ViolationFound, run.Result.Status);
    Assert.Equal(1, run.Population.Valid);
    Assert.Equal(Postcondition, Assert.Single(run.Result.Violations).Kind);
    Assert.Equal(ContractValueKind.Datatype, Assert.Single(run.Result.Violations[0].Inputs["items"].Items!).Kind);
    var proofs = run.Artifacts("specification-query-*.result.json").Select(path =>
      JsonSerializer.Deserialize<ContractSpecificationResult>(File.ReadAllText(path), ContractJson.Options)!);
    Assert.Contains(proofs, proof => proof.Verified && proof.Role == ContractSpecificationRole.Logical &&
      proof.Implementations.Any(name => name.Contains("Nonzero")));
  }

  // An unproved logical dependency cannot support a lemma conclusion even when its erased definition looks decidable.
  [Theory]
  [InlineData("Dependency")]
  [InlineData("Trusted")]
  [InlineData("SelfDependency")]
  [InlineData("BodylessDependency")]
  public async Task LeavesUncertifiedConclusionUnchecked(string section) {
    var run = await Campaign.RunAsync(Spec(section));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    var obligation = run.Obligation("Identity(x) == 0", Postcondition);
    Assert.Equal(1, obligation.Evaluations.Unchecked);
    Assert.Equal("callee_contract_unvalidated", obligation.UncheckedReason);
  }

  // The premise itself needs a complete logical dependency certificate before an input can indict the lemma.
  [Fact]
  public async Task LeavesUncertifiedPremiseUnadmitted() {
    var run = await Campaign.RunAsync(Spec("PremiseDependency"));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    Assert.Equal(0, run.Population.Valid);
    Assert.Equal("callee_contract_unvalidated", run.Obligation("Admitted(x)", EntryPrecondition).UncheckedReason);
  }

  // Even an independently verifiable target cannot serve as proof evidence for its own sampled conclusion.
  [Fact]
  public async Task RejectsVerifiableSelfDependencyBeforeCertification() {
    var spec = Spec("ValidSelfDependency");
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var original = await ContractSourceSnapshot.ParseAsync(reporter, spec.Sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var target = ContractCallableSelector.SelectMethod(original, new("M.Goal"), allowLemmaContract: true);
    var checker = new ContractSpecificationChecker(original, spec.Sources, options);
    var scope = checker.LogicalScope(target.Ens.Single().E);
    Assert.True(scope.ContainsDeclaration(target));
    foreach (var module in checker.PendingModules(scope)) {
      var proof = await checker.CheckModuleAsync(scope, module, CancellationToken.None);
      Assert.True(proof.Verified, proof.Diagnostics);
    }
    Assert.True(checker.Accept(scope));

    var run = await Campaign.RunAsync(spec);
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    var conclusion = Assert.Single(run.Result.Obligations.Where(obligation => obligation.Kind == Postcondition));
    Assert.Equal(1, conclusion.Evaluations.Unchecked);
    Assert.Equal("callee_contract_unvalidated", conclusion.UncheckedReason);
    Assert.Contains(run.Artifacts("specification-scope-*.json"), path =>
      CampaignRun.Json(path).GetProperty("failure").GetString() == "target_lemma_dependency");
    Assert.DoesNotContain(run.Artifacts("specification-query-*.result.json"), path =>
      JsonSerializer.Deserialize<ContractSpecificationResult>(File.ReadAllText(path), ContractJson.Options)!
        .Implementations.Any(name => name.Contains("Goal")));
  }

  // Refinement proof calls must be certified before typed admission, including global types that refer to the target.
  [Theory]
  [InlineData("BodylessRefinement")]
  [InlineData("TrustedRefinement")]
  [InlineData("SelfRefinement")]
  public async Task RejectsUncertifiedRefinementProofs(string section) {
    var run = await Campaign.RunAsync(Spec(section));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    Assert.Equal(0, run.Population.Valid);
    Assert.Equal(1, run.Population.PreconditionUnchecked);
    Assert.Contains(run.Result.RuntimeErrors, error => error.Message == "initial_heap_specification_unvalidated");
    Assert.Contains(run.Artifacts("specification-scope-*.json"), path =>
      CampaignRun.Json(path).GetProperty("role").GetString() == "execution" &&
      CampaignRun.Json(path).GetProperty("failure").ValueKind == JsonValueKind.String);
  }

  // A separately verified refinement proof admits the concrete input without treating the target as evidence.
  [Fact]
  public async Task AcceptsCertifiedRefinementProof() {
    var run = await Campaign.RunAsync(Spec("VerifiedRefinement"));
    Assert.Equal(ContractRuntimeStatus.ViolationFound, run.Result.Status);
    Assert.Equal(1, run.Population.Valid);
    Assert.Equal(Postcondition, Assert.Single(run.Result.Violations).Kind);
    Assert.Contains(run.Artifacts("specification-query-*.result.json"), path => {
      var proof = JsonSerializer.Deserialize<ContractSpecificationResult>(File.ReadAllText(path), ContractJson.Options)!;
      return proof.Verified && proof.Role == ContractSpecificationRole.Execution &&
        proof.Implementations.Any(name => name.Contains("Proof"));
    });
  }

  // Inputs used only in certified proof statements remain bound when the complete original conclusion is queried.
  [Fact]
  public async Task CapturesProofStatementOnlyInputs() {
    var run = await Campaign.RunAsync(Spec("ProofOnlyInput"));
    Assert.Equal(ContractRuntimeStatus.ViolationFound, run.Result.Status);
    Assert.Equal(1, run.Population.Valid);
    var violation = Assert.Single(run.Result.Violations);
    Assert.Equal(Postcondition, violation.Kind);
    Assert.Equal(ContractRuntimeDecisionMethod.ClosedSmt, violation.DecisionMethod);
    Assert.Equal("7", violation.Values["x"].Value);
    Assert.DoesNotContain(run.Result.Obligations, obligation => obligation.Kind == Assertion);
    Assert.Contains(run.Artifacts("specification-query-*.result.json"), path => {
      var proof = JsonSerializer.Deserialize<ContractSpecificationResult>(File.ReadAllText(path), ContractJson.Options)!;
      return proof.Verified && proof.Implementations.Any(name => name.Contains("GoodProof"));
    });
  }

  // An opaque dependency exported without its body cannot reveal a false conclusion in the original import view.
  [Fact]
  public async Task PreservesHiddenDefinitionBoundary() {
    var run = await Campaign.RunAsync(Spec("Hidden"));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    Assert.Equal(1, run.Obligation("Definition.Identity(x) == 0", Postcondition).Evaluations.Unchecked);
  }

  // Undefined arithmetic is a native query failure rather than evidence of a false conclusion.
  [Fact]
  public async Task RejectsUndefinedConclusion() {
    var run = await Campaign.RunAsync(Spec("Undefined"));
    Assert.Equal(ContractRuntimeStatus.Inconclusive, run.Result.Status);
    Assert.Empty(run.Result.Violations);
    Assert.Equal("closed_query_error", run.Obligation("x / x == 2", Postcondition).UncheckedReason);
  }

  // A generated nested datatype carrier violating its declared subset type cannot witness any lemma conclusion.
  [Fact]
  public async Task RejectsInvalidNestedInput() {
    var run = await Campaign.RunAsync(Spec("InvalidType"));
    Assert.Empty(run.Result.Violations);
    Assert.Equal(0, run.Population.Valid);
    Assert.Equal(1, run.Population.PreconditionRejected);
  }
}
