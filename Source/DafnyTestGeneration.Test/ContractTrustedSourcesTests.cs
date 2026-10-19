#nullable enable

using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractTrustedSourcesTests {
  // Schema-v2 requests round-trip exact trusted source identities and default to strict behavior.
  [Fact]
  public void RequestRoundTripsTrustedSources() {
    const string content = "predicate Positive(x:int) { x > 0 }";
    var source = new ContractSource("core.dfy", content, ContractHarnessBuilder.Hash(content));
    var strict = new ContractRuntimeCampaignRequest(2, [source], new("Goal"), "1");
    var trusted = strict with { TrustedSources = [new(source.Path, source.Sha256)] };

    Assert.Null(strict.TrustedSources);
    var json = JsonSerializer.Serialize(trusted, ContractJson.Options);
    var copy = JsonSerializer.Deserialize<ContractRuntimeCampaignRequest>(json, ContractJson.Options)!;
    Assert.Equal(trusted.TrustedSources, copy.TrustedSources);
  }

  // Duplicate trusted identities fail closed before any native checking begins.
  [Fact]
  public void TrustedSourcesRejectDuplicates() {
    var source = Source("core.dfy", "predicate Positive(x:int) { x > 0 }");
    var identity = new ContractDependency(source.Path, source.Sha256);

    Assert.Throws<System.ArgumentException>(() =>
      ContractSourceSnapshot.ValidateTrustedSources([source], [identity, identity]));
  }

  // A trusted digest must match the exact supplied path snapshot.
  [Fact]
  public void TrustedSourcesRejectMismatchedDigest() {
    var source = Source("core.dfy", "predicate Positive(x:int) { x > 0 }");

    Assert.Throws<System.ArgumentException>(() => ContractSourceSnapshot.ValidateTrustedSources(
      [source], [new ContractDependency(source.Path, "different-digest")]));
  }

  // A matching digest cannot authorize a different source path.
  [Fact]
  public void TrustedSourcesRejectMismatchedPath() {
    var source = Source("core.dfy", "predicate Positive(x:int) { x > 0 }");

    Assert.Throws<System.ArgumentException>(() => ContractSourceSnapshot.ValidateTrustedSources(
      [source], [new ContractDependency("other.dfy", source.Sha256)]));
  }

  // Trusting one parsed program cannot transfer declaration ownership to another AST at the same path.
  [Fact]
  public async Task TrustedSourceDoesNotAuthorizeAnotherAstAtSamePath() {
    const string content = "predicate Root(x:int) { x > 0 }";
    var (program, options, sources) = await Parse(("core.dfy", content));
    var (otherProgram, _, _) = await Parse(("core.dfy", content));
    var identity = new ContractDependency("core.dfy", Source("core.dfy", content).Sha256);
    var checker = new ContractSpecificationChecker(program, sources, options, [identity]);
    var foreignRoot = Functions(otherProgram).Single(function => function.Name == "Root");

    Assert.Contains("not from the original resolved program", checker.Scope([foreignRoot]).Failure!);
  }

  // Trust removes only original declarations from that source while candidate dependencies remain in scope.
  [Fact]
  public async Task TrustedSourceKeepsCandidateAndDependencyClosure() {
    var core = "predicate {:axiom} TrustedAxiom(x:int) predicate Trusted(x:int) { CandidateHelper(x) }";
    var candidate = "predicate CandidateHelper(x:int) { x > 0 } " +
      "predicate Root(x:int) { Trusted(x) && TrustedAxiom(x) }";
    var (program, options, sources) = await Parse(("core.dfy", core), ("candidate.dfy", candidate));
    var functions = Functions(program).ToList();
    var trustedAxiom = functions.Single(function => function.Name == "TrustedAxiom");
    var trusted = functions.Single(function => function.Name == "Trusted");
    var helper = functions.Single(function => function.Name == "CandidateHelper");
    var root = functions.Single(function => function.Name == "Root");
    var strict = new ContractSpecificationChecker(program, sources, options).Scope([root]);
    var scoped = new ContractSpecificationChecker(program, sources, options,
      [new ContractDependency("core.dfy", Source("core.dfy", core).Sha256)]).Scope([root]);

    Assert.Contains("Predicate:" + trusted.FullDafnyName, scoped.Symbols);
    Assert.Contains("Predicate:" + trustedAxiom.FullDafnyName, scoped.Symbols);
    Assert.Contains("Predicate:" + helper.FullDafnyName, scoped.Symbols);
    Assert.Contains("Predicate:" + root.FullDafnyName, scoped.Symbols);
    Assert.Contains(trusted.FullDafnyName + " (well-formedness)", strict.RequiredNativeChecks);
    Assert.DoesNotContain(trusted.FullDafnyName + " (well-formedness)", scoped.RequiredNativeChecks);
    Assert.DoesNotContain(trustedAxiom.FullDafnyName + " (well-formedness)", scoped.RequiredNativeChecks);
    Assert.Contains(helper.FullDafnyName + " (well-formedness)", scoped.RequiredNativeChecks);
    Assert.Contains(root.FullDafnyName + " (well-formedness)", scoped.RequiredNativeChecks);
    Assert.NotNull(strict.Failure);
    Assert.Null(scoped.Failure);
  }

  // Cache scope identity changes with trust policy even when the trusted source is outside the selected closure.
  [Fact]
  public async Task TrustSetSeparatesScopeCacheIdentity() {
    var core = "predicate Unused(x:int) { x > 0 }";
    var candidate = "predicate Root(x:int) { x >= 0 }";
    var (program, options, sources) = await Parse(("core.dfy", core), ("candidate.dfy", candidate));
    var root = Functions(program).Single(function => function.Name == "Root");
    var strict = new ContractSpecificationChecker(program, sources, options).Scope([root]);
    var trusted = new ContractSpecificationChecker(program, sources, options,
      [new ContractDependency("core.dfy", Source("core.dfy", core).Sha256)]).Scope([root]);

    Assert.Equal(strict.Symbols, trusted.Symbols);
    Assert.Equal(strict.RequiredNativeChecks, trusted.RequiredNativeChecks);
    Assert.NotEqual(strict.CacheIdentity, trusted.CacheIdentity);
  }

  // A same-named nested module in an untrusted file retains its native checks.
  [Fact]
  public async Task ModuleNameLookalikeRemainsUntrusted() {
    var core = "module Core { predicate Value(x:int) { x > 0 } }";
    var candidate = "module Client { module Core { predicate Root(x:int) { x > 0 } } }";
    var (program, options, sources) = await Parse(("core.dfy", core), ("candidate.dfy", candidate));
    var root = Functions(program).Single(function => function.Name == "Root");
    var checker = new ContractSpecificationChecker(program, sources, options,
      [new ContractDependency("core.dfy", Source("core.dfy", core).Sha256)]);

    Assert.Contains(root.FullDafnyName + " (well-formedness)", checker.Scope([root]).RequiredNativeChecks);
  }

  // A source assumption remains rejected when its source is not explicitly trusted.
  [Fact]
  public async Task UntrustedAssumptionRemainsRejected() {
    var (program, options, sources) = await Parse(("candidate.dfy", "function Root():int { assume false; 0 }"));
    var root = Functions(program).Single(function => function.Name == "Root");
    var scope = new ContractSpecificationChecker(program, sources, options).Scope([root]);

    Assert.Contains("assume", scope.Failure!);
  }

  // An external contract remains rejected when its source is not explicitly trusted.
  [Fact]
  public async Task UntrustedExternRemainsRejected() {
    var (program, options, sources) = await Parse(("candidate.dfy", "function {:extern} Root():int"));
    var root = Functions(program).Single(function => function.Name == "Root");
    var scope = new ContractSpecificationChecker(program, sources, options).Scope([root]);

    Assert.Contains("extern_contract", scope.Failure!);
  }

  // Explicitly trusting a library predicate does not make a concrete false predicate evaluate as valid.
  [Fact]
  public async Task TrustedPredicateStillRejectsConcreteFalseInput() {
    var core = "predicate Positive(x:int) { x > 0 }";
    var candidate = "method Goal() ensures Positive(-1) {}";
    var coreSource = Source("core.dfy", core);
    var (program, options, sources) = await Parse((coreSource.Path, core), ("candidate.dfy", candidate));
    var checker = new ContractSpecificationChecker(program, sources, options,
      [new ContractDependency(coreSource.Path, coreSource.Sha256)]);
    var goal = ContractRuntimeObligationTransformer.Members(program).OfType<Method>().Single(method => method.Name == "Goal");
    var expression = goal.Ens.Single().E;
    var scope = checker.LogicalScope(expression);
    var reducer = new ContractExpressionReducer(options, program.DefaultModuleDef, program.SystemModuleManager);
    var positive = Functions(program).Single(function => function.Name == "Positive");

    Assert.Null(scope.Failure);
    Assert.DoesNotContain(positive.FullDafnyName + " (well-formedness)", scope.RequiredNativeChecks);
    Assert.Equal(ContractReductionDecision.False, reducer.Reduce(expression).Decision);
  }

  // Initial admission cannot use a checker with a different trust policy before it inspects heap carriers.
  [Fact]
  public async Task InitialPreparationRejectsDifferentCheckerTrustSet() {
    var (program, options, sources, campaign, trusted) = await TrustedCampaign();
    var checker = new ContractSpecificationChecker(program, sources, options, trusted);

    Assert.Throws<System.ArgumentException>(() => ContractRuntimeHeapChecking.PrepareInitial(program,
      campaign with { TrustedSources = null }, new Dictionary<string, ContractValue>(), [], checker));
  }

  // An initial preparation retains its campaign trust context when bound to a checker.
  [Fact]
  public async Task InitialProofPreparationRejectsDifferentCheckerTrustSet() {
    var (program, options, sources, campaign, _) = await TrustedCampaign();
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      new Dictionary<string, ContractValue>(), []);
    var strict = new ContractSpecificationChecker(program, sources, options);

    Assert.Throws<System.ArgumentException>(() => ContractInitialTypeProof.Prepare(initial, strict));
  }

  // A prepared initial certificate cannot be replayed under another checker trust set.
  [Fact]
  public async Task InitialProofMatchRejectsDifferentCheckerTrustSet() {
    var (program, options, sources, campaign, trusted) = await TrustedCampaign();
    var checker = new ContractSpecificationChecker(program, sources, options, trusted);
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      new Dictionary<string, ContractValue>(), [], checker);
    var preparation = ContractInitialTypeProof.Prepare(initial, checker);
    var strict = new ContractSpecificationChecker(program, sources, options);

    Assert.Null(ContractInitialTypeProof.TryPrepare(preparation, strict));
  }

  // An observed heap certificate cannot be checked under a different campaign trust set.
  [Fact]
  public async Task ObservedProofRejectsDifferentCheckerTrustSet() {
    var (program, options, sources, campaign, _) = await TrustedCampaign();
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      new Dictionary<string, ContractValue>(), [], [], new Dictionary<string, ContractValue>());
    var strict = new ContractSpecificationChecker(program, sources, options);

    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, strict));
  }

  private static async Task<(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources,
    ContractRuntimeCampaignRequest Campaign, IReadOnlyList<ContractDependency> Trusted)> TrustedCampaign() {
    const string core = "predicate Positive(x:int) { x > 0 }";
    const string candidate = "method Goal() {}";
    var coreSource = Source("core.dfy", core);
    var (program, options, sources) = await Parse((coreSource.Path, core), ("candidate.dfy", candidate));
    var trusted = new[] { new ContractDependency(coreSource.Path, coreSource.Sha256) };
    var campaign = new ContractRuntimeCampaignRequest(2, sources, new("Goal"), "1", TrustedSources: trusted);
    return (program, options, sources, campaign, trusted);
  }

  private static ContractSource Source(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static IEnumerable<Function> Functions(Program program) => program.RawModules()
    .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
    .SelectMany(declaration => declaration.Members).OfType<Function>();

  private static async Task<(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources)> Parse(
    params (string Path, string Content)[] files) {
    var sources = files.Select(file => Source(file.Path, file.Content)).ToList();
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    return (program, options, sources);
  }
}
