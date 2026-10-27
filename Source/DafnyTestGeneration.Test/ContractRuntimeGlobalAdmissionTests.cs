#nullable enable

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeGlobalAdmissionTests {
  // Closed integer Add/Sub/Mul trees fold exactly and admit a fully trusted initial construction.
  [Fact]
  public async Task TrustedClosedIntegerArithmeticAdmitsInitialConstruction() {
    var (program, campaign, checker) = await Parse("const Size:nat := 64 * 1024 + 3 - 3", trusted: true);
    var size = Constants(program).Single();

    Assert.True(ContractExpressionReducer.TryFoldTotalIntegerArithmetic(size.Rhs!, out var value));
    Assert.Equal(new BigInteger(65536), value);
    Assert.True(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));

    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], checker);
    Assert.Null(scope.Failure);
    Assert.True(scope.ContainsDeclaration(size));
    Assert.Empty(scope.RequiredNativeChecks);
    Assert.True(checker.Accept(scope));

    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      new Dictionary<string, ContractValue>(), [], checker);
    var preparation = ContractInitialTypeProof.Prepare(initial, checker);
    var proof = ContractInitialTypeProof.TryPrepare(preparation, checker);
    Assert.NotNull(proof);
    Assert.False(proof!.RequiresNativeProof);
  }

  // A closed nat expression that computes a negative value remains outside constructive admission.
  [Fact]
  public async Task NegativeComputedNatIsRejected() {
    var (program, _, checker) = await Parse("const Value:nat := 1 - 2");
    var value = Constants(program).Single();

    Assert.True(ContractExpressionReducer.TryFoldTotalIntegerArithmetic(value.Rhs!, out var folded));
    Assert.Equal(new BigInteger(-1), folded);
    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
  }

  // Static constant references retain their existing recursion while their arithmetic RHS is folded.
  [Fact]
  public async Task DirectConstantReferenceRetainsClosedAdmission() {
    var (program, _, checker) = await Parse("const Base:nat := 32 * 2 const Copy:nat := Base");
    var copy = Constants(program).Single(field => field.Name == "Copy");

    Assert.False(ContractExpressionReducer.TryFoldTotalIntegerArithmetic(copy.Rhs!, out _));
    Assert.True(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
  }

  // Host folding does not remove the original native well-formedness requirement for an untrusted constant.
  [Fact]
  public async Task UntrustedArithmeticConstantStillRequiresNativeCheck() {
    var (program, campaign, checker) = await Parse("const Value:int := 6 * 7");

    Assert.True(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], checker);
    Assert.Null(scope.Failure);
    Assert.Contains("Globals.Value (well-formedness)", scope.RequiredNativeChecks);
    Assert.False(checker.Accept(scope));
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign,
      new Dictionary<string, ContractValue>(), [], checker));
  }

  // Integer-valued expressions outside the literal Add/Sub/Mul grammar remain rejected.
  [Theory]
  [InlineData("const Value:int := 6 / 3")]
  [InlineData("const Value:int := 0 * (1 / 0)")]
  [InlineData("function One():int { 1 } const Value:int := One()")]
  [InlineData("const Value:int := (1 as real) as int")]
  [InlineData("const Value:int := |\"a\" + \"b\"|")]
  [InlineData("const Value:int := if true then 1 else 2")]
  [InlineData("const Value:bv8 := (1 as bv8) + (2 as bv8)")]
  public async Task UnsupportedClosedSyntaxRemainsRejected(string declaration) {
    var (program, _, checker) = await Parse(declaration);
    var value = Constants(program).Single();

    Assert.False(ContractExpressionReducer.TryFoldTotalIntegerArithmetic(value.Rhs!, out _));
    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
  }

  // Arithmetic cannot bypass the existing membership boundary for a constrained integral subset.
  [Fact]
  public async Task ConstrainedIntegralDomainRemainsRejected() {
    var (program, _, checker) = await Parse(
      "type Positive = value:int | value > 0 witness 1 const Value:Positive := 1 + 1");

    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
  }

  // Arithmetic cannot bypass the existing membership boundary for a constrained integral newtype.
  [Fact]
  public async Task ConstrainedIntegralNewtypeRemainsRejected() {
    var (program, _, checker) = await Parse(
      "newtype Positive = value:int | value > 0 witness 1 const Value:Positive := 1 + 1");

    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
  }

  // A trusted bodyless non-null global constructs through one own immutable same-type field alias.
  [Fact]
  public async Task TrustedSingleHopImmutableAliasAdmitsIndependentGlobal() {
    var (program, campaign, checker) = await Parse(SingleHopAliasDeclarations, trusted: true);
    var handle = Members(program).Single(field => field.Name == "Handle");
    var alias = Members(program).Single(field => field.Name == "alias");
    var target = Members(program).Single(field => field.Name == "region");
    var source = ContractSourceSnapshot.Find(campaign.Sources, handle.Origin.Uri);
    var selection = Assert.IsType<MemberSelectExpr>(alias.Rhs!.Resolved);
    var handleType = Assert.IsType<UserDefinedType>(handle.Type.NormalizeExpandKeepConstraints());
    var nonNull = Assert.IsType<NonNullTypeDecl>(handleType.ResolvedClass);

    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], checker);
    Assert.Null(scope.Failure);
    Assert.Same(handle, ContractRuntimeHeapChecking.StaticConstants(program).Single(field => field.Name == "Handle"));
    Assert.Equal(campaign.Sources.Single(), source);
    Assert.Same(alias.EnclosingClass, nonNull.Class);
    Assert.Same(target, selection.Member);
    Assert.Same(alias.EnclosingClass, target.EnclosingClass);
    Assert.True(scope.ContainsDeclaration(alias));
    Assert.False(scope.ContainsDeclaration(target));
    Assert.Empty(scope.RequiredNativeChecks);
    Assert.True(checker.Accept(scope));
    Assert.Equal(true, ContractRuntimeHeapChecking.CheckInitialTypes(program, []));
    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
    Assert.True(ContractRuntimeHeapChecking.IndependentCertifiedGlobalsInhabited(program, checker));

    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      new Dictionary<string, ContractValue>(), [], checker);
    var proof = ContractInitialTypeProof.TryPrepare(ContractInitialTypeProof.Prepare(initial, checker), checker);
    Assert.NotNull(proof);
    Assert.False(proof!.RequiresNativeProof);
    Assert.NotNull(proof.IndependentGlobals);
  }

  // An untrusted immutable alias remains in the original native well-formedness scope.
  [Fact]
  public async Task UntrustedSingleHopImmutableAliasStillRequiresNativeCheck() {
    var (program, campaign, checker) = await Parse(SingleHopAliasDeclarations);
    var alias = Members(program).Single(field => field.Name == "alias");

    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], checker);
    Assert.True(scope.ContainsDeclaration(alias));
    Assert.Contains("Globals.IO.alias (well-formedness)", scope.RequiredNativeChecks);
    Assert.False(checker.Accept(scope));
  }

  // Initialized fields outside the exact own bodyless same-type alias shape remain unsupported.
  [Theory]
  [MemberData(nameof(UnsupportedAliasDeclarations))]
  public async Task UnsupportedImmutableAliasShapesRemainRejected(string declaration) {
    var (program, campaign, checker) = await Parse(declaration, trusted: true);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], checker);

    Assert.Null(scope.Failure);
    Assert.True(checker.Accept(scope));
    Assert.Null(ContractRuntimeHeapChecking.CheckInitialTypes(program, []));
    Assert.False(ContractRuntimeHeapChecking.IndependentCertifiedGlobalsInhabited(program, checker));
    Assert.False(ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, [], checker));
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      new Dictionary<string, ContractValue>(), [], checker);
    Assert.Null(ContractInitialTypeProof.TryPrepare(ContractInitialTypeProof.Prepare(initial, checker), checker));
  }

  public static IEnumerable<object[]> UnsupportedAliasDeclarations() {
    yield return ["class IO { ghost const alias:int := 0 } const {:extern} Handle:IO"];
    yield return ["class Region {} class IO { " +
      "ghost const alias:Region := intermediate ghost const intermediate:Region := region " +
      "ghost const region:Region constructor Init(region:Region) { this.region := region; } } " +
      "const {:extern} Handle:IO"];
    yield return ["class IO { ghost const alias:IO := target ghost const target:IO " +
      "constructor Init(target:IO) { this.target := target; } } const {:extern} Handle:IO"];
    yield return ["class Region {} class IO { ghost const alias:object := region " +
      "ghost const region:Region constructor Init(region:Region) { this.region := region; } } " +
      "const {:extern} Handle:IO"];
    yield return ["class Region {} class IO { ghost const alias:object := region as object " +
      "ghost const region:Region constructor Init(region:Region) { this.region := region; } } " +
      "const {:extern} Handle:IO"];
    yield return ["class Region {} class IO { ghost const alias:Region := region ghost var region:Region " +
      "constructor Init(region:Region) { this.region := region; } } const {:extern} Handle:IO"];
    yield return ["class Region {} class Holder { ghost static const {:extern} region:Region } " +
      "class IO { ghost const alias:Region := Holder.region } const {:extern} Handle:IO"];
    yield return ["class Region {} class Holder { ghost const region:Region " +
      "constructor Init(region:Region) { this.region := region; } } " +
      "class IO { ghost const holder:Holder ghost const alias:Region := holder.region " +
      "constructor Init(holder:Holder) { this.holder := holder; } } const {:extern} Handle:IO"];
    yield return ["class Region {} class IO { function Pick(value:Region):Region { value } " +
      "ghost const alias:Region := Pick(region) ghost const region:Region " +
      "constructor Init(region:Region) { this.region := region; } } const {:extern} Handle:IO"];
    yield return ["type Positive = value:int | value > 0 witness 1 class IO { " +
      "ghost const alias:int := value ghost const value:Positive " +
      "constructor Init(value:Positive) { this.value := value; } } const {:extern} Handle:IO"];
  }

  private const string SingleHopAliasDeclarations =
    "class Region {} class IO { ghost const alias:Region := region ghost const region:Region " +
    "constructor Init(region:Region) { this.region := region; } } const {:extern} Handle:IO";

  private static IEnumerable<ConstantField> Constants(Program program) =>
    ContractRuntimeHeapChecking.StaticConstants(program);

  private static IEnumerable<ConstantField> Members(Program program) =>
    ContractRuntimeObligationTransformer.Members(program).OfType<ConstantField>();

  private static async Task<(Program Program, ContractRuntimeCampaignRequest Campaign,
    ContractSpecificationChecker Checker)> Parse(string declaration, bool trusted = false) {
    const string path = "globals.dfy";
    var content = "module Globals { " + declaration + " method Goal() {} }";
    var source = new ContractSource(path, content, ContractHarnessBuilder.Hash(content));
    IReadOnlyList<ContractSource> sources = [source];
    IReadOnlyList<ContractDependency>? trustedSources = trusted
      ? [new ContractDependency(source.Path, source.Sha256)]
      : null;
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var campaign = new ContractRuntimeCampaignRequest(2, sources, new("Globals.Goal"), "1",
      TrustedSources: trustedSources);
    var checker = new ContractSpecificationChecker(program, sources, options, trustedSources);
    return (program, campaign, checker);
  }
}
