using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractSymbolicTests {
  private static async Task<ContractSymbolicResult> Check(string source,
    ContractSymbolicScope scope = ContractSymbolicScope.ReachableImplementations, string symbol = "Entry") {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var snapshot = new ContractSource("symbolic.dfy", source, ContractHarnessBuilder.Hash(source));
    var request = new ContractSymbolicRequest(1, [snapshot], new ContractSymbolicEntry(symbol, scope));
    return await ContractSymbolicChecker.CheckAsync(request, options, CancellationToken.None);
  }

  // A body that establishes its original postcondition is proved without producing an executable artifact.
  [Fact]
  public async Task ValidBodyVerifies() {
    var result = await Check("method Entry(x:int) returns(r:int) ensures r == x + 1 { r := x + 1; }");

    Assert.Equal(ContractSymbolicStatus.Verified, result.Status);
    Assert.Contains("Entry", result.CheckedSymbols!);
    Assert.Contains(result.SourceSnapshots!, source => source.Path == "symbolic.dfy" && source.Sha256.Length == 64);
  }

  // A false original postcondition is reported as a proof-obligation failure rather than a counterexample execution.
  [Fact]
  public async Task BadPostconditionFailsObligation() {
    var result = await Check("method Entry(x:int) returns(r:int) ensures r == x + 1 { r := x; }");

    Assert.Equal(ContractSymbolicStatus.ObligationFailed, result.Status);
    Assert.Contains(result.Obligations!, item => item.Kind == ContractSymbolicObligationKind.Implementation &&
      item.Status == ContractSymbolicStatus.ObligationFailed);
  }

  // Contradictory requires clauses are separated from successful implementation verification.
  [Fact]
  public async Task ContradictoryPreconditionIsInconsistent() {
    var result = await Check("method Entry(x:int) requires x > 0 requires x <= 0 ensures false { assert false; }");

    Assert.Equal(ContractSymbolicStatus.InconsistentPremise, result.Status);
  }

  // Ghost-only class state is handled by Dafny's symbolic heap without a concrete heap factory.
  [Fact]
  public async Task GhostClassStateVerifies() {
    var result = await Check("class Box { ghost var seen:set<int> method Entry() modifies this ensures 1 in seen { seen := seen + {1}; } }",
      symbol: "Box.Entry");

    Assert.Equal(ContractSymbolicStatus.Verified, result.Status);
  }

  // A bodyful external method is summarized by its original contract and its failing fallback body is ignored.
  [Fact]
  public async Task ExternalMethodFallbackIsNotVerified() {
    var result = await Check("method {:extern \"Native\"} Ext(x:int) returns(r:int) ensures r == x + 1 { r := x - 1; assert false; } method Entry(x:int) returns(r:int) ensures r == x + 1 { r := Ext(x); }");

    Assert.Equal(ContractSymbolicStatus.Verified, result.Status);
    Assert.Contains("Ext", result.SummarizedExternSymbols!);
    Assert.Contains(result.TrustDependencies!, item => item.Symbol == "Ext" && item.Kind == "extern_contract");
  }

  // External function expression and by-method fallbacks are ignored while callers retain the original contract.
  [Fact]
  public async Task ExternalFunctionFallbacksAreNotVerified() {
    var result = await Check("function {:extern \"NativeFunction\"} Ext(x:int):(r:int) ensures r == x + 1 { x - 1 } by method { assert false; return x - 2; } method Entry(x:int) returns(r:int) ensures r == x + 1 { r := Ext(x); }");

    Assert.Equal(ContractSymbolicStatus.Verified, result.Status);
    Assert.Contains("Ext", result.SummarizedExternSymbols!);
  }

  // Internal functions used by an external contract remain part of the checked implementation closure.
  [Fact]
  public async Task ExternalContractSpecificationDependenciesAreChecked() {
    const string source = "function Broken():int ensures Broken() == 1 { 0 } " +
      "method {:extern \"Native\"} Ext() returns(r:int) ensures r == Broken() { r := 0; } " +
      "method Entry() returns(r:int) ensures r == 1 { r := Ext(); }";

    var result = await Check(source);

    Assert.Equal(ContractSymbolicStatus.ObligationFailed, result.Status);
    Assert.Contains("Broken", result.CheckedSymbols!);
  }

  // Reachable scope verifies a callee's implementation even when its contract lets the entry itself verify.
  [Fact]
  public async Task ReachableInternalImplementationIsChecked() {
    const string source = "method Helper(x:int) returns(r:int) ensures r == x { r := x + 1; } method Entry(x:int) returns(r:int) ensures r == x { r := Helper(x); }";
    var entryOnly = await Check(source, ContractSymbolicScope.EntryImplementation);
    var reachable = await Check(source);

    Assert.Equal(ContractSymbolicStatus.Verified, entryOnly.Status);
    Assert.Equal(ContractSymbolicStatus.ObligationFailed, reachable.Status);
    Assert.DoesNotContain("Helper", entryOnly.CheckedSymbols!);
    Assert.Contains("Helper", reachable.CheckedSymbols!);
  }

  // Calls from specifications belong to the reachable closure and cannot become unchecked implementation axioms.
  [Fact]
  public async Task SpecificationCallAddsReachableImplementation() {
    var result = await Check("function Broken(x:int):int { x + 1 } method Entry(x:int) ensures Broken(x) == x { }");

    Assert.Equal(ContractSymbolicStatus.ObligationFailed, result.Status);
    Assert.Contains("Broken", result.CheckedSymbols!);
  }

  // Reachable scope checks internal overrides that can satisfy a dynamically dispatched trait call.
  [Fact]
  public async Task ReachableDynamicOverrideImplementationIsChecked() {
    const string source = "trait T { method M() returns(r:int) ensures r == 0 } " +
      "class C extends T { method M() returns(r:int) ensures r == 0 { r := 1; } } " +
      "method Entry(t:T) returns(r:int) ensures r == 0 { r := t.M(); }";

    var result = await Check(source);

    Assert.Equal(ContractSymbolicStatus.ObligationFailed, result.Status);
    Assert.Contains("C.M", result.CheckedSymbols!);
  }

  // Verification-altering Dafny features are retained as explicit trust dependencies.
  [Fact]
  public async Task VerificationAssumptionsAreReported() {
    var result = await Check("method Entry() decreases * { assert {:only} true; assert false; }");

    Assert.Equal(ContractSymbolicStatus.Verified, result.Status);
    Assert.Contains(result.TrustDependencies!, item => item.Symbol == "Entry" && item.Kind == "nontermination");
    Assert.Contains(result.TrustDependencies!, item => item.Symbol == "Entry" && item.Kind == "assert_only");
  }

  // A selected verify-false declaration is invalid instead of yielding a zero-obligation success.
  [Fact]
  public async Task VerifyFalseEntryIsRejected() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    const string source = "method {:verify false} Entry() ensures false { }";
    var request = new ContractSymbolicRequest(1,
      [new ContractSource("symbolic.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractSymbolicEntry("Entry"));

    await Assert.ThrowsAsync<System.ArgumentException>(() =>
      ContractSymbolicChecker.CheckAsync(request, options, CancellationToken.None));
  }

  // A present-but-null source collection is rejected as invalid input before snapshot access.
  [Fact]
  public async Task NullSourceCollectionIsRejected() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var request = new ContractSymbolicRequest(1, null!, new ContractSymbolicEntry("Entry"));

    await Assert.ThrowsAsync<System.ArgumentException>(() =>
      ContractSymbolicChecker.CheckAsync(request, options, CancellationToken.None));
  }

  // Version-1 symbolic DTOs reject unknown JSON fields and preserve enum spellings on round-trip.
  [Fact]
  public void JsonContractIsStrictAndRoundTrips() {
    const string source = "method Entry() {}";
    var request = new ContractSymbolicRequest(1,
      [new ContractSource("symbolic.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractSymbolicEntry("Entry"));
    var json = System.Text.Json.JsonSerializer.Serialize(request, ContractJson.Options);

    var roundTrip = System.Text.Json.JsonSerializer.Deserialize<ContractSymbolicRequest>(json, ContractJson.Options);
    Assert.NotNull(roundTrip);
    Assert.Equal(request.SchemaVersion, roundTrip.SchemaVersion);
    Assert.Equal(request.Entry, roundTrip.Entry);
    Assert.Equal(request.Sources, roundTrip.Sources);
    Assert.Throws<System.Text.Json.JsonException>(() =>
      System.Text.Json.JsonSerializer.Deserialize<ContractSymbolicRequest>(json.TrimEnd('}') + ",\"unknown\":true}", ContractJson.Options));
  }
}
