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

namespace DafnyTestGeneration.Test;

public class ContractRuntimeHeapQueryTests {
  // Private, opaque and transitively hidden initializer definitions cannot be replaced by an unconstrained model value.
  [Theory]
  [InlineData("private")]
  [InlineData("opaque")]
  [InlineData("function-chain")]
  [InlineData("constant-chain")]
  public async Task InitialQueriesRejectHiddenInitializerChains(string kind) {
    var chain = kind.EndsWith("-chain", StringComparison.Ordinal);
    var constant = kind == "constant-chain";
    var export = kind == "private" ? "" : chain ? "reveals Seed provides Hidden" : "provides Seed";
    var declaration = chain
      ? constant ? "const Hidden:int:=7 const Seed:int:=Hidden" : "function Hidden():int {7} function Seed():int {Hidden()}"
      : (kind == "opaque" ? "opaque " : "") + "function Seed():int {7}";
    var (program, campaign) = await Parse([
      SourceFile("hidden-initializer.dfy", "module Data { export View reveals Cell " + export + " " + declaration +
        " class Cell { const tag:int := Seed" + (constant ? "" : "()") + " } }"),
      SourceFile("hidden-entry.dfy", "module Store { import D=Data`View method Entry(cell:D.Cell) {} }")
    ]);
    var heap = new[] { new ContractHeapObject("cell", "Data.Cell", Values(("tag", Integer(8)))) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.Contains("Original initializer definition unavailable", Assert.Throws<NotSupportedException>(() =>
      ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency)).Message);
  }

  // A reusable preparation belongs to one checker and exact request/source/heap, and never authorizes a mutated state.
  [Theory]
  [InlineData("valid")]
  [InlineData("checker")]
  [InlineData("source")]
  [InlineData("input")]
  [InlineData("heap")]
  [InlineData("prepared")]
  public async Task InitialPreparationHandleBindsExactState(string scenario) {
    var sources = new[] { SourceFile("bound-state.dfy", "module Store { class Cell { var value:int } method Entry(cell:Cell,n:int) {} }") };
    var (program, campaign) = await Parse(sources);
    var heap = new List<ContractHeapObject> { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var inputs = Values(("cell", Reference("cell")), ("n", Integer(3)));
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, inputs, heap, specifications);
    var preparation = ContractInitialTypeProof.Prepare(initial, specifications);
    Assert.True(specifications.Accept(preparation.Scope));
    if (scenario == "prepared") {
      Assert.Throws<ArgumentException>(() => ContractInitialTypeProof.Prepare(
        initial with { Prepared = initial.Prepared with { Sources = [] } }, specifications));
      return;
    }
    if (scenario == "checker") { specifications = await CertifyInitial(program, campaign, heap); }
    if (scenario == "source") { sources[0] = SourceFile("bound-state.dfy", sources[0].Content + "\n// changed source\n"); }
    if (scenario == "input") { ((Dictionary<string, ContractValue>)initial.Request.Inputs)["n"] = Integer(4); }
    if (scenario == "heap") { heap[0] = Cell("cell", 5); }
    var proof = ContractInitialTypeProof.TryPrepare(preparation, specifications);
    if (scenario != "valid") { Assert.Null(proof); return; }
    Assert.NotNull(proof);
    Assert.Same(initial, proof.Initial);
    Assert.False(proof.RequiresNativeProof);
    var raw = ContractInitialTypeProof.TryPrepare(program, campaign, inputs, heap, specifications);
    Assert.NotNull(raw);
    Assert.Equal(raw.HostMembershipChecks, proof.HostMembershipChecks);
    Assert.Equal(raw.RuntimeChecks, proof.RuntimeChecks);
    Assert.Same(raw.IndependentGlobals, proof.IndependentGlobals);
  }

  // Imported initialized readonly fields retain the complete original function or constant definition chain.
  [Theory]
  [InlineData(false, false, 7)]
  [InlineData(false, false, 8)]
  [InlineData(false, true, 7)]
  [InlineData(false, true, 8)]
  [InlineData(true, false, 7)]
  [InlineData(true, false, 8)]
  [InlineData(true, true, 7)]
  [InlineData(true, true, 8)]
  public async Task InitialQueriesRequireTransitiveInitializedDefinitions(bool constant, bool revealed, int tag) {
    var definition = constant ? "const Seed:int := 7" : "function Seed():int {7}";
    var initializer = constant ? "Seed" : "Seed()";
    var (program, campaign) = await Parse([
      SourceFile("readonly-dependency.dfy", "module Data { export View reveals Cell " +
        (revealed ? "reveals" : "provides") + " Seed " + definition +
        " class Cell { const tag:int := " + initializer + " } }"),
      SourceFile("readonly-entry.dfy", "module Store { import D=Data`View method Entry(cell:D.Cell) {} }")
    ]);
    var heap = new[] { new ContractHeapObject("cell", "Data.Cell", Values(("tag", Integer(tag)))) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    if (!revealed) {
      var error = Assert.Throws<NotSupportedException>(() =>
        ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency));
      Assert.Contains("Original initializer definition unavailable", error.Message);
      return;
    }
    var query = ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.PremiseConsistency, program.Options,
      CancellationToken.None, queryName: ContractQueryBuilder.Name(check.Prepared),
      sourceSnapshots: check.Prepared.DiagnosticSourceSnapshots, sourcePath: check.Prepared.Source.Path);
    var directory = Path.Combine("/workspace/tmp", "contract-readonly-dependency-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "sources.json"), JsonSerializer.Serialize(check.Prepared.DiagnosticSourceSnapshots, ContractJson.Options));
    await File.WriteAllTextAsync(Path.Combine(directory, "query.dfy"), query);
    await File.WriteAllTextAsync(Path.Combine(directory, "result.json"), JsonSerializer.Serialize(new { constant, revealed, tag, result }, ContractJson.Options));
    var expected = tag == 8 ? ContractQueryOutcome.Unsat : ContractQueryOutcome.Sat;
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Independent fresh global heaps need certified leaf witnesses, without borrowing any captured object.
  [Theory]
  [InlineData("type Leaf = n:int | n > 0 witness 1", "Leaf", true)]
  [InlineData("type Leaf = n:int | false witness 0", "Leaf", false)]
  [InlineData("type Leaf = n:int | n > 0 witness *", "Leaf", false)]
  [InlineData("type Leaf = n:int | n > 0 witness 1", "int -> Leaf", true)]
  [InlineData("type Leaf = n:int | false witness *", "int -> Leaf", false)]
  [InlineData("", "Cell", false)]
  public async Task IndependentGlobalsRequireNonCircularWitnesses(string definition, string fieldType, bool expected) {
    var (program, campaign) = await Parse("module Store { " + definition +
      " class Cell { ghost var value:" + fieldType + " ghost constructor Init(value:" + fieldType +
      ") { this.value:=value; } } ghost const {:extern} unused:Cell " +
      "method Entry(n:int) returns(result:int, ghost evidence:int) { result:=n; evidence:=n; } }");
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], specifications);
    foreach (var module in specifications.PendingModules(scope)) {
      await specifications.CheckModuleAsync(scope, module, CancellationToken.None);
    }
    specifications.Accept(scope);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("n", Integer(2))), [], specifications);
    if (!expected) { Assert.Null(proof); return; }
    Assert.NotNull(proof);
    Assert.NotNull(proof.IndependentGlobals);
    Assert.False(proof.RequiresNativeProof);
    Assert.Equal(1, proof.HostMembershipChecks);
    var next = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("n", Integer(3))), [], specifications);
    Assert.Same(proof.IndependentGlobals, next!.IndependentGlobals);
  }

  // A cached global witness cannot certify an imported changed type, another resolved Program, or a bad exact input.
  [Fact]
  public async Task IndependentGlobalsKeepSourceAndInputIdentity() {
    var sources = new[] {
      SourceFile("global-type.dfy", "module Data { type Positive = n:int | n > 0 witness 1 }"),
      SourceFile("global-use.dfy", "module Store { import D=Data class Cell { ghost var value:D.Positive } " +
        "ghost const {:extern} unused:Cell method Entry(n:D.Positive) {} }")
    };
    var (program, campaign) = await Parse(sources);
    var specifications = await CertifyInitial(program, campaign, []);
    var first = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("n", Integer(2))), [], specifications);
    Assert.NotNull(first!.IndependentGlobals);
    Assert.Equal(ContractQueryOutcome.Unsat, (await CheckTypeProof(first)).Outcome);
    var invalid = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("n", Integer(-1))), [], specifications);
    Assert.Same(first.IndependentGlobals, invalid!.IndependentGlobals);
    Assert.Equal(ContractQueryOutcome.Error, (await CheckTypeProof(invalid)).Outcome);
    var changed = sources.ToArray();
    changed[0] = SourceFile("global-type.dfy", "module Data { type Positive = n:int | n > 9 witness 10 }");
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign with { Sources = changed },
      Values(("n", Integer(2))), [], specifications));
    var (otherProgram, otherCampaign) = await Parse(sources);
    Assert.Null(ContractInitialTypeProof.TryPrepare(otherProgram, otherCampaign, Values(("n", Integer(2))), [], specifications));
  }

  // Native queries preserve imported readonly equations and exact captured values without allocating replacement objects.
  [Theory]
  [InlineData(7, ContractQueryOutcome.Sat, false, false)]
  [InlineData(8, ContractQueryOutcome.Unsat, false, false)]
  [InlineData(7, ContractQueryOutcome.Sat, true, false)]
  [InlineData(8, ContractQueryOutcome.Unsat, true, false)]
  [InlineData(7, ContractQueryOutcome.Sat, true, true)]
  [InlineData(8, ContractQueryOutcome.Unsat, true, true)]
  public async Task InitialQueriesCheckImportedInitializedConstant(int tag, ContractQueryOutcome expected,
    bool imported, bool provided) {
    var sources = new List<ContractSource> {
      SourceFile("readonly-store.dfy", "module Data { " +
        (imported ? "export View reveals Cell " + (provided ? "provides Cell.tag " : "") : "") +
        "class Cell { const tag:int := 7 } " + (imported ? "" : "method Entry(cell:Cell) {} ") + "}")
    };
    if (imported) {
      sources.Add(SourceFile("readonly-client.dfy", "module Store { import D = Data`View method Entry(cell:D.Cell) {} }"));
    }
    var (program, campaign) = await Parse(sources, imported ? "Store.Entry" : "Data.Entry");
    var heap = new[] { new ContractHeapObject("cell", "Data.Cell", Values(("tag", Integer(tag)))) };
    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      Values(("cell", Reference("cell"))), heap);
    var query = ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.PremiseConsistency, program.Options,
      CancellationToken.None, queryName: ContractQueryBuilder.Name(check.Prepared),
      sourceSnapshots: check.Prepared.DiagnosticSourceSnapshots, sourcePath: check.Prepared.Source.Path);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Zero-query global admission constructs only finite logical heaps with independently inhabited complete fields.
  [Theory]
  [InlineData("class Region { ghost var value:int } class Cell { ghost const region:Region constructor Init(region:Region) requires false { this.region:=region; } }", "Cell", true)]
  [InlineData("class Cell { ghost var next:Cell? }", "Cell", true)]
  [InlineData("datatype Leaf = Leaf(value:int) class Cell { ghost var value:Leaf }", "Cell", true)]
  [InlineData("type Empty = value:int | false witness 0 class Cell { ghost var value:Empty }", "Cell", false)]
  [InlineData("type Positive = value:int | value > 0 witness 1 class Cell { ghost var value:Positive }", "Cell", false)]
  [InlineData("class Cell { ghost var next:Cell constructor Init(next:Cell) { this.next:=next; } }", "Cell", false)]
  [InlineData("class Cell<T> { ghost var value:T constructor Init(value:T) { this.value:=value; } }", "Cell<int>", false)]
  [InlineData("trait Parent { ghost var value:int } class Cell extends Parent {}", "Cell", false)]
  [InlineData("class Cell { const value:int := 1 }", "Cell", false)]
  [InlineData("datatype Value = Value { const extra:int := 1 } class Cell { ghost var value:Value }", "Cell", false)]
  [InlineData("", "array<int>", false)]
  public async Task HostGlobalAdmissionRequiresIndependentFiniteHeap(string declaration, string type, bool independent) {
    var (program, _) = await Parse("module Store { " + declaration +
      " ghost const {:extern} unused:" + type + " method Entry() {} }");
    var result = ContractRuntimeHeapChecking.CheckInitialTypes(program, []);
    if (independent) { Assert.True(result); } else { Assert.Null(result); }
  }

  // Datatype readonly constants impose global obligations even before an instance is captured.
  [Fact]
  public async Task DatatypeMemberConstantsBlockConstructiveAdmission() {
    var (program, campaign) = await Parse("module Store { datatype Value = Value { const extra:int := 1 } " +
      "class Cell { var value:Value } method Entry(cell:Cell) {} }");
    var heap = new[] { new ContractHeapObject("cell", "Store.Cell", Values(("value",
      new ContractValue(ContractValueKind.Datatype, Constructor: "Store.Value.Value", Fields: Values())))) };
    Assert.Null(ContractRuntimeHeapChecking.CheckInitialTypes(program, heap));
    Assert.Null(ContractRuntimeHeapChecking.CheckInitialTypes(program, []));
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, heap, specifications);
    Assert.NotNull(scope.Failure);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))), heap, heap, Values());
    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, specifications));
  }

  // Omitted initialized primitive constants need their defining equations, while an already false field stays rejected.
  [Theory]
  [InlineData(1)]
  [InlineData(-1)]
  public async Task InitializedConstantsCannotUseHostMembershipAlone(int value) {
    var (program, _) = await Parse("module Store { class Cell { var value:nat ghost const bad:nat := -1 } " +
      "method Entry(cell:Cell) {} }");
    var result = ContractRuntimeHeapChecking.CheckInitialTypes(program, [Cell("cell", value)]);
    if (value < 0) { Assert.False(result); } else { Assert.Null(result); }
  }

  // Abstract globals cannot make a false type witness prove itself, directly or through a captured reference field.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task ConstructiveAdmissionRejectsGlobalWitnessVacuity(bool reference) {
    var (program, campaign) = await Parse("module Store { type Empty = value:int | false witness 0 " +
      (reference ? "class Cell { var value:int ghost var bad:Empty } ghost const {:extern} unused:Cell " :
        "class Cell { var value:int } ghost const unused:Empty ") + "method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, heap, specifications);
    var results = new List<ContractSpecificationResult>();
    foreach (var module in specifications.PendingModules(scope)) {
      results.Add(await specifications.CheckModuleAsync(scope, module, CancellationToken.None));
    }
    Assert.Contains(results, result => !result.Verified);
    Assert.False(specifications.Accept(scope));
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))), heap, heap, Values());
    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, specifications));
  }

  // Unsupported global refinement or RHS equations fall back even when their own native WD is vacuous or successful.
  [Theory]
  [InlineData("type Empty = value:int | false witness * ghost const unused:Empty := 0")]
  [InlineData("type Positive = value:int | value > 0 witness 1 ghost const unused:Positive := 2")]
  [InlineData("function One():int { 1 } const unused:int := One()")]
  public async Task ConstructiveAdmissionDefersUnsupportedGlobalDefinitions(string declaration) {
    var (program, campaign) = await Parse("module Store { " + declaration +
      " class Cell { var value:int } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, heap, specifications);
    foreach (var module in specifications.PendingModules(scope)) {
      await specifications.CheckModuleAsync(scope, module, CancellationToken.None);
    }
    specifications.Accept(scope);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))), heap, heap, Values());
    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, specifications));
  }

  // Closed global constructor constants retain full native WD and exact component membership.
  [Fact]
  public async Task ConstructiveAdmissionChecksClosedGlobalValues() {
    var (program, campaign) = await Parse("module Store { datatype Value = Value(count:nat, bits:bv8) " +
      "const count:nat := 2 const unused:Value := Value(count, 3 as bv8) " +
      "class Cell { var value:int } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var construction = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.NotNull(construction);
    var result = await CheckTypeProof(construction);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Native certificates independently establish valid omitted refinements beneath an abstract reference global.
  [Fact]
  public async Task ConstructiveAdmissionChecksGlobalReferenceRefinements() {
    var (program, campaign) = await Parse("module Store { type Positive = value:int | value > 0 witness 1 " +
      "class Cell { var value:int ghost var hidden:Positive } ghost const {:extern} unused:Cell " +
      "method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var construction = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.NotNull(construction);
    var result = await CheckTypeProof(construction);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // A cyclic global equation is rejected by original resolution before any construction certificate is available.
  [Fact]
  public async Task CyclicGlobalConstantsDoNotReachConstruction() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    await ContractSourceSnapshot.ParseAsync(reporter,
      [SourceFile("cycle.dfy", "const first:int := second const second:int := first method Entry() {}")], CancellationToken.None);
    Assert.True(reporter.ErrorCount > 0);
  }

  // An abstract extern reference needs an exact original captured class, not a same-shaped unrelated object.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task ConstructiveAdmissionRequiresExactGlobalReference(bool sameType) {
    var (program, campaign) = await Parse("module Other { type Positive = n:int | n > 0 witness * " +
      "class Cell { var value:Positive constructor(value:Positive) { this.value:=value; } } " +
      "ghost const {:extern} unused:Cell } module Store { import O = Other " +
      "class Cell { var value:int } ghost const {:extern} unused:Cell method Entry(cell:Cell) {} }");
    var heap = new List<ContractHeapObject> { Cell("cell", 2) };
    if (sameType) { heap.Add(new("other", "Other.Cell", Values(("value", Integer(3))))); }
    var specifications = await CertifyInitial(program, campaign, heap);
    var construction = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    if (!sameType) { Assert.Null(construction); return; }
    Assert.NotNull(construction);
    Assert.Null(construction.IndependentGlobals);
    var result = await CheckTypeProof(construction);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Constructive observation checks every final field and output refinement independently of the original Q.
  [Theory]
  [InlineData(2, 2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, 2, ContractQueryOutcome.Error)]
  [InlineData(2, -1, ContractQueryOutcome.Error)]
  public async Task NativeObservedConstructionChecksFinalAndOutputCarriers(int field, int output, ContractQueryOutcome expected) {
    const string source = "module Store { type Positive = value:int | value > 0 witness 1 " +
      "class Cell { var value:Positive } method Entry(cell:Cell) returns(result:Positive) modifies cell " +
      "ensures result == cell.value { result := 1; } }";
    var (program, campaign) = await Parse(source);
    var initial = new[] { Cell("cell", 1) };
    var specifications = await CertifyInitial(program, campaign, initial);
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))),
      initial, [Cell("cell", field)], Values(("result", Integer(output))));
    var scope = ContractInitialTypeProof.RequiredObservedScope(program, check, specifications);
    foreach (var module in specifications.PendingModules(scope)) {
      var proof = await specifications.CheckModuleAsync(scope, module, CancellationToken.None);
      Assert.True(proof.Verified, proof.Diagnostics);
    }
    Assert.True(specifications.Accept(scope));
    var construction = ContractInitialTypeProof.TryPrepareObserved(program, check, specifications);
    Assert.NotNull(construction);
    Assert.True(construction.Observed);
    var result = await CheckTypeProof(construction);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Observed composition cannot manufacture an omitted empty value even when captured carriers are valid.
  [Fact]
  public async Task NativeObservedConstructionDefersEmptyOmission() {
    var (program, campaign) = await Parse("module Store { type Empty = value:int | false witness * " +
      "class Cell { var value:int ghost var unused:Empty constructor Init() requires false { value:=0; ghost var hidden:Empty :| true; unused:=hidden; } } " +
      "method Entry(cell:Cell) modifies cell {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))), heap, heap, Values());
    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, specifications));
  }

  // A final value outside the original modifies frame cannot receive a constructive observation certificate.
  [Fact]
  public async Task NativeObservedConstructionRejectsFrameViolation() {
    var (program, campaign) = await Parse(RuntimeEvidenceSource);
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))), heap, [Cell("cell", 3)], Values());
    Assert.NotNull(check.FrameViolation);
    Assert.Null(ContractInitialTypeProof.TryPrepareObserved(program, check, specifications));
  }

  // Collection cancellation and expiration never expose a partially collected positive witness.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task RuntimeTypeEvidenceCancelsWithoutPublishingPartialCollection(bool expired) {
    var (program, campaign) = await Parse(RuntimeEvidenceSource);
    using var cancellation = new CancellationTokenSource();
    Assert.Throws<OperationCanceledException>(() => Evidence(program, campaign, "valid", cancellationToken: cancellation.Token,
      deadlineTimestamp: expired ? 0 : null,
      phaseObserver: (_, state) => { if (state == "completed") { cancellation.Cancel(); } }));
  }

  // Exact repeated runtime type checks can cover every carrier, but only after original native WD certification.
  [Fact]
  public async Task RuntimeTypeEvidenceCompletesConstructionWithoutEmptyNativeQuery() {
    var (program, campaign) = await Parse(RuntimeEvidenceSource);
    var heap = new[] { Cell("cell", 2) };
    var evidence = Evidence(program, campaign, "valid");
    var uncertified = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, uncertified, evidence));
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications, evidence);
    Assert.NotNull(proof);
    Assert.False(proof.RequiresNativeProof);
    Assert.Single(proof.RuntimeChecks);
  }

  // Missing, mismatched, uncompiled, draft-owned or conflicting observations never replace the native carrier proof.
  [Theory]
  [InlineData("missing")]
  [InlineData("false")]
  [InlineData("conflicting")]
  [InlineData("ordinary")]
  [InlineData("uncompiled")]
  [InlineData("checkpoint")]
  [InlineData("wrong-value")]
  [InlineData("wrong-type")]
  [InlineData("wrong-source")]
  [InlineData("draft-owner")]
  [InlineData("draft-dependency")]
  [InlineData("duplicate-value-key")]
  [InlineData("malformed-value")]
  public async Task RuntimeTypeEvidenceRejectsUnavailableProvenance(string scenario) {
    var (program, campaign) = await Parse(RuntimeEvidenceSource);
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap,
      specifications, Evidence(program, campaign, scenario));
    Assert.NotNull(proof);
    Assert.True(proof.RequiresNativeProof);
    Assert.Empty(proof.RuntimeChecks);
  }

  // An unchanged owner file cannot transfer evidence across a changed imported refinement or resolved program.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task RuntimeTypeEvidenceRejectsChangedImportedConstraint(bool recollect) {
    const string owner = "module Store { import D = Data class Cell { var value:D.Positive } " +
      "method Check(value:D.Positive) {} method Entry(cell:Cell) {} }";
    var oldSources = new[] {
      new ContractSource("runtime-heap.dfy", owner, ContractHarnessBuilder.Hash(owner)),
      SourceFile("refinement.dfy", "module Data { type Positive = value:int | value > 0 witness 1 }")
    };
    var newSources = new[] { oldSources[0],
      SourceFile("refinement.dfy", "module Data { type Positive = value:int | value > 3 witness 4 }") };
    var (oldProgram, oldCampaign) = await Parse(oldSources);
    var (program, campaign) = await Parse(newSources);
    var evidence = Evidence(oldProgram, oldCampaign, "valid", recollect ? program : null, recollect ? campaign : null);
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications, evidence);
    Assert.NotNull(proof);
    Assert.True(proof.RequiresNativeProof);
    Assert.Empty(proof.RuntimeChecks);
    var result = await CheckTypeProof(proof);
    Assert.True(result.Outcome == ContractQueryOutcome.Error, result.Diagnostics);
  }

  private static ContractSource SourceFile(string path, string content) => new(path, content, ContractHarnessBuilder.Hash(content));

  private const string RuntimeEvidenceSource = "module Store { predicate Good(value:int) { value > 0 } " +
    "type Positive = value:int | Good(value) witness 1 type Other = value:int | Good(value) witness 1 " +
    "class Cell { var value:Positive } method Check(value:Positive) {} method OtherCheck(value:Other) {} method Entry(cell:Cell) {} }";

  private static ContractRuntimeTypeEvidence Evidence(Program program, ContractRuntimeCampaignRequest campaign, string scenario,
    Program? collectionProgram = null, ContractRuntimeCampaignRequest? collectionCampaign = null,
    CancellationToken cancellationToken = default, long? deadlineTimestamp = null, Action<string, string>? phaseObserver = null) {
    var owner = ContractCallableSelector.SelectMethod(program, new ContractEntry(scenario == "wrong-type" ? "Store.OtherCheck" : "Store.Check"));
    var formal = owner.Ins.Single();
    const string id = "runtime-type-check";
    var obligation = new ContractRuntimeObligation(id, ContractRuntimeObligationKind.CalleePostcondition,
      campaign.Sources[0].Path, 1, 1, "value membership", owner.FullDafnyName, ContractRuntimeDecisionMethod.Runtime, null, new());
    var clause = new ContractRuntimeClause(obligation, Expression.CreateBoolLiteral(owner.Origin, true), [formal], owner,
      TypeConstraint: scenario != "ordinary", OriginalSourceHash: scenario == "wrong-source" ? "wrong" : campaign.Sources[0].Sha256,
      OriginalSourceSetHash: ContractRuntimeTypeEvidence.SourceSetHash(campaign.Sources));
    var records = new List<JsonElement>();
    if (scenario != "missing") {
      records.Add(JsonSerializer.SerializeToElement(new {
        kind = scenario == "checkpoint" ? "checkpoint" : "check",
        id,
        passed = scenario != "false",
        values = Values(("value", Integer(scenario == "wrong-value" ? 3 : 2)))
      }, ContractJson.Options));
      if (scenario == "valid") { records.Add(records[0]); }
      if (scenario == "conflicting") {
        records.Add(JsonSerializer.SerializeToElement(new { kind = "check", id, passed = false, values = Values(("value", Integer(2))) }, ContractJson.Options));
      }
      if (scenario is "duplicate-value-key" or "malformed-value") {
        records.Clear();
        records.Add(JsonDocument.Parse(scenario == "duplicate-value-key"
          ? "{\"kind\":\"check\",\"id\":\"runtime-type-check\",\"passed\":true,\"values\":{\"value\":{\"kind\":\"integer\",\"value\":\"2\"},\"value\":{\"kind\":\"integer\",\"value\":\"2\"}}}"
          : "{\"kind\":\"check\",\"id\":\"runtime-type-check\",\"passed\":true,\"values\":{\"value\":{\"kind\":\"integer\",\"value\":\"2\",\"unexpected\":true}}}").RootElement.Clone());
      }
    }
    var drafts = new HashSet<string>();
    if (scenario == "draft-owner") { drafts.Add(owner.FullDafnyName); }
    if (scenario == "draft-dependency") { drafts.Add("Store.Good"); }
    return ContractRuntimeTypeEvidence.Collect(collectionProgram ?? program, (collectionCampaign ?? campaign).Sources, new Dictionary<string, ContractRuntimeClause> { [id] = clause }, records,
      scenario == "uncompiled" ? new HashSet<string>() : new HashSet<string> { ContractRuntimeObligationTransformer.Literal(id) }, drafts, cancellationToken, deadlineTimestamp, phaseObserver);
  }

  // A valid heap cannot hide an invalid refined root argument when native typed construction replaces global SAT.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Error)]
  public async Task NativeInitialConstructionIncludesRootInputs(int argument, ContractQueryOutcome expected) {
    const string source = "module Store { type Positive = value:int | value > 0 witness 1 " +
      "class Cell { var value:Positive } method Entry(cell:Cell, argument:Positive) {} }";
    var (program, campaign) = await Parse(source);
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign,
      Values(("cell", Reference("cell")), ("argument", Integer(argument))), heap, specifications);
    Assert.NotNull(proof);
    var result = await CheckTypeProof(proof);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Equal(source, campaign.Sources[0].Content);
  }

  // Native assignment WD checks imported generic constructors and their nested refined components.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Error)]
  public async Task NativeInitialConstructionChecksNestedGenericCarrier(int value, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("""
      module Data {
        type Positive = value:int | value > 0 witness 1
        datatype Box<T> = Box(value:T)
      }
      module Store {
        import D = Data
        class Cell { var items:seq<D.Box<D.Positive>> }
        method Entry(cell:Cell) {}
      }
      """);
    var boxed = new ContractValue(ContractValueKind.Datatype, Constructor: "Data.Box.Box", Fields: Values(("value", Integer(value))));
    var heap = new[] { new ContractHeapObject("cell", "Store.Cell", Values(("items",
      new ContractValue(ContractValueKind.Sequence, Items: [boxed])))) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.NotNull(proof);
    var result = await CheckTypeProof(proof);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Revealed original opaque constraints are checked during construction, including the false-membership case.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Error)]
  public async Task NativeInitialConstructionChecksOpaqueConstraint(int value, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("module Store { opaque predicate Good(value:int) { value > 0 } " +
      "type Positive = value:int | Good(value) witness * class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", value) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.NotNull(proof);
    var result = await CheckTypeProof(proof);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Native conversion obligations also check the original constraint of a distinct newtype.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Error)]
  public async Task NativeInitialConstructionChecksNewtype(int value, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("module Store { newtype Positive = value:int | value > 0 witness 1 " +
      "class Cell { var value:Positive } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", value) };
    var specifications = await CertifyInitial(program, campaign, heap);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications);
    Assert.NotNull(proof);
    var result = await CheckTypeProof(proof);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // A plain function without explicit requires/ensures still needs original body well-definedness before type admission.
  [Fact]
  public async Task NativeInitialConstructionRejectsUnprovedPlainFunction() {
    var (program, campaign) = await Parse("module Store { function Divide(value:int):int { 1 / value } " +
      "type Positive = value:int | Divide(value) > 0 witness * class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 1) };
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, heap, specifications);
    var result = await specifications.CheckModuleAsync(scope, "Store", CancellationToken.None);
    Assert.False(result.Verified);
    Assert.False(specifications.Accept(scope));
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
  }

  // Type membership alone cannot replace the defining equation of an initialized immutable field.
  [Fact]
  public async Task NativeInitialConstructionDefersInitializedConstants() {
    var (program, campaign) = await Parse("module Store { type Positive = value:int | value > 0 witness 1 " +
      "class Cell { const fixed:int := 0 var value:Positive } method Entry(cell:Cell) {} }");
    var heap = new[] { new ContractHeapObject("cell", "Store.Cell", Values(("fixed", Integer(0)), ("value", Integer(2)))) };
    var specifications = await CertifyInitial(program, campaign, heap);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
  }

  // An uncertified omitted empty type remains outside constructive admission even when every captured carrier is valid.
  [Fact]
  public async Task NativeInitialConstructionDoesNotInventOmittedInhabitant() {
    var (program, campaign) = await Parse("module Store { type Empty = value:int | false witness * " +
      "class Cell { var value:int ghost var unused:Empty constructor Init() requires false { value:=0; ghost var hidden:Empty :| true; unused:=hidden; } } " +
      "method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
  }

  // An opaque omitted type without a constructive witness stays outside compositional admission.
  [Fact]
  public async Task NativeInitialConstructionDefersOpaqueOmittedType() {
    var (program, campaign) = await Parse("module Store { type Hidden " +
      "class Cell { var value:int ghost var unused:Hidden constructor Init(hidden:Hidden) { value:=0; unused:=hidden; } } " +
      "method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, Values(("cell", Reference("cell"))), heap, specifications));
  }

  // Root reference identity must point to an actually captured object before pure carrier proofs can compose.
  [Fact]
  public async Task NativeInitialConstructionRejectsUnknownRootReference() {
    var (program, campaign) = await Parse("module Store { type Positive = value:int | value > 0 witness 1 " +
      "class Cell { var value:Positive } method Entry(cell:Cell) {} }");
    var heap = new[] { Cell("cell", 2) };
    var specifications = await CertifyInitial(program, campaign, heap);
    Assert.Throws<ArgumentException>(() => ContractInitialTypeProof.TryPrepare(program, campaign,
      Values(("cell", Reference("missing"))), heap, specifications));
  }

  private static async Task<ContractSpecificationChecker> CertifyInitial(Program program,
    ContractRuntimeCampaignRequest campaign, IReadOnlyList<ContractHeapObject> heap) {
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, heap, specifications);
    Assert.Null(scope.Failure);
    foreach (var module in specifications.PendingModules(scope)) {
      var result = await specifications.CheckModuleAsync(scope, module, CancellationToken.None);
      Assert.True(result.Verified, result.Diagnostics);
    }
    Assert.True(specifications.Accept(scope));
    return specifications;
  }

  private static async Task<ContractQueryResult> CheckTypeProof(ContractInitialTypeProof proof) {
    var reachedNativeProof = false;
    var result = await ContractSolver.CheckAsync(proof.BuildQuery(), ContractQueryKind.ClosedClause,
      proof.Initial.Prepared.Program.Options, CancellationToken.None,
      sourceSnapshots: proof.Initial.Prepared.DiagnosticSourceSnapshots, sourcePath: proof.Initial.Prepared.Source.Path,
      phaseObserver: (phase, state) => reachedNativeProof |= phase.StartsWith("boogie:", StringComparison.Ordinal) && state == "started");
    Assert.True(reachedNativeProof, result.Diagnostics);
    return result;
  }

  // Actual initial queries include explicit inhabitance for omitted refined fields; a bare object type would not suffice.
  [Theory]
  [InlineData("true", ContractQueryOutcome.Sat)]
  [InlineData("false", ContractQueryOutcome.Unsat)]
  public async Task InitialQueryRetainsOmittedRefinementInhabitance(string constraint, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("module Store { type Hidden = value:int | " + constraint + " witness * " +
      "class Cell { ghost var value:Hidden constructor Init() requires false { ghost var initial:Hidden :| true; value := initial; } } " +
      "method Entry(cell:Cell) {} }");
    var heap = new[] { new ContractHeapObject("cell", "Store.Cell", Values()) };
    Assert.Null(ContractRuntimeHeapChecking.CheckInitialTypes(program, heap));
    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, Values(("cell", Reference("cell"))), heap);
    var query = ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency,
      choiceConstraints: check.InitialTypeConstraints);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.PremiseConsistency,
      program.Options, CancellationToken.None, sourceSnapshots: check.Prepared.DiagnosticSourceSnapshots,
      sourcePath: check.Prepared.Source.Path);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Empty collections and constructors independent of an empty component supply real omitted-state inhabitants.
  [Theory]
  [InlineData("seq<Empty>")]
  [InlineData("set<Empty>")]
  [InlineData("map<Empty, Empty>")]
  [InlineData("multiset<Empty>")]
  [InlineData("int -> seq<Empty>")]
  [InlineData("Choice<Empty>")]
  [InlineData("Tree")]
  public async Task StructuredOmissionUsesConstructibleInhabitant(string omittedType) {
    var (program, _) = await Parse("""
      module Store {
        type Empty = value: int | false witness *
        datatype Choice<T> = Some(value: T) | None
        datatype Tree = Branch(child: Tree) | Leaf
        class Cell { ghost var unused: OMITTED }
        method Entry(cell: Cell) {}
      }
      """.Replace("OMITTED", omittedType));
    Assert.True(ContractRuntimeHeapChecking.CheckInitialTypes(program,
      [new ContractHeapObject("cell", "Store.Cell", Values())]));
  }

  // A constant arrow cannot inhabit an empty codomain merely because its component type is syntactically present.
  [Fact]
  public async Task StructuredOmissionKeepsEmptyCodomainUnsupported() {
    var (program, _) = await Parse("""
      module Store {
        type Empty = value: int | false witness *
        datatype Box<T> = Box(value: T)
        class Cell {
          ghost var unused: int -> Box<Empty>
          constructor Init() requires false {
            ghost var value: int -> Box<Empty> :| true;
            unused := value;
          }
        }
        method Entry(cell: Cell) {}
      }
      """);
    Assert.Throws<NotSupportedException>(() => ContractRuntimeHeapChecking.CheckInitialTypes(program,
      [new ContractHeapObject("cell", "Store.Cell", Values())]));
  }

  // A directly captured refined field supplies a conditional constructor/arrow witness only after its original premise is satisfiable.
  [Fact]
  public async Task CapturedRefinementSupportsOmittedArrowInhabitant() {
    Assert.Equal(ContractQueryOutcome.Sat, await CheckConditionalWitness(2));
  }

  // An invalid captured witness cannot make an omitted refined arrow admit an inconsistent initial state.
  [Fact]
  public async Task InvalidCapturedRefinementDoesNotSupportOmittedArrow() {
    Assert.Equal(ContractQueryOutcome.Unsat, await CheckConditionalWitness(-1));
  }

  // Initial consistency checks the actual opaque refinement body rather than an arbitrary predicate interpretation.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Sat)]
  [InlineData(-1, ContractQueryOutcome.Unsat)]
  public async Task InitialOpaqueRefinementUsesOriginalDefinition(int value, ContractQueryOutcome expected) {
    Assert.Equal(expected, await CheckConditionalWitness(value, opaque: true));
  }

  private static async Task<ContractQueryOutcome> CheckConditionalWitness(int value, bool opaque = false) {
    var source = """
      module Store {
        type Positive = value: int | value > 0 witness 1
        datatype Box<T> = Box(value: T)
        class Cell {
          var value: Positive
          ghost var unused: int -> Box<Positive>
        }
        method Entry(cell: Cell) {}
      }
      """;
    if (opaque) {
      source = source.Replace("type Positive = value: int | value > 0 witness 1",
        "opaque predicate Good(value:int) { value > 0 } type Positive = value:int | Good(value) witness 1");
    }
    var (program, campaign) = await Parse(source);
    var initial = new[] { Cell("cell", value) };
    Assert.Null(ContractRuntimeHeapChecking.CheckInitialTypes(program, initial));
    var check = ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      Values(("cell", Reference("cell"))), initial);
    var result = await ContractSolver.CheckAsync(
      ContractQueryBuilder.Build(check.Prepared, check.Request, ContractQueryKind.PremiseConsistency,
        choiceConstraints: check.InitialTypeConstraints), ContractQueryKind.PremiseConsistency,
      program.Options, CancellationToken.None, queryName: ContractQueryBuilder.Name(check.Prepared),
      sourceSnapshots: check.Prepared.DiagnosticSourceSnapshots, sourcePath: check.Prepared.Source.Path);
    return result.Outcome;
  }

  private const string Source = """
    module Store {
      class Cell { var value: int }
      twostate predicate Advanced(cell: Cell) reads cell { cell.value == old(cell.value) + 1 }
      method Entry(cell: Cell) returns (result: int)
        requires cell.value >= 0
        modifies cell
        ensures Advanced(cell)
        ensures result == cell.value
      { cell.value := cell.value + 9; result := -1; }
    }
    """;

  private static ContractValue Integer(int value) => new(ContractValueKind.Integer, value.ToString(System.Globalization.CultureInfo.InvariantCulture));
  private static ContractValue Reference(string id) => new(ContractValueKind.Reference, id);
  private static Dictionary<string, ContractValue> Values(params (string Name, ContractValue Value)[] values) =>
    values.ToDictionary(pair => pair.Name, pair => pair.Value);
  private static ContractHeapObject Cell(string id, int value) => new(id, "Store.Cell", Values(("value", Integer(value))));

  private static async Task<(Program Program, ContractRuntimeCampaignRequest Campaign)> Parse(
    string source = Source, string entry = "Store.Entry") {
    return await Parse([SourceFile("runtime-heap.dfy", source)], entry);
  }

  private static async Task<(Program Program, ContractRuntimeCampaignRequest Campaign)> Parse(
    IReadOnlyList<ContractSource> snapshots, string entry = "Store.Entry") {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (program, new ContractRuntimeCampaignRequest(1, snapshots, new ContractEntry(entry), "heap-query"));
  }

  private static Task<ContractQueryResult> Check(ContractRuntimeHeapCheck check, ContractQueryKind kind,
    bool negate = false, int clause = 0) => ContractSolver.CheckAsync(
    ContractQueryBuilder.Build(check.Prepared, check.Request, kind, check.Outputs, negate,
      check.Observations, postconditionClause: check.Prepared.Method.Ens[clause].E), kind,
    check.Prepared.Program.Options, CancellationToken.None, queryName: ContractQueryBuilder.Name(check.Prepared),
    sourceSnapshots: check.Prepared.DiagnosticSourceSnapshots, sourcePath: check.Prepared.Source.Path);

  // The original two-state predicate uses captured old/new cells independently of the defective body.
  [Theory]
  [InlineData(5, ContractQueryOutcome.Unsat, ContractQueryOutcome.Sat)]
  [InlineData(6, ContractQueryOutcome.Sat, ContractQueryOutcome.Unsat)]
  public async Task ObservedTransitionDeterminesOriginalClause(int finalValue,
    ContractQueryOutcome expected, ContractQueryOutcome oppositeExpected) {
    var (program, campaign) = await Parse();
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell")), ("cell.value", Integer(4))), [Cell("cell", 4)], [Cell("cell", finalValue)],
      Values(("result", Integer(-1))));
    Assert.Null(check.FrameViolation);
    var premise = await Check(check, ContractQueryKind.PremiseConsistency);
    Assert.True(premise.Outcome == ContractQueryOutcome.Sat, premise.Diagnostics);
    var result = await Check(check, ContractQueryKind.ObservedPostcondition);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    var opposite = await Check(check, ContractQueryKind.ObservedPostcondition, true);
    Assert.True(opposite.Outcome == oppositeExpected, opposite.Diagnostics);
    // The separate invalid return clause cannot be silently conjoined into the selected clause.
    var returnClause = await Check(check, ContractQueryKind.ObservedPostcondition, clause: 1);
    Assert.True(returnClause.Outcome == ContractQueryOutcome.Sat, returnClause.Diagnostics);
    Assert.Equal(Source, campaign.Sources[0].Content);
  }

  // A violated entry precondition makes the observed premise inconsistent, so Q cannot earn a verdict.
  [Fact]
  public async Task InvalidEntryHasUnsatisfiableObservedPremise() {
    var (program, campaign) = await Parse();
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, Values(("cell", Reference("cell"))),
      [Cell("cell", -1)], [Cell("cell", 0)], Values(("result", Integer(0))));
    var result = await Check(check, ContractQueryKind.PremiseConsistency);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Every captured object must retain its identity, type and complete field set at return.
  [Theory]
  [InlineData("allocated")]
  [InlineData("missing")]
  [InlineData("type")]
  [InlineData("field")]
  public async Task RejectsChangedHeapShape(string change) {
    var (program, campaign) = await Parse();
    ContractHeapObject[] final = change switch {
      "allocated" => [Cell("cell", 5), Cell("extra", 0)],
      "missing" => [],
      "type" => [Cell("cell", 5) with { Type = "Store.Other" }],
      _ => [Cell("cell", 5) with { Fields = Values() }]
    };
    Assert.Throws<NotSupportedException>(() => ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell"))), [Cell("cell", 4)], final, Values(("result", Integer(5)))));
  }

  // Duplicate final identities cannot overwrite a conflicting snapshot during observation flattening.
  [Fact]
  public async Task RejectsDuplicateFinalIdentity() {
    var (program, campaign) = await Parse();
    Assert.Throws<ArgumentException>(() => ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell"))), [Cell("cell", 4)], [Cell("cell", 5), Cell("cell", 99)],
      Values(("result", Integer(5)))));
  }

  // Mutable edges may point to existing objects while a nested frame still constrains other cells.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NestedFrameUsesInitialReferences(bool outsideFrame) {
    var (program, campaign) = await Parse("""
      module Store {
        class Cell { var value: int }
        class Handle { var cell: Cell constructor(cell: Cell) { this.cell := cell; } }
        method Entry(handle: Handle, other: Cell) modifies handle, handle.cell {}
      }
      """);
    ContractHeapObject Handle(string id) => new("handle", "Store.Handle", Values(("cell", Reference(id))));
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("handle", Reference("handle")), ("other", Reference("other"))),
      [Handle("cell"), Cell("cell", 4), Cell("other", 7)],
      [Handle("other"), Cell("cell", 5), Cell("other", outsideFrame ? 8 : 7)], Values());
    if (outsideFrame) {
      Assert.Contains("other.value", check.FrameViolation);
    } else {
      Assert.Null(check.FrameViolation);
    }
  }

  // An immutable reference edge cannot change merely because both target identities were captured.
  [Fact]
  public async Task RejectsChangedImmutableEdge() {
    var (program, campaign) = await Parse("""
      module Store {
        class Cell { var value: int }
        class Handle { const cell: Cell constructor(cell: Cell) { this.cell := cell; } }
        method Entry(handle: Handle) modifies handle.cell {}
      }
      """);
    ContractHeapObject Handle(string id) => new("handle", "Store.Handle", Values(("cell", Reference(id))));
    Assert.Throws<NotSupportedException>(() => ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("handle", Reference("handle"))), [Handle("cell"), Cell("cell", 4), Cell("other", 7)],
      [Handle("other"), Cell("cell", 4), Cell("other", 7)], Values()));
  }

  // An instance entry binds the captured receiver and preserves its native old-state semantics.
  [Fact]
  public async Task CapturedReceiverDeterminesInstancePostcondition() {
    var (program, campaign) = await Parse("""
      module Store {
        class Cell {
          var value: int
          method Entry() modifies this ensures value == old(value) + 1 {}
        }
      }
      """, "Store.Cell.Entry");
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("receiver", Reference("cell")), ("receiver.value", Integer(4))),
      [Cell("cell", 4)], [Cell("cell", 5)], Values());
    Assert.Equal("cell", check.Request.Entry.Receiver!.Value);
    Assert.Empty(check.Request.Inputs);
    var premise = await Check(check, ContractQueryKind.PremiseConsistency);
    Assert.True(premise.Outcome == ContractQueryOutcome.Sat, premise.Diagnostics);
    var result = await Check(check, ContractQueryKind.ObservedPostcondition);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // A captured ghost scalar is bound under its original type while old and current heap cells stay distinct.
  [Theory]
  [InlineData(5, ContractQueryOutcome.Unsat, ContractQueryOutcome.Sat)]
  [InlineData(6, ContractQueryOutcome.Sat, ContractQueryOutcome.Unsat)]
  public async Task CapturedGhostInputDeterminesObservedTransition(int finalValue,
    ContractQueryOutcome expected, ContractQueryOutcome oppositeExpected) {
    const string source = "module Store { class Cell { var value:int } " +
      "method Entry(cell:Cell, ghost amount:int) modifies cell " +
      "ensures cell.value == old(cell.value) + amount {} }";
    var (program, campaign) = await Parse(source);
    var inputs = Values(("cell", Reference("cell")), ("amount", Integer(1)));
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign, inputs,
      [Cell("cell", 4)], [Cell("cell", finalValue)], Values());
    Assert.Equal("1", check.Request.Inputs["amount"].Value);
    Assert.Null(check.FrameViolation);
    var premise = await Check(check, ContractQueryKind.PremiseConsistency);
    Assert.True(premise.Outcome == ContractQueryOutcome.Sat, premise.Diagnostics);
    var result = await Check(check, ContractQueryKind.ObservedPostcondition);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    var opposite = await Check(check, ContractQueryKind.ObservedPostcondition, true);
    Assert.True(opposite.Outcome == oppositeExpected, opposite.Diagnostics);
  }

  // Observed preparation cannot invent a ghost input that is absent from the runtime capture.
  [Fact]
  public async Task ObservedPreparationRejectsMissingGhostInput() {
    const string source = "module Store { class Cell { var value:int } " +
      "method Entry(cell:Cell, ghost amount:int) modifies cell " +
      "ensures cell.value == old(cell.value) + amount {} }";
    var (program, campaign) = await Parse(source);
    var error = Assert.Throws<ArgumentException>(() => ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell"))), [Cell("cell", 4)], [Cell("cell", 5)], Values()));
    Assert.Contains("amount", error.Message);
  }

  // A captured transition does not make ghost outputs available to the original postcondition query.
  [Fact]
  public async Task ObservedPreparationStillRejectsGhostOutput() {
    const string source = "module Store { class Cell { var value:int } " +
      "method Entry(cell:Cell) returns (ghost result:int) modifies cell " +
      "ensures result == old(cell.value) {} }";
    var (program, campaign) = await Parse(source);
    Assert.Throws<NotSupportedException>(() => ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell"))), [Cell("cell", 4)], [Cell("cell", 4)],
      Values(("result", Integer(4)))));
  }

  // Ghost reference arguments retain alias identity while old and current cells remain separately constrained.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task CapturedGhostReferencePreservesAliasIdentity(bool aliased) {
    const string source = "module Store { class Cell { var value:int } " +
      "method Entry(cell:Cell, ghost peer:Cell) modifies cell " +
      "ensures cell.value == old(cell.value) + 1 && " +
      "peer.value == old(peer.value) + (if cell == peer then 1 else 0) {} }";
    var (program, campaign) = await Parse(source);
    var peer = aliased ? "cell" : "peer";
    ContractHeapObject[] initial = aliased ? [Cell("cell", 4)] : [Cell("cell", 4), Cell("peer", 7)];
    ContractHeapObject[] final = aliased ? [Cell("cell", 5)] : [Cell("cell", 5), Cell("peer", 7)];
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell")), ("peer", Reference(peer))), initial, final, Values());
    Assert.Equal(peer, check.Request.Inputs["peer"].Value);
    Assert.Null(check.FrameViolation);
    var result = await Check(check, ContractQueryKind.ObservedPostcondition);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Undefined arithmetic in a ghost-dependent postcondition cannot become either native polarity.
  [Fact]
  public async Task CapturedGhostInputKeepsNativeWellDefinedness() {
    const string source = "module Store { class Cell { var value:int } " +
      "method Entry(cell:Cell, ghost divisor:int) modifies cell " +
      "ensures cell.value / divisor == old(cell.value) {} }";
    var (program, campaign) = await Parse(source);
    var check = ContractRuntimeHeapChecking.Prepare(program, campaign,
      Values(("cell", Reference("cell")), ("divisor", Integer(0))),
      [Cell("cell", 4)], [Cell("cell", 4)], Values());
    var result = await Check(check, ContractQueryKind.ObservedPostcondition);
    Assert.True(result.Outcome == ContractQueryOutcome.Error, result.Diagnostics);
    var opposite = await Check(check, ContractQueryKind.ObservedPostcondition, true);
    Assert.True(opposite.Outcome == ContractQueryOutcome.Error, opposite.Diagnostics);
  }
}
