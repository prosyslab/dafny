using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractHeapTests {
  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> PrepareModules(
    bool ghost, int value = 7, string export = "export reveals Box, Box.Value", string extraMember = "",
    string import = "import Store") {
    var library = $$"""
      module Store {
        {{export}}
        class Box {
          {{(ghost ? "ghost " : "")}}var value: int
          ghost function Value(): int { 7 }
          {{extraMember}}
        }
      }
      """;
    var entry = $$"""
      module Client {
        {{import}}
        method Entry(box: Store.Box) returns (r: int)
          requires box.Value() == 7
          ensures r == box.Value()
        { r := 7; }
      }
      """;
    var sources = new[] { new ContractSource("library.dfy", library, ContractHarnessBuilder.Hash(library)),
      new ContractSource("client.dfy", entry, ContractHarnessBuilder.Hash(entry)) };
    var request = new ContractTestRequest(1, sources, new("Client.Entry"),
      new Dictionary<string, ContractValue> { ["box"] = Reference("box") },
      [new("box", "Store.Box", new Dictionary<string, ContractValue> { ["value"] = Integer(value) })]);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  private static Task<ContractQueryResult> CheckModules(ContractPreparedProgram prepared,
    ContractTestRequest request, ContractQueryKind kind, bool negate = false,
    IReadOnlyDictionary<string, ContractValue> outputs = null,
    IReadOnlyList<string> choiceConstraints = null) =>
    ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, kind, outputs, negate,
        choiceConstraints: choiceConstraints),
      kind, prepared.Program.Options, CancellationToken.None, queryName: ContractQueryBuilder.Name(prepared),
      sourceSnapshots: prepared.DiagnosticSourceSnapshots, sourcePath: prepared.Source.Path);

  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> PrepareSameModule(
    bool ghost, int value) {
    var content = $$"""
      module Store {
        export reveals Box
        class Box {
          {{(ghost ? "ghost " : "")}}var value: int
        }
        method Entry(box: Box) returns (r: int)
          requires box.value == 7
          ensures r == box.value
        { r := 7; }
      }
      """;
    var sources = new[] { new ContractSource("store.dfy", content, ContractHarnessBuilder.Hash(content)) };
    var request = new ContractTestRequest(1, sources, new("Store.Entry"),
      new Dictionary<string, ContractValue> { ["box"] = Reference("box") },
      [new("box", "Store.Box", new Dictionary<string, ContractValue> { ["value"] = Integer(value) })]);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  // Hidden field bindings in another source must describe a satisfiable heap, including ghost cells.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task HiddenModuleFieldPremiseIsSatisfiable(bool ghost) {
    var (prepared, request) = await PrepareModules(ghost);
    var result = await CheckModules(prepared, request, ContractQueryKind.PremiseConsistency);
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
  }

  // A contradictory hidden-field premise is unsatisfiable, so the concrete binding cannot be omitted.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task HiddenModuleFieldBindingCannotBeContradicted(bool ghost) {
    var (prepared, request) = await PrepareModules(ghost);
    var access = prepared.Heap!.ReferenceExpression("box") + ".value";
    var result = await CheckModules(prepared, request, ContractQueryKind.PremiseConsistency,
      choiceConstraints: [access + " != 7"]);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Same-module P reads the hidden field and distinguishes valid from invalid concrete values.
  [Theory]
  [InlineData(true, 7, false, ContractQueryOutcome.Unsat)]
  [InlineData(false, 7, false, ContractQueryOutcome.Unsat)]
  [InlineData(true, 8, false, ContractQueryOutcome.Sat)]
  [InlineData(false, 8, true, ContractQueryOutcome.Unsat)]
  public async Task SameModuleHiddenFieldDeterminesPrecondition(bool ghost, int value, bool negate,
    ContractQueryOutcome expected) {
    var (prepared, request) = await PrepareSameModule(ghost, value);
    Assert.DoesNotContain(prepared.Heap!.SourceEdits, edit => edit.Text.Contains(" provides ", StringComparison.Ordinal));
    var result = await CheckModules(prepared, request, ContractQueryKind.EntryPrecondition, negate);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Same-module Q also remains tied to the requested hidden field value.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task SameModuleHiddenFieldRejectsWrongPostcondition(bool ghost) {
    var (prepared, request) = await PrepareSameModule(ghost, 7);
    var outputs = new Dictionary<string, ContractValue> { ["r"] = Integer(8) };
    var result = await CheckModules(prepared, request, ContractQueryKind.ObservedPostcondition, outputs: outputs);
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
  }

  // A wrong observed output remains a definite violation of the original Q over the hidden field.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task HiddenModuleFieldRejectsWrongPostcondition(bool ghost) {
    var (prepared, request) = await PrepareModules(ghost);
    var outputs = new Dictionary<string, ContractValue> { ["r"] = Integer(8) };
    var result = await CheckModules(prepared, request, ContractQueryKind.ObservedPostcondition, outputs: outputs);
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
    var opposite = await CheckModules(prepared, request, ContractQueryKind.ObservedPostcondition, true, outputs);
    Assert.True(opposite.Outcome == ContractQueryOutcome.Unsat, opposite.Diagnostics);
  }

  // Runtime constructors and field exports are inserted only into hash-bound diagnostic copies.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task HiddenModuleFieldRuntimeSourcesResolveWithoutChangingSnapshots(bool ghost) {
    var (prepared, request) = await PrepareModules(ghost);
    var original = request.Sources.ToList();
    var runtime = ContractHarnessBuilder.RuntimeSources(prepared, request);
    var reporter = new BatchErrorReporter(prepared.Program.Options);
    _ = await ContractSourceSnapshot.ParseAsync(reporter, runtime, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    Assert.Equal(original, request.Sources);
    Assert.Equal(original, prepared.SourceSnapshots);
    Assert.All(runtime, source => Assert.Equal(ContractHarnessBuilder.Hash(source.Content), source.Sha256));
    Assert.All(prepared.Heap.SourceEdits, edit => Assert.Equal(ContractSourceSnapshot.UriFor("library.dfy"), edit.SourceUri));
  }

  // A wildcard default view already exports the synthetic members and must not receive duplicate entries.
  [Fact]
  public async Task HiddenModuleWildcardDefaultExportRemainsResolvable() {
    var (prepared, request) = await PrepareModules(true, export: "export reveals Box provides *");
    var sources = ContractHarnessBuilder.RuntimeSources(prepared, request);
    var reporter = new BatchErrorReporter(prepared.Program.Options);

    _ = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);

    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // A selected named-only view that reveals the heap class receives the diagnostic constructor safely.
  [Theory]
  [InlineData("Public")]
  [InlineData("ContractDiagnosticCreate")]
  public async Task HiddenModuleNamedOnlyExportRemainsResolvable(string exportName) {
    var (prepared, request) = await PrepareModules(true,
      export: "export " + exportName + " reveals Box, Box.Value", import: "import Store = Store`" + exportName);
    var reporter = new BatchErrorReporter(prepared.Program.Options);

    _ = await ContractSourceSnapshot.ParseAsync(reporter,
      ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);

    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // A named import receives constructor access even when a different default export also exists.
  [Fact]
  public async Task HiddenModuleSelectedNamedExportAlongsideDefaultRemainsResolvable() {
    var (prepared, request) = await PrepareModules(true,
      export: "export reveals Box, Box.Value\nexport Public reveals Box, Box.Value",
      import: "import Store = Store`Public");
    var reporter = new BatchErrorReporter(prepared.Program.Options);

    _ = await ContractSourceSnapshot.ParseAsync(reporter,
      ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);

    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // A user-provided constructor cannot replace the diagnostic allocator or execute its body.
  [Fact]
  public async Task HiddenModuleReservedConstructorFailsClosed() {
    var error = await Assert.ThrowsAsync<ArgumentException>(() => PrepareModules(true,
      extraMember: "constructor ContractDiagnosticCreate() { value := 99; }"));
    Assert.Contains("reserved member 'ContractDiagnosticCreate'", error.Message);
  }

  private static async Task<(Program Program, ContractTestRequest Request)> Resolve(
    string source,
    string symbol,
    IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyList<ContractHeapObject> heap) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse(source, new Uri("untitled:contract-heap"), reporter);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var snapshot = new ContractSource("heap.dfy", source, ContractHarnessBuilder.Hash(source));
    return (parsed.Program, new ContractTestRequest(ContractJson.SchemaVersion, [snapshot],
      new ContractEntry(symbol), inputs, heap));
  }

  private static ContractValue Integer(int value) => new(ContractValueKind.Integer, value.ToString());
  private static ContractValue Reference(string id) => new(ContractValueKind.Reference, id);
  private static ContractHeapObject Cell(string id, int value) => new(id, "Heap.Cell",
    new Dictionary<string, ContractValue> { ["value"] = Integer(value) });
  private static Method FindMethod(Program program, string name) => program.RawModules()
    .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
    .SelectMany(type => type.Members).OfType<Method>().Single(method => method.Name == name);

  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> PreparePartialHeap(
    string source, IReadOnlyList<ContractHeapObject> heap) {
    var snapshot = new ContractSource("partial-heap.dfy", source, ContractHarnessBuilder.Hash(source));
    var request = new ContractTestRequest(ContractJson.SchemaVersion, [snapshot], new("PartialHeap.Entry"),
      new Dictionary<string, ContractValue> { ["box"] = Reference("box") }, heap);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  private const string IrrelevantFunctionFieldSource = """
module PartialHeap {
  class Box {
    ghost var callback: int -> int
    var value: int
  }

  method Entry(box: Box) returns (result: int)
    ensures result == box.value
  {
    result := box.value;
  }
}
""";

  private static ContractHeapObject PartialBox(string id = "box") => new(id, "PartialHeap.Box",
    new Dictionary<string, ContractValue> { ["value"] = Integer(7) });

  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)>
    PrepareCrossModuleSubsetHeap(bool useSubset) {
    var store = """
module Store {
  export reveals Box, GoodBox provides Box.callback
  class Box {
    ghost var callback: int -> int
    var value: int
  }
  type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *
}
""";
    var parameterType = useSubset ? "Store.GoodBox" : "Store.Box";
    var client = $$"""
module Client {
  import Store
  method Entry(box: {{parameterType}}) returns (result: int)
    ensures result == 7
  {
    result := 7;
  }
}
""";
    var sources = new[] {
      new ContractSource("store.dfy", store, ContractHarnessBuilder.Hash(store)),
      new ContractSource("client.dfy", client, ContractHarnessBuilder.Hash(client))
    };
    var request = new ContractTestRequest(ContractJson.SchemaVersion, sources, new("Client.Entry"),
      new Dictionary<string, ContractValue> { ["box"] = Reference("box") },
      [new("box", "Store.Box", new Dictionary<string, ContractValue> { ["value"] = Integer(7) })]);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  // An irrelevant unsupported ghost function field may be omitted while diagnostic source still resolves.
  [Fact]
  public async Task IrrelevantGhostFunctionFieldMayBeOmitted() {
    var (prepared, request) = await PreparePartialHeap(IrrelevantFunctionFieldSource, [PartialBox()]);

    var constructor = Assert.Single(prepared.Heap!.SourceInsertions).Text;
    Assert.Contains("constructor ContractDiagnosticCreate(value: int)", constructor);
    Assert.Contains("ghost var contractOmittedGhostWitness0: int -> int :| true;", constructor);
    Assert.DoesNotContain(prepared.Heap.InitialConstraints, constraint => constraint.Contains("callback"));
    Assert.DoesNotContain("callback", prepared.Heap.InitialCaptureStatements);
    Assert.Equal("contractHeap0.value := 7;", prepared.Heap.QueryAssignments(
      new Dictionary<string, ContractValue> { ["$final/box/value"] = Integer(7) }));
    var reporter = new BatchErrorReporter(prepared.Program.Options);
    _ = await ContractSourceSnapshot.ParseAsync(reporter,
      ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // A nested datatype mismatch identifies its containing heap cell and map/datatype path.
  [Fact]
  public async Task NestedDatatypeHeapMismatchReportsCellPath() {
    const string source = """
module PartialHeap {
  datatype Inner = InnerValue(number: int)
  datatype Outer = OuterValue(inner: Inner)
  class Box { var payload: map<int, Outer> }
  method Entry(box: Box) {}
}
""";
    var invalidInner = new ContractValue(ContractValueKind.Datatype, Constructor: "Inner.Missing",
      Fields: new Dictionary<string, ContractValue> { ["number"] = Integer(1) });
    var outer = new ContractValue(ContractValueKind.Datatype, Constructor: "Outer.OuterValue",
      Fields: new Dictionary<string, ContractValue> { ["inner"] = invalidInner });
    var payload = new ContractValue(ContractValueKind.Map,
      Entries: [new ContractMapEntry(Integer(0), outer)]);
    var box = new ContractHeapObject("box", "PartialHeap.Box",
      new Dictionary<string, ContractValue> { ["payload"] = payload });

    var error = await Assert.ThrowsAsync<ArgumentException>(() => PreparePartialHeap(source, [box]));

    Assert.Equal("Heap value at 'box.payload[0].value.inner': " +
      "Datatype constructor and fields do not match the expected heap value type.", error.Message);
  }

  // An omitted ghost field referenced by the selected entry precondition is rejected before source generation.
  [Fact]
  public async Task OmittedGhostFieldInEntryRequiresFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("ensures result == box.value",
      "requires box.callback(0) == 0\n    ensures result == box.value");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Entry", error.Message);
  }

  // An omitted ghost field referenced by the selected entry postcondition is rejected before source generation.
  [Fact]
  public async Task OmittedGhostFieldInEntryEnsuresFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("ensures result == box.value",
      "ensures result == box.value && box.callback(0) == 0");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Entry", error.Message);
  }

  // An omitted ghost field referenced by a reachable internal body is rejected through the resolved call graph.
  [Fact]
  public async Task OmittedGhostFieldInReachableInternalBodyFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "method Inspect(box: Box) { ghost var observed := box.callback(0); }\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Inspect", error.Message);
  }

  // A first-class function reference remains a transitive dependency when auditing an omitted ghost field.
  [Fact]
  public async Task OmittedGhostFieldUsedThroughFirstClassFunctionFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "ghost function Read(box: Box): int reads box { box.callback(0) }\n\n" +
      "  ghost function Select(): Box -> int { Read }\n\n  method Entry(box: Box)")
      .Replace("ensures result == box.value", "requires Select()(box) == 0\n    ensures result == box.value");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Read", error.Message);
  }

  // An entry formal's resolved subset type makes its field-reading constraint relevant to omission safety.
  [Fact]
  public async Task OmittedGhostFieldUsedByEntryFormalSubsetConstraintFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *\n\n" +
      "  method Entry(box: GoodBox)");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.GoodBox", error.Message);
  }

  // An imported subset formal transitively exposes its cross-module field-reading constraint to the audit.
  [Fact]
  public async Task OmittedGhostFieldUsedByCrossModuleFormalSubsetConstraintFailsClosed() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PrepareCrossModuleSubsetHeap(true));

    Assert.Contains("Store.Box.callback", error.Message);
    Assert.Contains("Store.GoodBox", error.Message);
  }

  // An unused imported subset declaration is not scanned globally when the entry uses the underlying class.
  [Fact]
  public async Task OmittedGhostFieldUsedByUnusedCrossModuleSubsetIsAllowed() {
    var (prepared, _) = await PrepareCrossModuleSubsetHeap(false);

    Assert.Contains(prepared.Heap!.SourceEdits,
      edit => edit.Text.Contains("contractOmittedGhostWitness", StringComparison.Ordinal));
  }

  // A reachable internal method's formal subset type is followed through the resolved type-dependency graph.
  [Fact]
  public async Task OmittedGhostFieldUsedByReachableInternalFormalTypeFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *\n\n" +
      "  method Inspect(box: GoodBox) {}\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.GoodBox", error.Message);
  }

  // A reachable bodyless extern's formal subset type remains relevant even though its source body is excluded.
  [Fact]
  public async Task OmittedGhostFieldUsedByReachableExternFormalTypeFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *\n\n" +
      "  method {:extern} Inspect(box: GoodBox)\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.GoodBox", error.Message);
  }

  // A subset type used only by an extern body local does not make its unexecuted constraint relevant.
  [Fact]
  public async Task OmittedGhostFieldUsedOnlyByExternBodyLocalTypeIsAllowed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *\n\n" +
      "  method {:extern} Inspect(box: Box) { ghost var ignored: GoodBox := box; }\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var (prepared, _) = await PreparePartialHeap(source, [PartialBox()]);

    Assert.Contains("contractOmittedGhostWitness", Assert.Single(prepared.Heap!.SourceInsertions).Text);
  }

  // An omitted ghost field referenced by a reachable extern contract is rejected without inspecting its body.
  [Fact]
  public async Task OmittedGhostFieldInReachableExternContractFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "method {:extern} Inspect(box: Box) requires box.callback(0) == 0\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Inspect", error.Message);
  }

  // Calls that occur only in an extern source body do not make that unexecuted helper relevant to omission safety.
  [Fact]
  public async Task OmittedGhostFieldUsedOnlyByExternBodyHelperIsAllowed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "ghost function Callback(box: Box): int reads box { box.callback(0) }\n\n" +
      "  method {:extern} Inspect(box: Box) { ghost var observed := Callback(box); }\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var (prepared, _) = await PreparePartialHeap(source, [PartialBox()]);

    Assert.Contains("contractOmittedGhostWitness", Assert.Single(prepared.Heap!.SourceInsertions).Text);
  }

  // A first-class function reference that occurs only in an extern source body remains irrelevant to omission safety.
  [Fact]
  public async Task OmittedGhostFieldUsedOnlyByExternBodyFunctionValueIsAllowed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "ghost function Read(box: Box): int reads box { box.callback(0) }\n\n" +
      "  method {:extern} Inspect(box: Box) {\n" +
      "    ghost var selected: Box -> int := Read;\n" +
      "    ghost var observed := selected(box);\n" +
      "  }\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var (prepared, _) = await PreparePartialHeap(source, [PartialBox()]);

    Assert.Contains("contractOmittedGhostWitness", Assert.Single(prepared.Heap!.SourceInsertions).Text);
  }

  // A pure helper called from an extern contract remains transitively relevant and rejects its omitted field read.
  [Fact]
  public async Task OmittedGhostFieldUsedByExternContractHelperFailsClosed() {
    var source = IrrelevantFunctionFieldSource.Replace("method Entry(box: Box)",
      "ghost function Callback(box: Box): int reads box { box.callback(0) }\n\n" +
      "  method {:extern} Inspect(box: Box) requires Callback(box) == 0\n\n  method Entry(box: Box)")
      .Replace("result := box.value;", "Inspect(box);\n    result := box.value;");

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => PreparePartialHeap(source, [PartialBox()]));

    Assert.Contains("PartialHeap.Box.callback", error.Message);
    Assert.Contains("PartialHeap.Callback", error.Message);
  }

  // Every runtime-visible field remains mandatory in a partial heap object.
  [Fact]
  public async Task OmittedNonGhostFieldFailsClosed() {
    var incomplete = new ContractHeapObject("box", "PartialHeap.Box",
      new Dictionary<string, ContractValue>());

    var error = await Assert.ThrowsAsync<ArgumentException>(() =>
      PreparePartialHeap(IrrelevantFunctionFieldSource, [incomplete]));

    Assert.Contains("omits required non-ghost field 'PartialHeap.Box.value'", error.Message);
  }

  // A supplied field name must resolve to a declared instance field of the requested class.
  [Fact]
  public async Task UnknownPartialHeapFieldFailsClosed() {
    var unknown = new ContractHeapObject("box", "PartialHeap.Box",
      new Dictionary<string, ContractValue> { ["value"] = Integer(7), ["missing"] = Integer(0) });

    var error = await Assert.ThrowsAsync<ArgumentException>(() =>
      PreparePartialHeap(IrrelevantFunctionFieldSource, [unknown]));

    Assert.Contains("supplies unknown field 'missing'", error.Message);
  }

  // Objects of one class cannot select different logical field subsets for shared runtime metadata.
  [Fact]
  public async Task SameClassInconsistentPartialFieldSetsFailClosed() {
    const string source = """
module PartialHeap {
  class Box {
    ghost var left: int
    ghost var right: int
    var value: int
  }
  method Entry(box: Box) {}
}
""";
    var first = new ContractHeapObject("box", "PartialHeap.Box",
      new Dictionary<string, ContractValue> { ["left"] = Integer(1), ["value"] = Integer(7) });
    var second = new ContractHeapObject("other", "PartialHeap.Box",
      new Dictionary<string, ContractValue> { ["right"] = Integer(2), ["value"] = Integer(8) });

    var error = await Assert.ThrowsAsync<ArgumentException>(() => PreparePartialHeap(source, [first, second]));

    Assert.Contains("must supply the same field set", error.Message);
  }

  private const string CellSource = """
module Heap {
  class Cell {
    var value: int

    constructor(initial: int) {
      value := initial;
    }

    predicate Valid()
      reads this
    {
      value >= 0
    }
  }

  method Entry(a: Cell, b: Cell)
    requires a != b
    modifies a
  {
  }
}
""";

  // A class-only heap request completes without evaluating the global resolved-array type index.
  [Fact]
  public async Task NoArrayHeapSkipsResolvedArrayTypeScan() {
    var (program, request) = await Resolve(CellSource, "Heap.Entry",
      new Dictionary<string, ContractValue> {
        ["a"] = Reference("first"),
        ["b"] = Reference("second")
      }, [Cell("first", 2), Cell("second", 10)]);

    var prepare = typeof(ContractHeapFactory).GetMethods(BindingFlags.Static | BindingFlags.NonPublic)
      .Single(method => method.Name == nameof(ContractHeapFactory.Prepare) && method.GetParameters().Length == 3);
    Func<Program, IReadOnlyDictionary<string, Microsoft.Dafny.Type>> rejectScan =
      _ => throw new InvalidOperationException("No-array heaps must not request the global array type index.");
    var plan = Assert.IsType<ContractHeapPlan>(prepare.Invoke(null, [program, request, rejectScan]));

    Assert.Equal("contractHeap0: Cell, contractHeap1: Cell", plan.QueryParameters);
  }

  // Produces resolvable diagnostic constructors and distinct allocations for two concrete objects.
  [Fact]
  public async Task DistinctHeapObjectsProduceResolvableDiagnosticSource() {
    var inputs = new Dictionary<string, ContractValue> {
      ["a"] = Reference("first"),
      ["b"] = Reference("second")
    };
    var (program, request) = await Resolve(CellSource, "Heap.Entry", inputs,
      [Cell("first", 2), Cell("second", 10)]);

    var plan = ContractHeapFactory.Prepare(program, request);

    Assert.Single(plan.SourceInsertions);
    Assert.Contains("constructor ContractDiagnosticCreate(value: int)", plan.SourceInsertions[0].Text);
    Assert.Contains("new Cell.ContractDiagnosticCreate(2)", plan.AllocationStatements);
    Assert.Contains("new Cell.ContractDiagnosticCreate(10)", plan.AllocationStatements);
    Assert.NotEqual(plan.InputExpression("a"), plan.InputExpression("b"));
    Assert.Contains(plan.InitialConstraints, constraint => constraint.Contains(" != ") &&
      constraint.Contains("contractHeap0") && constraint.Contains("contractHeap1"));
    Assert.Equal("contractHeap0: Cell, contractHeap1: Cell", plan.QueryParameters);
    Assert.Contains("\"$initial/first/value\", contractHeap0.value", plan.InitialCaptureStatements);
    Assert.Contains("\"$final/second/value\", contractHeap1.value", plan.FinalCaptureStatements);

    var method = FindMethod(program, "Entry");
    var finalObservations = new Dictionary<string, ContractValue> {
      ["$final/first/value"] = Integer(3),
      ["$final/second/value"] = Integer(10)
    };
    var queryRequires = string.Join("\n", plan.InitialConstraints.Select(constraint => "requires " + constraint));
    var probe = $$"""

  method ContractHeapProbe() {
    {{plan.AllocationStatements}}
    assert {{plan.InputExpression("a")}} != {{plan.InputExpression("b")}};
  }

  method ContractHeapQuery({{plan.QueryParameters}})
    {{queryRequires}}
    {{plan.QueryModifies}}
  {
    {{plan.QueryAssignments(finalObservations)}}
    assert old(contractHeap0.value) == 2;
  }
""";
    var generated = request.Sources[0].Content;
    foreach (var (position, text) in plan.SourceInsertions.Append((Position: method.StartToken.pos, Text: probe))
               .OrderByDescending(edit => edit.Position)) {
      generated = generated.Insert(position, text);
    }
    var generatedReporter = new BatchErrorReporter(program.Options);
    var parsed = await ProgramParser.Parse(generated, new Uri("untitled:generated-contract-heap"), generatedReporter);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(generatedReporter.ErrorCount == 0,
      string.Join("\n", generatedReporter.AllMessages.Select(diagnostic => diagnostic.Message)));
  }

  // Maps two formal inputs to one heap slot and treats the alias as inside a modifies-a frame.
  [Fact]
  public async Task AliasedInputsPreserveIdentityAndFramePermission() {
    var inputs = new Dictionary<string, ContractValue> {
      ["a"] = Reference("shared"),
      ["b"] = Reference("shared")
    };
    var (program, request) = await Resolve(CellSource.Replace("requires a != b", "requires a == b"),
      "Heap.Entry", inputs, [Cell("shared", 2)]);
    var plan = ContractHeapFactory.Prepare(program, request);
    var method = FindMethod(program, "Entry");
    var observations = new Dictionary<string, ContractValue> { ["$final/shared/value"] = Integer(3) };

    Assert.Equal(plan.InputExpression("a"), plan.InputExpression("b"));
    Assert.Null(plan.CheckFrame(method, inputs, observations));
  }

  // Allocates referenced objects before their owners and rejects no valid noncyclic dependency.
  [Fact]
  public async Task NoncyclicReferenceFieldsUseDependencyOrder() {
    const string source = """
module Graph {
  class Node {
    var next: Node?
    var value: int
    constructor(nextValue: Node?, initial: int) {
      next := nextValue;
      value := initial;
    }
  }
  method Entry(root: Node) {
  }
}
""";
    var inputs = new Dictionary<string, ContractValue> { ["root"] = Reference("root") };
    var heap = new List<ContractHeapObject> {
      new("root", "Graph.Node", new Dictionary<string, ContractValue> {
        ["next"] = Reference("leaf"), ["value"] = Integer(1)
      }),
      new("leaf", "Graph.Node", new Dictionary<string, ContractValue> {
        ["next"] = new(ContractValueKind.Null), ["value"] = Integer(2)
      })
    };
    var (program, request) = await Resolve(source, "Graph.Entry", inputs, heap);

    var plan = ContractHeapFactory.Prepare(program, request);

    var leafAllocation = plan.AllocationStatements.IndexOf("contractHeap1 :=", StringComparison.Ordinal);
    var rootAllocation = plan.AllocationStatements.IndexOf("contractHeap0 :=", StringComparison.Ordinal);
    Assert.True(leafAllocation >= 0 && leafAllocation < rootAllocation);
    Assert.Contains("ContractDiagnosticCreate(contractHeap1, 1)", plan.AllocationStatements);
  }

  // Reports a mutation of an unlisted object as a frame violation using requested initial values.
  [Fact]
  public async Task FrameCheckDetectsChangeOutsideModifiesObject() {
    var inputs = new Dictionary<string, ContractValue> {
      ["a"] = Reference("first"),
      ["b"] = Reference("second")
    };
    var (program, request) = await Resolve(CellSource, "Heap.Entry", inputs,
      [Cell("first", 2), Cell("second", 10)]);
    var plan = ContractHeapFactory.Prepare(program, request);
    var method = FindMethod(program, "Entry");
    var observations = new Dictionary<string, ContractValue> {
      ["$final/first/value"] = Integer(3),
      ["$final/second/value"] = Integer(11)
    };

    var reason = plan.CheckFrame(method, inputs, observations);

    Assert.Contains("second.value", reason);
  }

  // Ghost fields are initialized for SMT queries while runtime capture uses the logical sidecar.
  [Fact]
  public async Task GhostFieldsUseLogicalSidecarInsteadOfBeingDropped() {
    const string source = """
module HiddenHeap {
  class Box {
    ghost var proof: int
    var value: int
    constructor(initial: int) {
      proof := initial;
      value := initial;
    }
  }
  method Entry(box: Box) {
  }
}
""";
    var inputs = new Dictionary<string, ContractValue> { ["box"] = Reference("box") };
    var heap = new List<ContractHeapObject> {
      new("box", "HiddenHeap.Box", new Dictionary<string, ContractValue> {
        ["proof"] = Integer(1), ["value"] = Integer(1)
      })
    };
    var (program, request) = await Resolve(source, "HiddenHeap.Entry", inputs, heap);

    var plan = ContractHeapFactory.Prepare(program, request);

    Assert.Contains("ghost proof: int", Assert.Single(plan.SourceInsertions).Text);
    Assert.DoesNotContain("contractOmittedGhostWitness", plan.SourceInsertions[0].Text);
    Assert.Contains("ContractDiagnosticCreate(1, 1)", plan.AllocationStatements);
    Assert.DoesNotContain("proof", plan.InitialCaptureStatements);
    var assignments = plan.QueryAssignments(new Dictionary<string, ContractValue> {
      ["$final/box/proof"] = Integer(2),
      ["$final/box/value"] = Integer(2)
    });
    Assert.Contains("contractHeap0.proof := 2", assignments);
    Assert.Contains("contractHeap0.value := 2", assignments);
    var snapshotReporter = new BatchErrorReporter(program.Options);
    var snapshotProgram = await ContractSourceSnapshot.ParseAsync(snapshotReporter, request.Sources,
      CancellationToken.None);
    Assert.Equal(0, snapshotReporter.ErrorCount);
    var prepared = ContractHarnessBuilder.Prepare(snapshotProgram, request);
    var runtimeReporter = new BatchErrorReporter(program.Options);
    _ = await ContractSourceSnapshot.ParseAsync(runtimeReporter,
      ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);
    Assert.True(runtimeReporter.ErrorCount == 0,
      string.Join("\n", runtimeReporter.AllMessages.Select(message => message.Message)));
  }
}
