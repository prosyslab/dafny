using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractEntryTests {
  // Runtime source removes a reachable extern binding and body marker before installing the model bridge body.
  [Fact]
  public async Task ReachableExternalBodyCannotInvokeNativeImplementation() {
    const string source = "method {:extern \"NativeMarker\", \"Invoke\"} External(x:int) returns(r:int) ensures r == x+1 { print \"NATIVE_MARKER\"; r := -1; } method Entry(x:int) returns(r:int) { r := External(x); }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-extern-runtime.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1,
      [new("/tmp/contract-extern-runtime.dfy", source, ContractHarnessBuilder.Hash(source))], new("Entry"),
      new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "6") });
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var runtime = ContractHarnessBuilder.RuntimeSource(prepared, request);
    Assert.DoesNotContain("NativeMarker", runtime);
    Assert.Contains("ContractDiagnosticBridge.Realize(\"External\"", runtime);
    Assert.DoesNotContain("r := -1", runtime);
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(runtimeReporter,
      [new(request.Sources[0].Path, runtime, ContractHarnessBuilder.Hash(runtime))], CancellationToken.None);
    Assert.Equal(0, runtimeReporter.ErrorCount);
  }

  // Runtime source replaces an external function's expression and by-method bodies with one model bridge body.
  [Fact]
  public async Task ReachableExternalByMethodCannotInvokeNativeImplementation() {
    const string source = "function {:extern \"NativeFunction\"} External(x:int):int ensures External(x) == x+1 { x-1 } by method { print \"BY_METHOD_MARKER\"; return x-2; } method Entry(x:int) returns(r:int) { r := External(x); }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-extern-by-method-runtime.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1,
      [new("/tmp/contract-extern-by-method-runtime.dfy", source, ContractHarnessBuilder.Hash(source))], new("Entry"),
      new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "6") });
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var runtime = ContractHarnessBuilder.RuntimeSource(prepared, request);
    Assert.DoesNotContain("NativeFunction", runtime);
    Assert.DoesNotContain("BY_METHOD_MARKER", runtime);
    Assert.DoesNotContain("return x-2", runtime);
    Assert.Contains("ContractDiagnosticBridge.Choose<int>(\"External\"", runtime);
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(runtimeReporter,
      [new(request.Sources[0].Path, runtime, ContractHarnessBuilder.Hash(runtime))], CancellationToken.None);
    Assert.Equal(0, runtimeReporter.ErrorCount);
  }

  // A reachable internal body that writes a ghost field is rejected before the runtime bridge can erase it.
  [Fact]
  public async Task InternalGhostHeapWriteIsUnsupported() {
    const string source = "class Box { ghost var proof:int } method Entry(box:Box) requires box == null { if box != null { box.proof := 1; } }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-ghost-write.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1,
      [new("/tmp/contract-ghost-write.dfy", source, ContractHarnessBuilder.Hash(source))], new("Entry"),
      new Dictionary<string, ContractValue> { ["box"] = new(ContractValueKind.Null) });
    var prepared = ContractHarnessBuilder.Prepare(program, request);

    var exception = Assert.Throws<NotSupportedException>(() => ContractHarnessBuilder.RuntimeSource(prepared, request));

    Assert.Contains("tracked ghost heap field", exception.Message);
    Assert.Contains("Box.proof", exception.Message);
  }

  // Proof-local ghost state remains eligible for compiler erasure when it has no heap effect.
  [Fact]
  public async Task ProofLocalGhostStatementIsErasedWithoutRuntimeInstrumentation() {
    const string source = "method Entry() { ghost var proof:int := 1; }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-ghost-local.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1,
      [new("/tmp/contract-ghost-local.dfy", source, ContractHarnessBuilder.Hash(source))], new("Entry"),
      new Dictionary<string, ContractValue>());
    var prepared = ContractHarnessBuilder.Prepare(program, request);

    var runtime = ContractHarnessBuilder.RuntimeSource(prepared, request);

    Assert.Contains("ghost var proof", runtime);
    Assert.DoesNotContain("ContractDiagnosticBridge.Write", runtime);
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await Utils.Parse(runtimeReporter, runtime, uri: new Uri("file:///tmp/contract-ghost-local-runtime.dfy"));
    Assert.Equal(0, runtimeReporter.ErrorCount);
  }

  // Nested references use the existing typed heap renderer in both actual calls and observed output queries.
  [Fact]
  public async Task DatatypeReferenceInputAndOutputKeepHeapIdentity() {
    const string source = "class Cell {var value:int} datatype Package=Pack(cell:Cell) " +
      "method Entry(package:Package) returns(r:Package) requires package.cell.value==23 ensures r==package {r:=package;}";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reference = new ContractValue(ContractValueKind.Reference, "cell");
    var package = new ContractValue(ContractValueKind.Datatype, Constructor: "Package.Pack",
      Fields: new Dictionary<string, ContractValue> { ["cell"] = reference });
    var request = new ContractTestRequest(1, [new("Wrapper.dfy", source, ContractHarnessBuilder.Hash(source))], new("Entry"),
      new Dictionary<string, ContractValue> { ["package"] = package },
      [new("cell", "Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "23") })]);
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(runtimeReporter, ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);
    Assert.Equal(0, runtimeReporter.ErrorCount);
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition,
      new Dictionary<string, ContractValue> { ["r"] = package }), ContractQueryKind.ObservedPostcondition,
      options, CancellationToken.None, queryName: ContractQueryBuilder.Name(prepared),
      sourceSnapshots: request.Sources, sourcePath: prepared.Source.Path);
    Assert.Equal(ContractQueryOutcome.Unsat, query.Outcome);
  }

  // Native includes and implicit roots share one closed snapshot without duplicate declarations or lost file offsets.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task MultipleSnapshotsPreserveRuntimeAndQueryFiles(bool include) {
    var main = (include ? "include \"Helper.dfy\"\n" : "") +
      "method Entry(x:int) returns(r:int) ensures r==2*x {r:=Transform(x);}";
    const string helper = "function Transform(x:int):int {2*x+1}";
    var directory = Path.Combine(Path.GetTempPath(), "contract-snapshot-" + Guid.NewGuid().ToString("N"));
    IReadOnlyList<ContractSource> sources = [
      new(Path.Combine(directory, "Helper.dfy"), helper, ContractHarnessBuilder.Hash(helper)),
      new(Path.Combine(directory, "Main.dfy"), main, ContractHarnessBuilder.Hash(main))
    ];
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1, sources, new("Entry"),
      new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "2") });
    ContractHarnessBuilder.ValidateRequest(request);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    Assert.Equal(sources[1].Path, prepared.Source.Path);
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(runtimeReporter, ContractHarnessBuilder.RuntimeSources(prepared, request), CancellationToken.None);
    Assert.True(runtimeReporter.ErrorCount == 0, string.Join("\n", runtimeReporter.AllMessages.Select(message => message.Message)));
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request,
      ContractQueryKind.ObservedPostcondition, new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "5") }),
      ContractQueryKind.ObservedPostcondition, options, CancellationToken.None,
      queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: sources, sourcePath: prepared.Source.Path);
    Assert.Equal(ContractQueryOutcome.Sat, query.Outcome);
  }

  // An ambient include outside the supplied closure is rejected even when that file exists on disk.
  [Fact]
  public async Task MissingIncludeCannotReadAmbientFile() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-ambient-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(Path.Combine(directory, "source"));
    try {
      await File.WriteAllTextAsync(Path.Combine(directory, "Ambient.dfy"), "method Ambient() {}");
      const string main = "include \"../Ambient.dfy\" method Entry() {}";
      IReadOnlyList<ContractSource> sources = [new(Path.Combine(directory, "source", "Main.dfy"), main, ContractHarnessBuilder.Hash(main))];
      var options = new DafnyOptions(DafnyOptions.Default);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      var reporter = new BatchErrorReporter(options);
      var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
      Assert.True(reporter.ErrorCount > 0);
      Assert.DoesNotContain(program.DefaultModuleDef.TopLevelDecls.OfType<TopLevelDeclWithMembers>()
        .SelectMany(declaration => declaration.Members), member => member.Name == "Ambient");
    }
    finally {
      Directory.Delete(directory, true);
    }
  }

  // A secondary source cannot enter parsing with missing or mismatched provenance.
  [Theory]
  [InlineData("")]
  [InlineData("wrong")]
  public async Task SecondarySnapshotRequiresExactHash(string hash) {
    const string first = "method Entry() {}";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    await Assert.ThrowsAsync<ArgumentException>(() => ContractSourceSnapshot.ParseAsync(reporter,
      [new("Main.dfy", first, ContractHarnessBuilder.Hash(first)), new("Helper.dfy", "method Helper() {}", hash)], CancellationToken.None));
  }

  // Ambiguous type instantiations cannot be inferred from erased runtime values.
  [Fact]
  public async Task MultipleGenericInstantiationsAreExplicitlyUnsupported() {
    var (prepared, request) = await Prepare("method Child<T>(x:T) {} method Entry(x:int) {Child<int>(x); Child<bool>(true);}");
    Assert.Throws<NotSupportedException>(() => ContractHarnessBuilder.RuntimeSource(prepared, request));
  }

  // A user's diagnostic-looking declaration does not become the selected SMT assertion.
  [Fact]
  public async Task QueryNameCannotCollideWithSourceDeclaration() {
    var (prepared, request) = await Prepare("method ContractDiagnosticQuery() {} method Entry(x:int) returns(r:int) ensures r==x {r:=x+1;}");
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request,
      ContractQueryKind.ObservedPostcondition, new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "3") }),
      ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None,
      queryName: ContractQueryBuilder.Name(prepared));
    Assert.Equal(ContractQueryOutcome.Sat, query.Outcome);
  }

  // Instantiation checks reject a coinductive type that cannot satisfy compiled equality support.
  [Fact]
  public async Task GenericInstantiationRetainsNativeTypeCharacteristics() {
    const string source = "codatatype Stream = More(head:int, tail:Stream) method Entry<T(==)>(x:T) {}";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-generic-characteristic.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    Assert.Throws<ArgumentException>(() => ContractCallableSelector.SelectMethod(program, new ContractEntry("Entry", ["Stream"])));
  }

  // Concrete generic views substitute original contracts while executing the unchanged generic declaration.
  [Theory]
  [InlineData("int", false)]
  [InlineData("bool", false)]
  [InlineData("seq<int>", false)]
  [InlineData("Payload", false)]
  [InlineData("int", true)]
  public async Task ExplicitGenericCallableUsesConcreteDetachedDescriptor(string typeArgument, bool function) {
    var source = "datatype Payload = Full(value:int) " + (function
      ? "function Entry<T>(x:T):T ensures Entry(x) != x {x}"
      : "method Entry<T>(x:T) returns(r:T) ensures r != x {r:=x;}");
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-generic-entry.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var value = typeArgument switch {
      "bool" => new ContractValue(ContractValueKind.Boolean, "true"),
      "seq<int>" => new ContractValue(ContractValueKind.Sequence, Items: [new(ContractValueKind.Integer, "2")]),
      "Payload" => new ContractValue(ContractValueKind.Datatype, Constructor: "Payload.Full",
        Fields: new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "2") }),
      _ => new ContractValue(ContractValueKind.Integer, "2")
    };
    var request = new ContractTestRequest(1, [new("/tmp/contract-generic-entry.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("Entry", [typeArgument]), new Dictionary<string, ContractValue> { ["x"] = value });
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var descriptor = Assert.IsType<ContractConcreteMethod>(prepared.Method);
    Assert.Empty(descriptor.TypeArgs);
    Assert.Single(prepared.Callable.TypeArgs);
    Assert.NotSame(prepared.Callable.Ins[0], descriptor.Ins[0]);
    Assert.Equal(typeArgument, descriptor.Ins[0].Type.ToString());
    var runtimeReporter = new BatchErrorReporter(options);
    _ = await Utils.Parse(runtimeReporter, ContractHarnessBuilder.RuntimeSource(prepared, request),
      uri: new Uri("file:///tmp/contract-generic-runtime.dfy"));
    Assert.True(runtimeReporter.ErrorCount == 0, string.Join("\n", runtimeReporter.AllMessages.Select(message => message.Message)));
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request,
      ContractQueryKind.ObservedPostcondition, new Dictionary<string, ContractValue> { [descriptor.Outs[0].Name] = value }),
      ContractQueryKind.ObservedPostcondition, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, query.Outcome);
    Assert.Single(prepared.Callable.TypeArgs);
  }

  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> Prepare(string source, string symbol = "Entry") {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-function-entry.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1, [new ContractSource("/tmp/contract-function-entry.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractEntry(symbol), new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "2") });
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  // A function's original Q remains a check on the observed result, including unnamed self-result syntax.
  [Theory]
  [InlineData("function Entry(x: int): (r: int) ensures r == x + 1 { x }", "r")]
  [InlineData("function Entry(x: int): int ensures Entry(x) == x + 1 { x }", "contractResult")]
  public async Task FunctionDescriptorChecksOriginalPostcondition(string source, string outputName) {
    var (prepared, request) = await Prepare(source);
    var function = Assert.IsType<Function>(prepared.Callable);
    var originalBody = function.Body;
    var originalEnsures = function.Ens[0].E;
    var outputs = new Dictionary<string, ContractValue> { [outputName] = new(ContractValueKind.Integer, "2") };
    var premise = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.PremiseConsistency),
      ContractQueryKind.PremiseConsistency, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, premise.Outcome);
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs),
      ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, query.Outcome);
    Assert.Same(originalBody, function.Body);
    Assert.Same(originalEnsures, function.Ens[0].E);
    Assert.NotSame(function.Body, prepared.Method.Body);
  }

  // Generation sees a detached by-method implementation rather than a summary call to its logical function.
  [Fact]
  public async Task FunctionDescriptorPreservesByMethodImplementation() {
    var (prepared, _) = await Prepare("function Entry(x: int): int { x } by method { print \"body\"; return x + 7; }");
    var function = Assert.IsType<Function>(prepared.Callable);
    Assert.NotSame(function.ByMethodBody, prepared.Method.Body);
    Assert.Contains(prepared.Method.Body!.Descendants().OfType<PrintStmt>(), _ => true);
    Assert.Equal("contractResult", prepared.Method.Outs.Single().Name);
  }

  // A reachable helper in another source module retains a resolvable local precondition bridge.
  [Fact]
  public async Task RuntimeInstrumentationResolvesAcrossSourceModules() {
    const string source = "module Helpers { function Positive(x:int):int requires x>0 {x} } " +
      "module Caller { import H=Helpers method Entry(x:int) returns(r:int) ensures r==x {r:=H.Positive(x);} }";
    var (prepared, request) = await Prepare(source, "Caller.Entry");
    var reporter = new BatchErrorReporter(prepared.Program.Options);
    _ = await Utils.Parse(reporter, ContractHarnessBuilder.RuntimeSource(prepared, request),
      uri: new Uri("file:///tmp/contract-cross-module-runtime.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
  }

  // Reachable instrumentation executes the outer callable and brackets the actual selected invocation.
  [Theory]
  [InlineData("method Target(y:int) returns(r:int) ensures r==y+1 {return y;}")]
  [InlineData("function Target(y:int):(r:int) requires y>0 ensures r==y+1 {y}")]
  [InlineData("function Target(y:int):int ensures Target(y)==y {y} by method {return y+7;}")]
  public async Task ReachableInvocationInstrumentationResolves(string target) {
    var source = target + " method Outer(x:int) {var r:=Target(x+5); assert false;}";
    var (outer, originalRequest) = await Prepare(source, "Outer");
    var request = originalRequest with { Entry = new ContractEntry("Target", InputMode: ContractInputMode.EntryReachable, ReachableFrom: "Outer") };
    ContractHarnessBuilder.ValidateRequest(request);
    var prepared = ContractHarnessBuilder.Prepare(outer.Program, request);
    Assert.Equal("Outer", prepared.Method.FullDafnyName);
    Assert.Equal("Target", prepared.ReachableTarget!.FullDafnyName);
    var reporter = new BatchErrorReporter(prepared.Program.Options);
    _ = await Utils.Parse(reporter, ContractHarnessBuilder.RuntimeSource(prepared, request),
      uri: new Uri("file:///tmp/contract-reachable-runtime.dfy"));
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // An empty selected body still enters its frame before closing the same captured invocation.
  [Fact]
  public async Task ReachableEmptyBodyKeepsEntryBeforeReturn() {
    var (outer, originalRequest) = await Prepare("method Target(y:int) {} method Outer(x:int) {Target(x);}", "Outer");
    var request = originalRequest with { Entry = new ContractEntry("Target", InputMode: ContractInputMode.EntryReachable, ReachableFrom: "Outer") };
    var prepared = ContractHarnessBuilder.Prepare(outer.Program, request);
    var reporter = new BatchErrorReporter(prepared.Program.Options);
    _ = await Utils.Parse(reporter, ContractHarnessBuilder.RuntimeSource(prepared, request),
      uri: new Uri("file:///tmp/contract-reachable-empty.dfy"));
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // Instance contracts bind implicit this to the exact synthetic receiver and preserve its old heap.
  [Theory]
  [InlineData("method Entry(x: int) returns (r: int) requires value > 0 modifies this ensures value == old(value) + x && r == value { value := value + x; r := value; }")]
  [InlineData("function Entry(x: int): (r: int) requires value > 0 reads this ensures r == value + x { value + x }")]
  public async Task ReceiverContractsUseOriginalObject(string member) {
    var source = "class Cell { var value: int " + member + " }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-receiver-entry.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1, [new("/tmp/contract-receiver-entry.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractEntry("Cell.Entry", Receiver: new(ContractValueKind.Reference, "cell")),
      new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "2") },
      [new("cell", "Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "3") })]);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var premise = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.PremiseConsistency),
      ContractQueryKind.PremiseConsistency, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, premise.Outcome);
    var precondition = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.EntryPrecondition),
      ContractQueryKind.EntryPrecondition, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Unsat, precondition.Outcome);
    var observations = new Dictionary<string, ContractValue> {
      ["$final/cell/value"] = new(ContractValueKind.Integer, prepared.Callable is Function ? "3" : "5")
    };
    var query = await ContractSolver.CheckAsync(ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition,
      new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "5") }, observations: observations),
      ContractQueryKind.ObservedPostcondition, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Unsat, query.Outcome);
  }
}
