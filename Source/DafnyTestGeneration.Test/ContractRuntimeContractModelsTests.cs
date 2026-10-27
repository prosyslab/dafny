#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeContractModelsTests {
  private const string Source = """
    module M {
      class Device {
        ghost var count: int
        ghost var ready: bool
        ghost predicate Valid() reads this { count == 1 && !ready }
        method {:extern} {:axiom} Step(x: int) returns (y: int)
          requires !ready
          modifies this
          ensures count == old(count) + x && ready && y == count
      }
      method Goal(device: Device, x: int) returns (y: int)
        requires device.Valid()
        modifies device
        ensures y == 99
      { y := device.Step(x); }
    }
    """;
  private const string Generator = """
    method {:pbt_generator "M.Goal"}
      {:pbt_heap_constructor "M.Device", "M.Device.count", "M.Device.ready"}
      Generate(r: PbtRandom.Source) returns (device: Device, x: int) {
      device := new Device.ContractDiagnosticCreate(0, false);
      x := 1;
    }
    method {:pbt_contract_models "M.Goal", 0, 3, 64} ModelPolicy() {}
    """;

  // The source-only policy accepts explicit signed bounds without requiring a resolver or solver.
  [Fact]
  public async Task ReadsSignedFinitePolicyFromGeneratorPacket() {
    var policy = await ContractRuntimeContractModels.ReadPolicyAsync(
      Snapshot("Generator.dfy", Generator.Replace("0, 3, 64", "-2, 2, 64")), "M.Goal", Options(), CancellationToken.None);
    Assert.Equal(new ContractRuntimeContractModelPolicy("M.Goal", -2, 2, 64), policy);
  }

  // An agent can opt in through the editable helper region while native authoring preserves the original target contract.
  [Fact]
  public async Task ExtractsPolicyAddedInEditableGeneratorHelpers() {
    var options = Options();
    const string marker = "method {:pbt_contract_models \"M.Goal\", 0, 3, 64} ModelPolicy() {}";
    var request = new ContractRuntimeAuthoringRequest(ContractRuntimeSourceAuthoring.NativeSchemaVersion,
      ContractRuntimeAuthoringAction.Prepare, [Snapshot("M.dfy", Source)], new("M.Goal"),
      Generator: Snapshot(".top-down-pbt/generators/M.Goal.dfy", Generator.Replace(marker, "")), ExternExecution: ContractRuntimeExternExecution.Native);
    var prepared = await ContractRuntimeSourceAuthoring.RunAsync(request, options, CancellationToken.None);
    Assert.Equal(ContractRuntimeAuthoringStatus.Ready, prepared.Status);
    var view = await Parse(options, prepared.Sources!);
    var end = Assert.Single(view.RawModules().SelectMany(module => module.TopLevelDecls).OfType<DatatypeDecl>()
      .Where(declaration => declaration.Name.StartsWith("PbtAuthoringEnd_", StringComparison.Ordinal)));
    var authored = prepared.Sources!.Select(source => {
      if (source.Path != "M.dfy") { return source; }
      var offset = source.Content.IndexOf("datatype " + end.Name, StringComparison.Ordinal);
      return Snapshot(source.Path, source.Content.Insert(offset, marker + "\n"));
    }).ToArray();
    var extracted = await ContractRuntimeSourceAuthoring.RunAsync(request with {
      Action = ContractRuntimeAuthoringAction.Extract,
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    }, options, CancellationToken.None);
    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, extracted.Status);
    var policy = await ContractRuntimeContractModels.ReadPolicyAsync(extracted.Generator, "M.Goal", options, CancellationToken.None);
    Assert.Equal(new ContractRuntimeContractModelPolicy("M.Goal", 0, 3, 64), policy);
    Assert.Empty(extracted.Drafts!);
  }

  // An executable policy helper cannot hide work behind its configuration attribute.
  [Fact]
  public async Task RejectsNonemptyPolicyHelper() {
    await Assert.ThrowsAsync<NotSupportedException>(() => ContractRuntimeContractModels.ReadPolicyAsync(
      Snapshot("Generator.dfy", Generator.Replace("ModelPolicy() {}", "ModelPolicy() { assert true; }")),
      "M.Goal", Options(), CancellationToken.None));
  }

  // Model initialization and transitions resolve as executable assignments while the target body still calls its wrapper.
  [Fact]
  public async Task GeneratesResolvedInitialAndTransitionAssignments() {
    var (program, transformation) = await Transform();
    var main = Methods(program).Single(method => method.FullDafnyName == transformation.MainName);
    var calls = main.Body!.Descendants().OfType<CallStmt>().Distinct().ToList();
    var initialized = Assert.Single(calls.Where(call => call.Method.Name == "FindModel"));
    Assert.True(calls.FindIndex(call => call.Method.Name == "SetModelRandom") < calls.IndexOf(initialized));
    Assert.True(calls.IndexOf(initialized) < calls.FindIndex(call => call.Method.Name == "Generated"));
    var initialFields = main.Body.Descendants().OfType<SingleAssignStmt>()
      .Select(statement => statement.Lhs.Resolved).OfType<MemberSelectExpr>().Select(select => select.Member.Name).ToHashSet();
    Assert.True(initialFields.SetEquals(["count", "ready"]));

    var target = Methods(program).Single(method => method.FullDafnyName == "M.Goal");
    var targetCall = Assert.Single(target.Body!.Descendants().OfType<CallStmt>().Distinct());
    Assert.NotEqual("Step", targetCall.Method.Name);
    var wrapper = Assert.IsType<Method>(targetCall.Method);
    var transition = Assert.Single(wrapper.Body!.Descendants().OfType<CallStmt>().Distinct()
      .Where(call => call.Method.Name == "FindModel"));
    Assert.DoesNotContain(wrapper.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "Step");
    Assert.Equal(3, Assert.IsType<SeqDisplayExpr>(transition.Args[0].Resolved).Elements.Count);
    Assert.False(transformation.EntryRequiresOmitted);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition);
    Assert.Contains(transformation.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.CalleePostcondition);
  }

  // A target's deliberately false postcondition remains a check and never narrows the generated candidate domain.
  [Fact]
  public async Task DoesNotUseTargetEnsuresAsModelConstraints() {
    var (program, _) = await Transform();
    var searches = Methods(program).Where(method => method.Body != null)
      .SelectMany(method => method.Body!.Descendants().OfType<CallStmt>()).Distinct()
      .Where(call => call.Method.Name == "FindModel").ToList();
    Assert.Equal(2, searches.Count);
    Assert.All(searches, call => Assert.DoesNotContain(call.Args[4].Descendants().OfType<LiteralExpr>(),
      literal => literal.Value is BigInteger value && value == 99));
  }

  // Old-state captures are evaluated before candidate search and before any modeled field is committed.
  [Fact]
  public async Task CapturesOldStateBeforeTransitionSearch() {
    var (program, _) = await Transform();
    var wrapper = Methods(program).Single(method => method.Body != null && method.EnclosingClass.Name == "Device" &&
      method.Body.Descendants().OfType<CallStmt>().Any(call => call.Method.Name == "FindModel"));
    var assignments = wrapper.Body!.Descendants().OfType<SingleAssignStmt>().Distinct().ToList();
    var captures = assignments.Where(assignment => assignment.Lhs.Resolved is IdentifierExpr &&
      assignment.Rhs is ExprRhs { Expr.Resolved: MemberSelectExpr }).ToList();
    var search = Assert.Single(wrapper.Body.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "FindModel"));
    Assert.True(captures.Count >= 2);
    Assert.All(captures, capture => Assert.True(capture.Origin.pos < search.Origin.pos));
    Assert.All(assignments.Where(assignment => assignment.Lhs.Resolved is MemberSelectExpr),
      assignment => Assert.True(search.Origin.pos < assignment.Origin.pos));
    Assert.DoesNotContain(search.Args[4].Descendants().OfType<MemberSelectExpr>(), select => select.Member is Field);
  }

  // An undeclared frame leaves ghost fields frozen rather than adding them to the transition search vector.
  [Fact]
  public async Task EmptyExternFrameDoesNotCommitGhostFields() {
    var source = Source.Replace("modifies this", "").Replace("count == old(count) + x && ready && y == count", "y == count");
    var (program, _) = await Transform(source);
    var wrapper = Methods(program).Single(method => method.Body != null && method.EnclosingClass.Name == "Device" &&
      method.Body.Descendants().OfType<CallStmt>().Any(call => call.Method.Name == "FindModel"));
    var search = Assert.Single(wrapper.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "FindModel"));
    Assert.Single(Assert.IsType<SeqDisplayExpr>(search.Args[0].Resolved).Elements);
    Assert.DoesNotContain(wrapper.Body.Descendants().OfType<SingleAssignStmt>(), assignment => assignment.Lhs.Resolved is MemberSelectExpr);
  }

  // A quantified clause rejects the complete requested model instead of silently dropping a conjunct.
  [Fact]
  public async Task RejectsQuantifiedInitialPredicate() {
    await Assert.ThrowsAsync<NotSupportedException>(() => Transform(Source.Replace("count == 1 && !ready",
      "count == 1 && (forall n: int :: n == n)")));
  }

  // Recursive logical definitions are not expanded into a general-purpose symbolic engine.
  [Fact]
  public async Task RejectsRecursiveInitialPredicate() {
    await Assert.ThrowsAsync<NotSupportedException>(() => Transform(Source.Replace("count == 1 && !ready", "Valid()")));
  }

  // Repeated finite calls in argument positions are not recursive definitions, and signed arithmetic remains executable.
  [Fact]
  public async Task UnfoldsNestedScalarCallsAndNegativeArithmetic() {
    var source = Source.Replace("ghost predicate Valid()", "function Inc(n:int):int { n + 1 } ghost predicate Valid()")
      .Replace("count == 1 && !ready", "count == Inc(Inc(-2)) && !ready");
    var (program, _) = await Transform(source);
    var main = Methods(program).Single(method => method.Name.StartsWith("PbtMain", StringComparison.Ordinal));
    Assert.Single(main.Body!.Descendants().OfType<CallStmt>().Distinct().Where(call => call.Method.Name == "FindModel"));
  }

  // A short acyclic definition chain cannot expand substituted arguments into unbounded generated source text.
  [Fact]
  public async Task RejectsExponentialAcyclicPredicateText() {
    var nested = Enumerable.Range(0, 20).Aggregate("1", (argument, _) => "Dup(" + argument + ")");
    var source = Source.Replace("ghost predicate Valid()", "function Dup(n:int):int { n + n } ghost predicate Valid()")
      .Replace("count == 1 && !ready", "count == " + nested + " && !ready");
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Transform(source));
    Assert.Contains("rendered model predicate exceeds 65536 UTF-8 bytes", error.Message);
  }

  // Full model validation waits until the authored concrete target body has been installed and resolved.
  [Fact]
  public async Task SupportsAuthoredBodyForOriginallyBodylessTarget() {
    const string body = "method {:pbt_draft \"M.Goal\"} Goal(device:Device, x:int) returns(y:int) { y:=device.Step(x); }";
    var draft = new ContractRuntimeDraft("M.Goal", "GoalDraft.dfy", body, ContractHarnessBuilder.Hash(body));
    var (program, _) = await Transform(Source.Replace("{ y := device.Step(x); }", ""), draft: draft, selectedDrafts: true);
    var goal = Methods(program).Single(method => method.FullDafnyName == "M.Goal");
    Assert.Single(goal.Body!.Descendants().OfType<CallStmt>().Distinct());
  }

  // A missing target packet remains missing work rather than becoming a model-plan rejection during draft closure.
  [Fact]
  public async Task LeavesUnregisteredBodylessTargetForMissingDraftClassification() {
    var options = Options();
    var sources = new[] { Snapshot("M.dfy", Source.Replace("{ y := device.Step(x); }", "")) };
    var original = await Parse(options, sources);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var prepared = await ContractRuntimeSelectedDraftPreparation.PrepareAsync(original, sources, goal, [],
      Snapshot("Generator.dfy", Generator), false, options, CancellationToken.None,
      externExecution: ContractRuntimeExternExecution.Native);
    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    Assert.Null(Methods(prepared.Runtime.RuntimeProgram).Single(method => method.FullDafnyName == "M.Goal").Body);
  }

  // A reference returned by another declaration cannot substitute a different object for the selected receiver.
  [Fact]
  public async Task RejectsForeignReferenceReturnedByFunction() {
    var source = Source.Replace("method Goal(device:", "function {:axiom} Foreign(): Device method Goal(device:")
      .Replace("y := device.Step(x)", "y := Foreign().Step(x)");
    await Assert.ThrowsAsync<NotSupportedException>(() => Transform(source));
  }

  // Joint state/output cardinality is checked before any diagnostic compilation or sample execution.
  [Fact]
  public async Task RejectsTransitionDomainBeyondDeclaredCap() {
    await Assert.ThrowsAsync<NotSupportedException>(() => Transform(generator: Generator.Replace("0, 3, 64", "0, 3, 8")));
  }

  // A generator must finish constructing its receiver before the harness initializes and exposes model state.
  [Fact]
  public async Task RejectsGeneratorObservingUninitializedModelState() {
    await Assert.ThrowsAsync<NotSupportedException>(() => Transform(generator: Generator.Replace("x := 1;", "ghost var observed := device.count; x := 1;")));
  }

  // A task-owned marker is inert unless the harness supplies the generator-packet policy explicitly.
  [Fact]
  public async Task TaskSourceMarkerDoesNotActivateTransformer() {
    var options = Options();
    var text = "module M { import PbtRandom class Device { ghost var count:int } " +
      "method Goal(device:Device) {} method Generate(r:PbtRandom.Source) returns(device:Device) { device:=new Device; } " +
      "method {:pbt_contract_models \"M.Goal\",0,2,8} ModelPolicy() {} }";
    var sources = new[] { Snapshot("M.dfy", text), Snapshot("PbtRuntime.dfy", ContractRuntimeInstrumentation.DafnySource) };
    var program = await Parse(options, sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var transformed = new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
    var compiled = await Parse(options, transformed.Sources);
    var main = Methods(compiled).Single(method => method.FullDafnyName == transformed.MainName);
    Assert.DoesNotContain(main.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "FindModel");
  }

  // Every test uses bounded immutable source dictionaries; no compiler, native prover or filesystem test fixture is invoked.
  private static async Task<(Program Program, ContractRuntimeTransformation Transformation)> Transform(
    string source = Source, string generator = Generator, ContractRuntimeDraft? draft = null, bool selectedDrafts = false) {
    var options = Options();
    var sources = new[] { Snapshot("M.dfy", source) };
    var original = await Parse(options, sources);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Goal"), requireConcreteReceiver: false);
    var packet = Snapshot("Generator.dfy", generator);
    var policy = await ContractRuntimeContractModels.ReadPolicyAsync(packet, goal.FullDafnyName, options, CancellationToken.None);
    ContractRuntimePreparedSources prepared;
    IReadOnlyList<ContractSource> runtimeSources;
    Program runtime;
    if (selectedDrafts) {
      var selectedPreparation = await ContractRuntimeSelectedDraftPreparation.PrepareAsync(original, sources, goal,
        draft == null ? [] : [draft], packet, false, options, CancellationToken.None,
        externExecution: ContractRuntimeExternExecution.Native);
      prepared = selectedPreparation.Preparation;
      runtimeSources = selectedPreparation.Runtime.RuntimeSources;
      runtime = selectedPreparation.Runtime.RuntimeProgram;
      Assert.Contains(goal.FullDafnyName, prepared.InstalledDraftSymbols);
    } else {
      prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, goal, draft == null ? [] : [draft], packet,
        options, CancellationToken.None, ContractRuntimeExternExecution.Native);
      runtimeSources = prepared.Sources.Append(Snapshot("PbtRuntime.dfy", ContractRuntimeInstrumentation.DafnySource)).ToArray();
      runtime = await Parse(options, runtimeSources, deferred: true);
    }
    goal = ContractCallableSelector.SelectMethod(runtime, new("M.Goal"), requireConcreteReceiver: false);
    var selected = ContractRuntimeGeneratorSignature.Select(runtime, goal, prepared.GeneratorMethodName);
    ContractDiagnosticConstruction.AuditResolved(runtime, goal, selected, prepared.DiagnosticConstructors!);
    var transformed = new ContractRuntimeObligationTransformer(runtime, runtimeSources, goal, prepared.SourceMap,
      diagnosticConstructors: prepared.DiagnosticConstructors, selectedGenerator: selected, contractModelPolicy: policy).Transform();
    return (await Parse(options, transformed.Sources), transformed);
  }

  private static IEnumerable<Method> Methods(Program program) => ContractRuntimeObligationTransformer.Members(program).OfType<Method>();
  private static ContractSource Snapshot(string path, string content) => new(path, content, ContractHarnessBuilder.Hash(content));

  private static async Task<Program> Parse(DafnyOptions options, IReadOnlyList<ContractSource> sources, bool deferred = false) {
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None,
      deferredGhostDiagnostics: deferred ? new List<DafnyDiagnostic>() : null);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return program;
  }

  private static DafnyOptions Options() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null) {
      TheProverFactory = new NoProverFactory()
    };
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.XmlSink = null;
    options.DafnyPrintFile = null;
    options.DafnyPrintResolvedFile = null;
    options.AutoReqPrintFile = null;
    options.DafnyPrintExportedViews = [];
    options.AdditionalPlugins = [];
    options.AdditionalPluginArguments = [];
    options.PrintIncludesMode = DafnyOptions.IncludesModes.None;
    options.PrintStats = false;
    options.PrintFunctionCallGraph = false;
    return options;
  }

  private sealed class NoProverFactory : Microsoft.Boogie.ProverFactory {
    public override Microsoft.Boogie.ProverInterface SpawnProver(Microsoft.Boogie.SMTLibOptions options,
      Microsoft.Boogie.ProverOptions proverOptions, object context) => throw new InvalidOperationException("Model source tests cannot spawn a prover.");
    public override Microsoft.Boogie.ProverContext NewProverContext(Microsoft.Boogie.ProverOptions options) =>
      throw new InvalidOperationException("Model source tests cannot create a prover context.");
  }
}
