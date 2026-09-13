#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractInputTests {
  internal static DafnyOptions Options() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    return options;
  }
  internal static ContractGenerationRequest Request(string source, string symbol = "Entry", int count = 2,
    ContractGenerationBounds? bounds = null) => new(1,
    [new ContractSource("generation.dfy", source, ContractHarnessBuilder.Hash(source))], new ContractEntry(symbol),
    bounds ?? new(MaxInputs: count), TimeoutMilliseconds: 60000);

  // Public generation rejects includes outside the immutable snapshots without consulting ambient files.
  [Fact]
  public async Task PublicGeneratorRejectsAmbientIncludesBeforeResolution() {
    var request = Request("include \"/tmp/contract-generator-absent-" + Guid.NewGuid().ToString("N") + ".dfy\"\nmethod Entry() { }", count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Equal(ContractTestStatus.InvalidInput, result.Status);
    Assert.Empty(result.Inputs);
  }

  // Actual helper bodies from supplied includes participate in the original bounded path query.
  [Fact]
  public async Task ClosedSourceSnapshotsExpandIncludedHelper() {
    var main = "include \"helper.dfy\"\nmethod Entry(x:int) { var t := Transform(x); if t == 17 { assert false; } }";
    var helper = "function Transform(x:int):int { 2*x+1 }";
    var request = Request(main, count: 2) with {
      Sources = [new("/tmp/contract-snapshots/main.dfy", main, ContractHarnessBuilder.Hash(main)),
        new("/tmp/contract-snapshots/helper.dfy", helper, ContractHarnessBuilder.Hash(helper))]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.GoalKind == ContractInputGoalKind.ImplementationPath));
    Assert.Equal("8", input.Request.Inputs["x"].Value);
    Assert.Equal(2, input.Request.Sources.Count);
  }

  // A selected callable in a secondary snapshot inserts every diagnostic query into its own source.
  [Fact]
  public async Task ClosedSourceSnapshotsSelectSecondaryEntry() {
    var main = "include \"helper.dfy\"\nmethod Main() { }";
    var helper = "module Helpers { method Entry(x:int) requires x == 43 { } }";
    var request = Request(main, "Helpers.Entry", count: 1) with {
      Sources = [new("/tmp/contract-secondary/main.dfy", main, ContractHarnessBuilder.Hash(main)),
        new("/tmp/contract-secondary/helper.dfy", helper, ContractHarnessBuilder.Hash(helper))]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Equal("43", Assert.Single(result.Inputs).Request.Inputs["x"].Value);
  }

  // A heap constructor edit retains the included class's source identity instead of a root-file offset.
  [Fact]
  public async Task IncludedHeapConstructorEditRetainsSourceIdentity() {
    var main = "include \"cell.dfy\"\nmethod Entry(c:Cell) { }";
    var cell = "class Cell { var value:int }";
    ContractSource[] sources = [new("/tmp/contract-heap-snapshots/main.dfy", main, ContractHarnessBuilder.Hash(main)),
      new("/tmp/contract-heap-snapshots/cell.dfy", cell, ContractHarnessBuilder.Hash(cell))];
    var reporter = new BatchErrorReporter(Options());
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.False(reporter.HasErrors);
    var request = new ContractTestRequest(1, sources, new("Entry"),
      new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      [new("cell", "Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "0") })]);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    Assert.Equal(ContractSourceSnapshot.UriFor(sources[1].Path), Assert.Single(prepared.Heap!.SourceEdits).SourceUri);
    Assert.Empty(prepared.Heap.SourceInsertions);
  }

  // Datatype constructor fields discover and materialize the concrete referenced heap object.
  [Fact]
  public async Task DatatypeWrapperMaterializesCell() {
    var request = Request("class Cell { var value:int } datatype Package = Pack(cell:Cell) method Entry(package:Package) requires package.cell.value == 23 { }", count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request;
    Assert.Equal("23", Assert.Single(input.Heap!).Fields["value"].Value);
    Assert.Equal(Assert.Single(input.Heap!).Id, input.Inputs["package"].Fields!["cell"].Value);
  }

  // User formal and local names cannot capture generated leaf, body or trace variables.
  [Fact]
  public async Task ScalarDiagnosticNamesAvoidUserDeclarations() {
    var request = Request("function Transform(x:int):int { 2*x+1 } method Entry(contractLeaf0:int,contractExpansion0:int,contractTrace0:int) requires contractLeaf0 == 7 && contractTrace0 == 5 { var contractTraceCount := contractLeaf0; var t := Transform(contractExpansion0); if t == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.GoalKind == ContractInputGoalKind.ImplementationPath));
    Assert.Equal("8", input.Request.Inputs["contractExpansion0"].Value);
    Assert.Equal("7", input.Request.Inputs["contractLeaf0"].Value);
    Assert.NotEmpty(input.Path!.ExpectedBranches);
  }

  // Heap object aliases and fixed-heap variables avoid source formals with the same preferred names.
  [Fact]
  public async Task HeapDiagnosticNamesAvoidUserDeclarations() {
    var request = Request("class Cell { var value:int } method Entry(contractObject0:Cell,contractHeap0:int) requires contractObject0.value == 23 && contractHeap0 == 9 { }", count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Equal("23", Assert.Single(Assert.Single(result.Inputs).Request.Heap!).Fields["value"].Value);
  }

  // Native-call capture names do not shadow real arguments whose names resemble generated slots.
  [Fact]
  public async Task CaptureDiagnosticNamesAvoidUserDeclarations() {
    var request = Request("method Pick(x:int) returns(y:int) ensures y == x+1 method Entry(contractCall0Input0:int,contractCall0Count:int) requires contractCall0Input0 == 16 && contractCall0Count == 0 { var y := Pick(contractCall0Input0); if y == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var choice = Assert.Single(Assert.Single(result.Inputs.Where(input => input.Request.ReplayPrefix)).Request.ReplayChoices!);
    Assert.Equal("17", choice.Outputs!["y"].Value);
  }

  // A user declaration with the preferred query name cannot be selected as the diagnostic procedure.
  [Fact]
  public async Task QueryDiagnosticNameAvoidsUserDeclaration() {
    var request = Request("method ContractDiagnosticQuery() { assert false; } method Entry(x:int) requires x == 37 { }", count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Equal("37", Assert.Single(result.Inputs).Request.Inputs["x"].Value);
  }

  // Substring-shaped method or module names cannot select unrelated obligations through solver wildcards.
  [Theory]
  [InlineData("method OtherContractDiagnosticQuery() { assert false; } method Entry(x:int) requires x == 37 { }")]
  [InlineData("module OtherContractDiagnosticQuery { method Wrong() { assert false; } } method Entry(x:int) requires x == 37 { }")]
  public async Task QueryDiagnosticNameAvoidsSubstringTargets(string source) {
    var result = await ContractInputGenerator.GenerateAsync(Request(source, count: 1), Options(), CancellationToken.None);
    Assert.Equal("37", Assert.Single(result.Inputs).Request.Inputs["x"].Value);
  }

  // Captured generic calls retain the concrete type application required by exact runtime replay.
  [Fact]
  public async Task GenericCapturedCallRetainsConcreteTypeArguments() {
    var request = Request("method Pick<T>(x:T) returns(y:T) ensures y == x method Entry(x:int) requires x == 17 { var y := Pick<int>(x); if y == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var choice = Assert.Single(Assert.Single(result.Inputs.Where(input => input.Request.ReplayPrefix)).Request.ReplayChoices!);
    Assert.Equal("int", Assert.Single(choice.TypeArguments!));
  }

  // An external method is captured as a replayable contract choice instead of becoming a frontier.
  [Fact]
  public async Task ExternalMethodIsCapturedAsContractModel() {
    var request = Request("method {:extern} External() returns(b:bool) ensures b method Entry() { var b := External(); if b { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(item => item.Request.ReplayPrefix)).Request;
    var choice = Assert.Single(input.ReplayChoices!);
    Assert.DoesNotContain(result.Frontier, item => item.Reason == "external_body_requires_actual_expansion");
    Assert.True(input.ReplayPrefix);
    Assert.Equal("true", choice.Outputs!["b"].Value);
  }

  // A bodyful external function's captured SMT choice follows Q instead of its Dafny implementation body.
  [Fact]
  public async Task ExternalFunctionBodyDoesNotConstrainContractChoice() {
    var request = Request("function {:extern} External(x:int):(r:int) ensures r == x+1 { x-1 } method Entry(x:int) { var r := External(x); if r == x+1 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var choice = Assert.Single(Assert.Single(result.Inputs.Where(item => item.Request.ReplayPrefix)).Request.ReplayChoices!);
    var input = System.Numerics.BigInteger.Parse(choice.Inputs["x"].Value!);
    var output = System.Numerics.BigInteger.Parse(choice.Outputs!["r"].Value!);
    Assert.Equal(input + 1, output);
  }

  // Native explicit generic specialization exposes concrete structural types to input generation.
  [Fact]
  public async Task GenericSequenceEntryGeneratesConcreteElementType() {
    var request = Request("method Entry<T>(xs:seq<T>) requires |xs| == 1 { if xs[0] == xs[0] { assert false; } }", count: 1) with {
      Entry = new("Entry", TypeArguments: ["bool"])
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request.Inputs["xs"];
    Assert.Equal(ContractValueKind.Boolean, Assert.Single(input.Items!).Kind);
  }

  // Different legal modeled outputs remain distinct executions when the concrete input is identical.
  [Fact]
  public async Task SameInputRetainsDifferentAbstractChoices() {
    var request = Request("method Pick() returns(b:bool) method Entry(x:int) requires x == 0 { var b := Pick(); if b { assert false; } else { assert false; } }", count: 3);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var choices = result.Inputs.Where(input => input.Request.ReplayPrefix)
      .Select(input => Assert.Single(input.Request.ReplayChoices!).Outputs!["b"].Value).ToHashSet();
    Assert.Equal(2, choices.Count);
    Assert.Contains("true", choices);
    Assert.Contains("false", choices);
    Assert.All(result.Inputs, input => Assert.Equal("0", input.Request.Inputs["x"].Value));
  }

  // Native array models preserve the concrete identity, length and exact element transition.
  [Fact]
  public async Task AbstractArrayTransitionIsCapturedForReplay() {
    var request = Request("method Change(a:array<int>) requires a.Length == 1 modifies a ensures a[0] == old(a[0])+1 method Entry(a:array<int>) requires a.Length == 1 && a[0] == 16 modifies a { Change(a); if a[0] == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.Request.ReplayPrefix));
    var choice = Assert.Single(input.Request.ReplayChoices!);
    Assert.Equal("16", Assert.Single(Assert.Single(choice.PreHeap!).Elements!).Value);
    Assert.Equal("17", Assert.Single(Assert.Single(choice.PostHeap!).Elements!).Value);
    Assert.Equal(1, Assert.Single(Assert.Single(choice.PostHeap!).Dimensions!));
    Assert.Equal("object0", choice.Inputs["a"].Value);
  }

  // A body goal exports the exact native absent-call output needed to reproduce its branch.
  [Fact]
  public async Task AbstractOutputIsCapturedAsReplayPrefix() {
    var request = Request("method Choose(x:int) returns(y:int) ensures y == x || y == x+1 method Entry(x:int) { var y := Choose(x); if y == 17 { assert false; } }", count: 1) with {
      RequiredGoalId = "body0",
      CandidateInputs = new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "16") }
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request;
    var choice = Assert.Single(input.ReplayChoices!);
    Assert.True(input.ReplayPrefix);
    Assert.Equal("16", choice.Inputs["x"].Value);
    Assert.Equal("17", choice.Outputs!["y"].Value);
    Assert.Empty(choice.PreHeap!);
  }

  // A native heap model captures the actual call-state transition used by the selected guard.
  [Fact]
  public async Task AbstractHeapTransitionIsCapturedForReplay() {
    var request = Request("class Cell { var value:int } method Change(c:Cell) modifies c ensures c.value == old(c.value)+1 method Entry(c:Cell) requires c.value == 16 modifies c { Change(c); if c.value == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.Request.ReplayPrefix));
    var choice = Assert.Single(input.Request.ReplayChoices!);
    Assert.Equal("16", Assert.Single(choice.PreHeap!).Fields["value"].Value);
    Assert.Equal("17", Assert.Single(choice.PostHeap!).Fields["value"].Value);
    Assert.Equal("object0", choice.Inputs["c"].Value);
  }

  // Repeated pure calls with the same input and heap emit one memoized runtime choice.
  [Fact]
  public async Task RepeatedPureCallsShareReplayChoice() {
    var request = Request("function Choose(x:int):int ensures Choose(x) == x+1 method Entry(x:int) { var a := Choose(x); var b := Choose(x); if a == 17 && b == 17 { assert false; } }", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.Request.ReplayPrefix));
    Assert.Single(input.Request.ReplayChoices!);
    Assert.Equal("16", input.Request.Inputs["x"].Value);
  }

  // Reachable generation solves the actual outer prefix and retains outer input names.
  [Fact]
  public async Task ReachableGenerationFindsOuterTransformInput() {
    var request = Request("function Transform(x:int):int { 2*x+1 } method Target(value:int) { } method Outer(x:int) { var t := Transform(x); if t == 17 { Target(t); } }", "Target", count: 2) with {
      Entry = new("Target", InputMode: ContractInputMode.EntryReachable, ReachableFrom: "Outer")
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var reached = Assert.Single(result.Inputs.Where(input => input.Path?.ExpectedEntry != null));
    Assert.Equal("8", reached.Request.Inputs["x"].Value);
    Assert.Equal(request.Entry, reached.Request.Entry);
    Assert.Equal("Target", reached.Path!.ExpectedEntry!.Symbol);
    Assert.Contains(result.Frontier, item => item.Id == "spec_reachable_unsupported");
  }

  // The selected second invocation requires reaching the second call through the real outer guard.
  [Fact]
  public async Task ReachableGenerationCountsRequestedInvocation() {
    var request = Request("method Target(value:int) { } method Outer(x:int) { Target(x); if x == 41 { Target(x); } }", "Target", count: 2) with {
      Entry = new("Target", InputMode: ContractInputMode.EntryReachable, ReachableFrom: "Outer", ReachableInvocation: 1),
      GoalKinds = [ContractInputGoalKind.ImplementationPath]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var reached = Assert.Single(result.Inputs.Where(input => input.Path?.ExpectedEntry != null));
    Assert.Equal("41", reached.Request.Inputs["x"].Value);
    Assert.Equal(1, reached.Path!.ExpectedEntry!.Invocation);
  }

  // Progress checkpoints retain rechecked inputs and pending goals when cancellation stops later search.
  [Fact]
  public async Task ProgressCheckpointRetainsInputsOnCancellation() {
    using var cancellation = new CancellationTokenSource();
    ContractGenerationResult? checkpoint = null;
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(x:int) { if x == 31 { assert false; } }", count: 4), Options(), cancellation.Token, async partial => {
        checkpoint = partial;
        await cancellation.CancelAsync();
      });
    Assert.NotNull(checkpoint);
    Assert.Single(checkpoint.Inputs);
    Assert.Equal(ContractTestStatus.Passed, checkpoint.Status);
    Assert.Contains(checkpoint.Goals, goal => goal.Outcome == ContractQueryOutcome.Unknown);
    Assert.Equal(ContractTestStatus.Cancelled, result.Status);
    Assert.Equal(checkpoint.Inputs, result.Inputs);
    Assert.Equal(checkpoint.Counts.InputsGenerated, result.Counts.InputsGenerated);
  }

  // Imported public heap types use the caller's resolved import scope and source alias.
  [Fact]
  public async Task ImportedPublicClassUsesAccessibleAlias() {
    const string source = "module Helpers { class Cell { var value:int } } module Caller { import H=Helpers method Entry(c:H.Cell) requires c.value == 37 { } }";
    var result = await ContractInputGenerator.GenerateAsync(Request(source, "Caller.Entry", count: 1), Options(), CancellationToken.None);
    var cell = Assert.Single(Assert.Single(result.Inputs).Request.Heap!);
    Assert.Equal("Helpers.Cell", cell.Type);
    Assert.Equal("37", cell.Fields["value"].Value);
  }

  // An import that provides only an opaque class cannot expose or synthesize its hidden fields.
  [Fact]
  public async Task ImportedOpaqueClassCannotMaterializeHiddenFields() {
    const string source = "module Helpers { export API provides Cell class Cell { var value:int } } module Caller { import H=Helpers`API method Entry(c:H.Cell) { } }";
    var options = Options();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: ContractSourceSnapshot.UriFor("opaque.dfy"));
    Assert.False(reporter.HasErrors);
    var request = new ContractTestRequest(1, [new("opaque.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("Caller.Entry"), new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      [new("cell", "Helpers.Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "37") })]);
    Assert.Throws<NotSupportedException>(() => ContractHarnessBuilder.Prepare(program, request));
  }

  // Array generation bounds length locally and chooses an element satisfying the original P.
  [Fact]
  public async Task ArrayPreconditionCreatesConcreteElement() {
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(a:array<int>) requires a.Length == 1 && a[0] == 7 { }", count: 1), Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs);
    var array = Assert.Single(input.Request.Heap!);
    Assert.Equal("array<int>", array.Type);
    Assert.Equal(1, Assert.Single(array.Dimensions!));
    Assert.Equal("7", Assert.Single(array.Elements!).Value);
    Assert.Equal(array.Id, input.Request.Inputs["a"].Value);
  }

  // Actual array stores constrain initial element values before the selected branch.
  [Fact]
  public async Task ArrayMutationPathFindsInitialEight() {
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(a:array<int>) returns(r:int) requires a.Length == 1 modifies a { a[0] := 2*a[0]+1; r := if a[0] == 17 then -1 else 0; }", count: 2), Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.GoalKind == ContractInputGoalKind.ImplementationPath));
    Assert.Equal("8", Assert.Single(Assert.Single(input.Request.Heap!).Elements!).Value);
  }

  // Empty arrays retain their length observation even though there are no mutable element cells.
  [Fact]
  public async Task EmptyArrayRemainsAConcreteHeapObject() {
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(a:array<int>) requires a.Length == 0 { }", count: 1), Options(), CancellationToken.None);
    var array = Assert.Single(Assert.Single(result.Inputs).Request.Heap!);
    Assert.Equal(0, Assert.Single(array.Dimensions!));
    Assert.Empty(array.Elements!);
  }

  // Shared array arguments materialize one identity, preserving aliases in the original P.
  [Fact]
  public async Task ArrayPreconditionPreservesAlias() {
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(a:array<int>,b:array<int>) requires a == b && a.Length == 1 && a[0] == 9 { }", count: 1), Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request;
    Assert.Single(input.Heap!);
    Assert.Equal(input.Inputs["a"].Value, input.Inputs["b"].Value);
  }

  // Same-case reduction rechecks exact array elements rather than accepting the old generated path.
  [Fact]
  public async Task ArrayCandidateRechecksChangedElement() {
    var request = Request("method Entry(a:array<int>) requires a.Length == 1 modifies a { a[0] := 2*a[0]+1; if a[0] == 17 { assert false; } }", count: 1) with {
      RequiredGoalId = "body0",
      CandidateInputs = new Dictionary<string, ContractValue> { ["a"] = new(ContractValueKind.Reference, "object0") },
      CandidateHeap = [new("object0", "array<int>", new Dictionary<string, ContractValue>(), [1], [new(ContractValueKind.Integer, "7")])]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.BoundedUnsat > 0);
  }

  // Receiver fields participate in P and actual bodies before the entry reference is materialized.
  [Fact]
  public async Task ReceiverFieldConstrainsActualBranchInput() {
    var request = Request("class Cell { var value:int method Entry(x:int) returns(r:int) requires value == 5 modifies this { value := value + x; r := if value == 13 then -1 else 0; } }", "Cell.Entry", count: 2);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs.Where(input => input.GoalKind == ContractInputGoalKind.ImplementationPath));
    Assert.Equal("8", input.Request.Inputs["x"].Value);
    var receiver = Assert.Single(input.Request.Heap!);
    Assert.Equal(receiver.Id, input.Request.Entry.Receiver!.Value);
    Assert.Equal("5", receiver.Fields["value"].Value);
  }

  // Candidate rechecks preserve the chosen receiver instead of switching to another satisfying heap root.
  [Fact]
  public async Task ReceiverCandidateKeepsExactRootIdentity() {
    var request = Request("class Cell { var value:int method Entry() requires value == 5 { } }", "Cell.Entry", count: 1) with {
      Entry = new ContractEntry("Cell.Entry", Receiver: new(ContractValueKind.Reference, "object1")),
      RequiredGoalId = "precondition",
      CandidateInputs = new Dictionary<string, ContractValue>(),
      CandidateHeap = [
        new("object0", "Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "5") }),
        new("object1", "Cell", new Dictionary<string, ContractValue> { ["value"] = new(ContractValueKind.Integer, "0") })
      ]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.BoundedUnsat > 0);
  }

  // Input-only old(this.field) cases can be generated even when the instance body omitted its guard.
  [Fact]
  public async Task ReceiverSpecificationFindsMissingGuard() {
    var request = Request("class Cell { var value:int method Entry() returns(r:int) ensures if old(value) == 42 then r == 1 else r == 0 { r := 0; } }", "Cell.Entry", count: 2)
      with { GoalKinds = [ContractInputGoalKind.Precondition, ContractInputGoalKind.SpecificationCase] };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Contains(result.Inputs, input => input.GoalKind == ContractInputGoalKind.SpecificationCase &&
      Assert.Single(input.Request.Heap!).Fields["value"].Value == "42");
  }

  // Selecting the baseline source spends its budget only on P, preserving the unique goal denominator.
  [Fact]
  public async Task BaselineGoalSelectionExcludesOtherSources() {
    var request = Request("method Entry(s:seq<int>) returns(r:int) ensures if |s| == 1 then r == 1 else r == 0 { r := 0; }", count: 3)
      with { GoalKinds = [ContractInputGoalKind.Precondition] };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.All(result.Inputs, input => Assert.Equal(ContractInputGoalKind.Precondition, input.GoalKind));
    Assert.Equal(1, result.Counts.GoalsDiscovered);
    Assert.Equal(1, result.Counts.GoalsAttempted);
  }

  // A later branch records earlier decisions so an unrelated route cannot certify the same target.
  [Fact]
  public async Task GeneratedPathCapturesOrderedGuardPrefix() {
    const string source = "method Entry(x:int) returns(r:int) { r := 0; if x > 0 { r := 1; } if x == 8 { r := -1; } }";
    var request = Request(source, count: 1) with {
      CandidateInputs = new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "8") },
      RequiredGoalId = "body2"
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var trace = Assert.Single(result.Inputs).Path!;
    Assert.Equal(new[] { source.IndexOf("x > 0", StringComparison.Ordinal), source.IndexOf("x == 8", StringComparison.Ordinal) },
      trace.ExpectedBranches.Select(branch => branch.Position));
    Assert.All(trace.ExpectedBranches, branch => Assert.True(branch.Value));
  }

  // Actual uncontracted helper arithmetic must constrain the input of a failing branch.
  [Fact]
  public async Task UncontractedHelperFindsEight() {
    var result = await ContractInputGenerator.GenerateAsync(Request("""
      method Transform(x: int) returns (t: int) { t := 2 * x + 1; }
      method Entry(x: int) returns (r: int) ensures r >= 0 {
        var t := Transform(x);
        r := if t == 17 then -1 else 0;
      }
      """), Options(), CancellationToken.None);
    Assert.Equal(ContractTestStatus.Passed, result.Status);
    Assert.Contains(result.Inputs, input => input.Request.Inputs["x"].Value == "8" &&
      input.GoalKind == ContractInputGoalKind.ImplementationPath);
  }

  // A contradictory postcondition must not remove valid inputs from the independent P source.
  [Fact]
  public async Task ContradictoryPostconditionRetainsBaselineInput() {
    var result = await ContractInputGenerator.GenerateAsync(Request(
      "method Entry(x:int) returns(r:int) ensures false { r := x; }", count: 1), Options(), CancellationToken.None);
    Assert.Single(result.Inputs);
    Assert.Equal(ContractInputGoalKind.Precondition, result.Inputs[0].GoalKind);
  }

  // Specification branches remain input objectives even when the implementation omitted their branch.
  [Fact]
  public async Task MissingImplementationBranchHasSpecificationInput() {
    var request = Request("""
      method Entry(x:int) returns(r:int)
        ensures if x == 42 then r == 1 else r == 0
      { r := 0; }
      """, count: 4);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Contains(result.Inputs, input => input.Request.Inputs["x"].Value == "42" &&
      input.GoalKind == ContractInputGoalKind.SpecificationCase);
  }

  // Sequence generation introduces local structural bounds and materializes model-selected elements.
  [Fact]
  public async Task SequencePreconditionCreatesNonemptyConcreteSequence() {
    var request = Request("method Entry(s:seq<int>) requires |s| == 1 && s[0] == 7 { }", count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs);
    Assert.Equal("7", Assert.Single(input.Request.Inputs["s"].Items!).Value);
  }

  // Datatype constructors are obtained from the resolved type rather than a domain-specific factory.
  [Fact]
  public async Task DatatypePreconditionCreatesConstructorAndField() {
    var request = Request("""
      datatype Choice = Empty | Full(value:int)
      method Entry(c:Choice) requires c.Full? && c.value == 9 { }
      """, count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request.Inputs["c"];
    Assert.Equal("Choice.Full", input.Constructor);
    Assert.Equal("9", input.Fields!["value"].Value);
  }

  // A shrinking candidate outside the original selected branch is rejected by the same goal.
  [Fact]
  public async Task CandidateRecheckRejectsChangedBranch() {
    var request = Request("method Entry(x:int) returns(r:int) { r := if x == 8 then 1 else 0; }", count: 1) with {
      CandidateInputs = new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "7") },
      RequiredGoalId = "body0"
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.BoundedUnsat > 0);
  }

  // General object arguments are generated with alias identity and constrained mutable fields.
  [Fact]
  public async Task HeapPreconditionCreatesSharedReference() {
    var request = Request("""
      class Cell { var value:int }
      method Entry(a:Cell,b:Cell) requires a == b && a.value == 11 { }
      """, count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request;
    Assert.Equal(input.Inputs["a"], input.Inputs["b"]);
    Assert.Equal("11", Assert.Single(input.Heap!).Fields["value"].Value);
  }

  // Separate object slots satisfy nonaliasing requirements without an injected domain constructor.
  [Fact]
  public async Task HeapPreconditionCreatesDistinctObjects() {
    var request = Request("""
      class Cell { var value:int }
      method Entry(a:Cell,b:Cell) requires a != b && a.value == 3 && b.value == 4 { }
      """, count: 1);
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    var input = Assert.Single(result.Inputs).Request;
    Assert.NotEqual(input.Inputs["a"].Value, input.Inputs["b"].Value);
    Assert.Equal(2, input.Heap!.Count);
  }

  // A function entry receives generated arguments from its actual expression body.
  [Fact]
  public async Task FunctionEntryFindsItsFailingBranch() {
    var result = await ContractInputGenerator.GenerateAsync(Request("""
      function Entry(x:int):int
        ensures Entry(x) >= 0
      { if x == 8 then -1 else 0 }
      """), Options(), CancellationToken.None);
    Assert.Contains(result.Inputs, input => input.Request.Inputs["x"].Value == "8");
  }

  // Heap shrinking cannot omit a field and let the solver choose a replacement initial value.
  [Fact]
  public async Task CandidateHeapRejectsMissingFields() {
    var request = Request("class Cell { var x:int var y:int } method Entry(c:Cell) { }", count: 1) with {
      RequiredGoalId = "precondition",
      CandidateInputs = new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "object0") },
      CandidateHeap = [new("object0", "Cell", new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "0") })]
    };
    var result = await ContractInputGenerator.GenerateAsync(request, Options(), CancellationToken.None);
    Assert.Equal(ContractTestStatus.InvalidInput, result.Status);
    Assert.Empty(result.Inputs);
  }
}
