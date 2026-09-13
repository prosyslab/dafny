#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test;

public class ContractModelRealizerTests {
  private readonly ITestOutputHelper output;

  public ContractModelRealizerTests(ITestOutputHelper output) {
    this.output = output;
  }

  private static ContractValue Integer(string value) => new(ContractValueKind.Integer, value);

  // Original generic relations are instantiated only from resolved calls or explicit selected-entry types.
  [Theory]
  [InlineData(false, false)]
  [InlineData(true, false)]
  [InlineData(false, true)]
  public async Task GenericAbsentRelationUsesSourceTypeEvidence(bool function, bool entry) {
    var declaration = function ? "function Missing<T>(x:T):T ensures Missing(x)==x " :
      "method Missing<T>(x:T) returns(r:T) ensures r==x ";
    var source = declaration + "method Entry(x:int) { var r:=Missing<int>(x); }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-generic-model.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var inputs = new Dictionary<string, ContractValue> { ["x"] = Integer("7") };
    var request = new ContractTestRequest(1, [new("/tmp/contract-generic-model.dfy", source, ContractHarnessBuilder.Hash(source))],
      new(entry ? "Missing" : "Entry", entry ? ["int"] : null), inputs);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    Assert.Equal("int", prepared.ConcreteCalls["Missing"].ConcreteTypeArguments.Single().ToString());
    var result = await ContractModelRealizer.RealizeAsync(prepared, request, "Missing", inputs, CancellationToken.None);
    Assert.True(result.Status == ContractRealizationStatus.Realized, result.Reason + "\n" +
      string.Join("\n", result.Queries.Select(query => query.Diagnostics)));
    Assert.Equal(Integer("7"), result.Outputs![function ? "contractResult" : "r"]);
    var replay = await ContractModelRealizer.RealizeAsync(prepared, request, "Missing", inputs, CancellationToken.None,
      replayOutputs: result.Outputs);
    Assert.Equal(ContractRealizationStatus.Realized, replay.Status);
  }

  private async Task<ContractRealizationResult> Realize(string declaration,
    IReadOnlyDictionary<string, ContractValue> inputs, string child = "Missing",
    IReadOnlyList<ContractAbstractChoice>? choices = null,
    IReadOnlyDictionary<string, ContractValue>? replayOutputs = null, bool preconditionOnly = false,
    IReadOnlyList<ContractHeapObject>? heap = null, IReadOnlyList<ContractHeapObject>? currentHeap = null,
    IReadOnlyList<ContractHeapObject>? replayHeap = null, ContractValue? receiver = null) {
    var source = "module ModelContract {\n" + declaration + "\nmethod Entry() {}\n}\n";
    var sourceSnapshot = new ContractSource("ModelContract.dfy", source, ContractHarnessBuilder.Hash(source));
    var request = new ContractTestRequest(1, [sourceSnapshot], new ContractEntry("ModelContract.Entry"),
      new Dictionary<string, ContractValue>(), Heap: heap);
    var writer = new StringWriter();
    var options = DafnyOptions.CreateUsingOldParser(writer, TextReader.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var reporter = new BatchErrorReporter(options);
    using var deadline = new CancellationTokenSource(TimeSpan.FromSeconds(40));
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, deadline.Token);
    Assert.Equal(0, reporter.ErrorCount);
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var result = preconditionOnly
      ? await ContractModelRealizer.CheckPreconditionAsync(prepared, request, "ModelContract." + child,
        inputs, deadline.Token, choices)
      : await ContractModelRealizer.RealizeAsync(prepared, request, "ModelContract." + child,
        inputs, deadline.Token, choices, replayOutputs, currentHeap ?? heap, replayHeap, receiver);
    if (result.Status is not ContractRealizationStatus.Realized) {
      output.WriteLine(result.Reason);
      output.WriteLine(string.Join("\n", result.Queries.Select(query => query.Kind + ": " + query.Outcome + "\n" + query.Diagnostics)));
    }
    return result;
  }

  // Produces the constrained arithmetic output rather than a type default.
  [Fact]
  public async Task RealizesDeterministicAbsentMethod() {
    var result = await Realize("method Missing(x: int) returns (r: int) ensures r == x + 7",
      new Dictionary<string, ContractValue> { ["x"] = Integer("6") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("13"), result.Outputs!["r"]);
    Assert.False(result.TypeFrameOnly);
  }

  // An external method's implementation body is ignored while its original P/Q selects the result.
  [Fact]
  public async Task RealizesExternalMethodContractInsteadOfBody() {
    var result = await Realize("method {:extern} Missing(x:int) returns(r:int) requires x > 0 ensures r == x+7 { r := -1; }",
      new Dictionary<string, ContractValue> { ["x"] = Integer("6") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("13"), result.Outputs!["r"]);
  }

  // An external function is realized from its declared relation like an absent pure function.
  [Fact]
  public async Task RealizesExternalFunctionContract() {
    const string declaration = "function {:extern} Missing(x:int):(r:int) ensures r == x+1 { x-1 }";
    var result = await Realize(declaration,
      new Dictionary<string, ContractValue> { ["x"] = Integer("6") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("7"), result.Outputs!["r"]);
    var replay = await Realize(declaration,
      new Dictionary<string, ContractValue> { ["x"] = Integer("6") }, replayOutputs: result.Outputs);
    Assert.Equal(ContractRealizationStatus.Realized, replay.Status);
    Assert.Equal(Integer("7"), replay.Outputs!["r"]);
  }

  // An external call whose fixed input violates P stops before selecting an output model.
  [Fact]
  public async Task RejectsExternalMethodPreconditionViolation() {
    var result = await Realize("method {:extern} Missing(x:int) returns(r:int) requires x > 0 ensures r == x+1",
      new Dictionary<string, ContractValue> { ["x"] = Integer("0") });
    Assert.Equal(ContractRealizationStatus.CallPreconditionViolation, result.Status);
    Assert.Null(result.Outputs);
  }

  // A contradictory external postcondition is reported as an inconsistent contract.
  [Fact]
  public async Task RejectsInconsistentExternalMethodContract() {
    var result = await Realize("method {:extern} Missing() returns(r:int) ensures false",
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.InconsistentContract, result.Status);
    Assert.Null(result.Outputs);
  }

  // Preserves solver integers outside machine integer ranges.
  [Fact]
  public async Task PreservesArbitraryPrecisionOutput() {
    const string number = "123456789012345678901234567890123456789";
    var result = await Realize("method Missing() returns (r: int) ensures r == " + number,
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer(number), result.Outputs!["r"]);
  }

  // Negative SMT numerals must be decoded as signed values instead of completed with zero.
  [Fact]
  public async Task PreservesNegativeArbitraryPrecisionOutput() {
    const string number = "-123456789012345678901234567890123456789";
    var result = await Realize("method Missing() returns (r: int) ensures r == " + number,
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer(number), result.Outputs!["r"]);
    Assert.False(result.ModelCompleted);
  }

  private static ContractHeapObject Cell(string id, string value) => new(id, "ModelContract.Cell",
    new Dictionary<string, ContractValue> { ["value"] = Integer(value) });

  // A modeled heap update must materialize the finite map selected by the original postcondition.
  [Fact]
  public async Task RealizesFiniteMapHeapUpdate() {
    var empty = new ContractValue(ContractValueKind.Map, Entries: []);
    var result = await Realize("""
      class Box { var flags:map<int,bool> }
      method Missing(box:Box)
        modifies box
        ensures box.flags == old(box.flags)[7 := true]
      """, new Dictionary<string, ContractValue> {
      ["box"] = new(ContractValueKind.Reference, "box")
    }, heap: [new("box", "ModelContract.Box", new Dictionary<string, ContractValue> { ["flags"] = empty })]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    var entry = Assert.Single(Assert.Single(result.PostHeap!).Fields["flags"].Entries!);
    Assert.Equal(Integer("7"), entry.Key);
    Assert.Equal(new ContractValue(ContractValueKind.Boolean, "true"), entry.Value);
  }

  // A nonempty finite set output is decoded from positive model membership facts and rechecked.
  [Fact]
  public async Task RealizesFiniteSetOutput() {
    var result = await Realize("method Missing() returns (r:set<int>) ensures r == {1, 7}",
      new Dictionary<string, ContractValue>());

    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(ContractValueKind.Set, result.Outputs!["r"].Kind);
    Assert.Equal(2, result.Outputs["r"].Items!.Count);
  }

  // A nonempty multiset output retains repeated elements selected by the original relation.
  [Fact]
  public async Task RealizesFiniteMultisetOutput() {
    var result = await Realize("method Missing() returns (r:multiset<int>) ensures r == multiset{1, 7, 7}",
      new Dictionary<string, ContractValue>());

    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(new[] { "1", "7", "7" }, result.Outputs!["r"].Items!.Select(item => item.Value).Order());
  }

  // A solver bitvector literal is materialized with its exact resolved width and unsigned value.
  [Fact]
  public async Task RealizesBitvectorOutput() {
    var result = await Realize("method Missing() returns (r:bv32) ensures r == 4294967295",
      new Dictionary<string, ContractValue>());

    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(new ContractValue(ContractValueKind.Bitvector, "4294967295", Width: 32), result.Outputs!["r"]);
  }

  // Subset and newtype outputs materialize as base values while the solver retains their defining constraints.
  [Fact]
  public async Task RealizesRefinedTypeOutputs() {
    var result = await Realize("""
      type Positive = x:int | x > 0 witness 1
      newtype Small = x:int | 0 <= x < 10 witness 0
      method Missing() returns (x:Positive, y:Small) ensures x == 7 && y == 8
      """, new Dictionary<string, ContractValue>());

    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("7"), result.Outputs!["x"]);
    Assert.Equal(Integer("8"), result.Outputs["y"]);
  }

  // Datatype fields must follow resolved constructor names instead of model destructor sort order.
  [Fact]
  public async Task RealizesDatatypeWithCorrelatedFields() {
    var result = await Realize("""
      datatype Payload = Empty | Full(z:int, a:seq<int>)
      method Missing(x:int) returns(r:Payload) ensures r == Full(x+1, [x,-x])
      """, new Dictionary<string, ContractValue> { ["x"] = Integer("2") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    var value = result.Outputs!["r"];
    Assert.Equal("ModelContract.Payload.Full", value.Constructor);
    Assert.Equal(Integer("3"), value.Fields!["z"]);
    Assert.Equal(new[] { Integer("2"), Integer("-2") }, value.Fields["a"].Items);
    Assert.False(result.ModelCompleted);
  }

  // Recursive datatype results preserve the model's finite constructor tree.
  [Fact]
  public async Task RealizesNestedDatatypeOutput() {
    var result = await Realize("""
      datatype Tree = Leaf(value:int) | Node(left:Tree, right:Tree)
      method Missing() returns(r:Tree) ensures r == Node(Leaf(-3), Leaf(7))
      """, new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    var value = result.Outputs!["r"];
    Assert.Equal("ModelContract.Tree.Node", value.Constructor);
    Assert.Equal(Integer("-3"), value.Fields!["left"].Fields!["value"]);
    Assert.Equal(Integer("7"), value.Fields["right"].Fields!["value"]);
  }

  // A nullary constructor is a complete model value even though it has no fields.
  [Fact]
  public async Task RealizesNullaryDatatypeOutput() {
    var result = await Realize("""
      datatype Payload = Empty | Full(value:int)
      method Missing() returns(r:Payload) ensures r == Empty
      """, new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal("ModelContract.Payload.Empty", result.Outputs!["r"].Constructor);
    Assert.Empty(result.Outputs["r"].Fields!);
  }

  // The old heap belongs to the actual child call, even after the parent changed its initial state.
  [Fact]
  public async Task HeapModelUsesCallEntryStateAndCorrelatedOutput() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(c:Cell) returns(r:int)
        modifies c
        ensures c.value == old(c.value) + 1 && r == c.value
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "0")], currentHeap: [Cell("cell", "17")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("18"), result.Outputs!["r"]);
    Assert.Equal(Integer("18"), Assert.Single(result.PostHeap!).Fields["value"]);
  }

  // A heap-reading absent function uses the actual call state after parent mutations.
  [Fact]
  public async Task RealizesHeapReadingFunctionAtCallState() {
    var result = await Realize("""
      class Cell { var value:int }
      function Missing(c:Cell): (r:int) reads c ensures r == c.value + 1
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "0")], currentHeap: [Cell("cell", "17")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("18"), result.Outputs!["r"]);
    Assert.Equal(Integer("17"), Assert.Single(result.PostHeap!).Fields["value"]);
  }

  // An instance function's result contract reads the concrete receiver without inventing a new state.
  [Fact]
  public async Task RealizesHeapReadingInstanceFunction() {
    var result = await Realize("""
      class Cell {
        var value:int
        function Missing():int reads this ensures Missing() == value + 1
      }
      """, new Dictionary<string, ContractValue>(), child: "Cell.Missing", heap: [Cell("cell", "5")],
      receiver: new(ContractValueKind.Reference, "cell"));
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("6"), result.Outputs!["contractResult"]);
    Assert.Equal(Integer("5"), Assert.Single(result.PostHeap!).Fields["value"]);
  }

  // A function replay cannot mutate its read heap even if the supplied output satisfies Q.
  [Fact]
  public async Task RejectsHeapReadingFunctionReplayMutation() {
    var result = await Realize("""
      class Cell { var value:int }
      function Missing(c:Cell):(r:int) reads c ensures r == c.value
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "3")], replayOutputs: new Dictionary<string, ContractValue> { ["r"] = Integer("3") },
      replayHeap: [Cell("cell", "4")]);
    Assert.Equal(ContractRealizationStatus.Error, result.Status);
    Assert.Null(result.PostHeap);
  }

  // Aliased child arguments must read and update the same modeled object.
  [Fact]
  public async Task HeapModelPreservesAliasedArguments() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(a:Cell,b:Cell) returns(r:int)
        modifies a
        ensures b.value == old(b.value) + 2 && r == a.value
      """, new Dictionary<string, ContractValue> {
      ["a"] = new(ContractValueKind.Reference, "cell"),
      ["b"] = new(ContractValueKind.Reference, "cell")
    }, heap: [Cell("cell", "3")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("5"), result.Outputs!["r"]);
    Assert.Equal(Integer("5"), Assert.Single(result.PostHeap!).Fields["value"]);
  }

  // Replaying a heap model fixes the original output and next-state tuple and checks Q again.
  [Fact]
  public async Task ReplaysCorrelatedHeapTransition() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(c:Cell) returns(r:int)
        modifies c
        ensures c.value == old(c.value) + 1 && r == c.value
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "7")], replayOutputs: new Dictionary<string, ContractValue> { ["r"] = Integer("8") },
      replayHeap: [Cell("cell", "8")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("8"), Assert.Single(result.PostHeap!).Fields["value"]);
  }

  // An external heap call realizes and replays one correlated output/post-state within its modifies frame.
  [Fact]
  public async Task ReplaysExternalHeapTransition() {
    var inputs = new Dictionary<string, ContractValue> {
      ["c"] = new(ContractValueKind.Reference, "cell"),
      ["other"] = new(ContractValueKind.Reference, "other")
    };
    var realized = await Realize("""
      class Cell { var value:int }
      method {:extern} Missing(c:Cell, other:Cell) returns(r:int)
        modifies c
        ensures c.value == old(c.value) + 1 && r == c.value && other.value == old(other.value)
      """, inputs, heap: [Cell("cell", "7"), Cell("other", "19")]);
    Assert.Equal(ContractRealizationStatus.Realized, realized.Status);
    var replayed = await Realize("""
      class Cell { var value:int }
      method {:extern} Missing(c:Cell, other:Cell) returns(r:int)
        modifies c
        ensures c.value == old(c.value) + 1 && r == c.value && other.value == old(other.value)
      """, inputs, heap: [Cell("cell", "7"), Cell("other", "19")], replayOutputs: realized.Outputs,
      replayHeap: realized.PostHeap);
    Assert.Equal(ContractRealizationStatus.Realized, replayed.Status);
    Assert.Equal(Integer("8"), replayed.Outputs!["r"]);
    Assert.Equal(Integer("8"), replayed.PostHeap!.Single(item => item.Id == "cell").Fields["value"]);
    Assert.Equal(Integer("19"), replayed.PostHeap!.Single(item => item.Id == "other").Fields["value"]);
  }

  // A replay that changes an object outside the original modifies frame must be rejected.
  [Fact]
  public async Task RejectsHeapReplayOutsideCallFrame() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(a:Cell,b:Cell) modifies a ensures a.value == old(a.value) + 1
      """, new Dictionary<string, ContractValue> {
      ["a"] = new(ContractValueKind.Reference, "a"),
      ["b"] = new(ContractValueKind.Reference, "b")
    }, heap: [Cell("a", "1"), Cell("b", "9")], replayOutputs: new Dictionary<string, ContractValue>(),
      replayHeap: [Cell("a", "2"), Cell("b", "10")]);
    Assert.Equal(ContractRealizationStatus.Error, result.Status);
    Assert.Null(result.PostHeap);
  }

  // A false precondition at the call heap stops before any post-state model is chosen.
  [Fact]
  public async Task RejectsFalseHeapCallPrecondition() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(c:Cell) requires c.value > 0 modifies c ensures c.value == 1
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "0")]);
    Assert.Equal(ContractRealizationStatus.CallPreconditionViolation, result.Status);
    Assert.Null(result.PostHeap);
    Assert.DoesNotContain(result.Queries, query => query.Kind == ContractQueryKind.ContractRealization);
  }

  // Unsatisfiability in a represented heap space must not become an unbounded contract contradiction.
  [Fact]
  public async Task UnsatisfiableHeapModelPreservesItsScope() {
    var result = await Realize("""
      class Cell { var value:int }
      method Missing(c:Cell) modifies c ensures false
      """, new Dictionary<string, ContractValue> { ["c"] = new(ContractValueKind.Reference, "cell") },
      heap: [Cell("cell", "0")]);
    Assert.Equal(ContractRealizationStatus.Inconclusive, result.Status);
    Assert.False(result.ExactUnboundedContradiction);
    Assert.Null(result.PostHeap);
  }

  private static ContractHeapObject ArrayObject(params string[] values) => new("array", "array<int>",
    new Dictionary<string, ContractValue>(), Dimensions: [values.Length], Elements: values.Select(Integer).ToList());

  // Array elements and scalar outputs must come from one model with the original old-array relation.
  [Fact]
  public async Task RealizesArrayElementAndCorrelatedOutput() {
    var result = await Realize("""
      method Missing(a:array<int>) returns(r:int)
        requires a.Length == 2
        modifies a
        ensures a[0] == old(a[0]) + 1 && a[1] == old(a[1]) && r == a[0]
      """, new Dictionary<string, ContractValue> { ["a"] = new(ContractValueKind.Reference, "array") },
      heap: [ArrayObject("4", "9")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("5"), result.Outputs!["r"]);
    Assert.Equal(new[] { Integer("5"), Integer("9") }, Assert.Single(result.PostHeap!).Elements);
  }

  // Two references to one array must observe the same modeled element update.
  [Fact]
  public async Task ArrayModelPreservesAliasedInputs() {
    var result = await Realize("""
      method Missing(a:array<int>,b:array<int>)
        requires a.Length == 1 && b.Length == 1
        modifies a
        ensures b[0] == old(b[0]) + 1
      """, new Dictionary<string, ContractValue> {
      ["a"] = new(ContractValueKind.Reference, "array"),
      ["b"] = new(ContractValueKind.Reference, "array")
    }, heap: [ArrayObject("-2")]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("-1"), Assert.Single(Assert.Single(result.PostHeap!).Elements!));
  }

  // Replay cannot resize an existing array while keeping its object identity.
  [Fact]
  public async Task RejectsArrayReplayDimensionChange() {
    var result = await Realize("""
      method Missing(a:array<int>) requires a.Length == 2 modifies a ensures true
      """, new Dictionary<string, ContractValue> { ["a"] = new(ContractValueKind.Reference, "array") },
      heap: [ArrayObject("1", "2")], replayOutputs: new Dictionary<string, ContractValue>(),
      replayHeap: [ArrayObject("1")]);
    Assert.Equal(ContractRealizationStatus.Error, result.Status);
    Assert.Null(result.PostHeap);
  }

  // Classifies an impossible output relation at valid inputs as inconsistent.
  [Fact]
  public async Task RejectsContradictoryOutputRelation() {
    var result = await Realize("method Missing(x: int) returns (r: int) ensures r > x && r < x",
      new Dictionary<string, ContractValue> { ["x"] = Integer("1") });
    Assert.Equal(ContractRealizationStatus.InconsistentContract, result.Status);
    Assert.True(result.ExactUnboundedContradiction);
    Assert.Null(result.Outputs);
  }

  // Rejects an invalid call before treating its impossible premise as a successful relation.
  [Fact]
  public async Task RejectsViolatedCallPrecondition() {
    var result = await Realize("method Missing(x: int) returns (r: int) requires x > 0 ensures r == x",
      new Dictionary<string, ContractValue> { ["x"] = Integer("0") });
    Assert.Equal(ContractRealizationStatus.CallPreconditionViolation, result.Status);
    Assert.False(result.ExactUnboundedContradiction);
    Assert.Null(result.Outputs);
  }

  // Leaves an existing incorrect body available for actual execution instead of supplying a valid model.
  [Fact]
  public async Task RefusesToReplaceExistingBody() {
    var result = await Realize("method Missing() returns (r: int) ensures r >= 0 { r := -1; }",
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Error, result.Status);
    Assert.Null(result.Outputs);
  }

  // Returns an allowed choice for a non-unique contract without claiming uniqueness.
  [Fact]
  public async Task RealizesNonUniqueNamedFunctionResult() {
    var result = await Realize("function Missing(x: int): (r: int) ensures r == x || r == x + 1",
      new Dictionary<string, ContractValue> { ["x"] = Integer("5") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Contains(result.Outputs!["r"], new[] { Integer("5"), Integer("6") });
  }

  // Materializes a constrained Boolean result through the same original-contract query.
  [Fact]
  public async Task RealizesBooleanOutput() {
    var result = await Realize("method Missing(flag: bool) returns (r: bool) ensures r == !flag",
      new Dictionary<string, ContractValue> { ["flag"] = new(ContractValueKind.Boolean, "true") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(new ContractValue(ContractValueKind.Boolean, "false"), result.Outputs!["r"]);
  }

  // Carries a previous pure choice into a later relational call instead of choosing an incompatible model.
  [Fact]
  public async Task PreservesPureChoicesAcrossDifferentCallables() {
    var choice = new ContractAbstractChoice("ModelContract.Choose",
      new Dictionary<string, ContractValue> { ["x"] = Integer("5") },
      new Dictionary<string, ContractValue> { ["r"] = Integer("6") },
      ContractRealizationStatus.Realized, false);
    var result = await Realize("""
      function Choose(x: int): (r: int) ensures r == x || r == x + 1
      method Missing() returns (r: int) ensures r == Choose(5)
      """, new Dictionary<string, ContractValue>(), choices: [choice]);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("6"), result.Outputs!["r"]);
  }

  // Replays a selected non-unique model without replacing it with another valid choice.
  [Fact]
  public async Task ReplaysExactOutputChoice() {
    var result = await Realize("method Missing() returns (r: int) ensures r == 5 || r == 6",
      new Dictionary<string, ContractValue>(),
      replayOutputs: new Dictionary<string, ContractValue> { ["r"] = Integer("6") });
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(Integer("6"), result.Outputs!["r"]);
  }

  // Rejects replay values that no longer satisfy the current original contract.
  [Fact]
  public async Task RejectsInvalidReplayOutput() {
    var result = await Realize("method Missing() returns (r: int) ensures r == 5",
      new Dictionary<string, ContractValue>(),
      replayOutputs: new Dictionary<string, ContractValue> { ["r"] = Integer("6") });
    Assert.NotEqual(ContractRealizationStatus.Realized, result.Status);
    Assert.Null(result.Outputs);
    Assert.Equal(ContractQueryOutcome.Sat, result.Queries.Last().Outcome);
  }

  // Materializes correlated outputs from one solver state rather than independent per-output choices.
  [Fact]
  public async Task PreservesCorrelatedMultipleOutputs() {
    var result = await Realize("method Missing() returns (a: int, b: int) ensures 0 <= a <= 1 && b == 1 - a",
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(System.Numerics.BigInteger.One,
      System.Numerics.BigInteger.Parse(result.Outputs!["a"].Value!) +
      System.Numerics.BigInteger.Parse(result.Outputs["b"].Value!));
  }

  // Checks a void method's relation even though there are no output values to decode.
  [Fact]
  public async Task RejectsInconsistentVoidContract() {
    var result = await Realize("method Missing() ensures false", new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.InconsistentContract, result.Status);
  }

  // Records absent functional clauses while using a solver value allowed by the type relation.
  [Fact]
  public async Task MarksTypeOnlyModels() {
    var result = await Realize("method Missing() returns (r: int)", new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.True(result.TypeFrameOnly);
    Assert.Equal(ContractValueKind.Integer, result.Outputs!["r"].Kind);
  }

  // An existing function's precondition must be rejected without evaluating its result in the query.
  [Fact]
  public async Task RejectsExistingFunctionCallPrecondition() {
    var result = await Realize("function Missing(x: int): int requires x > 0 { x }",
      new Dictionary<string, ContractValue> { ["x"] = Integer("0") }, preconditionOnly: true);
    Assert.Equal(ContractRealizationStatus.CallPreconditionViolation, result.Status);
    Assert.Null(result.Outputs);
    Assert.DoesNotContain(result.Queries, query => query.Kind == ContractQueryKind.ContractRealization);
  }

  // Checking an existing function's valid P cannot manufacture an output satisfying its incorrect Q.
  [Fact]
  public async Task ExistingFunctionPreconditionCheckDoesNotModelBody() {
    var result = await Realize("function Missing(x: int): (r: int) requires x > 0 ensures r >= 0 { -x }",
      new Dictionary<string, ContractValue> { ["x"] = Integer("1") }, preconditionOnly: true);
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Null(result.Outputs);
    Assert.DoesNotContain(result.Queries, query => query.Kind == ContractQueryKind.ContractRealization);
  }

  // Materializes actual sequence length and elements from lazy model constraints before rechecking Q.
  [Fact]
  public async Task RealizesSequenceOutput() {
    var result = await Realize("method Missing() returns (r: seq<int>) ensures r == [1, 7]",
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(new[] { Integer("1"), Integer("7") }, result.Outputs!["r"].Items);
    Assert.False(result.ModelCompleted);
  }

  // Keeps nested sequence values separate instead of completing an observed inner sequence with empty data.
  [Fact]
  public async Task RealizesNestedSequenceOutput() {
    var result = await Realize("method Missing() returns (r: seq<seq<int>>) ensures r == [[2], []]",
      new Dictionary<string, ContractValue>());
    Assert.Equal(ContractRealizationStatus.Realized, result.Status);
    Assert.Equal(new[] { Integer("2") }, result.Outputs!["r"].Items![0].Items);
    Assert.Empty(result.Outputs["r"].Items![1].Items!);
  }
}
