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
