#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractRuntimeDraftDiscoveryTests {
  private const string IsolationSource = """
    module Isolation {
      iterator Unrelated() yields (value: int)
        yield ensures value >= 0

      iterator Typed() yields (value: int)
        yield ensures value == 1
      { value := 1; yield; }

      method Scalar(x: int) returns (y: int)
        requires x >= 0
        ensures y == x
      { var unused: Typed? := null; y := x + 1; }

      method Main(x: int) returns (y: int)
        requires x >= 0
        ensures y == x
      { y := Scalar(x); }
    }
    """ + "\n";

  // The public R07 source does not request an implementation for its type-only iterator dependency.
  [Fact]
  public async Task IgnoresGeneratedValidityFromNullableIteratorLocal() {
    var request = Request(IsolationSource, "Isolation.Scalar");
    Assert.Equal("55c6ab086ae101670855f36945a89c4d9a0be7bdf7d527be783f80feda52a07e",
      Assert.Single(request.Sources).Sha256);
    var (program, goal, _) = await ParseRequest(request);
    var iterator = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(declaration => declaration.Name == "Typed");

    Assert.Null(iterator.Member_Valid.Body);
    Assert.Contains(iterator.Member_Valid,
      ContractRuntimeObligationTransformer.ExecutionReachable(program, [goal]));
    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(program, goal));
    Assert.Empty(ContractRuntimeCampaignRunner.MissingDrafts(program, request.Sources, goal, []));
    Assert.Null(request.Generator);
  }

  // Selected body and specification helpers remain drafts while an unused iterator's yield-only helper does not.
  [Fact]
  public async Task KeepsSelectedHelpersAndOmitsYieldOnlyHelpers() {
    const string source = """
      module M {
        function SelectedSpec(x: int): bool
        function YieldOnly(x: int): bool

        iterator Typed() yields (value: int)
          yield ensures YieldOnly(value)
        { value := 1; yield; }

        method SelectedBody(x: int) returns (y: int)

        method Goal(x: int) returns (y: int)
          ensures SelectedSpec(y)
        { var unused: Typed? := null; y := SelectedBody(x); }
      }
      """;
    var request = Request(source, "M.Goal");
    var (program, goal, _) = await ParseRequest(request);

    var missing = ContractRuntimeCampaignRunner.MissingDrafts(program, request.Sources, goal, [])
      .Select(draft => draft.Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToList();

    Assert.Equal(["M.SelectedBody", "M.SelectedSpec"], missing);
  }

  // Native extern discovery omits only executable bodyless externs while retaining ordinary, ghost and scaffold drafts.
  [Fact]
  public async Task NativeExternModeKeepsOtherMissingImplementations() {
    const string source = """
      module M {
        method {:extern} NativeMethod(x: int) returns (y: int)
        function {:extern} NativeFunction(x: int): int
        ghost function {:extern} GhostNativeFunction(x: int): bool
        method Missing(x: int) returns (y: int)
        method Scaffold(x: int) returns (y: int) { assert false; }
        method Goal(x: int) returns (y: int)
          ensures GhostNativeFunction(y)
        {
          var first := NativeMethod(x);
          var second := Missing(first);
          var third := Scaffold(second);
          y := NativeFunction(third);
        }
      }
      """;
    var request = Request(source, "M.Goal");
    var (program, goal, _) = await ParseRequest(request);

    var drafted = ContractRuntimeCampaignRunner.MissingDrafts(program, request.Sources, goal, [])
      .Select(item => item.Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToArray();
    var native = ContractRuntimeCampaignRunner.MissingDrafts(program, request.Sources, goal, [],
        externExecution: ContractRuntimeExternExecution.Native)
      .Select(item => item.Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToArray();

    Assert.Equal(["M.GhostNativeFunction", "M.Missing", "M.NativeFunction", "M.NativeMethod", "M.Scaffold"], drafted);
    Assert.Equal(["M.GhostNativeFunction", "M.Missing", "M.Scaffold"], native);
  }

  // Native extern mode rejects even an unreachable supplied extern draft before reachability can filter it.
  [Fact]
  public async Task RejectsUnreachableNativeExternDraft() {
    const string source = """
      module M {
        method {:extern} Unused(x: int) returns (y: int)
        method Goal(x: int) returns (y: int) { y := x; }
      }
      """;
    const string content = "method {:pbt_draft \"M.Unused\"} Unused(x: int) returns (y: int) { y := x; }";
    var request = Request(source, "M.Goal");
    var (program, goal, _) = await ParseRequest(request);
    var draft = new ContractRuntimeDraft("M.Unused", "Unused.dfy", content,
      ContractHarnessBuilder.Hash(content));

    var error = Assert.Throws<NotSupportedException>(() => ContractRuntimeCampaignRunner.MissingDrafts(
      program, request.Sources, goal, [draft], externExecution: ContractRuntimeExternExecution.Native));

    Assert.Contains("Native extern execution", error.Message);
  }

  // Constructor and advancement calls retain the existing early unsupported iterator boundary.
  [Fact]
  public async Task RejectsConstructedAndAdvancedIterator() {
    const string source = """
      module M {
        iterator Typed() yields (value: int) { value := 1; yield; }
        method Goal() {
          var iter := new Typed();
          var more := iter.MoveNext();
        }
      }
      """;
    var request = Request(source, "M.Goal");
    var (program, goal, _) = await ParseRequest(request);

    var reason = Assert.IsType<string>(
      ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(program, goal));

    Assert.Contains("M.Typed", reason, StringComparison.Ordinal);
  }

  // Prepared generator discovery requests its actual helper without inheriting a type-only iterator's generated contracts.
  [Fact]
  public async Task PreparedGeneratorKeepsOnlyActualMissingHelper() {
    const string source = """
      module M {
        iterator Typed() yields (value: int)
          yield ensures GeneratorYieldOnly(value)
        { value := 1; yield; }

        function GeneratorYieldOnly(value: int): bool
        method GeneratorNeeded() returns (value: int)
        method Goal(x: int) returns (y: int) { y := x; }
      }
      """;
    const string generatorText = """
      method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) {
        var unused: Typed? := null;
        x := GeneratorNeeded();
      }
      """;
    var request = Request(source, "M.Goal", Source("Generator.dfy", generatorText));
    var (original, originalGoal, options) = await ParseRequest(request);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(original, request.Sources, originalGoal, [],
      request.Generator!, options, CancellationToken.None);
    var visibilityReporter = new BatchErrorReporter(options);
    var visibilityProgram = await ContractSourceSnapshot.ParseAsync(visibilityReporter, prepared.Sources,
      CancellationToken.None, resolve: false);
    AssertReporter(visibilityReporter);
    var snapshots = ContractRuntimeObligationTransformer.MakeGeneratorVisible(visibilityProgram, prepared.Sources,
      prepared.DiagnosticConstructors ?? new HashSet<string>()).ToList();
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    snapshots.Add(new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime)));
    var deferred = new List<DafnyDiagnostic>();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, CancellationToken.None,
      deferredGhostDiagnostics: deferred);
    AssertReporter(reporter);
    var goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false,
      allowLemmaContract: true);
    var generator = ContractRuntimeGeneratorSignature.Select(program, goal, prepared.GeneratorMethodName);

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(program, goal, generator));
    var missing = ContractRuntimeCampaignRunner.MissingDrafts(program, snapshots, generator, [], prepared.SourceMap)
      .Select(draft => draft.Symbol).OrderBy(symbol => symbol, StringComparer.Ordinal).ToList();
    Assert.Equal(["M.GeneratorNeeded"], missing);
  }

  private static ContractRuntimeCampaignRequest Request(string content, string entry, ContractSource? generator = null) =>
    new(ContractRuntimeCampaignSchema.ProvedInputRequestVersion, [Source("Main.dfy", content)], new(entry), "17",
      Generator: generator, SampleCount: 1, ProveGeneratorPreconditions: true);

  private static ContractSource Source(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static async Task<(Program Program, Method Goal, DafnyOptions Options)> ParseRequest(
    ContractRuntimeCampaignRequest request) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    options.DisableScopes = true;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    AssertReporter(reporter);
    var goal = ContractCallableSelector.SelectMethod(program, request.Entry, requireConcreteReceiver: false,
      allowLemmaContract: true);
    return (program, goal, options);
  }

  private static void AssertReporter(BatchErrorReporter reporter) => Assert.True(reporter.ErrorCount == 0,
    string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
}
