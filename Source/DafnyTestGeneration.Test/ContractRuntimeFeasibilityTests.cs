#nullable enable
using System;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

// Every operation uses immutable source snapshots and null writers; a prover attempt fails immediately.
public class ContractRuntimeFeasibilityTests {
  // A bodyless selected method remains authorable and needs a draft before its generator can execute it.
  [Fact]
  public async Task AllowsBodylessGoalWithoutGenerator() {
    var result = await Run("module M { method {:axiom} Goal(x:int) ensures x == x }");
    Assert.True(result.Possible);
    Assert.Empty(result.ReasonCodes);
    Assert.Empty(result.Diagnostics);
    Assert.Equal(new[] { "M.Goal" }, result.RequiredDraftSymbols);
  }

  // Missing function and method implementations remain explicit sorted source-local authoring prerequisites.
  [Fact]
  public async Task ReportsMissingDependenciesWithoutBlockingAuthoring() {
    var result = await Run("module M { function {:axiom} F(x:int):int " +
      "method {:axiom} Step(x:int) returns (y:int) " +
      "method Goal(x:int) returns (y:int) { y := Step(F(x)); } }");
    Assert.True(result.Possible);
    Assert.Equal(new[] { "M.F", "M.Step" }, result.RequiredDraftSymbols);
  }

  // The selected method's implementation stub is work under test rather than a child draft prerequisite.
  [Fact]
  public async Task DoesNotRequestDraftForSelectedStubBody() {
    var result = await Run("module M { method Goal() { assert false; } }");
    Assert.True(result.Possible);
    Assert.Empty(result.RequiredDraftSymbols);
  }

  // The selected extern policy changes the missing implementation prerequisite without claiming native linkage.
  [Fact]
  public async Task NativeExternDoesNotRequestItsBody() {
    var request = Request("module M { method {:extern} {:axiom} Step() method Goal() { Step(); } }");
    var result = await ContractRuntimeFeasibility.RunAsync(request with {
      ExternExecution = ContractRuntimeExternExecution.Native
    }, Options(), CancellationToken.None);
    Assert.True(result.Possible);
    Assert.Empty(result.RequiredDraftSymbols);
  }

  // A pure ordinary lemma contract is eligible without compiling or implementing its proof body.
  [Fact]
  public async Task AllowsValueOnlyLemmaContract() {
    var result = await Run("module M { lemma Goal(x:int) requires x >= 0 ensures x + 1 > 0 {} }");
    Assert.True(result.Possible);
    Assert.Empty(result.RequiredDraftSymbols);
  }

  // A runtime-inexpressible input is rejected before any missing-generator result or source template.
  [Fact]
  public async Task RejectsUnsupportedInputType() {
    var result = await Run("module M { method Goal(callback: int -> int) {} }");
    Assert.False(result.Possible);
    Assert.Contains("non_compilable_input_type", result.ReasonCodes);
  }

  // A known unsupported goal never requests otherwise missing dependency bodies.
  [Fact]
  public async Task UnsupportedGoalDoesNotRequestDrafts() {
    var result = await Run("module M { method {:axiom} Missing() " +
      "method Goal(callback:int -> int) { Missing(); } }");
    Assert.False(result.Possible);
    Assert.Empty(result.RequiredDraftSymbols);
  }

  // Many unsupported formals produce a bounded wire response instead of oversized diagnostics.
  [Fact]
  public async Task BoundsDiagnosticCountAndLength() {
    var formals = Enumerable.Range(0, 40).Select(index => "callback" + index + new string('x', 2100) + ":int -> int");
    var result = await Run("module M { method Goal(" + string.Join(",", formals) + ") {} }");
    Assert.False(result.Possible);
    Assert.InRange(result.Diagnostics.Count, 1, 32);
    Assert.All(result.Diagnostics, diagnostic => Assert.InRange(diagnostic.Length, 1, 2048));
    Assert.InRange(result.Diagnostics.Sum(diagnostic => diagnostic.Length), 1, 16384);
  }

  // Source-authoring shares the input gate and never constructs a generator template for this shape.
  [Fact]
  public async Task AuthoringRejectsUnsupportedInputBeforeTemplates() {
    var request = Request("module M { method Goal(callback: int -> int) {} }");
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => ContractRuntimeSourceAuthoring.RunAsync(
      new(1, ContractRuntimeAuthoringAction.Prepare, request.Sources, request.Entry), Options(), CancellationToken.None));
    Assert.Contains("non_compilable_input_type", error.Message);
  }

  // Selected iterator construction is a known runtime capability blocker even before generator authoring.
  [Fact]
  public async Task RejectsExecutedIterator() {
    var result = await Run("module M { iterator Items() yields (value:int) { value := 0; yield; } " +
      "method Goal() { var it := new Items(); } }");
    Assert.False(result.Possible);
    Assert.Contains("unsupported_iterator", result.ReasonCodes);
  }

  // Unused iterator bodies and diagnostic-looking declarations do not reject an independent selected goal.
  [Fact]
  public async Task IgnoresUnrelatedUnsupportedDeclarations() {
    var result = await Run("module M { iterator Items() yields (value:int) " +
      "method PbtUnused(callback: int -> int) {} method Goal(x:int) {} }");
    Assert.True(result.Possible);
  }

  // Referenced callback state cannot be encoded and cannot be omitted under the existing heap audit.
  [Fact]
  public async Task RejectsRequiredUnsupportedIoGhostState() {
    var result = await Run("module M { class IO { ghost var callback: int -> int } " +
      "method Goal(io:IO) requires io.callback(0) == 0 {} }");
    Assert.False(result.Possible);
    Assert.Contains("unsupported_required_ghost_field", result.ReasonCodes);
    Assert.Contains(result.Diagnostics, diagnostic => diagnostic.Contains("M.IO.callback", StringComparison.Ordinal));
  }

  // Unobserved ghost callback state remains omittable rather than banning its containing IO class.
  [Fact]
  public async Task AllowsUnusedUnsupportedGhostState() {
    var result = await Run("module M { class IO { ghost var callback: int -> int } method Goal(io:IO) {} }");
    Assert.True(result.Possible);
  }

  // Runtime-representable scalar and sequence ghost fields remain available to ordinary diagnostic constructors.
  [Fact]
  public async Task AllowsSupportedGhostState() {
    var result = await Run("module M { class IO { ghost var count:int ghost var bytes:seq<int> } " +
      "method Goal(io:IO) requires io.count == |io.bytes| {} }");
    Assert.True(result.Possible);
  }

  // Explicit bounded-model policy uses its existing flat scalar restriction instead of ordinary heap support.
  [Fact]
  public async Task RejectsSequenceStateOnlyForExplicitBoundedModels() {
    var request = Request("module M { class IO { ghost var bytes:seq<int> } method Goal(io:IO) {} }");
    var result = await ContractRuntimeFeasibility.RunAsync(request with {
      ContractModelPolicy = new("M.Goal", "0", "3", 16)
    }, Options(), CancellationToken.None);
    Assert.False(result.Possible);
    Assert.Contains("contract_models_unsupported", result.ReasonCodes);
  }

  // Supported bounded state is checked structurally before the selected method body is authored.
  [Fact]
  public async Task AllowsBodylessBoundedModelGoal() {
    var request = Request("module M { class IO { ghost var count:int } " +
      "method {:axiom} Goal(io:IO) requires io.count >= 0 }");
    var result = await ContractRuntimeFeasibility.RunAsync(request with {
      ContractModelPolicy = new("M.Goal", "0", "3", 16)
    }, Options(), CancellationToken.None);
    Assert.True(result.Possible);
    Assert.Equal(new[] { "M.Goal" }, result.RequiredDraftSymbols);
  }

  // The exact supplied native dependency identity participates in reuse even though no dependency file is opened.
  [Fact]
  public void DependencyDigestChangesRequestIdentity() {
    var request = Request("module M { method Goal() {} }") with {
      Dependencies = [new("runtime.cs", new string('a', 64))]
    };
    Assert.NotEqual(ContractRuntimeFeasibility.RequestIdentity(request),
      ContractRuntimeFeasibility.RequestIdentity(request with { Dependencies = [new("runtime.cs", new string('b', 64))] }));
    Assert.Equal(ContractRuntimeFeasibility.RequestIdentity(request),
      ContractRuntimeFeasibility.RequestIdentity(request with { TimeoutMilliseconds = 1000 }));
  }

  // Canonical path ordering and Unicode text match the protocol independently of UTF-16 ordinal order.
  [Fact]
  public void SourceIdentityUsesCanonicalUnicodeOrdering() {
    var digest = ContractHarnessBuilder.Hash("source");
    var expected = "[{\"path\":\"\uE000.dfy\",\"sha256\":\"" + digest +
      "\"},{\"path\":\"\U0001F600.dfy\",\"sha256\":\"" + digest + "\"}]";
    Assert.Equal(ContractHarnessBuilder.Hash(expected), ContractRuntimeFeasibility.SourceSetHash([
      new("\U0001F600.dfy", "source", digest),
      new("\uE000.dfy", "source", digest)
    ]));
  }

  // A source change invalidates feasibility independently of an unchanged entry and execution policy.
  [Fact]
  public async Task BindsExactSourcesAndTarget() {
    var request = Request("module M { method Goal(x:int) {} }");
    var result = await ContractRuntimeFeasibility.RunAsync(request, Options(), CancellationToken.None);
    var changed = await Run("module M { method Goal(x:int) { assert x == 0; } }");
    Assert.NotEqual(result.Binding.SourceSetHash, changed.Binding.SourceSetHash);
    Assert.Equal(ContractRuntimeFeasibility.SourceSetHash(request.Sources), result.Binding.SourceSetHash);
    Assert.Equal(ContractRuntimeFeasibility.RequestIdentity(request), result.Binding.RequestIdentity);
    Assert.Equal(result.Binding.TargetIdentity, changed.Binding.TargetIdentity);
    Assert.NotEmpty(result.Binding.ProducerIdentity);
    Assert.NotEmpty(result.Binding.OptionsIdentity);
  }

  // Malformed source is an operational error rather than an impossible-support judgment.
  [Fact]
  public async Task ParseFailureDoesNotProduceVerdict() {
    await Assert.ThrowsAsync<ArgumentException>(() => Run("module M { method Goal( }"));
  }

  // Cancellation interrupts assessment without manufacturing either boolean result.
  [Fact]
  public async Task CancellationDoesNotProduceVerdict() {
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractRuntimeFeasibility.RunAsync(
      Request("module M { method Goal() {} }"), Options(), new CancellationToken(true)));
  }

  // The wire requires an actual JSON boolean rather than a numeric or textual third outcome.
  [Fact]
  public async Task SerializesOnlyBinaryVerdict() {
    var result = await Run("module M { method Goal() {} }");
    using var document = JsonDocument.Parse(JsonSerializer.Serialize(result, ContractJson.Options));
    Assert.Equal(JsonValueKind.True, document.RootElement.GetProperty("possible").ValueKind);
    Assert.False(document.RootElement.TryGetProperty("status", out _));
  }

  private static ContractRuntimeFeasibilityRequest Request(string content) => new(1,
    [new("M.dfy", content, ContractHarnessBuilder.Hash(content))], new("M.Goal"), []);

  private static Task<ContractRuntimeFeasibilityResult> Run(string content) =>
    ContractRuntimeFeasibility.RunAsync(Request(content), Options(), CancellationToken.None);

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
      Microsoft.Boogie.ProverOptions proverOptions, object context) => throw new InvalidOperationException("Feasibility cannot spawn a prover.");
    public override Microsoft.Boogie.ProverContext NewProverContext(Microsoft.Boogie.ProverOptions options) =>
      throw new InvalidOperationException("Feasibility cannot create a prover context.");
  }
}
