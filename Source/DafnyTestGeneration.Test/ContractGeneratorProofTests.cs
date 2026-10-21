#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Xunit;

namespace DafnyTestGeneration.Test;

// Boundary trace: bounded source strings, fresh options, one embedded resource, dictionary-backed parsing,
// scanner fingerprints, and fake whole analyzer results only. No solver, assembly hashing, file writes,
// temporary directories, subprocesses, synchronization, or deferred disk cleanup is reached.
public sealed class ContractGeneratorProofTests {
  internal const string UserPath = "/workspace/tmp/pbt-generator-proof-memory/M.dfy";
  private const string RandomPath = "/workspace/tmp/pbt-generator-proof-memory/PbtRandom.dfy";
  internal const string Source = """
    module M {
      import PbtRandom
      method Goal(x: int) requires x >= 0 requires x % 2 == 0 ensures x > 0 { assert false; }
      method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int)
        ensures x >= 0
        ensures x % 2 == 0
      { x := 2; }
    }
    """;

  internal sealed record Fixture(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources,
    Method Goal, Method Generator);

  internal static DafnyOptions Options() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    Assert.True(options.TryCreateDetachedSnapshot(out var detached, out var failure), failure);
    return detached;
  }

  internal static ContractSource Snapshot(string path, string content) => new(path, content, ContractHarnessBuilder.Hash(content));

  internal static async Task<Program> Parse(IReadOnlyList<ContractSource> sources, DafnyOptions options, bool resolve = true) {
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None, resolve);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Take(16).Select(message => message.Message)));
    return program;
  }

  internal static Method Method(Program program, string name) => Assert.Single(program.Descendants().OfType<Method>()
    .Where(method => method.Name == name && method.EnclosingClass.EnclosingModuleDefinition.Name == "M"));

  internal static async Task<Fixture> Prepare(string source = Source) {
    var options = Options();
    IReadOnlyList<ContractSource> sources = [Snapshot(UserPath, source), Snapshot(RandomPath, ContractGeneratorProof.ExtractPinnedPbtRandomSource())];
    var program = await Parse(sources, options);
    return new(program, options, sources, Method(program, "Goal"), Method(program, "Generate"));
  }

  internal static async Task<(ContractGeneratorProofSourceBuild Build, Program Program)> Bridge(Fixture fixture) {
    var build = ContractGeneratorProof.PrepareProofSources(fixture.Program, fixture.Sources, fixture.Goal, fixture.Generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource(), out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    return (build!, await Parse(build!.Sources, fixture.Options));
  }

  private static DafnyProofInputs FakeInputs(Program program, IReadOnlySet<Uri> sources) =>
    new(1, new string('a', 64), new string('b', 64), [new(UserPath, "M.Generate", new string('c', 64))]);

  // Authored ensures and body survive the proof copy while the generated lemma has each contract in its own role.
  [Fact]
  public async Task BridgePreservesAuthoredGeneratorAndEveryClause() {
    var fixture = await Prepare();
    var (build, program) = await Bridge(fixture);
    var generator = Method(program, "Generate");
    var bridge = Assert.IsType<Lemma>(Method(program, build.AdmissionName));
    Assert.Equal(fixture.Generator.Ens.Select(ensure => Printer.ExprToString(fixture.Options, ensure.E)),
      generator.Ens.Select(ensure => Printer.ExprToString(fixture.Options, ensure.E)));
    Assert.Equal(fixture.Generator.Body!.EntireRange.PrintOriginal(), generator.Body!.EntireRange.PrintOriginal());
    Assert.Equal(2, bridge.Req.Count);
    Assert.Equal(2, bridge.Ens.Count);
    Assert.Empty(bridge.Body!.Body);
    Assert.Empty(bridge.Descendants().OfType<CallStmt>());
    Assert.Single(bridge.Ins);
  }

  // A false authored generator ensure is retained for body verification even if it makes the implication trivial.
  [Fact]
  public async Task WrongGeneratorEnsureRemainsARequiredBodyObligation() {
    var fixture = await Prepare(Source.Replace("ensures x % 2 == 0", "ensures false", StringComparison.Ordinal));
    var (build, program) = await Bridge(fixture);
    var generator = Method(program, "Generate");
    Assert.Contains(generator.Ens, ensure => ensure.E.Resolved is LiteralExpr { Value: false });
    var scopes = ContractGeneratorProof.ProofScopes(program, build.Sources, Method(program, "Goal"), generator,
      Method(program, build.AdmissionName), ContractGeneratorProof.ExtractPinnedPbtRandomSource());
    Assert.Contains("M.Generate (correctness)", scopes.SelectMany(scope => scope.RequiredNativeChecks));
  }

  // A weak authored contract does not acquire the target's missing condition in the private proof source.
  [Fact]
  public async Task WeakEnsureLeavesIndependentBridgeObligation() {
    var fixture = await Prepare(Source.Replace("ensures x % 2 == 0", "", StringComparison.Ordinal));
    var (build, program) = await Bridge(fixture);
    Assert.Single(Method(program, "Generate").Ens);
    Assert.Single(Method(program, build.AdmissionName).Req);
    Assert.Equal(2, Method(program, build.AdmissionName).Ens.Count);
  }

  // Prior requirements retain their order so later index expressions remain well-formed in the bridge.
  [Fact]
  public async Task BridgePreservesDependentRequirementOrder() {
    const string source = """
      module M {
        import PbtRandom
        method Goal(xs: seq<int>) requires |xs| > 0 requires xs[0] >= 0 {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>)
          ensures |xs| > 0 ensures xs[0] >= 0 { xs := [0]; }
      }
      """;
    var (build, program) = await Bridge(await Prepare(source));
    var bridge = Method(program, build.AdmissionName);
    Assert.Equal(2, bridge.Req.Count);
    Assert.Equal(2, bridge.Ens.Count);
    Assert.Contains(bridge.Ens[1].E.DescendantsAndSelf, expression => expression is SeqSelectExpr);
  }

  // Generated output names stay distinct from quantified binders when the clause is printed and resolved again.
  [Fact]
  public async Task QuantifiedBinderCannotCaptureGeneratedOutput() {
    var fixture = await Prepare(Source.Replace("ensures x >= 0",
      "ensures forall PbtGeneratorAdmissionOutput0: int :: 0 <= PbtGeneratorAdmissionOutput0 < 3 ==> x >= PbtGeneratorAdmissionOutput0"));
    var (build, program) = await Bridge(fixture);
    var bridge = Method(program, build.AdmissionName);
    var quantifier = Assert.IsType<ForallExpr>(bridge.Req[0].E.Resolved);
    Assert.NotEqual(Assert.Single(quantifier.BoundVars).Name, Assert.Single(bridge.Ins).Name);
    Assert.Contains(quantifier.DescendantsAndSelf.OfType<IdentifierExpr>(), identifier => ReferenceEquals(identifier.Var, bridge.Ins[0]));
  }

  // RNG-dependent ensures cannot be approximated by an output-only implication lemma.
  [Fact]
  public async Task RandomSourcePostconditionIsUnsupported() {
    var fixture = await Prepare(Source.Replace("ensures x >= 0", "ensures r == r", StringComparison.Ordinal));
    Assert.Null(ContractGeneratorProof.PrepareProofSources(fixture.Program, fixture.Sources, fixture.Goal, fixture.Generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource(), out var failure));
    Assert.Contains("random-source", failure, StringComparison.Ordinal);
  }

  // Old-state postconditions are outside the ordinary value-only bridge capability.
  [Fact]
  public async Task OldPostconditionIsUnsupported() {
    var fixture = await Prepare(Source.Replace("ensures x >= 0", "ensures old(r) == r", StringComparison.Ordinal));
    Assert.Null(ContractGeneratorProof.PrepareProofSources(fixture.Program, fixture.Sources, fixture.Goal, fixture.Generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource(), out _));
  }

  // Bodyless ghost helpers are rejected as proof dependencies without executing or compiling the generator.
  [Fact]
  public async Task BodylessLemmaRejectsProofScope() {
    var source = Source.Replace("{ x := 2; }", "{ x := 2; Missing(x); }\n lemma Missing(x: int) ensures x >= 0", StringComparison.Ordinal);
    var (build, program) = await Bridge(await Prepare(source));
    var scopes = ContractGeneratorProof.ProofScopes(program, build.Sources, Method(program, "Goal"), Method(program, "Generate"),
      Method(program, build.AdmissionName), ContractGeneratorProof.ExtractPinnedPbtRandomSource());
    Assert.Contains(scopes, scope => scope.Failure?.Contains("bodyless_contract", StringComparison.Ordinal) == true);
  }

  // Unrelated logical functions remain proof obligations while the buggy ordinary target body stays excluded.
  [Fact]
  public async Task AmbientLogicalBodyIsRequiredButTargetBodyIsNot() {
    var source = Source.Replace("method Goal", "function Ambient(): int ensures false { 0 }\n method Goal", StringComparison.Ordinal);
    var (build, program) = await Bridge(await Prepare(source));
    var goal = Method(program, "Goal");
    var scopes = ContractGeneratorProof.ProofScopes(program, build.Sources, goal, Method(program, "Generate"),
      Method(program, build.AdmissionName), ContractGeneratorProof.ExtractPinnedPbtRandomSource());
    Assert.All(scopes, scope => Assert.False(scope.ContainsDeclaration(goal)));
    Assert.Contains("M.Ambient (well-formedness)", scopes.SelectMany(scope => scope.RequiredNativeChecks));
  }

  // A source edit invalidates scanner binding even when a fake analyzer returns unchanged translated metadata.
  [Fact]
  public async Task SourceDriftInvalidatesBinding() {
    var fixture = await Prepare();
    var binding = ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator)], FakeInputs);
    Assert.NotNull(binding);
    var changed = fixture.Sources.Select(source => source.Path == UserPath
      ? Snapshot(source.Path, source.Content.Replace("x := 2", "x := 4", StringComparison.Ordinal)) : source).ToArray();
    Assert.False(binding!.Matches(fixture.Program, changed, FakeInputs));
    Assert.Equal("Source fingerprint changed.", binding.Mismatch(fixture.Program, changed, FakeInputs));
  }

  // A changed resolved proof identity invalidates evidence even when the source snapshots are identical.
  [Fact]
  public async Task AnalyzerDriftInvalidatesBinding() {
    var fixture = await Prepare();
    var binding = ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator)], FakeInputs);
    Assert.NotNull(binding);
    Assert.False(binding!.Matches(fixture.Program, fixture.Sources, (program, sources) => FakeInputs(program, sources) with {
      OptionsSha256 = new string('d', 64)
    }));
  }

  // Missing analyzer output cannot be replaced by an ad hoc fingerprint.
  [Fact]
  public async Task MissingAnalyzerIdentityCannotBind() {
    var fixture = await Prepare();
    Assert.Null(ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator)], (_, _) => null));
  }

  // Every required callable body needs its own row even when unrelated translated definitions remain available.
  [Theory]
  [InlineData("M.Generate")]
  [InlineData("M.PbtGeneratorAdmission")]
  [InlineData("M.Helper")]
  public async Task MissingRequiredAnalyzerDefinitionCannotBind(string missing) {
    var fixture = await Prepare();
    ContractGeneratorDefinitionIdentity[] required = [new(UserPath, "M.Generate"), new(UserPath, "M.PbtGeneratorAdmission"), new(UserPath, "M.Helper")];
    var rows = required.Append(new(UserPath, "M.Unrelated"))
      .Select(identity => new DafnyDefinitionProofInput(identity.SourcePath, identity.FullName, new string('c', 64))).ToArray();
    var inputs = FakeInputs(fixture.Program, new HashSet<Uri>()) with { Definitions = rows };
    Assert.NotNull(ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources, required, (_, _) => inputs));
    Assert.Null(ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources, required,
      (_, _) => inputs with { Definitions = rows.Where(row => row.FullName != missing).ToArray() }));
  }

  // Unsupported schemas, malformed identities and incomplete digests cannot form analyzer evidence.
  [Theory]
  [InlineData("schema")]
  [InlineData("toolchain")]
  [InlineData("options")]
  [InlineData("digest")]
  [InlineData("duplicate")]
  [InlineData("path")]
  [InlineData("name")]
  public async Task MalformedAnalyzerEvidenceCannotBind(string mutation) {
    var fixture = await Prepare();
    var inputs = FakeInputs(fixture.Program, new HashSet<Uri>());
    var row = inputs.Definitions[0];
    inputs = mutation switch {
      "schema" => inputs with { SchemaVersion = 2 },
      "toolchain" => inputs with { ToolchainSha256 = "" },
      "options" => inputs with { OptionsSha256 = "invalid" },
      "digest" => inputs with { Definitions = [row with { Sha256 = new string('z', 64) }] },
      "duplicate" => inputs with { Definitions = [row, row] },
      "path" => inputs with { Definitions = [row with { SourcePath = "other.dfy" }] },
      "name" => inputs with { Definitions = [row with { FullName = "" }] },
      _ => throw new InvalidOperationException("Unknown test mutation")
    };
    Assert.Null(ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator)], (_, _) => inputs));
  }

  // Unchanged complete analyzer evidence remains accepted and each comparison invokes the provider exactly once.
  [Fact]
  public async Task UnchangedBindingCapturesOnce() {
    var fixture = await Prepare();
    var binding = ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator)], FakeInputs)!;
    var calls = 0;
    Assert.Null(binding.Mismatch(fixture.Program, fixture.Sources, (program, sources) => {
      calls++;
      return FakeInputs(program, sources);
    }));
    Assert.Equal(1, calls);
  }

  // Diagnostic categories distinguish unavailable, invalid and changed evidence while every case still rejects.
  [Theory]
  [InlineData("unavailable", "Analyzer proof inputs are unavailable.")]
  [InlineData("schema", "Analyzer proof-input schema is unsupported.")]
  [InlineData("incomplete", "Analyzer toolchain/options identity is incomplete or malformed.")]
  [InlineData("toolchain", "Analyzer toolchain identity changed.")]
  [InlineData("options", "Analyzer verifier-options identity changed.")]
  [InlineData("helper", "Analyzer definition input changed:")]
  [InlineData("missing", "Analyzer required definition is missing:")]
  [InlineData("duplicate", "Analyzer definition identity is malformed, duplicated or outside the source snapshots:")]
  [InlineData("null-path", "Analyzer definition identity is malformed, duplicated or outside the source snapshots:")]
  [InlineData("null-name", "Analyzer definition identity is malformed, duplicated or outside the source snapshots:")]
  [InlineData("removed-unrelated", "Analyzer definition is missing:")]
  [InlineData("added", "Analyzer definition was added:")]
  [InlineData("order", "Analyzer serialized definition ordering or metadata changed.")]
  public async Task AnalyzerMismatchIdentifiesRejectedComponent(string mutation, string diagnostic) {
    var fixture = await Prepare();
    var generatorRow = FakeInputs(fixture.Program, new HashSet<Uri>()).Definitions[0];
    var helper = new DafnyDefinitionProofInput(UserPath, "M.Helper", new string('d', 64));
    var unrelated = new DafnyDefinitionProofInput(UserPath, "M.Unrelated", new string('e', 64));
    var inputs = FakeInputs(fixture.Program, new HashSet<Uri>()) with { Definitions = [generatorRow, helper, unrelated] };
    var binding = ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [ContractGeneratorDefinitionIdentity.For(fixture.Generator), new(UserPath, helper.FullName)], (_, _) => inputs)!;
    var changed = mutation switch {
      "unavailable" => null,
      "schema" => inputs with { SchemaVersion = 2 },
      "incomplete" => inputs with { ToolchainSha256 = "" },
      "toolchain" => inputs with { ToolchainSha256 = new string('f', 64) },
      "options" => inputs with { OptionsSha256 = new string('f', 64) },
      "helper" => inputs with { Definitions = [generatorRow, helper with { Sha256 = new string('f', 64) }, unrelated] },
      "missing" => inputs with { Definitions = [generatorRow, unrelated] },
      "duplicate" => inputs with { Definitions = [generatorRow, helper, helper, unrelated] },
      "null-path" => inputs with { Definitions = [generatorRow, helper with { SourcePath = null! }, unrelated] },
      "null-name" => inputs with { Definitions = [generatorRow, helper with { FullName = null! }, unrelated] },
      "removed-unrelated" => inputs with { Definitions = [generatorRow, helper] },
      "added" => inputs with { Definitions = [generatorRow, helper, unrelated, unrelated with { FullName = "M.Added" }] },
      "order" => inputs with { Definitions = [helper, generatorRow, unrelated] },
      _ => throw new InvalidOperationException("Unknown test mutation")
    };
    var calls = 0;
    var failure = binding.Mismatch(fixture.Program, fixture.Sources, (_, _) => { calls++; return changed; });
    Assert.StartsWith(diagnostic, failure, StringComparison.Ordinal);
    if (mutation is "helper" or "missing") { Assert.Contains("M.Helper", failure, StringComparison.Ordinal); }
    Assert.Equal(1, calls);
  }

  // Output truncation and escaped control characters do not hide a changed definition beyond the display limit.
  [Fact]
  public async Task BoundedIdentityDiagnosticStillRejectsFullDefinitionDrift() {
    var fixture = await Prepare();
    var name = "M.Helper\n" + new string('x', 512);
    var row = new DafnyDefinitionProofInput(UserPath, name, new string('c', 64));
    var inputs = FakeInputs(fixture.Program, new HashSet<Uri>()) with { Definitions = [row] };
    var binding = ContractGeneratorInputBinding.Capture(fixture.Program, fixture.Sources,
      [new(UserPath, name)], (_, _) => inputs)!;
    var failure = binding.Mismatch(fixture.Program, fixture.Sources,
      (_, _) => inputs with { Definitions = [row with { FullName = name + "changed" }] });
    Assert.NotNull(failure);
    Assert.True(failure!.Length < 512);
    Assert.DoesNotContain('\n', failure);
    Assert.Contains("...", failure, StringComparison.Ordinal);
  }

  // Final attribution preserves proof/runtime/policy ordering and never repeats or evaluates later binding captures.
  [Theory]
  [InlineData("proof", "Generator proof binding rejected:", 1)]
  [InlineData("runtime", "Generator runtime binding rejected:", 2)]
  [InlineData("policy", "Generator caller policy rejected:", 2)]
  [InlineData("unchanged", null, 2)]
  public async Task FinalBindingGateAttributesFirstFailure(string stage, string? prefix, int expectedCalls) {
    var proof = await Prepare();
    var runtime = await Prepare();
    var required = new[] { ContractGeneratorDefinitionIdentity.For(proof.Generator) };
    var proofBinding = ContractGeneratorInputBinding.Capture(proof.Program, proof.Sources, required, FakeInputs)!;
    var runtimeBinding = ContractGeneratorInputBinding.Capture(runtime.Program, runtime.Sources, required, FakeInputs)!;
    var callerOptions = Options();
    if (stage != "unchanged") { callerOptions.Set(BoogieOptionBag.NoVerify, true); }
    var calls = new List<Program>();
    var failure = ContractGeneratorProof.FinalBindingFailure(proofBinding, proof.Program, proof.Sources,
      runtimeBinding, runtime.Program, runtime.Sources, callerOptions, (program, sources) => {
        calls.Add(program);
        return stage == "proof" || stage == "runtime" && ReferenceEquals(program, runtime.Program)
          ? null : FakeInputs(program, sources);
      });
    if (prefix == null) { Assert.Null(failure); } else { Assert.StartsWith(prefix, failure, StringComparison.Ordinal); }
    Assert.Equal(expectedCalls, calls.Count);
    Assert.Same(proof.Program, calls[0]);
    if (calls.Count == 2) { Assert.Same(runtime.Program, calls[1]); }
  }

  // Trust-affecting source attributes are rejected before the ordinary backend can receive the program.
  [Theory]
  [InlineData("{:verify false}")]
  [InlineData("{:axiom}")]
  [InlineData("{:extern}")]
  public async Task TrustAttributeRejectsRawAudit(string attribute) {
    var fixture = await Prepare(Source.Replace("method Goal", "method " + attribute + " Goal", StringComparison.Ordinal));
    var raw = await Parse(fixture.Sources, fixture.Options, resolve: false);
    Assert.NotNull(ContractGeneratorProofAudit.AuditRawProgram(raw, fixture.Sources, fixture.Generator.Origin.Uri,
      fixture.Generator.Name, fixture.Goal.FullDafnyName, ContractGeneratorProof.ExtractPinnedPbtRandomSource()));
  }

  // Pre-resolution audit reaches forbidden expressions nested in concrete-syntax call arguments.
  [Fact]
  public async Task NestedLetSuchThatRejectsRawAudit() {
    var fixture = await Prepare();
    var source = Source.Replace("{ x := 2; }", "{ x := Pick((var z :| z == 2; z)); }\n function Pick(x: int): int { x }", StringComparison.Ordinal);
    var sources = fixture.Sources.Select(snapshot => snapshot.Path == UserPath ? Snapshot(UserPath, source) : snapshot).ToArray();
    var raw = await Parse(sources, fixture.Options, resolve: false);
    var failure = ContractGeneratorProofAudit.AuditRawProgram(raw, sources, fixture.Generator.Origin.Uri,
      fixture.Generator.Name, fixture.Goal.FullDafnyName, ContractGeneratorProof.ExtractPinnedPbtRandomSource());
    Assert.Contains("Let-such-that", failure, StringComparison.Ordinal);
  }

  // Verification skips are rejected instead of normalizing a skipped run into successful proof evidence.
  [Fact]
  public void VerificationSkipRejectsProofOptions() {
    var options = Options();
    options.Set(BoogieOptionBag.NoVerify, true);
    Assert.NotNull(ContractGeneratorProof.ProofOptionFailure(options));
  }

  // Unchecked division well-formedness cannot supply generator evidence.
  [Fact]
  public void AssumedWellFormednessRejectsProofOptions() {
    var options = Options();
    options.Set(CommonOptionBag.AssumeWellFormedDiv, true);
    Assert.NotNull(ContractGeneratorProof.ProofOptionFailure(options));
  }

  // Caller-supplied solver factories cannot enter the ordinary host proof path.
  [Fact]
  public void CustomSolverRejectsProofOptions() {
    var options = Options();
    options.CreateSolver = (_, _) => null!;
    Assert.NotNull(ContractGeneratorProof.ProofOptionFailure(options));
  }
}
