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

// Boundary trace: every helper parses bounded strings through ContractSourceSnapshot's dictionary filesystem,
// reads one embedded runtime resource, merges source strings, fingerprints ASTs and inspects native check sets.
// No fixtures, disk writes/directories, native compilation/verification, solver probes, processes or cleanup run here.
public sealed class ContractGeneratorProofHelperTests {
  private const string GoalPath = "/workspace/tmp/pbt-generator-helper-memory/Target.dfy";
  private const string GeneratorPath = "/workspace/.top-down-pbt/generators/M.Goal.dfy";
  private const string GoalSource = """
    module M {
      method Goal(x: int)
        requires x >= 0
        requires x % 2 == 0
        ensures x >= 0
      { assert false; }
    }
    """;
  private const string GeneratorSource = """
    method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) {
      x := Twice(2);
      TwiceIsNonnegative(2);
      assert x >= 0;
    }
    lemma TwiceIsNonnegative(value: int)
      requires value >= 0
      ensures Twice(value) >= 0
    { assert Twice(value) == value + value; }
    function Twice(value: int): int { Add(value, value) }
    function Add(left: int, right: int): int { left + right }
    """;

  private sealed record Prepared(Program Original, Program Program, DafnyOptions Options,
    ContractRuntimePreparedSources Preparation, IReadOnlyList<ContractSource> Sources,
    Method Goal, Method Generator, string RandomSource);

  private sealed record Proof(Program Program, Method Admission, ContractSpecificationScope Scope);

  private static ContractSource Snapshot(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static async Task<Program> Parse(IReadOnlyList<ContractSource> sources, DafnyOptions options,
    bool resolve = true) {
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None, resolve);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Take(16).Select(message => message.Message)));
    return program;
  }

  private static Method Method(Program program, string name) => Assert.Single(program.Descendants()
    .OfType<Method>().Where(method => method.Name == name && method.EnclosingClass.EnclosingModuleDefinition.Name == "M"));

  private static async Task<Prepared> Prepare(string generatorSource = GeneratorSource) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    IReadOnlyList<ContractSource> sources = [Snapshot(GoalPath, GoalSource)];
    var original = await Parse(sources, options);
    var preparation = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, Method(original, "Goal"),
      [], Snapshot(GeneratorPath, generatorSource), options, CancellationToken.None);
    var runtime = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");
    const string marker = "module {:extern \"DafnyPbtRandom\"} PbtRandom {";
    var start = runtime.IndexOf(marker, StringComparison.Ordinal);
    Assert.True(start >= 0);
    var random = runtime[start..];
    var preparedSources = preparation.Sources.Append(Snapshot(GoalPath + ".rng.dfy", random)).ToList();
    var program = await Parse(preparedSources, options);
    return new(original, program, options, preparation, preparedSources, Method(program, "Goal"),
      Method(program, "Generate"), random);
  }

  private static async Task<string?> RawAudit(Prepared prepared) {
    var raw = await Parse(prepared.Sources, prepared.Options, resolve: false);
    return ContractGeneratorProofAudit.AuditRawProgram(raw, prepared.Sources, prepared.Generator.Origin.Uri,
      prepared.Generator.Name, prepared.Goal.FullDafnyName, prepared.RandomSource);
  }

  private static async Task<Proof> PrepareProof(Prepared prepared) {
    var build = ContractGeneratorProof.PrepareProofSources(prepared.Program, prepared.Sources, prepared.Goal,
      prepared.Generator, prepared.RandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var program = await Parse(build!.Sources, prepared.Options);
    var audit = ContractGeneratorProofAudit.BindResolved(program, build.Sources, null, prepared.RandomSource);
    Assert.Null(audit.Failure);
    var admission = Method(program, build.AdmissionName);
    var generator = Method(program, "Generate");
    var checker = new ContractSpecificationChecker(program, build.Sources, prepared.Options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [admission, generator],
      Method(program, "Goal").Ins.Select(formal => formal.Type), [], audit);
    return new(program, admission, scope);
  }

  private static string Check(Declaration declaration, ContractNativeProofRole role) =>
    new ContractSpecificationCheck(declaration, role).VerboseName;

  private static ContractGeneratorProofCoverage Coverage(Proof proof, IReadOnlySet<string> covered, bool failed = false) {
    var admission = Check(proof.Admission, ContractNativeProofRole.Correctness);
    return new(proof.Scope.RequiredNativeChecks.ToHashSet(StringComparer.Ordinal), covered,
      proof.Scope.Failure == null, admission, new HashSet<string>([admission], StringComparer.Ordinal), failed);
  }

  // Sibling helpers retain their authored identity and location while the original target contract remains intact.
  [Fact]
  public async Task PreparationPreservesTargetContractAndMapsSiblingLemma() {
    var prepared = await Prepare();
    var original = Method(prepared.Original, "Goal");
    Assert.Equal(original.Req.Select(requirement => Printer.ExprToString(prepared.Options, requirement.E)),
      prepared.Goal.Req.Select(requirement => Printer.ExprToString(prepared.Options, requirement.E)));
    Assert.Equal(original.Ens.Select(ensure => Printer.ExprToString(prepared.Options, ensure.E)),
      prepared.Goal.Ens.Select(ensure => Printer.ExprToString(prepared.Options, ensure.E)));
    Assert.Empty(prepared.Generator.Req);
    Assert.IsType<AssertStmt>(Assert.Single(prepared.Goal.Body!.Body));
    var lemma = Method(prepared.Program, "TwiceIsNonnegative");
    Assert.IsType<Lemma>(lemma);
    var call = Assert.Single(prepared.Generator.Body!.Descendants().OfType<CallStmt>());
    Assert.Same(lemma, call.Method);
    var location = prepared.Preparation.SourceMap.ResolveLocation(lemma.Origin.Uri, lemma.Origin.pos, lemma.FullDafnyName);
    Assert.Equal(GeneratorPath, location.Path);
    Assert.Equal(ContractHarnessBuilder.Hash(GeneratorSource), location.Sha256);
    Assert.Null(await RawAudit(prepared));
  }

  // The exact called sibling lemma and the function reached through Twice remain required native proof declarations.
  [Fact]
  public async Task ProofClosureRequiresSiblingLemmaAndTransitiveFunction() {
    var proof = await PrepareProof(await Prepare());
    Assert.Null(proof.Scope.Failure);
    var lemma = Method(proof.Program, "TwiceIsNonnegative");
    var transitive = Assert.Single(proof.Program.Descendants().OfType<Function>().Where(function => function.Name == "Add"));
    Assert.True(proof.Scope.ContainsDeclaration(lemma));
    Assert.True(proof.Scope.ContainsDeclaration(transitive));
    Assert.Contains(Check(lemma, ContractNativeProofRole.Correctness), proof.Scope.RequiredNativeChecks);
    Assert.Contains(Check(transitive, ContractNativeProofRole.WellFormedness), proof.Scope.RequiredNativeChecks);
    Assert.False(proof.Scope.ContainsDeclaration(Method(proof.Program, "Goal")));
  }

  // Complete fake coverage over the discovered helper checks satisfies bookkeeping without minting any real certificate.
  [Fact]
  public async Task CompleteHelperCoverageSatisfiesCoverageContract() {
    var proof = await PrepareProof(await Prepare());
    var covered = proof.Scope.RequiredNativeChecks.ToHashSet(StringComparer.Ordinal);
    Assert.True(ContractGeneratorProof.AcceptCoverage(Coverage(proof, covered)));
  }

  // Positive admission evidence cannot hide a missing correctness check for the actual called sibling lemma.
  [Fact]
  public async Task MissingSiblingLemmaCoverageCannotCertifyGenerator() {
    var proof = await PrepareProof(await Prepare());
    var lemmaCheck = Check(Method(proof.Program, "TwiceIsNonnegative"), ContractNativeProofRole.Correctness);
    var covered = proof.Scope.RequiredNativeChecks.ToHashSet(StringComparer.Ordinal);
    Assert.True(covered.Remove(lemmaCheck));
    Assert.False(ContractGeneratorProof.AcceptCoverage(Coverage(proof, covered)));
  }

  // A false helper stays in the checked closure and simulated failed native evidence cannot certify admission.
  [Fact]
  public async Task FailedSiblingLemmaEvidenceCannotCertifyGenerator() {
    var prepared = await Prepare(GeneratorSource.Replace("ensures Twice(value) >= 0", "ensures false", StringComparison.Ordinal));
    var proof = await PrepareProof(prepared);
    var lemma = Method(proof.Program, "TwiceIsNonnegative");
    Assert.Contains(Check(lemma, ContractNativeProofRole.Correctness), proof.Scope.RequiredNativeChecks);
    Assert.False(ContractGeneratorProof.AcceptCoverage(Coverage(proof,
      proof.Scope.RequiredNativeChecks.ToHashSet(StringComparer.Ordinal), failed: true)));
  }

  // An assumption in a called sibling lemma cannot enter an audited generator proof closure.
  [Fact]
  public async Task AssumptionInSiblingLemmaRejectsProofScope() {
    var proof = await PrepareProof(await Prepare(GeneratorSource.Replace(
      "assert Twice(value) == value + value;", "assume Twice(value) >= 0;", StringComparison.Ordinal)));
    Assert.Contains("assume", proof.Scope.Failure, StringComparison.Ordinal);
  }

  // Marking a sibling lemma as an axiom is rejected even though preparation accepts its callable syntax.
  [Fact]
  public async Task AxiomaticSiblingLemmaRejectsRawAudit() {
    var prepared = await Prepare(GeneratorSource.Replace("lemma TwiceIsNonnegative", "lemma {:axiom} TwiceIsNonnegative",
      StringComparison.Ordinal));
    Assert.Contains("Unsupported or trust-affecting source attribute", await RawAudit(prepared), StringComparison.Ordinal);
  }

  // Authored generator preconditions cannot restrict the universal generation proof even when helpers are present.
  [Fact]
  public async Task AuthoredGeneratorRequiresRejectsRawAudit() {
    var prepared = await Prepare(GeneratorSource.Replace("returns (x: int) {", "returns (x: int) requires false {",
      StringComparison.Ordinal));
    Assert.Contains("must not have authored requires", await RawAudit(prepared), StringComparison.Ordinal);
  }

  // A generator file cannot smuggle an unsupported sibling class through the callable/datatype merge boundary.
  [Fact]
  public async Task UnsupportedSiblingClassRejectsPreparation() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(GeneratorSource + "\nclass Extra {}"));
    Assert.Contains("callable or datatype", error.Message, StringComparison.Ordinal);
  }
}
