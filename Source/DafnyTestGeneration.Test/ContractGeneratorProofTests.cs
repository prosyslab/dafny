#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test;

// Test boundary trace: helpers construct fresh DafnyOptions instances, detach bounded option values, inherited AI settings, C# backend and seven TestGenerationOptions fields, parse the bounded in-memory user module and embedded PbtRandom resource, and semantic binding tests re-resolve those source strings before printing the AST into a bounded in-memory writer and checking resolved references. No helper writes/stages source, creates directories, syncs, starts a process, invokes a native verifier/solver, or schedules deferred cleanup.
public sealed class ContractGeneratorProofTests {
  private const string UserPath = "/workspace/tmp/pbt-generator-proof-memory/M.dfy";
  private const string RandomPath = "/workspace/tmp/pbt-generator-proof-memory/PbtRandom.dfy";
  private readonly ITestOutputHelper output;

  private sealed record Parsed(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources,
    Method Goal, Method Generator);

  private sealed record PreparedBindingFixture(Program Program, DafnyOptions Options,
    IReadOnlyList<ContractSource> Sources, Method Goal, Method Generator,
    IReadOnlyList<Reference> ParentlessReferences);

  private sealed class CustomCsharpBackend : Microsoft.Dafny.Compilers.CsharpBackend {
    public CustomCsharpBackend(DafnyOptions options) : base(options) { }
  }

  public ContractGeneratorProofTests(ITestOutputHelper output) {
    this.output = output;
  }

  private static string PbtRandomSource {
    get {
      var runtime = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");
      const string marker = "module {:extern \"DafnyPbtRandom\"} PbtRandom {";
      var start = runtime.IndexOf(marker, StringComparison.Ordinal);
      return start < 0 ? throw new InvalidOperationException("Pinned PbtRandom module is missing.") : runtime[start..];
    }
  }

  private static DafnyOptions Options(bool allowNonterminationFunctions = false) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    if (!options.TryCreateDetachedSnapshot(out var detached, out var failure)) {
      throw new InvalidOperationException("Test option fixture could not be detached: " + failure);
    }
    options = detached;
    options.TimeLimit = 1;
    if (allowNonterminationFunctions) {
      options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);
    }
    return options;
  }

  private static IReadOnlyList<ContractSource> Sources(string userSource, string? randomSource = null) {
    var random = randomSource ?? PbtRandomSource;
    return [
      new(UserPath, userSource, ContractHarnessBuilder.Hash(userSource)),
      new(RandomPath, random, ContractHarnessBuilder.Hash(random))
    ];
  }

  private static async Task<(Program Program, DafnyOptions Options)> ParseSnapshots(IReadOnlyList<ContractSource> sources,
    bool resolve = true, bool allowNonterminationFunctions = false) {
    var options = Options(allowNonterminationFunctions);
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None, resolve);
    Assert.True(reporter.ErrorCount == 0, BoundedDiagnostics(reporter));
    return (program, options);
  }

  private static string BoundedDiagnostics(BatchErrorReporter reporter) => string.Join("\n",
    reporter.AllMessages.Take(16).Select(message => message.Message.Length <= 1024
      ? message.Message : message.Message[..1024]));

  private static async Task<(Program Program, DafnyOptions Options, IReadOnlyList<ContractSource> Sources)> Parse(
    string userSource, bool resolve = false, string? randomSource = null, bool allowNonterminationFunctions = false) {
    var sources = Sources(userSource, randomSource);
    var (program, options) = await ParseSnapshots(sources, resolve, allowNonterminationFunctions);
    return (program, options, sources);
  }

  private static async Task<Parsed> ParsePrepared(string generatorBody = "xs := [];", string requirement = "Allowed(xs)") {
    var source = $$"""
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 || xs[0] == 0 }
        method Goal(xs: seq<int>) requires {{requirement}} { assert false; }
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { {{generatorBody}} }
      }
      """;
    var (program, options, sources) = await Parse(source, resolve: true);
    var methods = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    return new(program, options, sources,
      Assert.Single(methods.Where(method => method.Name == "Goal")),
      Assert.Single(methods.Where(method => method.Name == "Generate")));
  }

  private static async Task<PreparedBindingFixture> ParseCliPreparedBindingFixture() {
    const string userSource = "module M { method Goal(x: int) requires x >= 0 { assert x < 0; } }\n";
    const string generatorText = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 2; }\n";
    IReadOnlyList<ContractSource> sources = [
      new(UserPath, userSource, ContractHarnessBuilder.Hash(userSource))
    ];
    var options = Options();
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    options.DisableScopes = true;
    var reporter = new BatchErrorReporter(options);
    var original = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, BoundedDiagnostics(reporter));
    var originalGoal = Assert.Single(original.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = new ContractSource("/workspace/tmp/pbt-generator-proof-memory/Generator.dfy", generatorText,
      ContractHarnessBuilder.Hash(generatorText));
    var preparation = await ContractRuntimeSourcePreparation.PrepareAsync(original, sources, originalGoal, [], generator,
      options, CancellationToken.None);
    var visibilityReporter = new BatchErrorReporter(options);
    var visibilityProgram = await ContractSourceSnapshot.ParseAsync(visibilityReporter, preparation.Sources,
      CancellationToken.None, resolve: false);
    Assert.True(visibilityReporter.ErrorCount == 0, BoundedDiagnostics(visibilityReporter));
    var snapshots = ContractRuntimeObligationTransformer.MakeGeneratorVisible(visibilityProgram, preparation.Sources,
      preparation.DiagnosticConstructors ?? new HashSet<string>()).ToList();
    var runtimeSource = ContractRuntimeInstrumentation.DafnySource;
    snapshots.Add(new("PbtRuntime.dfy", runtimeSource, ContractHarnessBuilder.Hash(runtimeSource)));
    var deferredDiagnostics = new List<DafnyDiagnostic>();
    reporter = new BatchErrorReporter(options);
    var preparedProgram = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, CancellationToken.None,
      deferredGhostDiagnostics: deferredDiagnostics);
    Assert.True(reporter.ErrorCount == 0, BoundedDiagnostics(reporter));
    var members = ContractRuntimeObligationTransformer.Members(preparedProgram).OfType<Method>().ToList();
    var goal = Assert.Single(members.Where(method => method.Name == "Goal"));
    var preparedGenerator = Assert.Single(members.Where(method => method.Name == "Generate" &&
      method.EnclosingClass.EnclosingModuleDefinition == goal.EnclosingClass.EnclosingModuleDefinition));
    var parentlessReferences = FingerprintReferences(preparedProgram)
      .Where(reference => reference.Referred is TopLevelDecl { EnclosingModuleDefinition: null }).ToList();
    return new(preparedProgram, options, snapshots, goal, preparedGenerator, parentlessReferences);
  }

  private static IEnumerable<Reference> FingerprintReferences(Program program) {
    foreach (var sourceNode in program.Descendants().OfType<IHasReferences>()) {
      foreach (var reference in sourceNode.GetReferences()) { yield return reference; }
    }
    foreach (var expression in program.Descendants().OfType<Expression>()) {
      if (expression.Type is { } type) {
        foreach (var referenceNode in type.Nodes.OfType<IHasReferences>()) {
          foreach (var reference in referenceNode.GetReferences()) { yield return reference; }
        }
      }
      foreach (var componentType in expression.ComponentTypes) {
        foreach (var referenceNode in componentType.Nodes.OfType<IHasReferences>()) {
          foreach (var reference in referenceNode.GetReferences()) { yield return reference; }
        }
      }
    }
  }

  private static string DescribeParentlessReferences(IEnumerable<Reference> references) => string.Join("\n",
    references.Select(reference => {
      var declaration = (TopLevelDecl)reference.Referred;
      var range = declaration.NavigationRange;
      var lexicalOwner = declaration is TypeParameter parameter
        ? $" parent={parameter.Parent?.GetType().FullName}:{parameter.Parent?.FullName} index={parameter.PositionalIndex}"
        : "";
      return $"{declaration.GetType().FullName} kind={declaration.WhatKind} name={declaration.Name} " +
        $"origin={declaration.Origin.Uri} navigation={range.StartToken.filename}:{range.StartToken.pos}-{range.EndToken.pos}" + lexicalOwner;
    }));

  private static string? RawAudit(Program rawProgram, IReadOnlyList<ContractSource> sources, Method generator,
    string goalFullName, string? randomSource = null) =>
    ContractGeneratorProofAudit.AuditRawProgram(rawProgram, sources, generator.Origin.Uri, generator.Name,
      goalFullName, randomSource ?? PbtRandomSource);

  private static (Method Goal, Method Generator, Method Admission) ProofMethods(Program program,
    ContractGeneratorProofSourceBuild build, Method originalGoal, Method originalGenerator) {
    var methods = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    return (
      Assert.Single(methods.Where(method => method.FullDafnyName == originalGoal.FullDafnyName && method.Origin.Uri == originalGoal.Origin.Uri)),
      Assert.Single(methods.Where(method => method.FullDafnyName == originalGenerator.FullDafnyName && method.Origin.Uri == originalGenerator.Origin.Uri)),
      Assert.Single(methods.Where(method => method.Name == build.AdmissionName && method.Origin.Uri == originalGoal.Origin.Uri)));
  }

  // A complete fake native state needs every expected check and verified admission correctness evidence.
  [Fact]
  public void CoverageAcceptsOnlyCompletePositiveAdmissionEvidence() {
    var required = new HashSet<string>(["Goal.Admission (correctness)", "M.Allowed (well-formedness)"], StringComparer.Ordinal);
    var complete = new ContractGeneratorProofCoverage(required, new HashSet<string>(required, StringComparer.Ordinal),
      true, "Goal.Admission (correctness)", new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal), false);

    Assert.True(ContractGeneratorProof.AcceptCoverage(complete));
  }

  // A failed native implementation can never be certified by fake state.
  [Fact]
  public void CoverageRejectsFailedNativeImplementation() {
    var required = new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal);
    var failed = new ContractGeneratorProofCoverage(required, new HashSet<string>(required, StringComparer.Ordinal),
      true, "Goal.Admission (correctness)", new HashSet<string>(), true);
    Assert.False(ContractGeneratorProof.AcceptCoverage(failed));
  }

  // An assertion-free admission implementation has no positive correctness evidence.
  [Fact]
  public void CoverageRejectsAssertionFreeAdmissionImplementation() {
    var required = new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal);
    var assertionFree = new ContractGeneratorProofCoverage(required, new HashSet<string>(required, StringComparer.Ordinal),
      true, "Goal.Admission (correctness)", new HashSet<string>(), false);

    Assert.False(ContractGeneratorProof.AcceptCoverage(assertionFree));
  }

  // A proof with no required native procedures cannot create a certificate.
  [Fact]
  public void CoverageRejectsZeroNativeProcedures() {
    var positive = new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal);
    var zero = new ContractGeneratorProofCoverage(new HashSet<string>(), new HashSet<string>(),
      true, "Goal.Admission (correctness)", positive, false);

    Assert.False(ContractGeneratorProof.AcceptCoverage(zero));
  }

  // Missing one required native declaration makes a partial proof non-certifying.
  [Fact]
  public void CoverageRejectsIncompleteNativeProcedureCoverage() {
    var positive = new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal);
    var missing = new ContractGeneratorProofCoverage(new HashSet<string>(["Goal.Admission (correctness)", "M.P (well-formedness)"], StringComparer.Ordinal),
      new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal), true,
      "Goal.Admission (correctness)", positive, false);

    Assert.False(ContractGeneratorProof.AcceptCoverage(missing));
  }

  // Verified work on an unrelated implementation cannot substitute for required admission correctness coverage.
  [Fact]
  public void CoverageRejectsUnrelatedAdmissionEvidence() {
    var required = new HashSet<string>(["M.Other (well-formedness)"], StringComparer.Ordinal);
    var unrelated = new ContractGeneratorProofCoverage(required, new HashSet<string>(required, StringComparer.Ordinal),
      true, "Goal.Admission (correctness)", new HashSet<string>(["Goal.Admission (correctness)"], StringComparer.Ordinal), false);

    Assert.False(ContractGeneratorProof.AcceptCoverage(unrelated));
  }

  // Division and index well-formedness cannot be assumed under the proof certificate policy.
  [Fact]
  public void ProofOptionsRejectAssumedWellFormednessChecks() {
    var options = Options();
    options.Set(CommonOptionBag.AssumeWellFormedDiv, true);

    Assert.Contains("assume division or index", ContractGeneratorProof.ProofOptionFailure(options));
  }

  // Index well-formedness cannot be assumed under the proof certificate policy.
  [Fact]
  public void ProofOptionsRejectAssumedIndexWellFormedness() {
    var options = Options();
    options.Set(CommonOptionBag.AssumeWellFormedIndex, true);

    Assert.Contains("assume division or index", ContractGeneratorProof.ProofOptionFailure(options));
  }

  // Explicit verifier skip flags cannot be normalized into a proof attempt.
  [Fact]
  public void ProofOptionsRejectVerificationSkip() {
    var options = Options();
    options.Set(BoogieOptionBag.NoVerify, true);
    options.Verify = false;
    options.DafnyVerify = false;

    Assert.Contains("Verification-skipping", ContractGeneratorProof.ProofOptionFailure(options));
  }

  // A backend subclass cannot replace the exact built-in C# target capability identity.
  [Fact]
  public void ProofOptionsRejectCustomBackend() {
    var options = Options();
    options.Backend = new CustomCsharpBackend(options);

    Assert.Contains("exact built-in C# backend", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.False(options.TryCreateDetachedSnapshot(out _, out _));
  }

  // A detached snapshot owns a distinct C# backend created for that detached options object.
  [Fact]
  public void DetachedSnapshotPreservesFreshCsharpBackend() {
    var options = Options();
    var originalBackend = options.Backend;

    Assert.True(options.TryCreateDetachedSnapshot(out var detached, out var failure), failure);
    Assert.IsType<Microsoft.Dafny.Compilers.CsharpBackend>(detached.Backend);
    Assert.NotSame(originalBackend, detached.Backend);
  }

  // A populated TestGenerationOptions object is copied without sharing mutable settings state.
  [Fact]
  public void DetachedSnapshotCopiesTestGenerationOptions() {
    var options = Options();
    var original = options.TestGenOptions;
    original.WarnDeadCode = true;
    original.IgnoreWarnings = true;
    original.Mode = TestGenerationOptions.Modes.Block;
    original.SeqLengthLimit = 7;
    original.PrintBpl = "before.bpl";
    original.ForcePrune = true;
    original.CoverageReport = "before.json";

    Assert.True(options.TryCreateDetachedSnapshot(out var detached, out var failure), failure);
    var copied = detached.TestGenOptions;
    Assert.NotSame(original, copied);
    Assert.True(copied.WarnDeadCode);
    Assert.True(copied.IgnoreWarnings);
    Assert.Equal(TestGenerationOptions.Modes.Block, copied.Mode);
    Assert.Equal(7U, copied.SeqLengthLimit);
    Assert.Equal("before.bpl", copied.PrintBpl);
    Assert.True(copied.ForcePrune);
    Assert.Equal("before.json", copied.CoverageReport);
    original.PrintBpl = "after.bpl";
    Assert.Equal("before.bpl", copied.PrintBpl);
  }

  // Lazily materializing default test-generation settings preserves the effective proof settings identity.
  [Fact]
  public void OptionsFingerprintPreservesLazyTestGenerationDefaults() {
    var options = Options();
    var fingerprint = ContractGeneratorProof.OptionsFingerprint(options);

    _ = options.TestGenOptions;

    Assert.Equal(fingerprint, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Non-default test-generation modes cannot silently change the proof settings policy.
  [Fact]
  public void ProofOptionsRejectNonDefaultTestGenerationMode() {
    var options = Options();
    options.TestGenOptions.Mode = TestGenerationOptions.Modes.Block;

    Assert.Contains("Non-default test-generation modes", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
  }

  // A raw prover preamble can inject un-audited Boogie axioms and is rejected even before verification.
  [Fact]
  public void ProofOptionsRejectRawProverPreamble() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.ProverPreamble = "axiom false;";

    Assert.Contains("Raw prover preambles", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Unsound loop-unrolling settings cannot remove generator proof obligations.
  [Fact]
  public void ProofOptionsRejectNonDefaultLoopUnrollCount() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.LoopUnrollCount++;

    Assert.Contains("loop-unrolling", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Stratified inlining must keep the pinned default verification semantics.
  [Fact]
  public void ProofOptionsRejectNonDefaultStratifiedInlining() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.StratifiedInlining++;

    Assert.Contains("stratified-inlining", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Contract inference cannot alter the obligations covered by the native proof report.
  [Fact]
  public void ProofOptionsRejectNonDefaultContractInference() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.ContractInfer = !options.ContractInfer;

    Assert.Contains("contract-inference", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Each case flips one public Boogie mode and confirms that both the proof policy and settings binding notice it.
  [Theory]
  [InlineData(nameof(DafnyOptions.ConcurrentHoudini))]
  [InlineData(nameof(DafnyOptions.HoudiniUseCrossDependencies))]
  [InlineData(nameof(DafnyOptions.StagedHoudini))]
  [InlineData(nameof(DafnyOptions.DebugStagedHoudini))]
  [InlineData(nameof(DafnyOptions.StagedHoudiniReachabilityAnalysis))]
  [InlineData(nameof(DafnyOptions.StagedHoudiniMergeIgnoredAnnotations))]
  [InlineData(nameof(DafnyOptions.StagedHoudiniThreads))]
  [InlineData(nameof(DafnyOptions.VariableDependenceIgnore))]
  [InlineData(nameof(DafnyOptions.ModifyTopologicalSorting))]
  [InlineData(nameof(DafnyOptions.DebugConcurrentHoudini))]
  [InlineData(nameof(DafnyOptions.UseUnsatCoreForContractInfer))]
  [InlineData(nameof(DafnyOptions.ExplainHoudini))]
  [InlineData(nameof(DafnyOptions.ReverseHoudiniWorklist))]
  [InlineData(nameof(DafnyOptions.InstrumentWithAsserts))]
  [InlineData(nameof(DafnyOptions.InstrumentInfer))]
  [InlineData(nameof(DafnyOptions.IntraproceduralInfer))]
  [InlineData(nameof(DafnyOptions.VerifySeparately))]
  [InlineData(nameof(DafnyOptions.VerifySnapshots))]
  [InlineData(nameof(DafnyOptions.UseSubsumption))]
  [InlineData(nameof(DafnyOptions.ReflectAdd))]
  [InlineData(nameof(DafnyOptions.KInductionDepth))]
  [InlineData(nameof(DafnyOptions.SoundnessSmokeTest))]
  public void ProofOptionsRejectNonDefaultNativeModes(string memberName) {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    SetNativeModeAwayFromCurrentValue(options, memberName);

    Assert.Contains("Non-default Houdini", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  private static void SetNativeModeAwayFromCurrentValue(DafnyOptions options, string memberName) {
    var flags = BindingFlags.Instance | BindingFlags.Public;
    var property = typeof(DafnyOptions).GetProperty(memberName, flags);
    var field = typeof(DafnyOptions).GetField(memberName, flags);
    var memberType = property?.PropertyType ?? field?.FieldType ??
      throw new InvalidOperationException("The Boogie mode member is not public: " + memberName);
    var currentValue = property != null ? property.GetValue(options) : field!.GetValue(options);
    var changedValue = currentValue switch {
      null when memberType == typeof(string) => "x",
      bool value => !value,
      int value => value == int.MaxValue ? int.MinValue : value + 1,
      uint value => value == uint.MaxValue ? 0U : value + 1,
      long value => value == long.MaxValue ? long.MinValue : value + 1,
      ulong value => value == ulong.MaxValue ? 0UL : value + 1,
      string value => value + "x",
      Enum value => Enum.ToObject(memberType, Convert.ToInt64(value) + 1),
      _ => throw new InvalidOperationException("The Boogie mode value has no bounded mutation: " + memberName)
    };
    if (property != null) {
      if (!property.CanWrite) { throw new InvalidOperationException("The Boogie mode property is read-only: " + memberName); }
      property.SetValue(options, changedValue);
    } else {
      field!.SetValue(options, changedValue);
    }
  }

  // A custom solver plugin cannot issue a trusted native proof certificate.
  [Fact]
  public void ProofOptionsRejectCustomSolverPlugin() {
    var options = Options();
    options.Set(BoogieOptionBag.SolverPlugin, "custom-plugin.dll");

    Assert.Contains("Custom verifier plugins", ContractGeneratorProof.ProofOptionFailure(options));
  }

  // Caller-selected solver paths cannot replace the exact trusted system executable.
  [Fact]
  public void ProofOptionsRejectCallerSelectedSolverPath() {
    var options = Options();
    options.Set(BoogieOptionBag.SolverPath, new FileInfo("/custom/z3"));

    Assert.Contains("Custom verifier plugins", ContractGeneratorProof.ProofOptionFailure(options));
  }

  // A concrete module, exact PbtRandom import and nontrivial sequence predicate survive the strict raw audit.
  [Fact]
  public async Task RawAuditAcceptsConcreteSequencePredicateAndExactGeneratorMarker() {
    const string source = """
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 || xs[0] == 0 }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source);
    var methods = rawProgram.Descendants().OfType<Method>().Where(method => method.Name is "Goal" or "Generate").ToList();
    Assert.Single(methods.Where(method => method.Name == "Goal"));
    var generator = Assert.Single(methods.Where(method => method.Name == "Generate"));

    Assert.Null(RawAudit(rawProgram, sources, generator, "M.Goal"));
    Assert.Equal(2, sources.Count);
  }

  // Trust-bearing user attributes are rejected before resolution can add compiler-generated attributes.
  [Fact]
  public async Task RawAuditRejectsAxiomAttributeOnUnrelatedGlobalPredicate() {
    const string source = """
      module M {
        import PbtRandom
        predicate {:axiom} Allowed(xs: seq<int>)
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source);
    Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));

    Assert.Contains("Unsupported or trust-affecting source attribute", RawAudit(rawProgram, sources, generator, "M.Goal"));
  }

  // A nested user module named PbtRandom cannot inherit the exact embedded runtime's trust exception.
  [Fact]
  public async Task RawAuditRejectsNestedUserPbtRandomModule() {
    const string source = """
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      module Wrapper {
        module PbtRandom {
          predicate {:axiom} Unsafe()
        }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source);
    Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));

    Assert.Contains("exact top-level module", RawAudit(rawProgram, sources, generator, "M.Goal"), StringComparison.Ordinal);
  }

  // An assumption in an unrelated method body is not retained in the proof scope for a different generator.
  [Fact]
  public async Task RawAuditAllowsAssumeInUnrelatedOrdinaryMethodBody() {
    const string source = """
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Pending() { assume true; }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source);
    Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));

    Assert.Null(RawAudit(rawProgram, sources, generator, "M.Goal"));
  }

  // Assumptions in the exact selected generator closure fail its audit-bound execution scope.
  [Fact]
  public async Task ExecutionScopeRejectsAssumeInSelectedGenerator() {
    var parsed = await ParsePrepared("assume true; xs := [];");
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(parsed.Program, parsed.Sources, parsed.Options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [parsed.Generator],
      parsed.Generator.Ins.Select(formal => formal.Type), [], audit);

    Assert.Contains("assume", scope.Failure, StringComparison.Ordinal);
  }

  // An expect statement is translated as an unchecked assumption and cannot remain in the selected generator closure.
  [Fact]
  public async Task ExecutionScopeRejectsExpectInSelectedGenerator() {
    var parsed = await ParsePrepared("expect false, \"generator guard\"; xs := [];");
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(parsed.Program, parsed.Sources, parsed.Options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [parsed.Generator],
      parsed.Generator.Ins.Select(formal => formal.Type), [], audit);

    Assert.Contains("expect", scope.Failure, StringComparison.Ordinal);
  }

  // A proof helper retained through the logical role cannot rely on an unchecked expect statement.
  [Fact]
  public async Task LogicalScopeRejectsExpectInRetainedMethodBody() {
    const string source = """
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Helper() { expect false, "logical guard"; }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (program, options, sources) = await Parse(source, resolve: true);
    var helper = Assert.Single(program.Descendants().OfType<Method>().Where(method => method.Name == "Helper"));
    var audit = ContractGeneratorProofAudit.BindResolved(program, sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(program, sources, options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Logical, [helper], [], [], audit);

    Assert.Contains("expect", scope.Failure, StringComparison.Ordinal);
  }

  // A retained unrelated ordinary method body remains outside the selected generator execution proof closure.
  [Fact]
  public async Task ExecutionScopeAllowsExpectInUnrelatedMethod() {
    const string source = """
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Unrelated() { expect false, "unrelated"; }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (program, options, sources) = await Parse(source, resolve: true);
    var generator = Assert.Single(program.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));
    var audit = ContractGeneratorProofAudit.BindResolved(program, sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(program, sources, options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [generator],
      generator.Ins.Select(formal => formal.Type), [], audit);

    Assert.Null(scope.Failure);
    Assert.DoesNotContain(scope.Declarations, declaration => declaration.Name == "Unrelated");
  }

  // Let-such-that is rejected because its translation contributes a global Skolem axiom.
  [Fact]
  public async Task RawAuditRejectsLetSuchThatInAnUnrelatedFunction() {
    const string source = """
      module M {
        import PbtRandom
        function Choose(): int { var x :| x >= 0; x }
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source);
    Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));

    Assert.Contains("Let-such-that", RawAudit(rawProgram, sources, generator, "M.Goal"));
  }

  // The unsound function-level decreases-star option cannot introduce retained nonterminating logical assumptions.
  [Fact]
  public async Task RawAuditRejectsFunctionDecreasesStarWhenOptionIsEnabled() {
    const string source = """
      module M {
        import PbtRandom
        function Diverges(): int decreases * { 0 }
        predicate Allowed(xs: seq<int>) { |xs| == 0 }
        method Goal(xs: seq<int>) requires Allowed(xs) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var (rawProgram, _, sources) = await Parse(source, allowNonterminationFunctions: true);
    Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var generator = Assert.Single(rawProgram.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));

    Assert.Contains("decreases *", RawAudit(rawProgram, sources, generator, "M.Goal"), StringComparison.Ordinal);
  }

  // Resolved substitution preserves shadowed binders, static-member identity and both requires clauses across UTF-8 byte edits.
  [Fact]
  public async Task PreparedSourcesPreserveRequirementBindingsAndUtf8Offsets() {
    const string source = """
      // UTF-8 anchor 🧭 before the module and every edited declaration
      module M {
        import PbtRandom
        predicate Allowed(xs: seq<int>) { false }
        class C {
          static predicate Allowed(xs: seq<int>) { |xs| == 0 || xs[0] >= 0 }
          static method Goal(xs: seq<int>)
            requires Allowed(xs)
            requires forall PbtGeneratorAdmissionOutput0: int :: PbtGeneratorAdmissionOutput0 >= 0 || xs == xs
          {}
        }
        method {:pbt_generator "M.C.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var parsedRaw = await Parse(source, resolve: true);
    var methods = parsedRaw.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    var goal = Assert.Single(methods.Where(method => method.Name == "Goal"));
    var generator = Assert.Single(methods.Where(method => method.Name == "Generate"));

    var build = ContractGeneratorProof.PrepareProofSources(parsedRaw.Program, parsedRaw.Sources,
      goal, generator, PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    Assert.NotEqual("PbtGeneratorAdmissionOutput0", build!.OutputNames[0]);
    var proof = await ParseSnapshots(build.Sources);
    var proofMethods = ProofMethods(proof.Program, build, goal, generator);
    Assert.Null(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      proofMethods.Goal, proofMethods.Generator, proofMethods.Admission, build, proof.Options));

    var originalClassPredicate = Assert.Single(proofMethods.Goal.Req[0].E.DescendantsAndSelf.OfType<FunctionCallExpr>()).Function;
    var helper = Assert.Single(proof.Program.Descendants().OfType<Function>()
      .Where(function => function.Name == build.RequirementHelperNames[0]));
    var copiedPredicate = Assert.Single(helper.Body!.DescendantsAndSelf.OfType<FunctionCallExpr>()).Function;
    Assert.Same(originalClassPredicate, copiedPredicate);
    Assert.Equal(2, proofMethods.Generator.Ens.Count);
    var generatedEnsureCalls = proofMethods.Generator.Ens.SelectMany(clause => clause.E.DescendantsAndSelf.OfType<FunctionCallExpr>())
      .Where(call => build.RequirementHelperNames.Contains(call.Function.Name, StringComparer.Ordinal)).ToList();
    Assert.Equal(build.RequirementHelperNames, generatedEnsureCalls.Select(call => call.Function.Name));
    Assert.Equal(2, proofMethods.Admission.Descendants().OfType<AssertStmt>().Count());
  }

  // Reordered generated postconditions cannot bind to the original ordered requirements.
  [Fact]
  public async Task PreparedSourcesRejectReorderedRequirementPostconditions() {
    var parsed = await ParsePrepared(requirement: "Allowed(xs) && true");
    var source = ContractSourceSnapshot.Find(parsed.Sources, parsed.Goal.Origin.Uri);
    var changed = ContractSourceSnapshot.Replace(parsed.Sources, source.Path,
      source.Content.Replace("requires Allowed(xs) && true", "requires Allowed(xs)\n          requires true", StringComparison.Ordinal));
    var reparsedInput = await ParseSnapshots(changed);
    var changedGoal = Assert.Single(reparsedInput.Program.Descendants().OfType<Method>().Where(method => method.Name == "Goal"));
    var changedGenerator = Assert.Single(reparsedInput.Program.Descendants().OfType<Method>().Where(method => method.Name == "Generate"));
    var build = ContractGeneratorProof.PrepareProofSources(reparsedInput.Program, changed, changedGoal, changedGenerator,
      PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var proofMethods = ProofMethods(proof.Program, build, changedGoal, changedGenerator);
    proofMethods.Generator.Ens.Reverse();

    Assert.NotNull(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      proofMethods.Goal, proofMethods.Generator, proofMethods.Admission, build, proof.Options));
  }

  // A later index requirement retains every earlier condition needed for its well-formedness.
  [Fact]
  public async Task PreparedSourcesPreserveSequentialRequirementPrefixes() {
    const string source = """
      module M {
        import PbtRandom
        method Goal(xs: seq<int>)
          requires |xs| > 0
          requires xs[0] == 0 && (forall value: int :: value == value)
        {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := [0]; }
      }
      """;
    var parsed = await Parse(source, resolve: true);
    var methods = parsed.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    var goal = Assert.Single(methods.Where(method => method.Name == "Goal"));
    var generator = Assert.Single(methods.Where(method => method.Name == "Generate"));
    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources, goal, generator,
      PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);

    var proof = await ParseSnapshots(build!.Sources);
    var proofMethods = ProofMethods(proof.Program, build, goal, generator);
    var helperFunctions = proof.Program.Descendants().OfType<Function>()
      .Where(function => build.RequirementHelperNames.Contains(function.Name, StringComparer.Ordinal))
      .ToDictionary(function => function.Name, StringComparer.Ordinal);
    var helpers = build.RequirementHelperNames.Select(name => helperFunctions[name]).ToList();

    Assert.Empty(helpers[0].Req);
    Assert.Single(helpers[1].Req);
    var helperBody = Assert.IsType<BinaryExpr>(helpers[1].Body!.Resolved);
    Assert.IsType<ForallExpr>(helperBody.E1.Resolved);
    Assert.Null(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      proofMethods.Goal, proofMethods.Generator, proofMethods.Admission, build, proof.Options));
  }

  // Same-spelling quantified variables must retain their lexical binder identities after proof-source reparsing.
  [Fact]
  public async Task PreparedSourcesRejectRetargetedShadowedBinder() {
    var parsed = await ParsePrepared(requirement: "forall value: int :: (forall value: int :: value == value) || xs == xs");
    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var methods = ProofMethods(proof.Program, build, parsed.Goal, parsed.Generator);
    var helper = Assert.Single(proof.Program.Descendants().OfType<Function>()
      .Where(function => function.Name == build.RequirementHelperNames[0]));
    var outerQuantifier = Assert.IsType<ForallExpr>(helper.Body!.Resolved);
    var disjunction = Assert.IsType<BinaryExpr>(outerQuantifier.Term.Resolved);
    var innerQuantifier = Assert.IsType<ForallExpr>(disjunction.E0.Resolved);
    var innerComparison = Assert.IsType<BinaryExpr>(innerQuantifier.Term.Resolved);
    var innerIdentifier = Assert.IsType<IdentifierExpr>(innerComparison.E0.Resolved);
    innerIdentifier.Var = outerQuantifier.BoundVars[0];

    Assert.NotNull(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      methods.Goal, methods.Generator, methods.Admission, build, proof.Options));
  }

  // A false original requirement remains a false helper body and an explicit Generate postcondition obligation.
  [Fact]
  public async Task PreparedSourcesRetainFalseRequirementObligation() {
    var parsed = await ParsePrepared(requirement: "false");
    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var methods = ProofMethods(proof.Program, build, parsed.Goal, parsed.Generator);
    var helper = Assert.Single(proof.Program.Descendants().OfType<Function>()
      .Where(function => function.Name == build.RequirementHelperNames[0]));

    Assert.Equal(false, Assert.IsType<LiteralExpr>(helper.Body).Value);
    Assert.Single(methods.Generator.Ens.SelectMany(clause => clause.E.DescendantsAndSelf.OfType<FunctionCallExpr>())
      .Where(call => call.Function == helper));
    Assert.Single(methods.Admission.Descendants().OfType<AssertStmt>());
  }

  // Proof-source growth beyond a caller-supplied small test budget is rejected before byte edits are allocated.
  [Fact]
  public async Task PreparedSourcesRejectGrowthBeyondBudget() {
    var parsed = await ParsePrepared();
    var originalBytes = parsed.Sources.Sum(source => System.Text.Encoding.UTF8.GetByteCount(source.Content));

    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, PbtRandomSource, out var failure, maximumPreparedSourceBytes: originalBytes);

    Assert.Null(build);
    Assert.Contains("bounded UTF-8 byte policy", failure, StringComparison.Ordinal);
  }

  // A generated admission method must remain precondition-free so proving it does not assume the original goal requirements.
  [Fact]
  public async Task PreparedSourcesRejectAdmissionPreconditionMutation() {
    var parsed = await ParsePrepared();
    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var methods = ProofMethods(proof.Program, build, parsed.Goal, parsed.Generator);
    methods.Admission.Req.Add(new AttributedExpression(methods.Goal.Req[0].E));

    Assert.NotNull(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      methods.Goal, methods.Generator, methods.Admission, build, proof.Options));
  }

  // A mutated resolved original property cannot become the authority for internally synthesized proof snapshots.
  [Fact]
  public async Task PreparedBindingRejectsMutatedResolvedRequirement() {
    var parsed = await ParsePrepared(requirement: "false");
    Assert.IsType<LiteralExpr>(parsed.Goal.Req[0].E).Value = true;

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, parsed.Options, null, CancellationToken.None);

    Assert.Null(binding.Binding);
    Assert.NotNull(binding.Failure);
  }

  // Ghost predicates and unbounded quantifiers remain valid proof-only requirements after resolved substitution and reparsing.
  [Fact]
  public async Task PreparedSourcesRetainGhostPredicateAndUnboundedQuantifier() {
    const string source = """
      module M {
        import PbtRandom
        ghost predicate Nonnegative(xs: seq<int>) {
          forall index: int :: 0 <= index < |xs| ==> xs[index] >= 0
        }
        method Goal(xs: seq<int>)
          requires Nonnegative(xs)
          requires forall value: int :: value == value || Nonnegative(xs)
        {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (xs: seq<int>) { xs := []; }
      }
      """;
    var parsed = await Parse(source, resolve: true);
    var methods = parsed.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    var goal = Assert.Single(methods.Where(method => method.Name == "Goal"));
    var generator = Assert.Single(methods.Where(method => method.Name == "Generate"));

    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources, goal, generator,
      PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var proofMethods = ProofMethods(proof.Program, build, goal, generator);
    var helperFunctions = proof.Program.Descendants().OfType<Function>()
      .Where(function => build.RequirementHelperNames.Contains(function.Name, StringComparer.Ordinal)).ToList();

    Assert.All(helperFunctions, helper => Assert.True(helper.IsGhost));
    Assert.Contains(helperFunctions[0].Body!.DescendantsAndSelf.OfType<FunctionCallExpr>(),
      call => call.Function.Name == "Nonnegative");
    Assert.NotEmpty(helperFunctions[1].Body!.DescendantsAndSelf.OfType<ForallExpr>());
    Assert.Null(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(proof.Program,
      proofMethods.Goal, proofMethods.Generator, proofMethods.Admission, build, proof.Options));
  }

  public enum ScaffoldMutation { WeakenEnsure, WeakenAssertion, ConditionalBody, ReorderAssertions, DropAssertion, ExtraStatement, ChangeHelper }

  // The fingerprint covers the complete synthesized property and ordered proof scaffold, not just descendant calls.
  [Theory]
  [InlineData(ScaffoldMutation.WeakenEnsure)]
  [InlineData(ScaffoldMutation.WeakenAssertion)]
  [InlineData(ScaffoldMutation.ConditionalBody)]
  [InlineData(ScaffoldMutation.ReorderAssertions)]
  [InlineData(ScaffoldMutation.DropAssertion)]
  [InlineData(ScaffoldMutation.ExtraStatement)]
  [InlineData(ScaffoldMutation.ChangeHelper)]
  public async Task SynthesizedFingerprintRejectsScaffoldTampering(ScaffoldMutation mutation) {
    var parsed = await ParsePrepared(requirement: "Allowed(xs) requires true");
    var build = ContractGeneratorProof.PrepareProofSources(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, PbtRandomSource, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await ParseSnapshots(build!.Sources);
    var methods = ProofMethods(proof.Program, build, parsed.Goal, parsed.Generator);
    var source = ContractSourceSnapshot.Find(build.Sources, methods.Admission.Origin.Uri);
    var originalBytes = System.Text.Encoding.UTF8.GetBytes(source.Content);
    var start = methods.Admission.StartToken.pos;
    var length = methods.Admission.EndToken.pos + methods.Admission.EndToken.val.Length - start;
    var declaration = System.Text.Encoding.UTF8.GetString(originalBytes, start, length);
    var open = declaration.IndexOf('{');
    var body = declaration[(open + 1)..^1];
    var lines = body.Split('\n', StringSplitOptions.RemoveEmptyEntries);
    string changed;
    switch (mutation) {
      case ScaffoldMutation.WeakenEnsure: {
          var ensure = methods.Generator.Ens[0].E;
          var ensureText = System.Text.Encoding.UTF8.GetString(originalBytes, ensure.StartToken.pos,
            ensure.EndToken.pos + ensure.EndToken.val.Length - ensure.StartToken.pos);
          changed = source.Content.Replace("ensures " + ensureText, "ensures (" + ensureText + ") || true", StringComparison.Ordinal);
          break;
        }
      case ScaffoldMutation.WeakenAssertion:
        lines[2] = lines[2].Replace("assert ", "assert (", StringComparison.Ordinal).Replace(";", ") || true;", StringComparison.Ordinal);
        changed = source.Content.Replace(declaration, declaration[..(open + 1)] + string.Join("\n", lines) + "}", StringComparison.Ordinal);
        break;
      case ScaffoldMutation.ConditionalBody:
        changed = source.Content.Replace(declaration, declaration[..(open + 1)] + " if false {" + body + "} }", StringComparison.Ordinal);
        break;
      case ScaffoldMutation.ReorderAssertions:
        (lines[2], lines[3]) = (lines[3], lines[2]);
        changed = source.Content.Replace(declaration, declaration[..(open + 1)] + string.Join("\n", lines) + "}", StringComparison.Ordinal);
        break;
      case ScaffoldMutation.DropAssertion:
        changed = source.Content.Replace(declaration, declaration[..(open + 1)] + string.Join("\n", lines.Take(3)) + "}", StringComparison.Ordinal);
        break;
      case ScaffoldMutation.ExtraStatement:
        changed = source.Content.Replace(declaration, declaration[..(open + 1)] + " assert true;" + body + "}", StringComparison.Ordinal);
        break;
      case ScaffoldMutation.ChangeHelper: {
          var helper = Assert.Single(proof.Program.Descendants().OfType<Function>()
            .Where(function => function.Name == build.RequirementHelperNames[0]));
          var expression = helper.Body!;
          var helperStart = expression.StartToken.pos;
          var helperLength = expression.EndToken.pos + expression.EndToken.val.Length - helperStart;
          changed = System.Text.Encoding.UTF8.GetString(originalBytes, 0, helperStart) + "true" +
            System.Text.Encoding.UTF8.GetString(originalBytes, helperStart + helperLength, originalBytes.Length - helperStart - helperLength);
          break;
        }
      default:
        throw new InvalidOperationException("Unknown mutation.");
    }
    Assert.NotEqual(source.Content, changed);
    var altered = await ParseSnapshots(ContractSourceSnapshot.Replace(build.Sources, source.Path, changed));
    var alteredMethods = ProofMethods(altered.Program, build, parsed.Goal, parsed.Generator);

    Assert.NotNull(await ContractGeneratorProof.ValidateProofSourceBindingsAsync(altered.Program,
      alteredMethods.Goal, alteredMethods.Generator, alteredMethods.Admission, build, altered.Options));
  }

  // Clearing an audited scope's native checks cannot turn unverified declarations into accepted coverage.
  [Fact]
  public async Task AuditedScopeRejectsChangedCoverage() {
    var parsed = await ParsePrepared();
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(parsed.Program, parsed.Sources, parsed.Options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [parsed.Generator], [], [], audit);
    Assert.Null(scope.Failure);
    Assert.NotEmpty(scope.Checks);
    scope.Checks.Clear();

    Assert.False(checker.Accept(scope));
  }

  // A changed helper body invalidates an already captured audited closure even when source text is unchanged.
  [Fact]
  public async Task AuditedScopeRejectsChangedProgram() {
    var parsed = await ParsePrepared();
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, PbtRandomSource);
    var helper = Assert.Single(parsed.Program.Descendants().OfType<Function>().Where(function => function.Name == "Allowed"));
    helper.Body = Expression.CreateBoolLiteral(helper.Origin, true);

    Assert.False(audit.IsBoundTo(parsed.Program, parsed.Sources));
  }

  // A changed original declaration cannot be paired with its previously resolved program.
  [Fact]
  public async Task PreparedProgramRejectsChangedSourceSnapshot() {
    var parsed = await ParsePrepared();
    var original = ContractSourceSnapshot.Find(parsed.Sources, parsed.Goal.Origin.Uri);
    var changed = ContractSourceSnapshot.Replace(parsed.Sources, original.Path,
      original.Content.Replace("Allowed(xs)", "Allowed(xs) && true", StringComparison.Ordinal));

    Assert.False(ContractGeneratorProof.PreparedInputsMatchSnapshots(parsed.Program, changed,
      parsed.Goal, parsed.Generator, out _));
  }

  // A normal prepared in-memory generator and its unchanged snapshots pass the source and capability boundary.
  [Fact]
  public async Task PreparedProgramAcceptsMatchingSnapshotsAndSupportedTarget() {
    var parsed = await ParsePrepared();

    Assert.True(ContractGeneratorProof.PreparedInputsMatchSnapshots(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, out var sourceFailure), sourceFailure);
    Assert.True(ContractGeneratorProof.SupportedSelectedGoal(parsed.Program, parsed.Goal, parsed.Generator,
      out var capabilityFailure), capabilityFailure);
    Assert.Null(ContractGeneratorProof.ProofOptionFailure(parsed.Options));
    Assert.True(ContractGeneratorProof.TryOptionsFingerprint(parsed.Options, out _));
  }

  // A prepared Program is admitted only after a fresh resolve of its exact snapshots has the same complete semantics.
  [Fact]
  public async Task PreparedProgramBindingAcceptsExactResolvedSnapshot() {
    var parsed = await ParsePrepared();
    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, parsed.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.NotNull(binding.Binding);
    Assert.Null(binding.Failure);
  }

  // CLI preparation and DisableScopes preserve parentless navigation references through fresh semantic binding.
  [Fact]
  public async Task PreparedProgramBindingAcceptsCliPreparedParentlessNavigationReferences() {
    var fixture = await ParseCliPreparedBindingFixture();
    Assert.NotEmpty(fixture.ParentlessReferences);
    Assert.All(fixture.ParentlessReferences, reference => {
      var parameter = Assert.IsType<TypeParameter>(reference.Referred);
      Assert.NotNull(parameter.Parent);
    });
    output.WriteLine("Parentless prepared references:\n" + DescribeParentlessReferences(fixture.ParentlessReferences));

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(fixture.Program, fixture.Sources,
      fixture.Goal, fixture.Generator, fixture.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.NotNull(binding.Binding);
    Assert.Null(binding.Failure);
  }

  // A changed top-level module and its navigation references cannot reuse the prepared Program binding.
  [Fact]
  public async Task PreparedProgramBindingRejectsChangedRootSourceSnapshot() {
    var fixture = await ParseCliPreparedBindingFixture();
    var userSource = ContractSourceSnapshot.Find(fixture.Sources, ContractSourceSnapshot.UriFor(UserPath));
    var changed = ContractSourceSnapshot.Replace(fixture.Sources, UserPath,
      userSource.Content.Replace("module M", "module N", StringComparison.Ordinal));

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(fixture.Program, changed,
      fixture.Goal, fixture.Generator, fixture.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.Null(binding.Binding);
    Assert.NotNull(binding.Failure);
  }

  // A changed type-parameter owner cannot reuse a fingerprint for the original lexical binding.
  [Fact]
  public async Task PreparedProgramBindingRejectsChangedTypeParameterOwner() {
    var fixture = await ParseCliPreparedBindingFixture();
    var parameter = Assert.IsType<TypeParameter>(fixture.ParentlessReferences[0].Referred);
    parameter.Parent = null;

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(fixture.Program, fixture.Sources,
      fixture.Goal, fixture.Generator, fixture.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.Null(binding.Binding);
    Assert.Equal("The resolved prepared Program differs semantically from a fresh resolve of its exact source snapshots.",
      binding.Failure);
  }

  // A type parameter owner shape without a stable identity fails through the bounded fingerprint error path.
  [Fact]
  public async Task PreparedProgramBindingRejectsUnsupportedTypeParameterOwner() {
    var fixture = await ParseCliPreparedBindingFixture();
    var parameter = Assert.IsType<TypeParameter>(fixture.ParentlessReferences[0].Referred);
    var unsupportedOwner = fixture.ParentlessReferences.Select(reference => reference.Referred)
      .OfType<TypeParameter>().First(candidate => !ReferenceEquals(candidate, parameter));
    parameter.Parent = unsupportedOwner;

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(fixture.Program, fixture.Sources,
      fixture.Goal, fixture.Generator, fixture.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.Null(binding.Binding);
    Assert.NotNull(binding.Failure);
    Assert.True(binding.Failure.StartsWith("The resolved Program cannot be fingerprinted within the proof bounds:",
      StringComparison.Ordinal), binding.Failure);
  }

  // A mutated Generate body cannot be paired with unchanged source snapshots.
  [Fact]
  public async Task PreparedProgramBindingRejectsMutatedGeneratorBody() {
    var parsed = await ParsePrepared();
    var sequence = Assert.Single(parsed.Generator.Body!.Descendants().OfType<SeqDisplayExpr>());
    sequence.Elements.Add(Expression.CreateIntLiteral(sequence.Origin, 1));

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, parsed.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.Null(binding.Binding);
  }

  // A mutated global predicate body cannot be paired with unchanged source snapshots.
  [Fact]
  public async Task PreparedProgramBindingRejectsMutatedLogicalContributor() {
    var parsed = await ParsePrepared();
    var predicate = Assert.Single(parsed.Program.Descendants().OfType<Function>().Where(function => function.Name == "Allowed"));
    Assert.IsType<LiteralExpr>(predicate.Body!.Descendants().OfType<LiteralExpr>()
      .First(literal => Equals(literal.Value, BigInteger.Zero))).Value = BigInteger.One;

    var binding = await ContractGeneratorProof.BindPreparedProgramAsync(parsed.Program, parsed.Sources,
      parsed.Goal, parsed.Generator, parsed.Options, ContractQueryDeadline.AfterMilliseconds(10_000), CancellationToken.None);

    Assert.Null(binding.Binding);
  }

  // The solver version parser accepts only bounded successful Z3 version output.
  [Fact]
  public void SolverVersionParserAcceptsPinnedVersionOutput() {
    Assert.True(ContractGeneratorProof.TryParseZ3Version(0, false, "Z3 version 4.8.12 - 64 bit\n", out var version));
    Assert.Equal("4.8.12", version);
  }

  // Nonzero solver exit status cannot supply a trusted version identity.
  [Fact]
  public void SolverVersionParserRejectsFailedProcess() {
    Assert.False(ContractGeneratorProof.TryParseZ3Version(1, false, "Z3 version 4.8.12", out _));
  }

  // Malformed solver output cannot supply a trusted version identity.
  [Fact]
  public void SolverVersionParserRejectsMalformedOutput() {
    Assert.False(ContractGeneratorProof.TryParseZ3Version(0, false, "not a Z3 version", out _));
  }

  // Oversized solver output cannot supply a trusted version identity.
  [Fact]
  public void SolverVersionParserRejectsOversizedOutput() {
    Assert.False(ContractGeneratorProof.TryParseZ3Version(0, true, "Z3 version 4.8.12", out _));
  }

  // An exact pinned solver path, content hash and version match.
  [Fact]
  public void SolverIdentityAcceptsExactPathHashAndVersion() {
    Assert.True(ContractGeneratorProof.SolverIdentityMatches("/usr/bin/z3", "abc", "4.8.12",
      "/usr/bin/z3", "abc", "4.8.12"));
  }

  // A different executable path cannot match a pinned solver identity.
  [Fact]
  public void SolverIdentityRejectsDifferentPath() {
    Assert.False(ContractGeneratorProof.SolverIdentityMatches("/usr/bin/z3", "abc", "4.8.12",
      "/usr/local/bin/z3", "abc", "4.8.12"));
  }

  // Changed executable bytes cannot match a pinned solver identity.
  [Fact]
  public void SolverIdentityRejectsChangedContentHash() {
    Assert.False(ContractGeneratorProof.SolverIdentityMatches("/usr/bin/z3", "abc", "4.8.12",
      "/usr/bin/z3", "def", "4.8.12"));
  }

  // A different reported solver version cannot match a pinned solver identity.
  [Fact]
  public void SolverIdentityRejectsChangedVersion() {
    Assert.False(ContractGeneratorProof.SolverIdentityMatches("/usr/bin/z3", "abc", "4.8.12",
      "/usr/bin/z3", "abc", "4.8.13"));
  }

  // An inductive datatype input accepts a nested sequence of scalar fields and arguments.
  [Fact]
  public async Task SupportedInputAuditAcceptsNestedSequenceDatatype() {
    const string source = """
      module M {
        datatype Good<T> = GoodValue(item: T)
        method Input(value: Good<seq<int>>) {}
      }
      """;
    var (program, _, _) = await Parse(source, resolve: true);
    var methods = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();
    var method = Assert.Single(methods.Where(candidate => candidate.Name == "Input"));
    Assert.True(ContractGeneratorProof.SupportedValueType(method.Ins[0].Type, new HashSet<string>()));
  }

  // An inductive datatype field cannot hide a reference class input.
  [Fact]
  public async Task SupportedInputAuditRejectsClassTypeInDatatypeField() {
    const string source = """
      module M {
        class Boxed {}
        datatype Holder = HolderValue(item: Boxed)
        method FieldInput(value: Holder) {}
      }
      """;
    var (program, _, _) = await Parse(source, resolve: true);
    var methods = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>().ToList();

    Assert.False(ContractGeneratorProof.SupportedValueType(
      Assert.Single(methods.Where(method => method.Name == "FieldInput")).Ins[0].Type, new HashSet<string>()));
  }

  // A phantom datatype argument cannot hide a reference class input.
  [Fact]
  public async Task SupportedInputAuditRejectsClassTypeInPhantomTypeArgument() {
    const string source = """
      module M {
        class Boxed {}
        datatype Phantom<T> = PhantomValue
        method ArgumentInput(value: Phantom<Boxed>) {}
      }
      """;
    var (program, _, _) = await Parse(source, resolve: true);
    var method = Assert.Single(program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>()
      .Where(candidate => candidate.Name == "ArgumentInput"));

    Assert.False(ContractGeneratorProof.SupportedValueType(method.Ins[0].Type, new HashSet<string>()));
  }

  // Only the exact extracted RNG module declarations are removed by the audit-bound checker scope.
  [Fact]
  public async Task BoundScopeRemovesOnlyExactPinnedRngDeclarations() {
    var parsed = await ParsePrepared("var bit := r.Bool(); xs := if bit then [0] else [];");
    var (rawProgram, _, rawSources) = await Parse(parsed.Sources[0].Content);
    Assert.Null(RawAudit(rawProgram, rawSources, parsed.Generator, "M.Goal"));
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, PbtRandomSource);
    var checker = new ContractSpecificationChecker(parsed.Program, parsed.Sources, parsed.Options);
    var scope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [parsed.Generator],
      parsed.Generator.Ins.Select(formal => formal.Type), [], audit);

    Assert.Null(audit.Failure);
    Assert.Null(scope.Failure);
    Assert.DoesNotContain(scope.Symbols, symbol => symbol.Contains("PbtRandom", StringComparison.Ordinal));
    Assert.Contains(scope.RequiredNativeChecks, check => check.Contains("Generate", StringComparison.Ordinal));
  }

  // Generator execution closure excludes a target whose body is unrelated to generation.
  [Fact]
  public async Task GeneratorExecutionClosureDoesNotIncludeTargetBody() {
    var parsed = await ParsePrepared();

    var reachable = ContractRuntimeObligationTransformer.ExecutionReachable(parsed.Program, [parsed.Generator]);

    Assert.Contains(parsed.Generator, reachable);
    Assert.DoesNotContain(parsed.Goal, reachable);
  }

  // A target-body call reachable from Generate is visible to the pre-verification rejection boundary.
  [Fact]
  public async Task GeneratorExecutionClosureDetectsTargetBodyReentry() {
    var parsed = await ParsePrepared("xs := []; Goal(xs);");

    var reachable = ContractRuntimeObligationTransformer.ExecutionReachable(parsed.Program, [parsed.Generator]);

    Assert.Contains(parsed.Goal, reachable);
  }

  // A changed embedded RNG module cannot bind a resolved proof scope to the pinned trust exception.
  [Fact]
  public async Task AuditRejectsChangedRngModuleBytes() {
    var parsed = await ParsePrepared();
    var changed = PbtRandomSource + "\n// drift";
    var audit = ContractGeneratorProofAudit.BindResolved(parsed.Program, parsed.Sources, null, changed);

    Assert.NotNull(audit.Failure);
  }

  // Verifier option changes alter the immutable proof-settings fingerprint without loading tool files.
  [Fact]
  public void OptionsFingerprintBindsMutableVerifierOptions() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.TimeLimit = 2;

    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // The private proof copy installs the captured default factory and delegate references before any parsing or native work.
  [Fact]
  public void ProofVerifierFactoryNormalizationUsesCapturedDefaults() {
    var options = Options();
    options.TheProverFactory = null!;
    options.CreateSolver = null!;

    Assert.True(ContractGeneratorProof.NormalizeProofVerifierFactory(options));
    Assert.NotNull(options.TheProverFactory);
    Assert.True(ContractGeneratorProof.HasExactTrustedVerifierFactory(options));
  }

  // A proof-specific checker rejects a missing verifier factory instead of accepting a same-named class policy.
  [Fact]
  public void ProofVerifierIdentityRejectsMissingFactoryReference() {
    var options = Options();
    options.TheProverFactory = null!;

    Assert.False(ContractGeneratorProof.HasExactTrustedVerifierFactory(options));
  }

  // A changed solver delegate fails the exact private proof-checker identity test without invoking it.
  [Fact]
  public void ProofVerifierIdentityRejectsChangedSolverDelegate() {
    var options = Options();
    options.CreateSolver = (_, _) => null!;

    Assert.False(ContractGeneratorProof.HasExactTrustedVerifierFactory(options));
  }

  // The proof-specific checker rejects a substituted factory before it reparses source or reaches native verification.
  [Fact]
  public async Task ProofCheckerRejectsMismatchedFactoryAtEntry() {
    var parsed = await ParsePrepared();
    parsed.Options.TheProverFactory = null!;
    var checker = new ContractSpecificationChecker(parsed.Program, parsed.Sources, parsed.Options,
      new ContractPinnedSolverIdentity("/usr/bin/z3", "test-digest", "4.8.12"));

    var result = await checker.CheckModuleAsync(checker.UnsupportedScope("pure identity check"), "M", CancellationToken.None);

    Assert.False(result.Verified);
    Assert.Contains("exact captured trusted Boogie verifier factory", result.Diagnostics, StringComparison.Ordinal);
  }

  // Each inherited trust setting changes the proof fingerprint and fails the proof input policy after mutation.
  [Theory]
  [InlineData(nameof(DafnyOptions.TrustMoverTypes))]
  [InlineData(nameof(DafnyOptions.TrustNoninterference))]
  [InlineData(nameof(DafnyOptions.TrustRefinement))]
  [InlineData(nameof(DafnyOptions.TrustSequentialization))]
  [InlineData(nameof(DafnyOptions.TrustLayersUpto))]
  [InlineData(nameof(DafnyOptions.TrustLayersDownto))]
  public void OptionsFingerprintBindsEveryInheritedTrustSetting(string setting) {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    Assert.Null(ContractGeneratorProof.ProofOptionFailure(options));
    switch (setting) {
      case nameof(DafnyOptions.TrustMoverTypes): options.TrustMoverTypes = true; break;
      case nameof(DafnyOptions.TrustNoninterference): options.TrustNoninterference = true; break;
      case nameof(DafnyOptions.TrustRefinement): options.TrustRefinement = true; break;
      case nameof(DafnyOptions.TrustSequentialization): options.TrustSequentialization = true; break;
      case nameof(DafnyOptions.TrustLayersUpto): options.TrustLayersUpto = 0; break;
      case nameof(DafnyOptions.TrustLayersDownto): options.TrustLayersDownto = 0; break;
      default: throw new InvalidOperationException("Unknown trust setting.");
    }

    Assert.NotNull(ContractGeneratorProof.ProofOptionFailure(options));
    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Legacy resolution settings participate in the proof-settings fingerprint even when newer option bags are unchanged.
  [Fact]
  public void OptionsFingerprintBindsLegacyResolutionSetting() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.OptimizeResolution++;

    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Inherited Boogie pruning settings cannot drift outside the detached proof-settings fingerprint.
  [Fact]
  public void OptionsFingerprintBindsInheritedPruningSetting() {
    var options = Options();
    var before = ContractGeneratorProof.OptionsFingerprint(options);
    options.Prune = !options.Prune;

    Assert.NotEqual(before, ContractGeneratorProof.OptionsFingerprint(options));
  }

  // Length-framed option values cannot collide through separators embedded in solver arguments.
  [Fact]
  public void OptionsFingerprintSeparatesDelimitedProverArguments() {
    var oneValue = Options();
    Assert.True(oneValue.TryCreateDetachedSnapshot(out var twoValues, out _));
    oneValue.ProverOptions = ["a\nProverOptions=b"];
    Assert.Same(oneValue.TheProverFactory, twoValues.TheProverFactory);
    Assert.Equal(oneValue.CreateSolver, twoValues.CreateSolver);
    twoValues.ProverOptions = ["a", "ProverOptions=b"];

    Assert.NotEqual(ContractGeneratorProof.OptionsFingerprint(oneValue), ContractGeneratorProof.OptionsFingerprint(twoValues));
  }

  // Unsupported oversized legacy solver settings fail closed rather than sharing a truncated fingerprint.
  [Fact]
  public void OptionsFingerprintRejectsOversizedProverCollection() {
    var options = Options();
    options.ProverOptions = Enumerable.Range(0, 4097).Select(index => "option-" + index).ToList();

    Assert.False(ContractGeneratorProof.TryOptionsFingerprint(options, out _));
  }

  // Aggregate option strings fail the configured small budget before fingerprint copies are materialized.
  [Fact]
  public void OptionsFingerprintRejectsAggregateStringsAtConfiguredBudget() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null) {
      MainMethod = "12345",
      DafnyPrintFile = "67890"
    };

    Assert.True(ContractGeneratorProof.OptionsFitFingerprintBudget(options, 10, 8192));
    options.MainMethod += "x";
    Assert.False(ContractGeneratorProof.OptionsFitFingerprintBudget(options, 10, 8192));
  }

  // Mutating a private detached option value, legacy list or plugin cache does not change its caller's settings.
  [Fact]
  public void DetachedOptionSnapshotSeparatesMutableSettings() {
    var options = Options();
    var logFormat = new List<string> { "text" };
    options.Options.OptionArguments[CommonOptionBag.VerificationLogFormat] = logFormat;
    var originalPluginCount = options.Plugins.Count;
    Assert.True(options.TryCreateDetachedSnapshot(out var detached, out _));

    ((List<string>)detached.Options.OptionArguments[CommonOptionBag.VerificationLogFormat]).Add("csv");
    detached.ProverOptions.Add("O:smt.mbqi=true");
    detached.Plugins.Add(DafnyOptions.DefaultPlugins[0]);
    detached.Ai.J_Intervals = !options.Ai.J_Intervals;
    detached.Libraries.Add("detached-only.bpl");

    Assert.Single(logFormat);
    Assert.Empty(options.ProverOptions);
    Assert.Equal(originalPluginCount, options.Plugins.Count);
    Assert.NotSame(options.Ai, detached.Ai);
    Assert.NotSame(options.UseResolvedProgram, detached.UseResolvedProgram);
    Assert.NotSame(options.Libraries, detached.Libraries);
    Assert.NotSame(options.Cho, detached.Cho);
    Assert.True(options.Ai.J_Intervals);
    Assert.Empty(options.Libraries);
  }

  // Caller-provided Boogie resolution callbacks cannot contribute unchecked verifier program mutations.
  [Fact]
  public void ProofOptionsRejectBoogieResolutionCallbacks() {
    var options = Options();
    options.UseResolvedProgram.Add((_, _) => { });

    Assert.Contains("Boogie callbacks", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
  }

  // External Boogie libraries cannot add un-audited global axioms to the proof context.
  [Fact]
  public void ProofOptionsRejectExternalBoogieLibraries() {
    var options = Options();
    options.Libraries.Add("foreign.bpl");

    Assert.Contains("external libraries", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
  }

  // A caller-supplied solver-construction delegate cannot replace the baseline Boogie solver factory.
  [Fact]
  public void ProofOptionsRejectCustomSolverConstructionCallback() {
    var options = Options();
    options.CreateSolver = (_, _) => null!;

    Assert.Contains("solver factory", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
  }

  // Unknown mutable option values cannot enter a proof through a shallow settings copy.
  [Fact]
  public void DetachedOptionSnapshotRejectsUnsupportedMutableValue() {
    var options = Options();
    options.Options.OptionArguments[CommonOptionBag.VerificationLogFormat] = new List<int> { 1 };

    Assert.False(options.TryCreateDetachedSnapshot(out _, out var failure));
    Assert.Contains("unsupported mutable representation", failure, StringComparison.Ordinal);
  }

  // A cached plugin list with an extra built-in instance is not the exact trusted plugin configuration.
  [Fact]
  public void ProofOptionsRejectAlteredEffectivePluginList() {
    var options = Options();
    options.Plugins.Add(DafnyOptions.DefaultPlugins[0]);

    Assert.Contains("effective verifier plugin list", ContractGeneratorProof.ProofOptionFailure(options), StringComparison.Ordinal);
    Assert.False(ContractGeneratorProof.TryOptionsFingerprint(options, out _));
  }
}
