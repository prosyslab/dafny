#nullable enable

using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;
using Declaration = Microsoft.Dafny.Declaration;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Classifies the outcome of one bounded proof attempt.</summary>
public enum ContractGeneratorProofStatus { Verified, Unsupported, Failed, Cancelled, TimedOut }

/// <summary>Describes one bounded native attempt to prove every selected goal input condition.</summary>
public sealed record ContractGeneratorProofReport(ContractGeneratorProofStatus Status, string Diagnostics,
  IReadOnlyList<string> RequiredNativeChecks, IReadOnlyList<string> CoveredNativeChecks) {
  internal ContractGeneratorProof.Certificate? VerifiedCertificate { get; init; }
}

internal sealed record ContractGeneratorProofCoverage(IReadOnlySet<string> RequiredChecks,
  IReadOnlySet<string> CoveredChecks, bool ScopesAccepted, string AdmissionCorrectnessCheck,
  IReadOnlySet<string> VerifiedImplementationChecks, bool Failed) {
  internal bool Complete => !Failed && ScopesAccepted && RequiredChecks.Count != 0 &&
    RequiredChecks.Contains(AdmissionCorrectnessCheck) && CoveredChecks.Contains(AdmissionCorrectnessCheck) &&
    RequiredChecks.SetEquals(CoveredChecks) && VerifiedImplementationChecks.Contains(AdmissionCorrectnessCheck);
}

internal sealed class ContractGeneratorProofSourceBuild {
  internal IReadOnlyList<ContractSource> Sources { get; }
  internal string AdmissionName { get; }
  internal string RandomName { get; }
  internal IReadOnlyList<string> OutputNames { get; }
  internal IReadOnlyList<string> RequirementHelperNames { get; }
  private readonly string synthesizedSourceFingerprint;

  internal ContractGeneratorProofSourceBuild(IReadOnlyList<ContractSource> sources, string admissionName,
    string randomName, IReadOnlyList<string> outputNames, IReadOnlyList<string> requirementHelperNames) {
    Sources = Array.AsReadOnly(sources.ToArray());
    AdmissionName = admissionName;
    RandomName = randomName;
    OutputNames = Array.AsReadOnly(outputNames.ToArray());
    RequirementHelperNames = Array.AsReadOnly(requirementHelperNames.ToArray());
    synthesizedSourceFingerprint = ContractRuntimeTypeEvidence.SourceSetHash(Sources);
  }

  internal bool MatchesSynthesizedSources() => synthesizedSourceFingerprint ==
    ContractRuntimeTypeEvidence.SourceSetHash(Sources);
}

internal sealed record ContractPinnedSolverIdentity(string Path, string Sha256, string Version);
internal sealed record ContractGeneratorProofProgramBinding(string SemanticFingerprint);

/// <summary>Attempts a source-bound native proof that the selected generator satisfies the goal's original input requirements.</summary>
public static class ContractGeneratorProof {
  private const int MaximumTimeoutMilliseconds = 600_000;
  private const long MaximumSolverBytes = 128L * 1024 * 1024;
  private const int MaximumSolverVersionOutputCharacters = 4096;
  private const int MaximumSemanticPrintCharacters = 64 * 1024 * 1024;
  private const long MaximumSemanticFingerprintBytes = 64L * 1024 * 1024;
  private const int MaximumSemanticReferences = 1_000_000;
  private const int MaximumSemanticSources = 4096;
  private const long MaximumProofSourceBytes = 64L * 1024 * 1024;
  private const int MaximumProofOptionTextCharacters = 8 * 1024 * 1024;
  private const int MaximumProofOptionFingerprintItems = 8192;
  private static readonly UTF8Encoding StrictUtf8 = new(false, true);
  private static readonly Lazy<DafnyOptions> DefaultBoogieSettings = new(CreateDefaultBoogieSettings);
  private const string TrustedSolverPath = "/usr/bin/z3";
  private const string AdmissionBaseName = "PbtGeneratorAdmission";

  /// <summary>Proves every original requires clause from the outputs of the exact selected Generate method.</summary>
  public static async Task<ContractGeneratorProofReport> TryProveAsync(Program preparedProgram,
    IReadOnlyList<ContractSource> preparedSources, Method goal, Method generator, DafnyOptions options,
    int timeoutMilliseconds, CancellationToken cancellationToken = default) {
    if (timeoutMilliseconds is <= 0 or > MaximumTimeoutMilliseconds) {
      return Report(ContractGeneratorProofStatus.Unsupported,
        "The bounded proof timeout must be between 1 and " + MaximumTimeoutMilliseconds + " milliseconds.");
    }
    if (preparedProgram == null || preparedSources == null || goal == null || generator == null || options == null) {
      return Report(ContractGeneratorProofStatus.Unsupported, "The prepared program, snapshots, goal, generator and options are required.");
    }
    if (options.AdditionalPlugins.Count != 0 || options.AdditionalPluginArguments.Count != 0 || options.DafnyPrelude != null) {
      return Report(ContractGeneratorProofStatus.Unsupported,
        "Custom plugins and replacement Dafny preludes are outside the bounded proof policy.");
    }
    var deadline = ContractQueryDeadline.AfterMilliseconds(timeoutMilliseconds);
    using var timedCancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    timedCancellation.CancelAfter(timeoutMilliseconds);
    var token = timedCancellation.Token;
    try {
      ContractQueryDeadline.Check(deadline, token);
      if (!TrySnapshotSources(preparedSources, deadline, token, out var sourceSnapshot, out var sourceFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, sourceFailure);
      }
      if (!options.TryCreateDetachedSnapshot(out var proofInputOptions, out var snapshotFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "Verifier options could not be isolated safely: " + snapshotFailure);
      }
      var unsupportedOptions = ProofOptionFailure(proofInputOptions);
      if (unsupportedOptions != null) {
        return Report(ContractGeneratorProofStatus.Unsupported, unsupportedOptions);
      }
      if (!TryOptionsFingerprint(options, out var inputOptionsFingerprint) ||
          !TryOptionsFingerprint(proofInputOptions, out var detachedOptionsFingerprint) ||
          !TryOptionsFingerprint(preparedProgram.Options, out var programOptionsFingerprint) ||
          inputOptionsFingerprint != detachedOptionsFingerprint || inputOptionsFingerprint != programOptionsFingerprint) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "Verifier options must have a complete detached fingerprint matching the prepared Program settings.");
      }
      if (!NormalizeProofVerifierFactory(proofInputOptions)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "The trusted built-in Boogie verifier factory could not be isolated for the private proof attempt.");
      }
      var originalSourceHash = ContractRuntimeTypeEvidence.SourceSetHash(sourceSnapshot);
      if (!TryCapturePinnedSolverFile(out var solverFile, out var solverFailure, deadline, token)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          solverFailure ?? "The trusted installed system Z3 executable could not be identified.");
      }
      if (!PreparedInputsMatchSnapshots(preparedProgram, sourceSnapshot, goal, generator,
            out var mismatch, deadline, token)) {
        return Report(ContractGeneratorProofStatus.Unsupported, mismatch);
      }
      var binding = await BindPreparedProgramAsync(preparedProgram, sourceSnapshot, goal, generator,
        proofInputOptions, deadline, token);
      if (binding.Binding == null) {
        return Report(ContractGeneratorProofStatus.Unsupported, binding.Failure ?? "The resolved prepared Program is not bound to its exact source snapshots.");
      }
      var solverProbe = await ProbePinnedSolverVersionAsync(solverFile.Path, deadline, token);
      if (solverProbe.Version == null) {
        return Report(ContractGeneratorProofStatus.Unsupported, solverProbe.Failure ?? "The pinned system Z3 version could not be established safely.");
      }
      var probedSolverVersion = solverProbe.Version;
      if (proofInputOptions.SolverIdentifier is not (null or "Z3") ||
          proofInputOptions.SolverVersion != null && proofInputOptions.SolverVersion != Version.Parse(probedSolverVersion)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "Caller-pinned solver metadata does not match the installed trusted system Z3 executable.");
      }
      if (!TryCapturePinnedSolverFile(out var solverFileAfterProbe, out var solverAfterProbeFailure, deadline, token) ||
          !SolverIdentityMatches(solverFile.Path, solverFile.Sha256, probedSolverVersion,
            solverFileAfterProbe.Path, solverFileAfterProbe.Sha256, probedSolverVersion)) {
        return Report(ContractGeneratorProofStatus.Failed,
          solverAfterProbeFailure ?? "The pinned Z3 executable changed during the bounded version probe.");
      }
      solverFile = solverFile with { Version = probedSolverVersion };
      if (!SupportedSelectedGoal(preparedProgram, goal, generator, out var capabilityFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, capabilityFailure);
      }
      var randomSource = ExtractPinnedPbtRandomSource();
      var sourceBuild = PrepareProofSources(preparedProgram, sourceSnapshot, goal, generator, randomSource,
        out var sourceBuildFailure, deadline, token);
      if (sourceBuild == null) {
        return Report(ContractGeneratorProofStatus.Unsupported, sourceBuildFailure ?? "Unable to prepare the proof source.");
      }
      var proofSources = sourceBuild.Sources;
      ContractQueryDeadline.Check(deadline, token);

      var parseOptions = ProofOptions(proofInputOptions, timeoutMilliseconds, solverFile.Path);
      if (!HasExactTrustedVerifierFactory(parseOptions)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "Private proof options do not carry the exact captured trusted Boogie verifier factory.");
      }
      var rawReporter = new BatchErrorReporter(new DafnyOptions(parseOptions));
      var rawProgram = await ContractSourceSnapshot.ParseAsync(rawReporter, proofSources, token, resolve: false);
      if (rawReporter.ErrorCount != 0) {
        return Report(ContractGeneratorProofStatus.Failed, FormatDiagnostics(rawReporter));
      }
      var rawFailure = ContractGeneratorProofAudit.AuditRawProgram(rawProgram, proofSources, generator.Origin.Uri,
        generator.Name, goal.FullDafnyName, randomSource);
      if (rawFailure != null) {
        return Report(ContractGeneratorProofStatus.Unsupported, rawFailure);
      }
      ContractQueryDeadline.Check(deadline, token);

      var proofReporter = new BatchErrorReporter(new DafnyOptions(parseOptions));
      var proofProgram = await ContractSourceSnapshot.ParseAsync(proofReporter, proofSources, token);
      if (proofReporter.ErrorCount != 0) {
        return Report(ContractGeneratorProofStatus.Failed, FormatDiagnostics(proofReporter));
      }
      if (!TryFindProofTargets(proofProgram, sourceSnapshot, goal, generator, sourceBuild.AdmissionName,
            out var proofGoal, out var proofGenerator, out var admission, out var targetFailure)) {
        return Report(ContractGeneratorProofStatus.Failed, targetFailure);
      }
      var admissionCorrectness = ContractSpecificationChecker.Name(admission) + " (correctness)";
      var proofBindingFailure = await ValidateProofSourceBindingsAsync(proofProgram, proofGoal, proofGenerator, admission,
        sourceBuild, parseOptions, deadline, token);
      if (proofBindingFailure != null) {
        return Report(ContractGeneratorProofStatus.Failed, proofBindingFailure);
      }
      var audit = ContractGeneratorProofAudit.BindResolved(proofProgram, proofSources, rawFailure, randomSource);
      if (audit.Failure != null) {
        return Report(ContractGeneratorProofStatus.Unsupported, audit.Failure);
      }
      if (!GoalRequiresAreValueOnly(proofProgram, proofGoal, out var requiresFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, requiresFailure);
      }
      var generatedReachable = ContractRuntimeObligationTransformer.ExecutionReachable(proofProgram, [admission, proofGenerator]);
      if (generatedReachable.Contains(proofGoal)) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          "The selected generator or one of its execution helpers can re-enter the target goal body.");
      }
      ContractQueryDeadline.Check(deadline, token);

      var checker = new ContractSpecificationChecker(proofProgram, proofSources, parseOptions, solverFile);
      var inputTypes = proofGoal.Ins.Select(formal => formal.Type).ToList();
      var goalExpressions = proofGoal.Req.Select(requirement => requirement.E).ToList();
      var expressionNodes = goalExpressions.SelectMany(expression => ContractRuntimeObligationTransformer.LogicalNodes(expression)
        .Prepend(expression)).ToList();
      var directProofRoots = expressionNodes.OfType<CallStmt>().Select(call => call.Method);
      var allSourceCallables = SourceDeclarations(proofProgram, proofSources, audit)
        .OfType<Function>().Cast<MethodOrFunction>().ToList();
      var logicalRoots = allSourceCallables.Concat(directProofRoots).Distinct().ToList();
      var constrainedTypes = SourceDeclarations(proofProgram, proofSources, audit).OfType<TopLevelDecl>()
        .Where(declaration => (declaration is SubsetTypeDecl or NewtypeDecl) && declaration is not NonNullTypeDecl)
        .Select(declaration => UserDefinedType.FromTopLevelDecl(declaration.Origin, declaration)).Cast<Type>().ToList();
      var definedConstants = SourceDeclarations(proofProgram, proofSources, audit).OfType<ConstantField>()
        .Where(constant => constant.Rhs != null).ToList();
      var logicalScope = checker.AuditedProofScope(ContractSpecificationRole.Logical, logicalRoots,
        constrainedTypes.Concat(inputTypes), definedConstants, audit);
      var executionConstants = expressionNodes.OfType<MemberSelectExpr>().Select(select => select.Member)
        .OfType<ConstantField>().Concat(definedConstants).Distinct().ToList();
      var executionScope = checker.AuditedProofScope(ContractSpecificationRole.Execution, [admission, proofGenerator],
        inputTypes, executionConstants, audit);
      if (executionScope.Failure != null || logicalScope.Failure != null) {
        return Report(ContractGeneratorProofStatus.Unsupported,
          string.Join("\n", new[] { executionScope.Failure, logicalScope.Failure }.Where(value => value != null)));
      }

      var required = executionScope.RequiredNativeChecks.Concat(logicalScope.RequiredNativeChecks)
        .ToHashSet(StringComparer.Ordinal);
      var covered = new HashSet<string>(StringComparer.Ordinal);
      var verifiedImplementations = new HashSet<string>(StringComparer.Ordinal);
      var diagnostics = new List<string>();
      var scopesAccepted = true;
      var failed = false;
      foreach (var scope in new[] { executionScope, logicalScope }) {
        foreach (var moduleName in checker.PendingModules(scope)) {
          ContractQueryDeadline.Check(deadline, token);
          ContractSpecificationResult checkedModule;
          checkedModule = await checker.CheckModuleAsync(scope, moduleName, token, deadlineTimestamp: deadline);
          diagnostics.Add(checkedModule.Diagnostics);
          covered.UnionWith(checkedModule.CoveredNativeChecks);
          verifiedImplementations.UnionWith(checkedModule.VerifiedImplementationChecks);
          if (!checkedModule.Verified) {
            failed = true;
            break;
          }
        }
        if (failed) { break; }
      }
      scopesAccepted = !failed && checker.Accept(executionScope) && checker.Accept(logicalScope);
      var coverage = new ContractGeneratorProofCoverage(required, covered, scopesAccepted,
        admissionCorrectness, verifiedImplementations, failed);
      if (!coverage.Complete) {
        var missing = required.Except(covered).OrderBy(name => name, StringComparer.Ordinal).ToList();
        if (missing.Count > 0) { diagnostics.Add("Missing native proof coverage: " + string.Join(", ", missing)); }
        if (!verifiedImplementations.Contains(admissionCorrectness)) {
          diagnostics.Add("The admission method did not receive positive native correctness verification.");
        }
        if (!scopesAccepted) { diagnostics.Add("The complete audited proof scopes were not accepted."); }
        return new(failed ? ContractGeneratorProofStatus.Failed : ContractGeneratorProofStatus.Unsupported,
          string.Join("\n", diagnostics.Where(text => !string.IsNullOrWhiteSpace(text))), required.OrderBy(name => name, StringComparer.Ordinal).ToList(),
          covered.OrderBy(name => name, StringComparer.Ordinal).ToList());
      }
      ContractQueryDeadline.Check(deadline, token);
      var solverVersion = checker.ResolvedSolverVersion(solverFile.Path);
      var actualNativeOptionsFingerprint = checker.FinalNativeOptionsFingerprint;
      if (solverVersion == null || solverVersion != solverFile.Version || actualNativeOptionsFingerprint == null) {
        return Report(ContractGeneratorProofStatus.Failed,
          "The native checker did not resolve the exact pinned system Z3 executable and version.");
      }
      if (!audit.IsBoundTo(proofProgram, proofSources)) {
        return Report(ContractGeneratorProofStatus.Failed,
          "The synthesized proof program or audited closure changed while native verification was running.");
      }
      if (!TryResolvedProgramFingerprint(preparedProgram, deadline, token, out var finalSemanticFingerprint, out var finalFingerprintFailure) ||
          finalSemanticFingerprint != binding.Binding.SemanticFingerprint) {
        return Report(ContractGeneratorProofStatus.Failed,
          finalFingerprintFailure ?? "The prepared Program changed while the proof was running.");
      }
      if (!TryCapturePinnedSolverFile(out var solverFileAfter, out var solverAfterFailure, deadline, token) ||
          !SolverIdentityMatches(solverFile.Path, solverFile.Sha256, solverVersion,
            solverFileAfter.Path, solverFileAfter.Sha256, solverVersion)) {
        return Report(ContractGeneratorProofStatus.Failed,
          solverAfterFailure ?? "The pinned Z3 executable changed while the native proof was running.");
      }
      if (!CallerInputsStillMatch(preparedProgram, preparedSources, sourceSnapshot, options,
            inputOptionsFingerprint, deadline, token, out var changedInputFailure)) {
        return Report(ContractGeneratorProofStatus.Failed, changedInputFailure);
      }
      var solverIdentity = new ContractPinnedSolverIdentity(solverFile.Path, solverFile.Sha256, solverVersion);
      var certificate = new Certificate(preparedProgram, goal, generator, sourceSnapshot, proofInputOptions,
        originalSourceHash, ContractRuntimeTypeEvidence.SourceSetHash(proofSources),
        ContractGeneratorProofAudit.PolicyVersion, audit.PbtRandomSourceHash,
        ContractHarnessBuilder.Hash(ContractRuntimeLibrary.Read("PbtRandom.cs")),
        inputOptionsFingerprint, OptionsFingerprint(parseOptions), actualNativeOptionsFingerprint,
        solverIdentity, binding.Binding.SemanticFingerprint, timeoutMilliseconds,
        required.OrderBy(name => name, StringComparer.Ordinal).ToList(), verifiedImplementations.OrderBy(name => name, StringComparer.Ordinal).ToList());
      return new(ContractGeneratorProofStatus.Verified,
        string.Join("\n", diagnostics.Where(text => !string.IsNullOrWhiteSpace(text))),
        required.OrderBy(name => name, StringComparer.Ordinal).ToList(), covered.OrderBy(name => name, StringComparer.Ordinal).ToList()) {
        VerifiedCertificate = certificate
      };
    } catch (OperationCanceledException error) {
      var timedOut = !cancellationToken.IsCancellationRequested;
      return Report(timedOut ? ContractGeneratorProofStatus.TimedOut : ContractGeneratorProofStatus.Cancelled,
        error.Message);
    }
  }

  internal static bool AcceptCoverage(ContractGeneratorProofCoverage coverage) => coverage.Complete;

  internal static string? ProofOptionFailure(DafnyOptions options) {
    if (options.GetType() != typeof(DafnyOptions)) {
      return "DafnyOptions subclasses are outside the bounded proof policy.";
    }
    if (options.Backend?.GetType() != typeof(CsharpBackend)) {
      return "Only the exact built-in C# backend is supported by the bounded proof policy.";
    }
    if (!options.TryCopyTestGenerationOptions(out var testGenerationOptions)) {
      return "Custom test-generation settings are outside the bounded proof policy.";
    }
    if (!TestGenerationOptionsAreDefault(testGenerationOptions)) {
      return "Non-default test-generation modes are outside the bounded proof policy.";
    }
    if (options.AdditionalPlugins.Count != 0 || options.AdditionalPluginArguments.Count != 0 || options.DafnyPrelude != null) {
      return "Custom plugins and replacement Dafny preludes are outside the bounded proof policy.";
    }
    if (options.DafnyProject != null) {
      return "Project-backed source selection is outside the closed prepared-source proof policy.";
    }
    if (!EffectivePluginsMatchPolicy(options)) {
      return "The effective verifier plugin list is outside the exact built-in plugin policy.";
    }
    if (options.UseResolvedProgram.Count != 0 || options.Cho.Count != 0 || options.Libraries.Count != 0) {
      return "Boogie callbacks, concurrent Houdini settings and external libraries are outside the bounded proof policy.";
    }
    if (options.GetOrOptionDefault(CommonOptionBag.AssumeWellFormedDiv) ||
        options.GetOrOptionDefault(CommonOptionBag.AssumeWellFormedIndex)) {
      return "Options that assume division or index well-formedness checks are outside the proof policy.";
    }
    if (options.GetOrOptionDefault(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas)) {
      return "The unsound function/lemma decreases-star option is outside the proof policy.";
    }
    if (options.GetOrOptionDefault(CommonOptionBag.AllowAxioms)) {
      return "The allow-axioms option is outside the proof policy.";
    }
    if (options.GetOrOptionDefault(BoogieOptionBag.NoVerify) || options.GetOrOptionDefault(BoogieOptionBag.HiddenNoVerify) ||
        !options.Verify || !options.DafnyVerify) {
      return "Verification-skipping options are outside the proof policy.";
    }
    if (options.GetOrOptionDefault(BoogieOptionBag.SolverPlugin) != null || !options.IsUsingZ3() ||
        options.GetOrOptionDefault(BoogieOptionBag.SolverPath) != null ||
        options.ProverOptions.Any(option => option.StartsWith("PROVER_PATH=", StringComparison.Ordinal))) {
      return "Custom verifier plugins or non-Z3 solver selection are outside the proof policy.";
    }
    if (!UsesDefaultBoogieVerifierFactory(options)) {
      return "The custom Boogie solver factory or solver-creation callback is outside the exact built-in verifier policy.";
    }
    if (options.NoResolve || options.NoTypecheck || options.OverlookBoogieTypeErrors || options.AlwaysAssumeFreeLoopInvariants ||
        options.TrustMoverTypes || options.TrustNoninterference || options.TrustRefinement || options.TrustSequentialization ||
        options.TrustLayersUpto != -1 || options.TrustLayersDownto != int.MaxValue) {
      return "Boogie verification skip, trust or free-invariant options are outside the proof policy.";
    }
    var defaultBoogieSettings = DefaultBoogieSettings.Value;
    if (options.ProverPreamble != null || options.LoopUnrollCount != defaultBoogieSettings.LoopUnrollCount ||
        options.StratifiedInlining != defaultBoogieSettings.StratifiedInlining ||
        options.ContractInfer != defaultBoogieSettings.ContractInfer) {
      return "Raw prover preambles and non-default loop-unrolling, stratified-inlining or contract-inference modes are outside the proof policy.";
    }
    if (options.ConcurrentHoudini != defaultBoogieSettings.ConcurrentHoudini ||
        options.HoudiniUseCrossDependencies != defaultBoogieSettings.HoudiniUseCrossDependencies ||
        options.StagedHoudini != defaultBoogieSettings.StagedHoudini ||
        options.DebugStagedHoudini != defaultBoogieSettings.DebugStagedHoudini ||
        options.StagedHoudiniReachabilityAnalysis != defaultBoogieSettings.StagedHoudiniReachabilityAnalysis ||
        options.StagedHoudiniMergeIgnoredAnnotations != defaultBoogieSettings.StagedHoudiniMergeIgnoredAnnotations ||
        options.StagedHoudiniThreads != defaultBoogieSettings.StagedHoudiniThreads ||
        options.VariableDependenceIgnore != defaultBoogieSettings.VariableDependenceIgnore ||
        options.ModifyTopologicalSorting != defaultBoogieSettings.ModifyTopologicalSorting ||
        options.DebugConcurrentHoudini != defaultBoogieSettings.DebugConcurrentHoudini ||
        options.UseUnsatCoreForContractInfer != defaultBoogieSettings.UseUnsatCoreForContractInfer ||
        options.ExplainHoudini != defaultBoogieSettings.ExplainHoudini ||
        options.ReverseHoudiniWorklist != defaultBoogieSettings.ReverseHoudiniWorklist ||
        options.InstrumentWithAsserts != defaultBoogieSettings.InstrumentWithAsserts ||
        options.InstrumentInfer != defaultBoogieSettings.InstrumentInfer ||
        options.IntraproceduralInfer != defaultBoogieSettings.IntraproceduralInfer ||
        options.VerifySeparately != defaultBoogieSettings.VerifySeparately ||
        options.VerifySnapshots != defaultBoogieSettings.VerifySnapshots ||
        options.UseSubsumption != defaultBoogieSettings.UseSubsumption ||
        options.ReflectAdd != defaultBoogieSettings.ReflectAdd ||
        options.KInductionDepth != defaultBoogieSettings.KInductionDepth ||
        options.SoundnessSmokeTest != defaultBoogieSettings.SoundnessSmokeTest) {
      return "Non-default Houdini, instrumentation, snapshot, subsumption, reflected-arithmetic, k-induction or smoke-test modes are outside the proof policy.";
    }
    if (options.GetOrOptionDefault(DafnyFile.DoNotVerifyDependencies)) {
      return "The option to accept unverified dependencies is outside the proof policy.";
    }
    return null;
  }

  internal static bool EffectivePluginsMatchPolicy(DafnyOptions options) {
    if (options.AdditionalPlugins.Count != 0 || options.AdditionalPluginArguments.Count != 0) { return false; }
    var plugins = options.Plugins;
    return plugins.Count == DafnyOptions.DefaultPlugins.Count &&
      plugins.Select((plugin, index) => ReferenceEquals(plugin, DafnyOptions.DefaultPlugins[index])).All(matches => matches);
  }

  private static bool TestGenerationOptionsAreDefault(TestGenerationOptions? settings) => settings == null ||
    !settings.WarnDeadCode && !settings.IgnoreWarnings && settings.Mode == TestGenerationOptions.Modes.None &&
    settings.SeqLengthLimit == 0 && settings.PrintBpl == null && !settings.ForcePrune && settings.CoverageReport == null;

  private static string BackendFingerprint(CsharpBackend backend) {
    var type = backend.GetType();
    var identity = new StringBuilder()
      .Append(Frame(type.FullName ?? type.Name)).Append(Frame(AssemblyFingerprint(type.Assembly)))
      .Append(Frame(backend.TargetName)).Append(Frame(backend.TargetId)).Append(Frame(backend.TargetExtension))
      .Append(Frame(backend.TargetIndentSize.ToString(CultureInfo.InvariantCulture)))
      .Append(Frame(backend.IsStable.ToString(CultureInfo.InvariantCulture)))
      .Append(Frame(backend.SupportsInMemoryCompilation.ToString(CultureInfo.InvariantCulture)))
      .Append(Frame(backend.TextualTargetIsExecutable.ToString(CultureInfo.InvariantCulture)));
    foreach (var extension in backend.SupportedExtensions.OrderBy(value => value, StringComparer.Ordinal)) {
      identity.Append(Frame("extension")).Append(Frame(extension));
    }
    foreach (var nativeType in backend.SupportedNativeTypes.OrderBy(value => value, StringComparer.Ordinal)) {
      identity.Append(Frame("native-type")).Append(Frame(nativeType));
    }
    return ContractHarnessBuilder.Hash(identity.ToString());
  }

  private static string TestGenerationOptionsFingerprint(TestGenerationOptions? settings) {
    settings ??= new TestGenerationOptions();
    return Frame(settings.WarnDeadCode.ToString(CultureInfo.InvariantCulture)) +
      Frame(settings.IgnoreWarnings.ToString(CultureInfo.InvariantCulture)) +
      Frame(settings.Mode.ToString()) +
      Frame(settings.SeqLengthLimit.ToString(CultureInfo.InvariantCulture)) +
      Frame(settings.PrintBpl ?? "") +
      Frame(settings.ForcePrune.ToString(CultureInfo.InvariantCulture)) +
      Frame(settings.CoverageReport ?? "");
  }

  private static DafnyOptions CreateDefaultBoogieSettings() {
    var defaults = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    defaults.ApplyDefaultOptionsWithoutSettingsDefault();
    return defaults;
  }

  private static bool UsesDefaultBoogieVerifierFactory(DafnyOptions options) {
    if (options.ProverDllName is not (null or "SMTLib")) { return false; }
    var defaults = DefaultBoogieSettings.Value;
    if (!Delegate.Equals(options.CreateSolver, defaults.CreateSolver)) { return false; }
    if (options.TheProverFactory == null) { return true; }
    var defaultFactory = defaults.TheProverFactory;
    return defaultFactory != null && options.TheProverFactory.GetType() == defaultFactory.GetType() &&
      options.TheProverFactory.GetType().Assembly.ManifestModule.ModuleVersionId ==
      defaultFactory.GetType().Assembly.ManifestModule.ModuleVersionId;
  }

  internal static bool NormalizeProofVerifierFactory(DafnyOptions options) {
    var defaults = DefaultBoogieSettings.Value;
    if (defaults.TheProverFactory == null) { return false; }
    options.TheProverFactory = defaults.TheProverFactory;
    options.CreateSolver = defaults.CreateSolver;
    return HasExactTrustedVerifierFactory(options);
  }

  internal static bool HasExactTrustedVerifierFactory(DafnyOptions options) {
    var defaults = DefaultBoogieSettings.Value;
    return defaults.TheProverFactory != null &&
      ReferenceEquals(options.TheProverFactory, defaults.TheProverFactory) &&
      ReferenceEquals(options.CreateSolver, defaults.CreateSolver);
  }

  private static string ProverFactoryFingerprint(Microsoft.Boogie.ProverFactory? factory) {
    if (factory == null) { return "null"; }
    var type = factory.GetType();
    return Frame(type.FullName ?? type.Name) + Frame(AssemblyFingerprint(type.Assembly)) +
      Frame(RuntimeHelpers.GetHashCode(factory).ToString(CultureInfo.InvariantCulture));
  }

  private static string DelegateFingerprint(Delegate? value) {
    if (value == null) { return "null"; }
    if (value.GetInvocationList().Length != 1) {
      throw new NotSupportedException("A composed delegate cannot be used as the verifier solver factory.");
    }
    var method = value.Method;
    return Frame(method.DeclaringType?.FullName ?? "") + Frame(method.Module.ModuleVersionId.ToString("N")) +
      Frame(method.MetadataToken.ToString(CultureInfo.InvariantCulture)) +
      Frame(value.Target == null ? "null" : RuntimeHelpers.GetHashCode(value.Target).ToString(CultureInfo.InvariantCulture));
  }

  private static ContractGeneratorProofReport Report(ContractGeneratorProofStatus status, string message) =>
    new(status, message, [], []);

  private static string FormatDiagnostics(BatchErrorReporter reporter) =>
    string.Join("\n", reporter.AllMessages.Select(message => message.Message));

  private static DafnyOptions ProofOptions(DafnyOptions options, int timeoutMilliseconds, string? solverPath = null) {
    var proofOptions = new DafnyOptions(options, useNullWriters: true) {
      Compile = false,
      TimeLimit = (uint)Math.Max(1, (timeoutMilliseconds + 999L) / 1000L)
    };
    if (solverPath != null) { proofOptions.ProverOptions.Add("PROVER_PATH=" + solverPath); }
    return proofOptions;
  }

  internal static string OptionsFingerprint(DafnyOptions options) {
    if (options.GetType() != typeof(DafnyOptions) || options.Backend?.GetType() != typeof(CsharpBackend) ||
        !options.TryCopyTestGenerationOptions(out var testGenerationOptions)) {
      throw new NotSupportedException("Only exact DafnyOptions instances with the built-in C# backend and supported test-generation settings can be fingerprinted.");
    }
    if (options.AdditionalPlugins.Count != 0 || options.AdditionalPluginArguments.Count != 0 || options.DafnyPrelude != null) {
      throw new NotSupportedException("Custom plugins and replacement Dafny preludes are outside the bounded proof policy.");
    }
    if (options.DafnyProject != null) {
      throw new NotSupportedException("Project-backed source selection is outside the closed prepared-source proof policy.");
    }
    if (!EffectivePluginsMatchPolicy(options)) {
      throw new NotSupportedException("The effective verifier plugin list is outside the exact built-in plugin policy.");
    }
    if (!UsesDefaultBoogieVerifierFactory(options)) {
      throw new NotSupportedException("The custom Boogie solver factory or solver-creation callback is outside the exact built-in verifier policy.");
    }
    if (!OptionsFitFingerprintBudget(options, MaximumProofOptionTextCharacters, MaximumProofOptionFingerprintItems)) {
      throw new NotSupportedException("Verifier option text exceeds the bounded fingerprint character or item budget.");
    }
    // Boogie PrintAssignment and diagnostic-output-only switches are omitted because they do not change generated proof obligations.
    var identity = new StringBuilder()
      .Append(AssemblyFingerprint(typeof(DafnyOptions).Assembly)).Append('\n')
      .Append(AssemblyFingerprint(typeof(Microsoft.Boogie.ExecutionEngine).Assembly)).Append('\n')
      .Append(AssemblyFingerprint(typeof(ContractGeneratorProof).Assembly)).Append('\n')
      .Append("Backend=").Append(BackendFingerprint((CsharpBackend)options.Backend)).Append('\n')
      .Append("TestGenerationOptions=").Append(TestGenerationOptionsFingerprint(testGenerationOptions)).Append('\n')
      .Append("Compile=").Append(options.Compile).Append('\n')
      .Append("UseAbstractInterpretation=").Append(options.UseAbstractInterpretation).Append('\n')
      .Append("BoogieAiIntervals=").Append(options.Ai.J_Intervals).Append('\n')
      .Append("BoogieAiTrivial=").Append(options.Ai.J_Trivial).Append('\n')
      .Append("BoogieAiDebugStatistics=").Append(options.Ai.DebugStatistics).Append('\n')
      .Append("BoogieAiStepsBeforeWidening=").Append(options.Ai.StepsBeforeWidening).Append('\n')
      .Append("BoogieUseResolvedProgramCount=").Append(options.UseResolvedProgram.Count).Append('\n')
      .Append("BoogieChoCount=").Append(options.Cho.Count).Append('\n')
      .Append("BoogieLibraries=").Append(OptionValueFingerprint(options.Libraries)).Append('\n')
      .Append("BoogieFactory=").Append(ProverFactoryFingerprint(options.TheProverFactory)).Append('\n')
      .Append("BoogieCreateSolver=").Append(DelegateFingerprint(options.CreateSolver)).Append('\n')
      .Append("TimeLimit=").Append(options.TimeLimit).Append('\n')
      .Append("RunLanguageServer=").Append(options.RunLanguageServer).Append('\n')
      .Append("UnicodeOutput=").Append(options.UnicodeOutput).Append('\n')
      .Append("DiagnosticsFormat=").Append(options.DiagnosticsFormat).Append('\n')
      .Append("DafnyPrintFile=").Append(options.DafnyPrintFile ?? "").Append('\n')
      .Append("PrintMode=").Append(options.PrintMode).Append('\n')
      .Append("DafnyPrintResolvedFile=").Append(options.DafnyPrintResolvedFile ?? "").Append('\n')
      .Append("FormatCheck=").Append(options.FormatCheck).Append('\n')
      .Append("CompilerName=").Append(options.CompilerName ?? "").Append('\n')
      .Append("Verbose=").Append(options.Verbose).Append('\n')
      .Append("DafnyPrintCompiledFile=").Append(options.DafnyPrintCompiledFile ?? "").Append('\n')
      .Append("CoverageLegendFile=").Append(options.CoverageLegendFile ?? "").Append('\n')
      .Append("MainMethod=").Append(options.MainMethod ?? "").Append('\n')
      .Append("ForceCompile=").Append(options.ForceCompile).Append('\n')
      .Append("RunAfterCompile=").Append(options.RunAfterCompile).Append('\n')
      .Append("SpillTargetCode=").Append(options.SpillTargetCode).Append('\n')
      .Append("AutoReqPrintFile=").Append(options.AutoReqPrintFile ?? "").Append('\n')
      .Append("IgnoreAutoReq=").Append(options.ignoreAutoReq).Append('\n')
      .Append("PrintTooltips=").Append(options.PrintTooltips).Append('\n')
      .Append("PrintStats=").Append(options.PrintStats).Append('\n')
      .Append("MethodsToTest=").Append(options.MethodsToTest ?? "").Append('\n')
      .Append("DisallowConstructorCaseWithoutParentheses=").Append(options.DisallowConstructorCaseWithoutParentheses).Append('\n')
      .Append("PrintFunctionCallGraph=").Append(options.PrintFunctionCallGraph).Append('\n')
      .Append("WarnShadowing=").Append(options.WarnShadowing).Append('\n')
      .Append("VerifyAllModules=").Append(options.VerifyAllModules).Append('\n')
      .Append("Verify=").Append(options.Verify).Append('\n')
      .Append("FunctionSyntax=").Append(options.FunctionSyntax).Append('\n')
      .Append("QuantifierSyntax=").Append(options.QuantifierSyntax).Append('\n')
      .Append("UsingNewCli=").Append(options.UsingNewCli).Append('\n')
      .Append("DafnyVerify=").Append(options.DafnyVerify).Append('\n')
      .Append("SolverIdentifier=").Append(options.SolverIdentifier ?? "").Append('\n')
      .Append("SolverVersion=").Append(options.SolverVersion?.ToString() ?? "").Append('\n')
      .Append("ProverDllName=").Append(options.ProverDllName ?? "").Append('\n')
      .Append("IncludeRuntime=").Append(options.IncludeRuntime).Append('\n')
      .Append("DisallowIncludes=").Append(options.DisallowIncludes).Append('\n')
      .Append("DisallowExterns=").Append(options.DisallowExterns).Append('\n')
      .Append("SystemModuleTranslationMode=").Append(options.SystemModuleTranslationMode).Append('\n')
      .Append("RunningBoogieFromCommandLine=").Append(options.RunningBoogieFromCommandLine).Append('\n')
      .Append("ArithMode=").Append(options.ArithMode).Append('\n')
      .Append("DisableNLarith=").Append(options.DisableNLarith).Append('\n')
      .Append("Induction=").Append(options.Induction).Append('\n')
      .Append("InductionHeuristic=").Append(options.InductionHeuristic).Append('\n')
      .Append("AutoTriggers=").Append(options.AutoTriggers).Append('\n')
      .Append("Optimize=").Append(options.Optimize).Append('\n')
      .Append("DefiniteAssignmentLevel=").Append(options.DefiniteAssignmentLevel).Append('\n')
      .Append("OptimizeResolution=").Append(options.OptimizeResolution).Append('\n')
      .Append("DisableScopes=").Append(options.DisableScopes).Append('\n')
      .Append("RewriteFocalPredicates=").Append(options.RewriteFocalPredicates).Append('\n')
      .Append("EnforcePrintEffects=").Append(options.EnforcePrintEffects).Append('\n')
      .Append("TestContracts=").Append(options.TestContracts).Append('\n')
      .Append("ForbidNondeterminism=").Append(options.ForbidNondeterminism).Append('\n')
      .Append("AllowSourceFolders=").Append(options.AllowSourceFolders).Append('\n')
      .Append("DeprecationNoise=").Append(options.DeprecationNoise).Append('\n')
      .Append("SeparateModuleOutput=").Append(options.SeparateModuleOutput).Append('\n')
      .Append("PrintIncludesMode=").Append(options.PrintIncludesMode).Append('\n')
      .Append("UseJavadocLikeDocstringRewriter=").Append(options.UseJavadocLikeDocstringRewriter).Append('\n')
      .Append("UseStdin=").Append(options.UseStdin).Append('\n')
      .Append("FailOnWarnings=").Append(options.FailOnWarnings).Append('\n')
      .Append("ExtractCounterexample=").Append(options.ExtractCounterexample).Append('\n')
      .Append("ShowProofObligationExpressions=").Append(options.ShowProofObligationExpressions).Append('\n')
      .Append("AuditProgram=").Append(options.AuditProgram).Append('\n')
      .Append("BoogiePrune=").Append(options.Prune).Append('\n')
      .Append("BoogieNormalizeNames=").Append(options.NormalizeNames).Append('\n')
      .Append("BoogieEmitDebugInformation=").Append(options.EmitDebugInformation).Append('\n')
      .Append("BoogieErrorTrace=").Append(options.ErrorTrace).Append('\n')
      .Append("BoogieEnhancedErrorMessages=").Append(options.EnhancedErrorMessages).Append('\n')
      .Append("BoogieUseBaseNameForFileName=").Append(options.UseBaseNameForFileName).Append('\n')
      .Append("BoogieProverPreamble=").Append(Frame(options.ProverPreamble ?? "")).Append('\n')
      .Append("BoogieLoopUnrollCount=").Append(options.LoopUnrollCount).Append('\n')
      .Append("BoogieStratifiedInlining=").Append(options.StratifiedInlining).Append('\n')
      .Append("BoogieContractInfer=").Append(options.ContractInfer).Append('\n')
      .Append("BoogieConcurrentHoudini=").Append(OptionValueFingerprint(options.ConcurrentHoudini)).Append('\n')
      .Append("BoogieHoudiniUseCrossDependencies=").Append(OptionValueFingerprint(options.HoudiniUseCrossDependencies)).Append('\n')
      .Append("BoogieStagedHoudini=").Append(OptionValueFingerprint(options.StagedHoudini)).Append('\n')
      .Append("BoogieDebugStagedHoudini=").Append(OptionValueFingerprint(options.DebugStagedHoudini)).Append('\n')
      .Append("BoogieStagedHoudiniReachabilityAnalysis=").Append(OptionValueFingerprint(options.StagedHoudiniReachabilityAnalysis)).Append('\n')
      .Append("BoogieStagedHoudiniMergeIgnoredAnnotations=").Append(OptionValueFingerprint(options.StagedHoudiniMergeIgnoredAnnotations)).Append('\n')
      .Append("BoogieStagedHoudiniThreads=").Append(OptionValueFingerprint(options.StagedHoudiniThreads)).Append('\n')
      .Append("BoogieVariableDependenceIgnore=").Append(OptionValueFingerprint(options.VariableDependenceIgnore)).Append('\n')
      .Append("BoogieModifyTopologicalSorting=").Append(OptionValueFingerprint(options.ModifyTopologicalSorting)).Append('\n')
      .Append("BoogieDebugConcurrentHoudini=").Append(OptionValueFingerprint(options.DebugConcurrentHoudini)).Append('\n')
      .Append("BoogieUseUnsatCoreForContractInfer=").Append(OptionValueFingerprint(options.UseUnsatCoreForContractInfer)).Append('\n')
      .Append("BoogieExplainHoudini=").Append(OptionValueFingerprint(options.ExplainHoudini)).Append('\n')
      .Append("BoogieReverseHoudiniWorklist=").Append(OptionValueFingerprint(options.ReverseHoudiniWorklist)).Append('\n')
      .Append("BoogieInstrumentWithAsserts=").Append(OptionValueFingerprint(options.InstrumentWithAsserts)).Append('\n')
      .Append("BoogieInstrumentInfer=").Append(OptionValueFingerprint(options.InstrumentInfer)).Append('\n')
      .Append("BoogieIntraproceduralInfer=").Append(OptionValueFingerprint(options.IntraproceduralInfer)).Append('\n')
      .Append("BoogieVerifySeparately=").Append(OptionValueFingerprint(options.VerifySeparately)).Append('\n')
      .Append("BoogieVerifySnapshots=").Append(OptionValueFingerprint(options.VerifySnapshots)).Append('\n')
      .Append("BoogieUseSubsumption=").Append(OptionValueFingerprint(options.UseSubsumption)).Append('\n')
      .Append("BoogieReflectAdd=").Append(OptionValueFingerprint(options.ReflectAdd)).Append('\n')
      .Append("BoogieKInductionDepth=").Append(OptionValueFingerprint(options.KInductionDepth)).Append('\n')
      .Append("BoogieSoundnessSmokeTest=").Append(OptionValueFingerprint(options.SoundnessSmokeTest)).Append('\n')
      .Append("BoogieUseAbstractInterpretation=").Append(options.UseAbstractInterpretation).Append('\n')
      .Append("BoogieNoResolve=").Append(options.NoResolve).Append('\n')
      .Append("BoogieNoTypecheck=").Append(options.NoTypecheck).Append('\n')
      .Append("BoogieOverlookBoogieTypeErrors=").Append(options.OverlookBoogieTypeErrors).Append('\n')
      .Append("BoogieAlwaysAssumeFreeLoopInvariants=").Append(options.AlwaysAssumeFreeLoopInvariants).Append('\n')
      .Append("BoogieTrustMoverTypes=").Append(options.TrustMoverTypes).Append('\n')
      .Append("BoogieTrustNoninterference=").Append(options.TrustNoninterference).Append('\n')
      .Append("BoogieTrustRefinement=").Append(options.TrustRefinement).Append('\n')
      .Append("BoogieTrustSequentialization=").Append(options.TrustSequentialization).Append('\n')
      .Append("BoogieTrustLayersUpto=").Append(options.TrustLayersUpto).Append('\n')
      .Append("BoogieTrustLayersDownto=").Append(options.TrustLayersDownto).Append('\n')
      .Append("BoogieSoundLoopUnrolling=").Append(options.SoundLoopUnrolling).Append('\n')
      .Append("BoogieProcedureInlining=").Append(options.ProcedureInlining).Append('\n')
      .Append("BoogieInlineDepth=").Append(options.InlineDepth).Append('\n')
      .Append("BoogieExpandLambdas=").Append(options.ExpandLambdas).Append('\n')
      .Append("BoogieInferModifies=").Append(options.InferModifies).Append('\n')
      .Append("BoogieKeepQuantifier=").Append(options.KeepQuantifier).Append('\n')
      .Append("BoogieNormalizeDeclarationOrder=").Append(options.NormalizeDeclarationOrder).Append('\n')
      .Append("BoogieRemoveEmptyBlocks=").Append(options.RemoveEmptyBlocks).Append('\n')
      .Append("BoogieCoalesceBlocks=").Append(options.CoalesceBlocks).Append('\n')
      .Append("BoogiePruneInfeasibleEdges=").Append(options.PruneInfeasibleEdges).Append('\n')
      .Append("BoogieResourceLimit=").Append(options.ResourceLimit).Append('\n')
      .Append("BoogieProcessTimeLimit=").Append(options.ProcessTimeLimit).Append('\n')
      .Append("BoogieVcsMaxCost=").Append(options.VcsMaxCost.ToString("R", CultureInfo.InvariantCulture)).Append('\n')
      .Append("BoogieVcsPathJoinMult=").Append(options.VcsPathJoinMult.ToString("R", CultureInfo.InvariantCulture)).Append('\n')
      .Append("BoogieVcsPathCostMult=").Append(options.VcsPathCostMult.ToString("R", CultureInfo.InvariantCulture)).Append('\n')
      .Append("BoogieVcsAssumeMult=").Append(options.VcsAssumeMult.ToString("R", CultureInfo.InvariantCulture)).Append('\n')
      .Append("BoogieVcsPathSplitMult=").Append(options.VcsPathSplitMult.ToString("R", CultureInfo.InvariantCulture)).Append('\n')
      .Append("BoogieVcsMaxSplits=").Append(options.VcsMaxSplits).Append('\n')
      .Append("BoogieVcsMaxKeepGoingSplits=").Append(options.VcsMaxKeepGoingSplits).Append('\n')
      .Append("BoogieVcsSplitOnEveryAssert=").Append(options.VcsSplitOnEveryAssert).Append('\n')
      .Append("BoogieVcsFinalAssertTimeout=").Append(options.VcsFinalAssertTimeout).Append('\n')
      .Append("BoogieVcsKeepGoingTimeout=").Append(options.VcsKeepGoingTimeout).Append('\n')
      .Append("BoogieVcsCores=").Append(options.VcsCores).Append('\n')
      .Append("BoogieErrorLimit=").Append(options.ErrorLimit).Append('\n')
      .Append("DisallowSoundnessCheating=").Append(options.DisallowSoundnessCheating).Append('\n')
      .Append("TypeEncodingMethod=").Append(options.TypeEncodingMethod).Append('\n')
      .Append("UseArrayTheory=").Append(options.UseArrayTheory).Append('\n')
      .Append("ProverOptions=").Append(OptionValueFingerprint(options.ProverOptions)).Append('\n')
      .Append("ProcsToCheck=").Append(OptionValueFingerprint(options.ProcsToCheck)).Append('\n')
      .Append("ProcsToIgnore=").Append(OptionValueFingerprint(options.ProcsToIgnore)).Append('\n')
      .Append("SourceFolders=").Append(OptionValueFingerprint(options.SourceFolders)).Append('\n')
      .Append("MainArgs=").Append(OptionValueFingerprint(options.MainArgs)).Append('\n')
      .Append("DafnyPrintExportedViews=").Append(OptionValueFingerprint(options.DafnyPrintExportedViews)).Append('\n')
      .Append("LibraryFiles=").Append(OptionValueFingerprint(options.LibraryFiles)).Append('\n')
      .Append("CliRootSourceUris=").Append(OptionValueFingerprint(options.CliRootSourceUris)).Append('\n');
    foreach (var plugin in options.Plugins) {
      identity.Append("plugin-instance:").Append(RuntimeHelpers.GetHashCode(plugin).ToString(CultureInfo.InvariantCulture)).Append('\n');
    }
    foreach (var item in options.Options.OptionArguments.OrderBy(pair => pair.Key.Name, StringComparer.Ordinal)) {
      identity.Append("option:").Append(Frame(item.Key.Name)).Append(Frame(OptionValueFingerprint(item.Value)));
    }
    foreach (var item in options.Options.Arguments.OrderBy(pair => pair.Key.Name, StringComparer.Ordinal)) {
      identity.Append("argument:").Append(Frame(item.Key.Name)).Append(Frame(OptionValueFingerprint(item.Value)));
    }
    return ContractHarnessBuilder.Hash(identity.ToString());
  }

  internal static bool TryOptionsFingerprint(DafnyOptions options, out string fingerprint) {
    try {
      fingerprint = OptionsFingerprint(options);
      return true;
    } catch (NotSupportedException) {
      fingerprint = "";
      return false;
    } catch (InvalidOperationException) {
      fingerprint = "";
      return false;
    }
  }

  internal static bool OptionsFitFingerprintBudget(DafnyOptions options, int maximumCharacters,
    int maximumItems) {
    if (maximumCharacters < 0 || maximumItems < 0) { return false; }
    if (!options.TryCopyTestGenerationOptions(out var testGenerationOptions)) { return false; }
    long characters = 0;
    var items = 0;
    bool AddText(string? text) {
      if (++items > maximumItems) { return false; }
      characters += text?.Length ?? 0;
      return characters <= maximumCharacters;
    }
    bool AddValue(object? value, int depth) {
      if (depth > 24 || ++items > maximumItems) { return false; }
      if (value == null) { return true; }
      var type = value.GetType();
      if (!AddText(type.AssemblyQualifiedName ?? type.FullName ?? type.Name)) { return false; }
      switch (value) {
        case string text:
          return AddText(text);
        case FileInfo file:
          return AddText(file.FullName);
        case Uri uri:
          return AddText(uri.OriginalString);
        case IEnumerable enumerable when IsStableCollection(type):
          foreach (var item in enumerable) {
            if (!AddValue(item, depth + 1)) { return false; }
          }
          return true;
        case bool or byte or sbyte or short or ushort or int or uint or long or ulong or float or double or decimal:
        case char or DateTime or DateTimeOffset or TimeSpan or Guid or Version:
          return true;
        default:
          return type.IsEnum;
      }
    }
    bool AddStrings(IEnumerable<string> values) {
      foreach (var value in values) {
        if (!AddText(value)) { return false; }
      }
      return true;
    }
    var directStrings = new[] { options.DafnyPrintFile, options.DafnyPrintResolvedFile, options.CompilerName,
      options.DafnyPrintCompiledFile, options.CoverageLegendFile, options.MainMethod, options.AutoReqPrintFile,
      options.MethodsToTest, options.SolverIdentifier, options.ProverDllName, options.ProverPreamble,
      options.StagedHoudini, options.VariableDependenceIgnore };
    if (!AddStrings(directStrings) || !AddStrings(options.ProverOptions) || !AddStrings(options.ProcsToCheck) ||
        !AddStrings(options.ProcsToIgnore) || !AddStrings(options.SourceFolders) ||
        !AddStrings(options.DafnyPrintExportedViews) || !AddStrings(options.MainArgs) ||
        !AddStrings(options.Libraries) || !AddStrings(options.LibraryFiles)) {
      return false;
    }
    if (testGenerationOptions != null &&
        (!AddText(testGenerationOptions.PrintBpl) || !AddText(testGenerationOptions.CoverageReport))) { return false; }
    foreach (var uri in options.CliRootSourceUris) {
      if (!AddText(uri.OriginalString)) { return false; }
    }
    foreach (var (option, value) in options.Options.OptionArguments) {
      if (!AddText(option.Name) || !AddValue(value, 0)) { return false; }
    }
    foreach (var (argument, value) in options.Options.Arguments) {
      if (!AddText(argument.Name) || !AddValue(value, 0)) { return false; }
    }
    return true;
  }

  private static DafnyOptions NativeProofOptions(DafnyOptions options, int timeoutMilliseconds,
    ContractPinnedSolverIdentity solverIdentity) {
    var nativeOptions = ProofOptions(options, timeoutMilliseconds, solverIdentity.Path);
    nativeOptions.RunningBoogieFromCommandLine = true;
    nativeOptions.ProcsToCheck = ["*"];
    nativeOptions.ProcsToIgnore = [];
    nativeOptions.VerifyAllModules = true;
    nativeOptions.SetZ3Options(Version.Parse(solverIdentity.Version));
    return nativeOptions;
  }

  private static bool TryCapturePinnedSolverFile(out ContractPinnedSolverIdentity identity, out string? failure,
    long? deadlineTimestamp = null, CancellationToken cancellationToken = default) {
    failure = null;
    try {
      if (!File.Exists(TrustedSolverPath)) {
        identity = null!;
        failure = "The trusted installed system Z3 executable is unavailable at " + TrustedSolverPath + ".";
        return false;
      }
      using var stream = new FileStream(TrustedSolverPath, FileMode.Open, FileAccess.Read, FileShare.Read);
      var expectedLength = stream.Length;
      if (expectedLength is <= 0 or > MaximumSolverBytes) {
        identity = null!;
        failure = "The trusted system Z3 executable exceeds the bounded 128 MiB identity limit.";
        return false;
      }
      using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
      var buffer = new byte[64 * 1024];
      long total = 0;
      while (true) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        var read = stream.Read(buffer, 0, buffer.Length);
        if (read == 0) { break; }
        total += read;
        if (total > MaximumSolverBytes) {
          identity = null!;
          failure = "The trusted system Z3 executable exceeds the bounded 128 MiB identity limit.";
          return false;
        }
        hash.AppendData(buffer, 0, read);
      }
      if (total != expectedLength || stream.Length != expectedLength) {
        identity = null!;
        failure = "The trusted system Z3 executable changed while its identity was read.";
        return false;
      }
      identity = new(Path.GetFullPath(TrustedSolverPath), Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant(), "");
      return true;
    } catch (IOException error) {
      identity = null!;
      failure = "The trusted system Z3 executable could not be read: " + error.Message;
      return false;
    } catch (UnauthorizedAccessException error) {
      identity = null!;
      failure = "The trusted system Z3 executable could not be read: " + error.Message;
      return false;
    } catch (System.Security.SecurityException error) {
      identity = null!;
      failure = "The trusted system Z3 executable could not be read: " + error.Message;
      return false;
    }
  }

  private static readonly Regex Z3VersionRegex = new(@"Z3 version (?<major>\d+)\.(?<minor>\d+)\.(?<patch>\d+)", RegexOptions.CultureInvariant);
  private sealed record BoundedOutput(string Text, bool Exceeded);
  private sealed record SolverProbeResult(string? Version, string? Failure);

  internal static bool TryParseZ3Version(int exitCode, bool outputExceeded, string standardOutput, out string version) {
    version = "";
    if (exitCode != 0 || outputExceeded) { return false; }
    var match = Z3VersionRegex.Match(standardOutput);
    if (!match.Success || !int.TryParse(match.Groups["major"].Value, NumberStyles.None, CultureInfo.InvariantCulture, out var major) ||
        !int.TryParse(match.Groups["minor"].Value, NumberStyles.None, CultureInfo.InvariantCulture, out var minor) ||
        !int.TryParse(match.Groups["patch"].Value, NumberStyles.None, CultureInfo.InvariantCulture, out var patch)) {
      return false;
    }
    version = new Version(major, minor, patch).ToString();
    return true;
  }

  private static async Task<SolverProbeResult> ProbePinnedSolverVersionAsync(string path, long deadlineTimestamp,
    CancellationToken cancellationToken) {
    if (!StringComparer.Ordinal.Equals(path, Path.GetFullPath(TrustedSolverPath))) {
      return new(null, "Only the exact trusted system Z3 path is supported.");
    }
    Process? process = null;
    Task? waitTask = null;
    Task<BoundedOutput>? stdoutTask = null;
    Task<BoundedOutput>? stderrTask = null;
    try {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      process = new Process {
        StartInfo = new ProcessStartInfo {
          FileName = path,
          UseShellExecute = false,
          CreateNoWindow = true,
          RedirectStandardError = true,
          RedirectStandardOutput = true,
          RedirectStandardInput = true
        }
      };
      process.StartInfo.ArgumentList.Add("-version");
      if (!process.Start()) {
        return new(null, "The trusted system Z3 version probe did not start.");
      }
      process.StandardInput.Close();
      var currentStdoutTask = ReadBoundedOutputAsync(process.StandardOutput, cancellationToken);
      var currentStderrTask = ReadBoundedOutputAsync(process.StandardError, cancellationToken);
      stdoutTask = currentStdoutTask;
      stderrTask = currentStderrTask;
      try {
        var currentWaitTask = process.WaitForExitAsync(cancellationToken);
        waitTask = currentWaitTask;
        var pending = new List<Task> { currentWaitTask, currentStdoutTask, currentStderrTask };
        while (true) {
          var completed = await Task.WhenAny(pending);
          if (ReferenceEquals(completed, currentWaitTask)) {
            await currentWaitTask;
            break;
          }
          if (ReferenceEquals(completed, currentStdoutTask)) {
            var output = await currentStdoutTask;
            pending.Remove(currentStdoutTask);
            if (output.Exceeded) {
              await StopAndObserveProbeAsync(process, currentWaitTask, currentStdoutTask, currentStderrTask);
              return new(null, "The trusted system Z3 exceeded the bounded version-output limit.");
            }
          } else {
            var output = await currentStderrTask;
            pending.Remove(currentStderrTask);
            if (output.Exceeded) {
              await StopAndObserveProbeAsync(process, currentWaitTask, currentStdoutTask, currentStderrTask);
              return new(null, "The trusted system Z3 exceeded the bounded version-output limit.");
            }
          }
        }
        var outputs = await Task.WhenAll(currentStdoutTask, currentStderrTask);
        var stdout = outputs[0];
        var stderr = outputs[1];
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        if (!TryParseZ3Version(process.ExitCode, stdout.Exceeded || stderr.Exceeded, stdout.Text, out var version)) {
          return new(null, "The trusted system Z3 returned an unsupported, oversized or invalid version response.");
        }
        return new(version, null);
      } catch (OperationCanceledException) {
        TryKillProbe(process);
        throw;
      }
    } catch (Win32Exception error) {
      return new(null, "The trusted system Z3 version probe failed to start: " + error.Message);
    } catch (IOException error) {
      return new(null, "The trusted system Z3 version probe failed: " + error.Message);
    } catch (InvalidOperationException error) {
      return new(null, "The trusted system Z3 version probe failed: " + error.Message);
    }
    finally {
      if (process != null) { await StopAndObserveProbeAsync(process, waitTask, stdoutTask, stderrTask); }
      process?.Dispose();
    }
  }

  private static async Task<BoundedOutput> ReadBoundedOutputAsync(StreamReader reader, CancellationToken cancellationToken) {
    var builder = new StringBuilder();
    var buffer = new char[512];
    while (true) {
      var remaining = MaximumSolverVersionOutputCharacters - builder.Length;
      var read = await reader.ReadAsync(buffer.AsMemory(0, Math.Min(buffer.Length, remaining + 1)), cancellationToken);
      if (read == 0) { break; }
      if (read > remaining) {
        return new(builder.ToString(), true);
      }
      builder.Append(buffer, 0, read);
    }
    return new(builder.ToString(), false);
  }

  private static async Task StopAndObserveProbeAsync(Process process, Task? waitTask,
    Task<BoundedOutput>? stdoutTask, Task<BoundedOutput>? stderrTask) {
    TryKillProbe(process);
    var tasks = new[] { waitTask, stdoutTask, stderrTask }.OfType<Task>().ToArray();
    if (tasks.Length == 0) { return; }
    try {
      await Task.WhenAll(tasks);
    } catch (OperationCanceledException) {
      // The cancelled probe's wait and bounded readers are observed before disposing its streams.
    } catch (IOException) {
      // Closing a pipe after a forced child exit can race an outstanding read.
    } catch (ObjectDisposedException) {
      // Process disposal may close pipes after their child has exited.
    } catch (InvalidOperationException) {
      // A process wait can fail if the operating system closed the process handle.
    } catch (Win32Exception) {
      // A process wait can fail if the operating system invalidated the process handle.
    }
  }

  private static void TryKillProbe(Process process) {
    try {
      if (!process.HasExited) { process.Kill(entireProcessTree: true); }
    } catch (InvalidOperationException) {
      // The process exited between the status check and kill request.
    } catch (Win32Exception) {
      // The process can no longer be signalled; cancellation still fails closed.
    }
  }

  internal static bool SolverIdentityMatches(string expectedPath, string expectedHash, string expectedVersion,
    string actualPath, string actualHash, string actualVersion) =>
    StringComparer.Ordinal.Equals(expectedPath, actualPath) &&
    StringComparer.Ordinal.Equals(expectedHash, actualHash) &&
    StringComparer.Ordinal.Equals(expectedVersion, actualVersion);

  internal static bool IsPinnedSolverFileCurrent(ContractPinnedSolverIdentity expected,
    long? deadlineTimestamp, CancellationToken cancellationToken) =>
    TryCapturePinnedSolverFile(out var actual, out _, deadlineTimestamp, cancellationToken) &&
    SolverIdentityMatches(expected.Path, expected.Sha256, "", actual.Path, actual.Sha256, "");

  private static string AssemblyFingerprint(Assembly assembly) {
    var name = assembly.GetName();
    return string.Join("/", name.Name, name.Version?.ToString() ?? "", assembly.ManifestModule.ModuleVersionId.ToString("D"));
  }

  private static string OptionValueFingerprint(object? value) => OptionValueFingerprint(value, new HashSet<object>(), 0);

  private static string OptionValueFingerprint(object? value, HashSet<object> visiting, int depth) {
    if (depth > 24) { throw new NotSupportedException("An option value exceeds the proof fingerprint nesting limit."); }
    if (value == null) { return "null"; }
    var typeName = value.GetType().AssemblyQualifiedName ?? value.GetType().FullName ?? value.GetType().Name;
    if (value is string text) { return "s" + Frame(typeName) + Frame(text); }
    if (value is System.IO.FileInfo file) { return "f" + Frame(typeName) + Frame(file.FullName); }
    if (value is Uri uri) { return "u" + Frame(typeName) + Frame(uri.OriginalString); }
    if (value.GetType().IsEnum) { return "e" + Frame(typeName) + Frame(Enum.Format(value.GetType(), value, "D")); }
    if (value is bool boolean) { return "b" + Frame(typeName) + Frame(boolean ? "1" : "0"); }
    if ((value is IFormattable && value.GetType().IsPrimitive) || value is decimal or DateTime or TimeSpan or Guid or Version) {
      var scalar = ((IFormattable)value).ToString(null, CultureInfo.InvariantCulture);
      return "v" + Frame(typeName) + Frame(scalar ?? "");
    }
    if (value is IEnumerable enumerable && IsStableCollection(value.GetType())) {
      if (!value.GetType().IsValueType && !visiting.Add(value)) {
        throw new NotSupportedException("A cyclic option collection cannot be fingerprinted.");
      }
      try {
        var items = new List<string>();
        foreach (var item in enumerable) {
          if (items.Count == 4096) { throw new NotSupportedException("An option collection exceeds the proof fingerprint item limit."); }
          items.Add(OptionValueFingerprint(item, visiting, depth + 1));
        }
        if (IsSetCollection(value.GetType())) { items.Sort(StringComparer.Ordinal); }
        return "c" + Frame(typeName) + Frame(string.Concat(items.Select(Frame)));
      }
      finally {
        if (!value.GetType().IsValueType) { visiting.Remove(value); }
      }
    }
    throw new NotSupportedException("An option value has no supported canonical proof fingerprint: " + typeName);
  }

  private static bool IsStableCollection(System.Type type) => type.IsArray || typeof(IList).IsAssignableFrom(type) ||
    type.GetInterfaces().Any(candidate => candidate.IsGenericType &&
      (candidate.GetGenericTypeDefinition() == typeof(IReadOnlyList<>) || candidate.GetGenericTypeDefinition() == typeof(ISet<>) ||
       candidate.GetGenericTypeDefinition().FullName == "System.Collections.Generic.IReadOnlySet`1"));

  private static bool IsSetCollection(System.Type type) => type.GetInterfaces().Any(candidate => candidate.IsGenericType &&
    (candidate.GetGenericTypeDefinition() == typeof(ISet<>) || candidate.GetGenericTypeDefinition().FullName == "System.Collections.Generic.IReadOnlySet`1"));

  private static string Frame(string value) => value.Length.ToString(CultureInfo.InvariantCulture) + ":" + value;

  private static string ExtractPinnedPbtRandomSource() {
    var runtime = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");
    const string marker = "module {:extern \"DafnyPbtRandom\"} PbtRandom {";
    var start = runtime.IndexOf(marker, StringComparison.Ordinal);
    if (start < 0) { throw new InvalidOperationException("The embedded runtime has no pinned PbtRandom module."); }
    var source = runtime[start..];
    if (ContractHarnessBuilder.Hash(source) != ContractGeneratorProofAudit.PbtRandomSourceSha256) {
      throw new InvalidOperationException("The embedded PbtRandom source hash changed without a proof-policy update.");
    }
    return source;
  }

  internal static ContractGeneratorProofSourceBuild? PrepareProofSources(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, Method generator, string randomModuleSource,
    out string? failure, long? deadlineTimestamp = null, CancellationToken cancellationToken = default,
    long maximumPreparedSourceBytes = MaximumProofSourceBytes) {
    failure = null;
    if (maximumPreparedSourceBytes < 0 || maximumPreparedSourceBytes > MaximumProofSourceBytes ||
        sources.Count == 0 || sources.Count > MaximumSemanticSources ||
        goal.Ins.Count > MaximumSemanticReferences || goal.Req.Count > MaximumSemanticReferences) {
      failure = "The prepared proof source exceeds the bounded source or declaration policy.";
      return null;
    }
    var originalSourceBytes = 0L;
    var originalSourceByteCounts = new Dictionary<Uri, int>();
    foreach (var source in sources) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      if (source.Content.Length > maximumPreparedSourceBytes ||
          !TryUtf8ByteCount(source.Content, out var sourceBytes) ||
          !TryAddWithinBudget(ref originalSourceBytes, sourceBytes, maximumPreparedSourceBytes)) {
        failure = "The prepared proof source snapshots exceed the bounded UTF-8 byte policy.";
        return null;
      }
      originalSourceByteCounts.Add(ContractSourceSnapshot.UriFor(source.Path), sourceBytes);
    }
    if (!TryUtf8ByteCount(randomModuleSource, out var randomModuleBytes) ||
        randomModuleBytes > maximumPreparedSourceBytes) {
      failure = "The pinned RNG proof source exceeds the bounded UTF-8 byte policy.";
      return null;
    }
    var family = ContractBodyNames.Family(program, AdmissionBaseName);
    var admissionName = family;
    var randomName = family + "Random";
    var outputNames = goal.Ins.Select((_, index) => family + "Output" + index.ToString(CultureInfo.InvariantCulture)).ToList();
    var helperNames = goal.Req.Select((_, index) => family + "Requirement" + index.ToString(CultureInfo.InvariantCulture)).ToList();
    var edits = new List<ByteEdit>();
    var goalSource = ContractSourceSnapshot.Find(sources, goal.Origin.Uri);
    var goalScope = goal.EnclosingClass.EnclosingModuleDefinition;
    var generatorScope = generator.EnclosingClass.EnclosingModuleDefinition;
    var helperFormalNames = goal.Ins.Select((_, index) => family + "Argument" + index.ToString(CultureInfo.InvariantCulture)).ToList();
    var formals = goal.Ins.Select((formal, index) => new Formal(formal.Origin, helperFormalNames[index],
      formal.Type, true, false, null)).ToList();
    var helperFormalParts = new List<string>(formals.Count);
    var helperFormalBytes = 0L;
    foreach (var formal in formals) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var part = formal.Name + ": " + ContractQueryBuilder.QualifiedType(program, goalScope, formal.Type);
      if (!TryUtf8ByteCount(part, out var partBytes) ||
          helperFormalParts.Count > 0 && !TryAddWithinBudget(ref helperFormalBytes, StrictUtf8.GetByteCount(", "), maximumPreparedSourceBytes) ||
          !TryAddWithinBudget(ref helperFormalBytes, partBytes, maximumPreparedSourceBytes)) {
        failure = "Generated helper formals exceed the bounded UTF-8 byte policy.";
        return null;
      }
      helperFormalParts.Add(part);
    }
    var expressionSources = new List<string>(goal.Req.Count);
    var expressionByteCounts = new List<int>(goal.Req.Count);
    for (var requirementIndex = 0; requirementIndex < goal.Req.Count; requirementIndex++) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var copied = SubstituteGoalInputs(goal, formals, goal.Req[requirementIndex].E);
      var qualified = ContractQueryBuilder.QualifyExpression(program, goalScope, copied);
      var expressionSource = Printer.ExprToString(program.Options, qualified);
      if (expressionSource.Length > maximumPreparedSourceBytes || !TryUtf8ByteCount(expressionSource, out var expressionBytes)) {
        failure = "A generated requirement expression exceeds the bounded UTF-8 byte policy.";
        return null;
      }
      expressionSources.Add(expressionSource);
      expressionByteCounts.Add(expressionBytes);
    }
    var helperOwnerReference = MemberOwnerReference(program, generatorScope, goal.EnclosingClass);
    var helperReferences = helperNames.Select(helperName =>
      helperOwnerReference.Length == 0 ? helperName : helperOwnerReference + "." + helperName).ToList();
    var outputFormalNames = generator.Outs.Select(output => output.Name).ToList();
    var outputNameBytes = 0L;
    for (var index = 0; index < outputNames.Count; index++) {
      if (!TryUtf8ByteCount(outputNames[index], out var outputNameByteCount) ||
          index > 0 && !TryAddWithinBudget(ref outputNameBytes, StrictUtf8.GetByteCount(", "), maximumPreparedSourceBytes) ||
          !TryAddWithinBudget(ref outputNameBytes, outputNameByteCount, maximumPreparedSourceBytes)) {
        failure = "Generated admission output names exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }
    var outputFormalBytes = 0L;
    for (var index = 0; index < outputFormalNames.Count; index++) {
      if (!TryUtf8ByteCount(outputFormalNames[index], out var outputFormalByteCount) ||
          index > 0 && !TryAddWithinBudget(ref outputFormalBytes, StrictUtf8.GetByteCount(", "), maximumPreparedSourceBytes) ||
          !TryAddWithinBudget(ref outputFormalBytes, outputFormalByteCount, maximumPreparedSourceBytes)) {
        failure = "Generated Generate postconditions exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }
    var generatorSource = ContractSourceSnapshot.Find(sources, generator.Origin.Uri);
    var goalUri = ContractSourceSnapshot.UriFor(goalSource.Path);
    var generatorUri = ContractSourceSnapshot.UriFor(generatorSource.Path);
    var runtimeSources = sources.Where(source => source.Content == ContractRuntimeInstrumentation.DafnySource).ToList();
    if (runtimeSources.Count > 1) {
      failure = "The prepared source snapshots contain multiple embedded runtime files.";
      return null;
    }
    var exactRandomSources = sources.Where(source => source.Content == randomModuleSource).ToList();
    if (exactRandomSources.Count > 1) {
      failure = "The prepared source snapshots contain multiple copies of the pinned PbtRandom module.";
      return null;
    }
    var appendRandomSource = runtimeSources.Count == 0 && exactRandomSources.Count == 0;
    if (appendRandomSource && sources.Count == MaximumSemanticSources) {
      failure = "Adding the proof-only RNG file would exceed the bounded source count.";
      return null;
    }
    var randomPath = appendRandomSource ? sources[0].Path + ".pbt-generator-rng-proof.dfy" : null;
    if (appendRandomSource && sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == ContractSourceSnapshot.UriFor(randomPath!))) {
      failure = "The proof-only RNG source path collides with a supplied source snapshot.";
      return null;
    }

    // Preflight all generated UTF-8 bytes before materializing the quadratic prefix clauses.
    var generatedByteCount = 0L;
    var prefixLabelBytes = StrictUtf8.GetByteCount("\n  requires ");
    var helperFixedBytes = StrictUtf8.GetByteCount("\nstatic ghost predicate ") +
      StrictUtf8.GetByteCount("(") + helperFormalBytes + StrictUtf8.GetByteCount(")\n{  }\n");
    var expressionPrefixBytes = 0L;
    for (var requirementIndex = 0; requirementIndex < goal.Req.Count; requirementIndex++) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var headerBytes = helperFixedBytes + StrictUtf8.GetByteCount(helperNames[requirementIndex]);
      var declarationBytes = (long)headerBytes + requirementIndex * (long)prefixLabelBytes +
        expressionPrefixBytes + expressionByteCounts[requirementIndex];
      if (!TryAddWithinBudget(ref generatedByteCount, declarationBytes, maximumPreparedSourceBytes)) {
        failure = "Generated proof declarations exceed the bounded UTF-8 byte policy.";
        return null;
      }
      if (!TryAddWithinBudget(ref expressionPrefixBytes,
            (long)expressionByteCounts[requirementIndex] + prefixLabelBytes, maximumPreparedSourceBytes)) {
        failure = "Generated requirement prefixes exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }
    var helperDeclarationsBytes = generatedByteCount;
    var ensuresByteCount = 0L;
    for (var index = 0; index < helperReferences.Count; index++) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var ensureBytes = (long)StrictUtf8.GetByteCount("ensures ") + StrictUtf8.GetByteCount(helperReferences[index]) +
        StrictUtf8.GetByteCount("(") + outputFormalBytes + StrictUtf8.GetByteCount(")");
      if ((index > 0 && !TryAddWithinBudget(ref ensuresByteCount, StrictUtf8.GetByteCount("\n  "), maximumPreparedSourceBytes)) ||
          !TryAddWithinBudget(ref ensuresByteCount, ensureBytes, maximumPreparedSourceBytes)) {
        failure = "Generated Generate postconditions exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }
    if (!TryAddWithinBudget(ref ensuresByteCount, StrictUtf8.GetByteCount("\n  "), maximumPreparedSourceBytes)) {
      failure = "Generated Generate postconditions exceed the bounded UTF-8 byte policy.";
      return null;
    }
    var admissionPrefixBytes = (long)StrictUtf8.GetByteCount("\nstatic method ") + StrictUtf8.GetByteCount(admissionName) +
      StrictUtf8.GetByteCount("() {\n  var ") + StrictUtf8.GetByteCount(randomName) +
      StrictUtf8.GetByteCount(" := PbtRandom.New();\n");
    var admissionCallBytes = outputNames.Count > 0
      ? (long)StrictUtf8.GetByteCount("  var ") + outputNameBytes + StrictUtf8.GetByteCount(" := ") +
        StrictUtf8.GetByteCount(generator.Name) + StrictUtf8.GetByteCount("(") + StrictUtf8.GetByteCount(randomName) + StrictUtf8.GetByteCount(");\n")
      : (long)StrictUtf8.GetByteCount("  ") + StrictUtf8.GetByteCount(generator.Name) + StrictUtf8.GetByteCount("(") +
        StrictUtf8.GetByteCount(randomName) + StrictUtf8.GetByteCount(");\n");
    var admissionByteCount = admissionPrefixBytes + admissionCallBytes + StrictUtf8.GetByteCount("}\n");
    foreach (var helperReference in helperReferences) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var assertionBytes = (long)StrictUtf8.GetByteCount("  assert ") + StrictUtf8.GetByteCount(helperReference) +
        StrictUtf8.GetByteCount("(") + outputNameBytes + StrictUtf8.GetByteCount(");\n");
      if (!TryAddWithinBudget(ref admissionByteCount, assertionBytes, maximumPreparedSourceBytes)) {
        failure = "The admission assertions exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }

    var runtimeUri = runtimeSources.Count == 1 ? ContractSourceSnapshot.UriFor(runtimeSources[0].Path) : null;
    if (runtimeUri == goalUri || runtimeUri == generatorUri) {
      failure = "The pinned RNG replacement overlaps a selected goal or generator source edit.";
      return null;
    }
    var finalSourceBytes = 0L;
    foreach (var (uri, originalBytes) in originalSourceByteCounts) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var finalLength = (long)originalBytes;
      if (uri == goalUri && !TryAddWithinBudget(ref finalLength, helperDeclarationsBytes, maximumPreparedSourceBytes) ||
          uri == generatorUri && (!TryAddWithinBudget(ref finalLength, ensuresByteCount, maximumPreparedSourceBytes) ||
                                  !TryAddWithinBudget(ref finalLength, admissionByteCount, maximumPreparedSourceBytes))) {
        failure = "Prepared proof sources exceed the bounded UTF-8 byte policy.";
        return null;
      }
      if (runtimeUri == uri) {
        finalLength = randomModuleBytes;
      }
      if (!TryAddWithinBudget(ref finalSourceBytes, finalLength, maximumPreparedSourceBytes)) {
        failure = "Prepared proof sources exceed the bounded UTF-8 byte policy.";
        return null;
      }
    }
    if (appendRandomSource && !TryAddWithinBudget(ref finalSourceBytes, randomModuleBytes, maximumPreparedSourceBytes)) {
      failure = "Prepared proof sources exceed the bounded UTF-8 byte policy.";
      return null;
    }

    var helperFormalText = string.Join(", ", helperFormalParts);
    var outputNamesText = string.Join(", ", outputNames);
    var generatedEnsures = helperReferences.Select(reference =>
      "ensures " + reference + "(" + string.Join(", ", outputFormalNames) + ")").ToList();
    var ensuresText = string.Join("\n  ", generatedEnsures) + "\n  ";
    var admissionPrefix = "\nstatic method " + admissionName + "() {\n  var " + randomName + " := PbtRandom.New();\n";
    var admissionCall = outputNames.Count > 0
      ? "  var " + outputNamesText + " := " + generator.Name + "(" + randomName + ");\n"
      : "  " + generator.Name + "(" + randomName + ");\n";
    const string admissionSuffix = "}\n";
    var admissionAssertions = helperReferences.Select(reference =>
      "  assert " + reference + "(" + outputNamesText + ");\n").ToList();
    var body = new StringBuilder(admissionPrefix).Append(admissionCall);
    foreach (var assertion in admissionAssertions) { body.Append(assertion); }
    body.Append(admissionSuffix);

    var helperDeclarations = new StringBuilder();
    for (var requirementIndex = 0; requirementIndex < goal.Req.Count; requirementIndex++) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      helperDeclarations.Append("\nstatic ghost predicate ").Append(helperNames[requirementIndex]).Append('(')
        .Append(helperFormalText).Append(')');
      for (var prefixIndex = 0; prefixIndex < requirementIndex; prefixIndex++) {
        helperDeclarations.Append("\n  requires ").Append(expressionSources[prefixIndex]);
      }
      helperDeclarations.Append("\n{ ").Append(expressionSources[requirementIndex]).Append(" }\n");
    }
    var methodContractPosition = MethodContractInsertionPosition(generator);
    edits.Add(new(generatorUri, methodContractPosition, ensuresText));
    var goalInsertion = goal.EnclosingClass is DefaultClassDecl ? goal.StartToken.pos : goal.EnclosingClass.EndToken.pos;
    edits.Add(new(goalUri, goalInsertion, helperDeclarations.ToString()));
    var admissionInsertion = generator.EnclosingClass is DefaultClassDecl ? generator.StartToken.pos : generator.EnclosingClass.EndToken.pos;
    edits.Add(new(ContractSourceSnapshot.UriFor(generatorSource.Path), admissionInsertion, body.ToString()));
    if (runtimeSources.Count == 1) {
      edits.Add(new(ContractSourceSnapshot.UriFor(runtimeSources[0].Path), 0, randomModuleSource, ReplaceWholeFile: true));
    }
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var proofSources = ApplyByteEdits(sources, edits, appendRandomSource ? randomPath : null,
      appendRandomSource ? randomModuleSource : null, maximumPreparedSourceBytes, deadlineTimestamp, cancellationToken);
    return new(proofSources, admissionName, randomName, outputNames, helperNames);
  }

  private sealed record ByteEdit(Uri Uri, int Start, string Text, bool ReplaceWholeFile = false);

  private sealed record EncodedByteEdit(int Start, byte[] Text, int Sequence);

  private static IReadOnlyList<ContractSource> ApplyByteEdits(IReadOnlyList<ContractSource> sources,
    IReadOnlyList<ByteEdit> edits, string? appendedPath, string? appendedContent, long maximumPreparedSourceBytes,
    long? deadlineTimestamp, CancellationToken cancellationToken) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var sourceUris = sources.Select(source => ContractSourceSnapshot.UriFor(source.Path)).ToList();
    var replaceEdits = new Dictionary<Uri, ByteEdit>();
    var predictedTotalBytes = 0L;
    foreach (var source in sources) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var uri = ContractSourceSnapshot.UriFor(source.Path);
      if (!TryUtf8ByteCount(source.Content, out var sourceLength)) {
        throw new NotSupportedException("A source snapshot is not valid UTF-8 text.");
      }
      var local = edits.Where(edit => edit.Uri == uri).ToList();
      var replacements = local.Where(edit => edit.ReplaceWholeFile).ToList();
      if (replacements.Count > 0) {
        if (replacements.Count != 1 || local.Count != 1 || replacements[0].Start != 0 ||
            !TryUtf8ByteCount(replacements[0].Text, out var replacementLength)) {
          throw new ArgumentException("Whole-file RNG replacement cannot overlap source edits.");
        }
        replaceEdits.Add(uri, replacements[0]);
        if (!TryAddWithinBudget(ref predictedTotalBytes, replacementLength, maximumPreparedSourceBytes)) {
          throw new NotSupportedException("Prepared proof sources exceed the bounded UTF-8 byte policy.");
        }
      } else {
        var finalLength = (long)sourceLength;
        foreach (var edit in local) {
          ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
          if (!TryUtf8ByteCount(edit.Text, out var editLength)) {
            throw new NotSupportedException("A generated proof edit is not valid UTF-8 text.");
          }
          finalLength += editLength;
          if (finalLength > maximumPreparedSourceBytes) {
            throw new NotSupportedException("Prepared proof sources exceed the bounded UTF-8 byte policy.");
          }
        }
        if (!TryAddWithinBudget(ref predictedTotalBytes, finalLength, maximumPreparedSourceBytes)) {
          throw new NotSupportedException("Prepared proof sources exceed the bounded UTF-8 byte policy.");
        }
      }
    }
    if (appendedPath != null && appendedContent != null) {
      if (sourceUris.Contains(ContractSourceSnapshot.UriFor(appendedPath)) ||
          !TryUtf8ByteCount(appendedContent, out var appendedLength) ||
          !TryAddWithinBudget(ref predictedTotalBytes, appendedLength, maximumPreparedSourceBytes)) {
        throw new NotSupportedException("The proof-only RNG source exceeds the bounded source policy or collides with an existing path.");
      }
    }

    // All result lengths are known and below budget before allocating source or output byte buffers.
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var result = new List<ContractSource>(sources.Count + (appendedPath == null ? 0 : 1));
    foreach (var source in sources) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var uri = ContractSourceSnapshot.UriFor(source.Path);
      if (replaceEdits.TryGetValue(uri, out var replacement)) {
        var replacementContent = replacement.Text;
        result.Add(source with { Content = replacementContent, Sha256 = ContractHarnessBuilder.Hash(replacementContent) });
        continue;
      }
      var sourceBytes = StrictUtf8.GetBytes(source.Content);
      var local = edits.Select((edit, index) => (edit, index)).Where(pair => pair.edit.Uri == uri)
        .Select(pair => new EncodedByteEdit(pair.edit.Start, StrictUtf8.GetBytes(pair.edit.Text), pair.index))
        .OrderBy(pair => pair.Start).ThenBy(pair => pair.Sequence).ToList();
      foreach (var edit in local) {
        if (edit.Start < 0 || edit.Start > sourceBytes.Length ||
            edit.Start > 0 && edit.Start < sourceBytes.Length && (sourceBytes[edit.Start] & 0xC0) == 0x80) {
          throw new ArgumentException("A generator proof edit is outside a UTF-8 token boundary.");
        }
      }
      var outputLength = checked(sourceBytes.Length + local.Sum(edit => edit.Text.Length));
      var output = new byte[outputLength];
      var sourcePosition = 0;
      var outputPosition = 0;
      for (var editIndex = 0; editIndex < local.Count;) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        var editPosition = local[editIndex].Start;
        var unchangedLength = editPosition - sourcePosition;
        System.Buffer.BlockCopy(sourceBytes, sourcePosition, output, outputPosition, unchangedLength);
        sourcePosition = editPosition;
        outputPosition += unchangedLength;
        var groupEnd = editIndex + 1;
        while (groupEnd < local.Count && local[groupEnd].Start == editPosition) { groupEnd++; }
        for (var groupedIndex = groupEnd - 1; groupedIndex >= editIndex; groupedIndex--) {
          var text = local[groupedIndex].Text;
          System.Buffer.BlockCopy(text, 0, output, outputPosition, text.Length);
          outputPosition += text.Length;
        }
        editIndex = groupEnd;
      }
      System.Buffer.BlockCopy(sourceBytes, sourcePosition, output, outputPosition, sourceBytes.Length - sourcePosition);
      var content = StrictUtf8.GetString(output);
      result.Add(source with { Content = content, Sha256 = ContractHarnessBuilder.Hash(content) });
    }
    if (appendedPath != null && appendedContent != null) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      result.Add(new(appendedPath, appendedContent, ContractHarnessBuilder.Hash(appendedContent)));
    }
    return result;
  }

  private static bool TryUtf8ByteCount(string value, out int byteCount) {
    try {
      byteCount = StrictUtf8.GetByteCount(value);
      return true;
    } catch (EncoderFallbackException) {
      byteCount = 0;
      return false;
    }
  }

  private static bool TryAddWithinBudget(ref long total, long amount, long maximum) {
    if (amount < 0 || amount > maximum || total > maximum - amount) { return false; }
    total += amount;
    return true;
  }

  private static int MethodContractInsertionPosition(Method method) {
    var bodyStart = method.Body?.StartToken.pos ?? throw new NotSupportedException("The selected generator must have a body.");
    for (var token = method.StartToken; token != null && token.pos < bodyStart; token = token.Next) {
      if (token.val == "decreases") { return token.pos; }
    }
    return bodyStart;
  }

  private static string MemberOwnerReference(Program program, ModuleDefinition scope, TopLevelDecl owner) => owner switch {
    DefaultClassDecl => ContractHeapFactory.SourceModuleName(program, scope, owner.EnclosingModuleDefinition),
    TopLevelDeclWithMembers => ContractHeapFactory.SourceTypeName(program, scope, owner),
    _ => throw new NotSupportedException("A proof helper owner must be a source class.")
  };

  private static Expression SubstituteGoalInputs(Method goal, IReadOnlyList<Formal> helperFormals,
    Expression expression) {
    var substitution = goal.Ins.Select((formal, index) => (formal, index)).ToDictionary(pair =>
      (IVariable)pair.formal, pair => (Expression)new IdentifierExpr(pair.formal.Origin, helperFormals[pair.index]));
    return new Substituter(null, substitution, new Dictionary<TypeParameter, Type>()).Substitute(expression);
  }

  internal static async Task<string?> ValidateProofSourceBindingsAsync(Program program, Method goal,
    Method generator, Method admission, ContractGeneratorProofSourceBuild build, DafnyOptions options,
    long? deadlineTimestamp = null, CancellationToken cancellationToken = default) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    if (!build.MatchesSynthesizedSources() || admission.Name != build.AdmissionName ||
        !program.Descendants().OfType<Method>().Any(method => ReferenceEquals(method, admission))) {
      return "The proof scaffold is not bound to the exact internally synthesized source snapshots.";
    }
    // The authority is captured immediately by the internal source builder. Compare the
    // entire resolved program, including every helper, contract and ordered statement,
    // with an independent resolve of those exact snapshots rather than searching for calls.
    var binding = await BindPreparedProgramAsync(program, build.Sources, goal, generator, options,
      deadlineTimestamp, cancellationToken);
    return binding.Failure;
  }

  internal static async Task<(ContractGeneratorProofProgramBinding? Binding, string? Failure)> BindPreparedProgramAsync(
    Program program, IReadOnlyList<ContractSource> sources, Method goal, Method generator, DafnyOptions options,
    long? deadlineTimestamp, CancellationToken cancellationToken) {
    if (!program.Descendants().OfType<Method>().Any(method => ReferenceEquals(method, goal)) ||
        !program.Descendants().OfType<Method>().Any(method => ReferenceEquals(method, generator))) {
      return (null, "The selected goal and generator must be declarations owned by the exact prepared Program.");
    }
    if (!TryResolvedProgramFingerprint(program, deadlineTimestamp, cancellationToken, out var preparedFingerprint, out var fingerprintFailure)) {
      return (null, fingerprintFailure);
    }
    var reporter = new BatchErrorReporter(new DafnyOptions(options, useNullWriters: true));
    var reparsed = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken);
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    if (reporter.ErrorCount != 0) {
      return (null, "The exact prepared source snapshots could not be resolved again: " + FormatDiagnostics(reporter));
    }
    if (!TryResolvedProgramFingerprint(reparsed, deadlineTimestamp, cancellationToken, out var snapshotFingerprint, out fingerprintFailure)) {
      return (null, fingerprintFailure);
    }
    if (!StringComparer.Ordinal.Equals(preparedFingerprint, snapshotFingerprint)) {
      return (null, "The resolved prepared Program differs semantically from a fresh resolve of its exact source snapshots.");
    }
    if (!HasExactlyOneMatchingMethod(reparsed, goal, out var reboundGoal) ||
        !HasExactlyOneMatchingMethod(reparsed, generator, out var reboundGenerator) ||
        !StringComparer.Ordinal.Equals(NavigationIdentity(goal), NavigationIdentity(reboundGoal)) ||
        !StringComparer.Ordinal.Equals(NavigationIdentity(generator), NavigationIdentity(reboundGenerator))) {
      return (null, "The selected goal or generator does not resolve to the same exact source declaration in its snapshots.");
    }
    return (new(preparedFingerprint), null);
  }

  private static bool HasExactlyOneMatchingMethod(Program program, Method original, out Method match) {
    var candidates = program.Descendants().OfType<Method>().Where(method => method.FullDafnyName == original.FullDafnyName &&
      method.Origin.Uri == original.Origin.Uri && method.Name == original.Name).ToList();
    match = candidates.Count == 1 ? candidates[0] : null!;
    return candidates.Count == 1;
  }

  internal static bool TryResolvedProgramFingerprint(Program program, out string fingerprint) =>
    TryResolvedProgramFingerprint(program, null, CancellationToken.None, out fingerprint, out _);

  private static bool TryResolvedProgramFingerprint(Program program, long? deadlineTimestamp,
    CancellationToken cancellationToken, out string fingerprint, out string? failure) {
    fingerprint = "";
    failure = null;
    try {
      void CheckBoundary() => ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      CheckBoundary();
      var printOptions = new DafnyOptions(program.Options, useNullWriters: true) {
        DafnyPrintResolvedFile = null,
        ShowEnv = Microsoft.Boogie.ExecutionEngineOptions.ShowEnvironment.Never,
        PrintMode = PrintModes.Everything
      };
      using var writer = new BoundedSemanticWriter(CheckBoundary);
      new Printer(writer, printOptions, PrintModes.Everything, new PrintFlags(UseOriginalDafnyNames: true), CheckBoundary)
        .PrintProgram(program, afterResolver: true);
      var canonicalSource = writer.ToString();
      using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
      const string fingerprintSource = "/workspace/pbt-generator-proof-resolved.dfy";
      var semanticSource = SourceFingerprint.Compute(printOptions,
        new SourceFingerprintRequest([new("resolved", fingerprintSource, null, [])]),
        new Dictionary<string, string>(StringComparer.Ordinal) { [fingerprintSource] = canonicalSource },
        out var semanticSourceFailure);
      if (semanticSource == null) {
        throw new NotSupportedException(semanticSourceFailure ?? "The analyzer could not fingerprint the resolved proof program.");
      }
      long totalBytes = AppendSemanticField(hash, "resolved-dafny-tokens", semanticSource.Fingerprints.Single().Sha256, 0);
      var references = 0;
      void AppendReferences(INode sourceNode, IEnumerable<Reference> resolvedReferences) {
        foreach (var reference in resolvedReferences) {
          if (++references > MaximumSemanticReferences) {
            throw new NotSupportedException("The resolved Program exceeds the proof reference fingerprint limit.");
          }
          totalBytes = AppendSemanticField(hash, "node-kind", sourceNode.GetType().FullName ?? sourceNode.GetType().Name, totalBytes);
          totalBytes = AppendSemanticField(hash, "referer-range", RangeIdentity(reference.Referer), totalBytes);
          totalBytes = AppendSemanticField(hash, "resolved-target", NavigationIdentity(reference.Referred), totalBytes);
        }
      }
      foreach (var sourceNode in program.Descendants().OfType<IHasReferences>()) {
        CheckBoundary();
        AppendReferences(sourceNode, sourceNode.GetReferences());
      }
      foreach (var expression in program.Descendants().OfType<Expression>()) {
        CheckBoundary();
        var resolvedKind = expression switch {
          BinaryExpr binary => "binary:" + binary.ResolvedOp_PossiblyStillUndetermined,
          UnaryOpExpr unary => "unary:" + unary.ResolvedOp,
          _ => expression.GetType().FullName ?? expression.GetType().Name
        };
        totalBytes = AppendSemanticField(hash, "resolved-expression", RangeIdentity(expression.ReportingRange) + ":" + resolvedKind, totalBytes);
        if (expression.Type != null) {
          totalBytes = AppendSemanticField(hash, "resolved-expression-type", expression.Type.ToString(), totalBytes);
          AppendTypeReferences(expression.Type, expression, AppendReferences);
        }
        foreach (var componentType in expression.ComponentTypes) {
          AppendTypeReferences(componentType, expression, AppendReferences);
        }
      }
      CheckBoundary();
      fingerprint = Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
      return true;
    } catch (NotSupportedException error) {
      failure = "The resolved Program cannot be fingerprinted within the proof bounds: " + error.Message;
      return false;
    }
  }

  private static void AppendTypeReferences(Type type, Expression expression,
    Action<INode, IEnumerable<Reference>> appendReferences) {
    foreach (var referenceNode in type.Nodes.OfType<IHasReferences>()) {
      appendReferences(expression, referenceNode.GetReferences());
    }
  }

  private static long AppendSemanticField(IncrementalHash hash, string label, string value, long currentBytes) {
    var labelBytes = Encoding.UTF8.GetBytes(label);
    var valueBytes = Encoding.UTF8.GetBytes(value);
    var framing = Encoding.UTF8.GetBytes(Frame(valueBytes.Length.ToString(CultureInfo.InvariantCulture)));
    var needed = (long)labelBytes.Length + valueBytes.Length + framing.Length + sizeof(int);
    if (needed > MaximumSemanticFingerprintBytes - currentBytes) {
      throw new NotSupportedException("The canonical source/reference fingerprint exceeds 64 MiB.");
    }
    hash.AppendData(BitConverter.GetBytes(labelBytes.Length));
    hash.AppendData(labelBytes);
    hash.AppendData(framing);
    hash.AppendData(valueBytes);
    return currentBytes + needed;
  }

  private static string NavigationIdentity(IHasNavigationToken declaration) {
    var scopeIdentity = "";
    var qualifiedName = "";
    var kindIdentity = "";
    switch (declaration) {
      case TypeParameter typeParameter:
        scopeIdentity = "lexical-type-parameter";
        qualifiedName = TypeParameterQualifiedIdentity(typeParameter);
        kindIdentity = typeParameter.WhatKind;
        break;
      case MemberDecl member:
        scopeIdentity = "member";
        qualifiedName = MemberQualifiedIdentity(member);
        kindIdentity = member.WhatKind;
        break;
      case TopLevelDecl topLevel:
        (scopeIdentity, qualifiedName) = TopLevelQualifiedIdentity(topLevel);
        kindIdentity = topLevel.WhatKind;
        break;
      case DatatypeCtor constructor: {
          if (constructor.EnclosingDatatype == null) {
            throw new NotSupportedException("A resolved datatype constructor has no enclosing datatype.");
          }
          var (datatypeScope, datatypeName) = TopLevelQualifiedIdentity(constructor.EnclosingDatatype);
          scopeIdentity = "datatype-constructor";
          qualifiedName = Frame(datatypeScope) + Frame(datatypeName) + Frame(constructor.Name);
          kindIdentity = "datatype constructor";
          break;
        }
      case ModuleDefinition module:
        scopeIdentity = module.EnclosingModule == null ? "root" : "scoped";
        qualifiedName = module.FullDafnyName;
        kindIdentity = module.WhatKind;
        break;
      case LoopStmt loop:
        scopeIdentity = "loop-statement";
        qualifiedName = RangeIdentity(loop.NavigationRange);
        kindIdentity = loop.GetType().Name;
        break;
      case IVariable variable:
        scopeIdentity = "variable";
        qualifiedName = variable.Name + ":" + variable.Type;
        break;
      default:
        throw new NotSupportedException("The resolved reference target has no supported stable navigation identity: " +
          (declaration.GetType().FullName ?? declaration.GetType().Name));
    }
    return Frame(declaration.GetType().FullName ?? declaration.GetType().Name) +
      Frame(scopeIdentity) + Frame(qualifiedName) + Frame(kindIdentity) +
      Frame(declaration.Origin.Uri?.ToString() ?? "") +
      Frame(RangeIdentity(declaration.NavigationRange));
  }

  private static (string Scope, string QualifiedName) TopLevelQualifiedIdentity(TopLevelDecl declaration) {
    if (declaration.EnclosingModuleDefinition == null) {
      // _module has always denoted the empty Dafny name; retain that special case while framing root scope.
      var rootName = declaration.Name == "_module" ? declaration.FullDafnyName : declaration.FullName;
      return ("root", rootName);
    }
    return ("scoped", declaration.FullDafnyName);
  }

  private static string MemberQualifiedIdentity(MemberDecl declaration) {
    if (declaration.EnclosingClass == null) {
      throw new NotSupportedException("A resolved member has no enclosing top-level declaration.");
    }
    var (parentScope, parentName) = TopLevelQualifiedIdentity(declaration.EnclosingClass);
    return Frame(parentScope) + Frame(parentName) + Frame(declaration.Name);
  }

  private static string TypeParameterQualifiedIdentity(TypeParameter declaration) {
    var ownerIdentity = declaration.Parent switch {
      null => Frame("unowned-type-parameter"),
      MemberDecl member => Frame("member-owner") + Frame(NavigationIdentity(member)),
      TopLevelDecl topLevel when topLevel is not TypeParameter => Frame("top-level-owner") + Frame(NavigationIdentity(topLevel)),
      DatatypeCtor constructor => Frame("datatype-constructor-owner") + Frame(NavigationIdentity(constructor)),
      QuantifierExpr quantifier => Frame("quantifier-owner") + Frame(quantifier.GetType().FullName ?? quantifier.GetType().Name) +
        Frame(quantifier.WhatKind) + Frame(quantifier.Origin.Uri?.ToString() ?? "") +
        Frame(RangeIdentity(quantifier.Origin.ReportingRange)),
      var owner => throw new NotSupportedException("A type parameter has no supported stable lexical-owner identity: " +
        owner.GetType().FullName)
    };
    return Frame(ownerIdentity) +
      Frame(declaration.PositionalIndex.ToString(CultureInfo.InvariantCulture)) + Frame(declaration.Name);
  }

  private static string RangeIdentity(TokenRange range) =>
    (range.StartToken.filename ?? "") + ":" + range.StartToken.pos.ToString(CultureInfo.InvariantCulture) + ":" +
    range.EndToken.pos.ToString(CultureInfo.InvariantCulture) + ":" + range.EndToken.val.Length.ToString(CultureInfo.InvariantCulture);

  private sealed class BoundedSemanticWriter(Action checkBoundary) : StringWriter {
    private int written;

    private void Reserve(int count) {
      checkBoundary();
      if (count < 0 || count > MaximumSemanticPrintCharacters - written) {
        throw new NotSupportedException("The canonical resolved Program print exceeds 64 MiB.");
      }
      written += count;
    }

    public override void Write(char value) {
      Reserve(1);
      GetStringBuilder().Append(value);
    }

    public override void Write(string? value) {
      Reserve(value?.Length ?? 0);
      GetStringBuilder().Append(value);
    }

    public override void Write(char[] buffer, int index, int count) {
      Reserve(count);
      GetStringBuilder().Append(buffer, index, count);
    }

    public override void Write(ReadOnlySpan<char> buffer) {
      Reserve(buffer.Length);
      GetStringBuilder().Append(buffer);
    }

    public override void WriteLine(string? value) {
      Reserve((value?.Length ?? 0) + NewLine.Length);
      GetStringBuilder().Append(value).Append(NewLine);
    }

    public override void WriteLine() {
      Reserve(NewLine.Length);
      GetStringBuilder().Append(NewLine);
    }
  }

  private static IEnumerable<Declaration> GlobalReferenceSequence(Node root) => root.Descendants().Prepend(root).SelectMany(node => node switch {
    FunctionCallExpr call => new Declaration[] { call.Function },
    MemberSelectExpr member => new[] { member.Member },
    DatatypeValue { Ctor: { } constructor } => new Declaration[] { constructor },
    IdentifierExpr { Var: Declaration declaration } => new[] { declaration },
    _ => []
  });

  internal static bool PreparedInputsMatchSnapshots(Program program, IReadOnlyList<ContractSource> sources,
    Method goal, Method generator, out string failure, long? deadlineTimestamp = null,
    CancellationToken cancellationToken = default) {
    failure = "The resolved goal and generator must be bound to the supplied source snapshots.";
    try {
      if (!TryBuildSourceBufferMap(sources, deadlineTimestamp, cancellationToken, out var byUri, out failure)) {
        return false;
      }
      long comparedSpanBytes = 0;
      if (goal.Origin.Uri == null || !byUri.TryGetValue(goal.Origin.Uri, out var goalSource)) {
        failure = "The selected goal URI is absent from the supplied source snapshots: " + SourceBindingDescription(goal) + ".";
        return false;
      }
      if (!DeclarationSpanMatches(goal, goalSource.Bytes, ref comparedSpanBytes)) {
        failure = "The selected goal span does not match its exact source snapshot: " + SourceBindingDescription(goal) + ".";
        return false;
      }
      if (generator.Origin.Uri == null || !byUri.TryGetValue(generator.Origin.Uri, out var generatorSource)) {
        failure = "The selected generator URI is absent from the supplied source snapshots: " + SourceBindingDescription(generator) + ".";
        return false;
      }
      if (!DeclarationSpanMatches(generator, generatorSource.Bytes, ref comparedSpanBytes)) {
        failure = "The selected generator span does not match its exact source snapshot: " + SourceBindingDescription(generator) + ".";
        return false;
      }
      var systemModule = program.SystemModuleManager.SystemModule;
      var declarationCount = 0;
      foreach (var declaration in program.Descendants().OfType<Declaration>().Distinct()) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        if (++declarationCount > MaximumSemanticReferences) {
          failure = "The prepared Program exceeds the bounded source declaration audit limit.";
          return false;
        }
        if (ReferenceEquals(declaration, program.DefaultModule) || declaration is NonNullTypeDecl ||
            declaration is DefaultClassDecl && declaration.Origin == SourceOrigin.NoToken ||
            DeclarationModule(declaration) == systemModule) { continue; }
        var uri = declaration.Origin.Uri;
        if (uri == null) {
          failure = "The source-bound declaration has no URI: " + SourceBindingDescription(declaration) + ".";
          return false;
        }
        if (!byUri.TryGetValue(uri, out var source)) {
          failure = "The source-bound declaration URI is absent from the supplied snapshots: " + SourceBindingDescription(declaration) + ".";
          return false;
        }
        if (!DeclarationSpanMatches(declaration, source.Bytes, ref comparedSpanBytes)) {
          failure = "The resolved declaration span does not match its exact source snapshot: " + SourceBindingDescription(declaration) + ".";
          return false;
        }
      }
      failure = "";
      return true;
    } catch (ArgumentException) {
      return false;
    }
  }

  private static string SourceBindingDescription(Declaration declaration) {
    var range = declaration.EntireRange;
    var name = declaration.Name;
    var uri = declaration.Origin.Uri?.ToString() ?? "<no-uri>";
    return declaration.GetType().Name + " '" + (name.Length <= 256 ? name : name[..256]) + "' at " +
      (uri.Length <= 512 ? uri : uri[..512]) + " bytes " + range.StartToken.pos + ".." + range.EndToken.pos;
  }

  private static bool TryBuildSourceBufferMap(IReadOnlyList<ContractSource> sources, long? deadlineTimestamp,
    CancellationToken cancellationToken, out Dictionary<Uri, (ContractSource Source, byte[] Bytes)> byUri,
    out string failure) {
    byUri = [];
    failure = "Source snapshots are empty, duplicated or exceed the bounded source audit.";
    if (sources.Count == 0 || sources.Count > MaximumSemanticSources) { return false; }
    long aggregateSourceBytes = 0;
    var records = new List<(Uri Uri, ContractSource Source, int ByteCount)>(sources.Count);
    var seenUris = new HashSet<Uri>();
    for (var index = 0; index < sources.Count; index++) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var source = sources[index];
      if (source == null || string.IsNullOrWhiteSpace(source.Path) || source.Path.Length > 4096 || source.Content == null ||
          source.Content.Length > MaximumSemanticFingerprintBytes) {
        return false;
      }
      var byteCount = Encoding.UTF8.GetByteCount(source.Content);
      aggregateSourceBytes += byteCount;
      if (aggregateSourceBytes > MaximumSemanticFingerprintBytes) { return false; }
      var uri = ContractSourceSnapshot.UriFor(source.Path);
      if (!seenUris.Add(uri)) { return false; }
      records.Add((uri, source, byteCount));
    }
    foreach (var (uri, source, byteCount) in records) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var bytes = Encoding.UTF8.GetBytes(source.Content);
      if (bytes.Length != byteCount || Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant() != source.Sha256) {
        failure = "Source snapshots contain a stale content hash or changed while their bounded buffers were built.";
        return false;
      }
      byUri.Add(uri, (source, bytes));
    }
    failure = "";
    return true;
  }

  private static bool DeclarationSpanMatches(Declaration declaration, byte[] sourceBytes, ref long comparedSpanBytes) {
    var range = declaration.EntireRange;
    var length = TokenByteLength(range);
    if (range.StartToken.pos < 0 || length < 0 || length > int.MaxValue ||
        (long)range.StartToken.pos + length > sourceBytes.Length) { return false; }
    comparedSpanBytes += length;
    if (comparedSpanBytes > MaximumSemanticFingerprintBytes) { return false; }
    return Encoding.UTF8.GetString(sourceBytes, range.StartToken.pos, (int)length) == range.PrintOriginal();
  }

  private static long TokenByteLength(TokenRange range) => (long)range.EndToken.pos +
    Encoding.UTF8.GetByteCount(range.EndToken.val) - range.StartToken.pos;

  private static bool TrySnapshotSources(IReadOnlyList<ContractSource> sources, long deadlineTimestamp,
    CancellationToken cancellationToken, out ContractSource[] snapshot, out string failure) {
    snapshot = [];
    failure = "Source snapshots are empty or exceed the bounded proof input limit.";
    try {
      var count = sources.Count;
      if (count == 0 || count > MaximumSemanticSources) { return false; }
      var copy = new ContractSource[count];
      long aggregateBytes = 0;
      for (var index = 0; index < count; index++) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        var source = sources[index];
        if (source == null || string.IsNullOrWhiteSpace(source.Path) || source.Path.Length > 4096 || source.Content == null ||
            source.Content.Length > MaximumSemanticFingerprintBytes) { return false; }
        aggregateBytes += Encoding.UTF8.GetByteCount(source.Content);
        if (aggregateBytes > MaximumSemanticFingerprintBytes) { return false; }
        copy[index] = source with { };
      }
      snapshot = copy;
      failure = "";
      return true;
    } catch (InvalidOperationException) {
      failure = "Source snapshots changed while a private proof input copy was being made.";
      return false;
    } catch (ArgumentException) {
      failure = "A source snapshot path or content value is outside the bounded proof input policy.";
      return false;
    }
  }

  private static bool CallerSourcesMatch(IReadOnlyList<ContractSource> current, IReadOnlyList<ContractSource> snapshot,
    long? deadlineTimestamp, CancellationToken cancellationToken) {
    try {
      if (current.Count != snapshot.Count) { return false; }
      for (var index = 0; index < snapshot.Count; index++) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        if (current[index] != snapshot[index]) { return false; }
      }
      return true;
    } catch (ArgumentException) {
      return false;
    } catch (InvalidOperationException) {
      return false;
    }
  }

  private static bool CallerInputsStillMatch(Program program, IReadOnlyList<ContractSource> currentSources,
    IReadOnlyList<ContractSource> sourceSnapshot, DafnyOptions currentOptions, string initialOptionsFingerprint,
    long? deadlineTimestamp, CancellationToken cancellationToken, out string failure) {
    failure = "The caller's source, Program or verifier options changed while the proof was running.";
    if (!CallerSourcesMatch(currentSources, sourceSnapshot, deadlineTimestamp, cancellationToken) ||
        ProofOptionFailure(currentOptions) != null || ProofOptionFailure(program.Options) != null ||
        !TryOptionsFingerprint(currentOptions, out var currentOptionsFingerprint) ||
        currentOptionsFingerprint != initialOptionsFingerprint ||
        !TryOptionsFingerprint(program.Options, out var programOptionsFingerprint) ||
        programOptionsFingerprint != initialOptionsFingerprint) {
      return false;
    }
    failure = "";
    return true;
  }

  private static ModuleDefinition? DeclarationModule(Declaration declaration) => declaration switch {
    MemberDecl member => member.EnclosingClass.EnclosingModuleDefinition,
    TopLevelDecl topLevel => topLevel.EnclosingModuleDefinition,
    _ => null
  };

  internal static bool SupportedSelectedGoal(Program program, Method goal, Method generator, out string failure) {
    failure = "";
    if (!goal.IsStatic || goal.IsGhost || goal.TypeArgs.Count != 0) {
      failure = "Only a concrete, nongeneric static goal with value inputs is supported; receiver and heap proofs are not enabled.";
      return false;
    }
    if (goal.Ins.Any(formal => formal.IsGhost || !SupportedValueType(formal.Type, new HashSet<string>()))) {
      failure = "A goal input is ghost or outside the supported scalar, sequence and inductive datatype value domain.";
      return false;
    }
    var canonicalGeneratorName = ContractRuntimeGeneratorSignature.Names(goal, generator).MethodName;
    var exactGeneratorIdentity = program.Descendants().OfType<Method>()
      .Any(method => ReferenceEquals(method, generator)) &&
      generator.EnclosingClass is DefaultClassDecl &&
      generator.EnclosingClass.EnclosingModuleDefinition == goal.EnclosingClass.EnclosingModuleDefinition &&
      generator.Origin.Uri == goal.Origin.Uri && generator.Name == canonicalGeneratorName &&
      ContractRuntimeGeneratorSignature.HasExactMarker(generator, goal.FullDafnyName);
    if (!exactGeneratorIdentity || generator.IsGhost || !generator.IsStatic || generator.Body == null ||
        generator.TypeArgs.Count != 0 || generator.AllowsNontermination || generator.Ins.Count != 1 ||
        generator.Ins[0].SafeSyntacticType.ToString() != "PbtRandom.Source" ||
        generator.Outs.Count != goal.Ins.Count || generator.Outs.Any(formal => formal.IsGhost) ||
        generator.Req.Count > 0) {
      failure = "The exact canonical generator method must carry the target marker in the goal module and source, be terminating and non-ghost, have no authored requires, and match the goal inputs.";
      return false;
    }
    foreach (var pair in goal.Ins.Zip(generator.Outs)) {
      if (pair.First.Name != pair.Second.Name || !pair.First.Type.Equals(pair.Second.Type)) {
        failure = "Generator outputs must match goal input identities by position, name and resolved type.";
        return false;
      }
    }
    var randomModules = program.RawModules().Where(module => module.Name == ContractGeneratorProofAudit.PbtRandomModuleName).ToList();
    var randomModule = randomModules.Count == 1 ? randomModules[0] : null;
    var randomSourceType = generator.Ins[0].Type.NormalizeExpandKeepConstraints();
    var randomSource = randomSourceType is UserDefinedType { ResolvedClass: ClassDecl sourceClass }
      ? sourceClass
      : randomSourceType is UserDefinedType { ResolvedClass: NonNullTypeDecl { Class: ClassDecl nonNullSourceClass } }
        ? nonNullSourceClass
        : null;
    if (randomModule == null || randomSource == null || randomSource.EnclosingModuleDefinition != randomModule ||
        randomSource.Name != "Source") {
      failure = "Generate must receive the Source type from the exact embedded PbtRandom module.";
      return false;
    }
    if (goal.Req.Count == 0) {
      failure = "At least one original goal requires clause is needed for positive admission-correctness coverage.";
      return false;
    }
    return true;
  }

  internal static bool SupportedValueType(Type type, HashSet<string> visiting, int depth = 0) {
    if (depth > 96) { return false; }
    type = type.NormalizeExpandKeepConstraints();
    if (type.IsIntegerType || type.IsBoolType || type.IsCharType || type.IsBitVectorType) { return true; }
    if (type is SeqType sequence) { return SupportedValueType(sequence.Arg, visiting, depth + 1); }
    if (type is not UserDefinedType userType || userType.ResolvedClass == null) { return false; }
    if (userType.TypeArgs.Any(argument => !SupportedValueType(argument, visiting, depth + 1))) { return false; }
    var declaration = userType.ResolvedClass;
    var key = TypeIdentity(type);
    if (declaration is IndDatatypeDecl datatype) {
      if (!visiting.Add(key)) { return true; }
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, userType.TypeArgs);
      var supported = datatype.Ctors.SelectMany(constructor => constructor.Formals)
        .All(formal => SupportedValueType(formal.Type.Subst(substitution), visiting, depth + 1));
      visiting.Remove(key);
      return supported;
    }
    if (declaration is SubsetTypeDecl subset) {
      if (!visiting.Add(key)) { return true; }
      var substitution = TypeParameter.SubstitutionMap(subset.TypeArgs, userType.TypeArgs);
      var supported = SupportedValueType(subset.Rhs.Subst(substitution), visiting, depth + 1);
      visiting.Remove(key);
      return supported;
    }
    if (declaration is NewtypeDecl newtype && newtype.BaseType != null) {
      if (!visiting.Add(key)) { return true; }
      var supported = SupportedValueType(newtype.ConcreteBaseType(userType.TypeArgs), visiting, depth + 1);
      visiting.Remove(key);
      return supported;
    }
    return false;
  }

  private static string TypeIdentity(Type type) {
    type = type.NormalizeExpandKeepConstraints();
    return type switch {
      SeqType sequence => "seq<" + TypeIdentity(sequence.Arg) + ">",
      UserDefinedType userType => (userType.ResolvedClass?.FullDafnyName ?? userType.Name) + "<" +
        string.Join(",", userType.TypeArgs.Select(TypeIdentity)) + ">",
      _ => type.GetType().FullName + ":" + type
    };
  }

  private static bool GoalRequiresAreValueOnly(Program program, Method goal, out string failure) {
    failure = "";
    foreach (var expression in goal.Req.Select(requirement => requirement.E)) {
      if (expression.DescendantsAndSelf.OfType<OldExpr>().Any() || expression.DescendantsAndSelf.OfType<ThisExpr>().Any()) {
        failure = "Old-state and receiver-dependent goal requirements need a separate heap-aware proof capability.";
        return false;
      }
      if (expression.DescendantsAndSelf.OfType<MemberSelectExpr>().Any(select => select.Member is Field field &&
            (field.IsMutable || field is not ConstantField { Rhs: not null, HasStaticKeyword: true }))) {
        failure = "Goal requirements that read mutable heap fields or instance state are outside the value-only proof scope.";
        return false;
      }
      if (expression.DescendantsAndSelf.OfType<FunctionCallExpr>().Any(call => call.Function is TwoStateFunction or ExtremePredicate or PrefixPredicate)) {
        failure = "Two-state, extreme or prefix functions are outside the bounded goal requirement scope.";
        return false;
      }
      var directFunctions = ContractRuntimeObligationTransformer.FunctionReferences(expression).ToList();
      var reachableFunctions = ContractRuntimeObligationTransformer.ExecutionReachable(program, directFunctions).OfType<Function>();
      if (reachableFunctions.Any(function => function.ReadsHeap || function.Body?.DescendantsAndSelf.OfType<MemberSelectExpr>()
            .Any(select => select.Member is Field field && (field.IsMutable || field is not ConstantField { Rhs: not null, HasStaticKeyword: true })) == true)) {
        failure = "Goal requirement functions that read mutable or instance heap state are outside the value-only proof scope.";
        return false;
      }
    }
    return true;
  }

  private static IEnumerable<Declaration> SourceDeclarations(Program program, IReadOnlyList<ContractSource> sources,
    ContractGeneratorProofAudit audit) {
    var uris = sources.Select(source => ContractSourceSnapshot.UriFor(source.Path)).ToHashSet();
    foreach (var declaration in program.Descendants().OfType<Declaration>().Distinct()) {
      if (audit.IsPinnedRngDeclaration(declaration) || declaration is NonNullTypeDecl) { continue; }
      if (declaration.Origin.Uri != null && uris.Contains(declaration.Origin.Uri)) { yield return declaration; }
    }
  }

  private static bool TryFindProofTargets(Program program, IReadOnlyList<ContractSource> originalSources,
    Method originalGoal, Method originalGenerator, string admissionName, out Method proofGoal,
    out Method proofGenerator, out Method admission, out string failure) {
    var goalCandidates = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>()
      .Where(method => method.FullDafnyName == originalGoal.FullDafnyName && method.Origin.Uri == originalGoal.Origin.Uri).ToList();
    var generatorCandidates = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>()
      .Where(method => method.FullDafnyName == originalGenerator.FullDafnyName && method.Origin.Uri == originalGenerator.Origin.Uri).ToList();
    var admissionCandidates = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members).OfType<Method>()
      .Where(method => method.Name == admissionName && method.Origin.Uri == originalGenerator.Origin.Uri).ToList();
    if (goalCandidates.Count != 1 || generatorCandidates.Count != 1 || admissionCandidates.Count != 1) {
      proofGoal = proofGenerator = admission = null!;
      failure = "The exact goal, generator or generated admission method was not uniquely found in the proof snapshots.";
      return false;
    }
    proofGoal = goalCandidates[0];
    proofGenerator = generatorCandidates[0];
    admission = admissionCandidates[0];
    failure = "";
    return true;
  }

  internal sealed class Certificate {
    private readonly Program originalProgram;
    private readonly Method originalGoal;
    private readonly Method originalGenerator;
    private readonly ContractSource[] originalSources;
    private readonly DafnyOptions proofInputOptions;
    private readonly string originalSourceHash;
    private readonly string proofSourceHash;
    private readonly string policyVersion;
    private readonly string randomSourceHash;
    private readonly string randomRuntimeHash;
    private readonly string inputOptionsFingerprint;
    private readonly string parseOptionsFingerprint;
    private readonly string nativeOptionsFingerprint;
    private readonly ContractPinnedSolverIdentity solverIdentity;
    private readonly string semanticProgramFingerprint;
    private readonly int timeoutMilliseconds;
    private readonly IReadOnlyList<string> coveredChecks;
    private readonly IReadOnlyList<string> positiveImplementations;

    internal Certificate(Program originalProgram, Method originalGoal, Method originalGenerator,
      IReadOnlyList<ContractSource> originalSources, DafnyOptions proofInputOptions,
      string originalSourceHash, string proofSourceHash, string policyVersion, string randomSourceHash,
      string randomRuntimeHash, string inputOptionsFingerprint, string parseOptionsFingerprint,
      string nativeOptionsFingerprint, ContractPinnedSolverIdentity solverIdentity,
      string semanticProgramFingerprint, int timeoutMilliseconds, IReadOnlyList<string> coveredChecks,
      IReadOnlyList<string> positiveImplementations) {
      this.originalProgram = originalProgram;
      this.originalGoal = originalGoal;
      this.originalGenerator = originalGenerator;
      this.originalSources = originalSources.ToArray();
      this.proofInputOptions = proofInputOptions;
      this.originalSourceHash = originalSourceHash;
      this.proofSourceHash = proofSourceHash;
      this.policyVersion = policyVersion;
      this.randomSourceHash = randomSourceHash;
      this.randomRuntimeHash = randomRuntimeHash;
      this.inputOptionsFingerprint = inputOptionsFingerprint;
      this.parseOptionsFingerprint = parseOptionsFingerprint;
      this.nativeOptionsFingerprint = nativeOptionsFingerprint;
      this.solverIdentity = solverIdentity;
      this.semanticProgramFingerprint = semanticProgramFingerprint;
      this.timeoutMilliseconds = timeoutMilliseconds;
      this.coveredChecks = coveredChecks;
      this.positiveImplementations = positiveImplementations;
    }

    internal bool Matches(Program program, IReadOnlyList<ContractSource> sources, Method goal, Method generator,
      DafnyOptions options) {
      if (ProofOptionFailure(options) != null || ProofOptionFailure(program.Options) != null ||
          !ReferenceEquals(originalProgram, program) || !ReferenceEquals(originalGoal, goal) ||
          !ReferenceEquals(originalGenerator, generator) ||
          originalSourceHash.Length != 64 || !CallerSourcesMatch(sources, originalSources, null, CancellationToken.None) ||
          policyVersion != ContractGeneratorProofAudit.PolicyVersion ||
          ContractGeneratorProofAudit.PbtRandomSourceSha256 != randomSourceHash ||
          ContractHarnessBuilder.Hash(ContractRuntimeLibrary.Read("PbtRandom.cs")) != randomRuntimeHash ||
          coveredChecks.Count == 0 || positiveImplementations.Count == 0 || proofSourceHash.Length != 64 ||
          !TryResolvedProgramFingerprint(program, out var currentSemanticFingerprint) ||
          currentSemanticFingerprint != semanticProgramFingerprint ||
          !TryCapturePinnedSolverFile(out var currentSolver, out _) ||
          !SolverIdentityMatches(solverIdentity.Path, solverIdentity.Sha256, solverIdentity.Version,
            currentSolver.Path, currentSolver.Sha256, solverIdentity.Version) ||
          !TryOptionsFingerprint(options, out var currentInputFingerprint) ||
          !TryOptionsFingerprint(program.Options, out var currentProgramFingerprint) ||
          currentInputFingerprint != inputOptionsFingerprint || currentProgramFingerprint != inputOptionsFingerprint) {
        return false;
      }
      var parseOptions = ProofOptions(proofInputOptions, timeoutMilliseconds, solverIdentity.Path);
      return TryOptionsFingerprint(parseOptions, out var currentParseFingerprint) &&
        parseOptionsFingerprint == currentParseFingerprint &&
        TryOptionsFingerprint(NativeProofOptions(proofInputOptions, timeoutMilliseconds, solverIdentity), out var currentNativeFingerprint) &&
        nativeOptionsFingerprint == currentNativeFingerprint;
    }
  }
}
