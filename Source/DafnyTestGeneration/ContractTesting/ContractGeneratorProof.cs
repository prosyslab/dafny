#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Classifies the outcome of one bounded proof attempt.</summary>
public enum ContractGeneratorProofStatus { Verified, Unsupported, Failed, Cancelled, TimedOut }

/// <summary>Reports generator and implication verification without exposing omission authority.</summary>
public sealed record ContractGeneratorProofReport(ContractGeneratorProofStatus Status, string Diagnostics,
  IReadOnlyList<string> RequiredNativeChecks, IReadOnlyList<string> CoveredNativeChecks) {
  internal ContractGeneratorProof.Certificate? VerifiedCertificate { get; init; }
}

internal sealed record ContractGeneratorProofCoverage(IReadOnlySet<string> RequiredChecks,
  IReadOnlySet<string> CoveredChecks, bool ScopesAccepted, string AdmissionCorrectnessCheck,
  string GeneratorCorrectnessCheck, IReadOnlySet<string> VerifiedImplementationChecks, bool Failed) {
  internal bool Complete => !Failed && ScopesAccepted && RequiredChecks.Count != 0 &&
    RequiredChecks.SetEquals(CoveredChecks) &&
    new[] { AdmissionCorrectnessCheck, GeneratorCorrectnessCheck }.All(check =>
      RequiredChecks.Contains(check) && VerifiedImplementationChecks.Contains(check));
}

internal sealed record ContractGeneratorProofSourceBuild(IReadOnlyList<ContractSource> Sources, string AdmissionName);

/// <summary>Proves the authored generator contract and its implication of the selected input requirements.</summary>
public static class ContractGeneratorProof {
  private const int MaximumTimeoutMilliseconds = 600_000;
  private const long MaximumProofSourceBytes = 64L * 1024 * 1024;
  private static readonly UTF8Encoding StrictUtf8 = new(false, true);
  private static readonly Lazy<DafnyOptions> DefaultBoogieSettings = new(CreateDefaultBoogieSettings);
  private const string AdmissionBaseName = "PbtGeneratorAdmission";

  // Only the native host can supply the ordinary verifier. Public reports cannot supply a backend or a certificate.
  internal static async Task<ContractGeneratorProofReport> TryProveAsync(
    IReadOnlyList<ContractSource> preparedSources, IReadOnlyList<ContractSource> authoredSources,
    string goalName, string generatorName, DafnyOptions options,
    IProgramVerifier verifier, int timeoutMilliseconds, CancellationToken cancellationToken = default,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze = null) {
    if (timeoutMilliseconds is <= 0 or > MaximumTimeoutMilliseconds) {
      return Report(ContractGeneratorProofStatus.Unsupported, "The generator proof timeout is outside the supported bounds.");
    }
    var deadline = ContractQueryDeadline.AfterMilliseconds(timeoutMilliseconds);
    using var bounded = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    bounded.CancelAfter(timeoutMilliseconds);
    var token = bounded.Token;
    try {
      ContractQueryDeadline.Check(deadline, token);
      var sourceSnapshot = preparedSources.Select(source => source with { }).ToArray();
      ContractSourceSnapshot.ValidateTrustedSources(sourceSnapshot, null);
      if (ProofOptionFailure(options) is { } optionFailure) {
        return Report(ContractGeneratorProofStatus.Unsupported, optionFailure);
      }
      if (!options.TryCreateDetachedSnapshot(out var proofOptions, out var snapshotFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, snapshotFailure);
      }
      var snapshotReporter = new BatchErrorReporter(proofOptions);
      var authoredSnapshot = await AuthoredProofSourcesAsync(authoredSources, sourceSnapshot, proofOptions, token);
      if (authoredSnapshot == null) {
        return Report(ContractGeneratorProofStatus.Unsupported, "The authored and executable source snapshots do not match the ordinary visibility transformation.");
      }
      var authoredProgram = await ContractSourceSnapshot.ParseAsync(snapshotReporter, authoredSnapshot, token);
      if (snapshotReporter.ErrorCount != 0) {
        return Report(ContractGeneratorProofStatus.Unsupported, "Authored generator proof sources do not resolve normally: " +
          string.Join("\n", snapshotReporter.AllMessages.Select(message => message.Message)));
      }
      var runtimeReporter = new BatchErrorReporter(proofOptions);
      var runtimeProgram = await ContractSourceSnapshot.ParseAsync(runtimeReporter, sourceSnapshot, token);
      if (runtimeReporter.ErrorCount != 0) {
        return Report(ContractGeneratorProofStatus.Unsupported, "Runtime snapshots require deferred diagnostic resolution.");
      }
      var goal = ContractCallableSelector.SelectMethod(authoredProgram, new(goalName), requireConcreteReceiver: false, allowLemmaContract: true);
      var generator = ContractRuntimeGeneratorSignature.Select(authoredProgram, goal, generatorName);
      var runtimeGoal = ContractCallableSelector.SelectMethod(runtimeProgram, new(goalName), requireConcreteReceiver: false, allowLemmaContract: true);
      var runtimeGenerator = ContractRuntimeGeneratorSignature.Select(runtimeProgram, runtimeGoal, generatorName);
      if (!SupportedSelectedGoal(authoredProgram, goal, generator, out var capabilityFailure) ||
          !ContractsAreValueOnly(authoredProgram, goal, generator, out capabilityFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, capabilityFailure);
      }
      ContractQueryDeadline.Check(deadline, token);
      var randomSource = ExtractPinnedPbtRandomSource();
      var build = PrepareProofSources(authoredProgram, authoredSnapshot, goal, generator, randomSource, out var failure,
        deadline, token);
      if (build == null) { return Report(ContractGeneratorProofStatus.Unsupported, failure!); }
      var rawReporter = new BatchErrorReporter(proofOptions);
      var raw = await ContractSourceSnapshot.ParseAsync(rawReporter, build.Sources, token, resolve: false);
      if (rawReporter.ErrorCount != 0) {
        return Report(ContractGeneratorProofStatus.Failed, string.Join("\n", rawReporter.AllMessages.Select(message => message.Message)));
      }
      var rawFailure = ContractGeneratorProofAudit.AuditRawProgram(raw, build.Sources, generator.Origin.Uri,
        generator.Name, goal.FullDafnyName, randomSource);
      if (rawFailure != null) { return Report(ContractGeneratorProofStatus.Unsupported, rawFailure); }

      // Keep the fresh original-source resolve's options unchanged for later exact binding checks.
      if (!proofOptions.TryCreateDetachedSnapshot(out var verificationOptions, out snapshotFailure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, snapshotFailure);
      }
      proofOptions = verificationOptions;
      proofOptions.Compile = false;
      proofOptions.VerifyAllModules = true;
      proofOptions.ProcsToCheck = ["*"];
      proofOptions.ProcsToIgnore = [];
      proofOptions.TimeLimit = (uint)Math.Max(1, (timeoutMilliseconds + 999) / 1000);
      var diagnostics = new List<string>();
      var reporter = new ObservableErrorReporter(proofOptions, generator.Origin.Uri);
      using var reporting = reporter.Updates.Subscribe(diagnostic => diagnostics.Add(diagnostic.Diagnostic.Message));
      var proofProgram = await ContractSourceSnapshot.ParseAsync(reporter, build.Sources, token);
      if (reporter.ErrorCount != 0) { return Report(ContractGeneratorProofStatus.Failed, string.Join("\n", diagnostics)); }
      if (!TryFindProofTargets(proofProgram, sourceSnapshot, goal, generator, build.AdmissionName,
            out var proofGoal, out var proofGenerator, out var admission, out failure)) {
        return Report(ContractGeneratorProofStatus.Unsupported, failure);
      }
      var scopes = ProofScopes(proofProgram, build.Sources, proofGoal, proofGenerator, admission, randomSource);
      if (scopes.Any(scope => scope.Failure != null)) {
        return Report(ContractGeneratorProofStatus.Unsupported, string.Join("\n", scopes.Select(scope => scope.Failure).OfType<string>()));
      }
      if (scopes.Any(scope => scope.ContainsDeclaration(proofGoal))) {
        return Report(ContractGeneratorProofStatus.Unsupported, "A generator proof dependency reaches the selected target body.");
      }
      var requiredDefinitions = scopes.SelectMany(scope => scope.Checks).Select(check => check.Declaration)
        .OfType<MethodOrFunction>().Distinct().Select(ContractGeneratorDefinitionIdentity.For).ToArray();
      var originalDefinitions = requiredDefinitions.Where(identity => identity != ContractGeneratorDefinitionIdentity.For(admission)).ToArray();
      var originalBinding = ContractGeneratorInputBinding.Capture(runtimeProgram, sourceSnapshot, originalDefinitions, analyze);
      if (originalBinding == null) {
        return Report(ContractGeneratorProofStatus.Unsupported, "The analyzer could not bind every required original callable body.");
      }
      proofOptions.ProcessSolverOptions(reporter, generator.Origin);
      if (reporter.ErrorCount != 0) { return Report(ContractGeneratorProofStatus.Failed, string.Join("\n", diagnostics)); }
      var proofBinding = ContractGeneratorInputBinding.Capture(proofProgram, build.Sources, requiredDefinitions, analyze);
      if (proofBinding == null) { return Report(ContractGeneratorProofStatus.Unsupported, "The analyzer could not identify the implication proof inputs."); }
      ContractQueryDeadline.Check(deadline, token);
      var checkedProof = await ContractGeneratorVerification.VerifyAsync(proofProgram, verifier, scopes,
        proofGenerator, admission, deadline, token);
      diagnostics.Add(checkedProof.Diagnostics);
      if (!checkedProof.Coverage.Complete) {
        return new(checkedProof.TimedOut ? ContractGeneratorProofStatus.TimedOut : ContractGeneratorProofStatus.Failed, string.Join("\n", diagnostics),
          checkedProof.Coverage.RequiredChecks.Order().ToArray(), checkedProof.Coverage.CoveredChecks.Order().ToArray());
      }
      ContractQueryDeadline.Check(deadline, token);
      var bindingFailure = FinalBindingFailure(proofBinding, proofProgram, build.Sources,
        originalBinding, runtimeProgram, preparedSources, options);
      if (bindingFailure != null) {
        return Report(ContractGeneratorProofStatus.Unsupported, bindingFailure);
      }
      var certificate = new Certificate(runtimeProgram, runtimeGoal, runtimeGenerator, originalBinding,
        proofProgram, build.Sources, proofBinding, checkedProof.Coverage.RequiredChecks);
      return new(ContractGeneratorProofStatus.Verified, string.Join("\n", diagnostics),
        checkedProof.Coverage.RequiredChecks.Order().ToArray(), checkedProof.Coverage.CoveredChecks.Order().ToArray()) {
        VerifiedCertificate = certificate
      };
    } catch (OperationCanceledException error) {
      return Report(cancellationToken.IsCancellationRequested ? ContractGeneratorProofStatus.Cancelled : ContractGeneratorProofStatus.TimedOut,
        error.Message);
    }
  }

  internal static IReadOnlyList<ContractSpecificationScope> ProofScopes(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, Method generator, Method admission, string randomSource) {
    var audit = ContractGeneratorProofAudit.BindResolved(program, sources, null, randomSource);
    var checker = new ContractSpecificationChecker(program, sources, program.Options);
    var declarations = SourceDeclarations(program, sources, audit).ToList();
    var functions = declarations.OfType<Function>().Cast<MethodOrFunction>();
    var types = declarations.OfType<TopLevelDecl>()
      .Where(declaration => declaration is SubsetTypeDecl or NewtypeDecl && declaration is not NonNullTypeDecl)
      .Select(declaration => (Type)UserDefinedType.FromTopLevelDecl(declaration.Origin, declaration));
    var constants = declarations.OfType<ConstantField>().Where(constant => constant.Rhs != null).ToList();
    return [
      checker.AuditedProofScope(ContractSpecificationRole.Execution, [generator, admission], goal.Ins.Select(formal => formal.Type), constants, audit),
      checker.AuditedProofScope(ContractSpecificationRole.Logical, functions, types.Concat(goal.Ins.Select(formal => formal.Type)), constants, audit)
    ];
  }

  internal static bool AcceptCoverage(ContractGeneratorProofCoverage coverage) => coverage.Complete;
  private static ContractGeneratorProofReport Report(ContractGeneratorProofStatus status, string diagnostics) => new(status, diagnostics, [], []);

  internal static string? FinalBindingFailure(ContractGeneratorInputBinding proofBinding, Program proofProgram,
    IReadOnlyList<ContractSource> proofSources, ContractGeneratorInputBinding runtimeBinding, Program runtimeProgram,
    IReadOnlyList<ContractSource> runtimeSources, DafnyOptions callerOptions,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze = null) {
    if (proofBinding.Mismatch(proofProgram, proofSources, analyze) is { } proofFailure) {
      return "Generator proof binding rejected: " + proofFailure;
    }
    if (runtimeBinding.Mismatch(runtimeProgram, runtimeSources, analyze) is { } runtimeFailure) {
      return "Generator runtime binding rejected: " + runtimeFailure;
    }
    return ProofOptionFailure(callerOptions) is { } policyFailure
      ? "Generator caller policy rejected: " + policyFailure : null;
  }

  // Authenticate the pre-erasure source through the same visibility operation used by the runtime host.
  internal static async Task<IReadOnlyList<ContractSource>?> AuthoredProofSourcesAsync(
    IReadOnlyList<ContractSource> authoredSources, IReadOnlyList<ContractSource> runtimeSources,
    DafnyOptions options, CancellationToken cancellationToken) {
    var authored = authoredSources.Select(source => source with { }).ToArray();
    ContractSourceSnapshot.ValidateTrustedSources(authored, null);
    ContractSourceSnapshot.ValidateTrustedSources(runtimeSources, null);
    var runtime = runtimeSources.Where(source => source.Content == ContractRuntimeInstrumentation.DafnySource).ToArray();
    if (runtime.Length != 1) { return null; }
    var reporter = new BatchErrorReporter(options);
    var raw = await ContractSourceSnapshot.ParseAsync(reporter, authored, cancellationToken, resolve: false);
    if (reporter.ErrorCount != 0) { return null; }
    var expected = ContractRuntimeObligationTransformer.MakeGeneratorVisible(raw, authored, new HashSet<string>())
      .Append(runtime[0]).ToArray();
    return ContractRuntimeTypeEvidence.SourceSetHash(expected) == ContractRuntimeTypeEvidence.SourceSetHash(runtimeSources)
      ? authored.Append(runtime[0]).ToArray() : null;
  }

  internal static string ExtractPinnedPbtRandomSource() {
    var runtime = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");
    const string marker = "module {:extern \"DafnyPbtRandom\"} PbtRandom {";
    var start = runtime.IndexOf(marker, StringComparison.Ordinal);
    if (start < 0) { throw new InvalidOperationException("The embedded PbtRandom module is missing."); }
    return runtime[start..];
  }

  internal static ContractGeneratorProofSourceBuild? PrepareProofSources(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, Method generator, string randomModuleSource,
    out string? failure, long? deadlineTimestamp = null, CancellationToken cancellationToken = default,
    long maximumPreparedSourceBytes = MaximumProofSourceBytes) {
    failure = null;
    if (maximumPreparedSourceBytes < 0 || maximumPreparedSourceBytes > MaximumProofSourceBytes ||
        sources.Count == 0 || sources.Count > 4096 ||
        sources.Sum(source => (long)StrictUtf8.GetByteCount(source.Content)) > maximumPreparedSourceBytes) {
      failure = "The prepared proof sources exceed the bounded source policy.";
      return null;
    }
    if (!ContractsAreValueOnly(program, goal, generator, out var contractFailure)) {
      failure = contractFailure;
      return null;
    }
    var name = ContractBodyNames.Family(program, AdmissionBaseName);
    var scope = generator.EnclosingClass.EnclosingModuleDefinition;
    var formals = generator.Outs.Select((formal, index) => new Formal(formal.Origin, name + "Output" + index,
      formal.Type, true, false, null)).ToList();
    var lemma = new StringBuilder("\nlemma ").Append(name).Append('(')
      .Append(string.Join(", ", formals.Select(formal => formal.Name + ": " + ContractQueryBuilder.QualifiedType(program, scope, formal.Type))))
      .Append(")\n");
    foreach (var (keyword, originalFormals, expressions) in new[] {
               ("requires", generator.Outs, generator.Ens), ("ensures", goal.Ins, goal.Req) }) {
      var substitution = originalFormals.Select((formal, index) => (formal, index)).ToDictionary(pair =>
        (IVariable)pair.formal, pair => (Expression)new IdentifierExpr(pair.formal.Origin, formals[pair.index]));
      foreach (var clause in expressions) {
        ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
        var copied = new Substituter(null, substitution, new Dictionary<TypeParameter, Type>()).Substitute(clause.E);
        var qualified = ContractQueryBuilder.QualifyExpression(program, scope, copied);
        lemma.Append("  ").Append(keyword).Append(' ').Append(Printer.ExprToString(program.Options, qualified)).Append('\n');
        if (StrictUtf8.GetByteCount(lemma.ToString()) > maximumPreparedSourceBytes) {
          failure = "The generated implication lemma exceeds the bounded source policy.";
          return null;
        }
      }
    }
    lemma.Append("{}\n");
    var edits = new List<ByteEdit> { new(generator.Origin.Uri, generator.StartToken.pos, lemma.ToString()) };
    var runtime = sources.Where(source => source.Content == ContractRuntimeInstrumentation.DafnySource).ToList();
    var random = sources.Where(source => source.Content == randomModuleSource).ToList();
    if (runtime.Count > 1 || random.Count > 1) {
      failure = "The proof sources contain duplicate embedded runtime modules.";
      return null;
    }
    if (runtime.Count == 1) { edits.Add(new(ContractSourceSnapshot.UriFor(runtime[0].Path), 0, randomModuleSource, true)); }
    var append = runtime.Count == 0 && random.Count == 0;
    try {
      var prepared = ApplyByteEdits(sources, edits, append ? sources[0].Path + ".pbt-generator-rng-proof.dfy" : null,
        append ? randomModuleSource : null, maximumPreparedSourceBytes, deadlineTimestamp, cancellationToken);
      return new(prepared, name);
    } catch (NotSupportedException error) {
      failure = error.Message;
      return null;
    }
  }

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

  private static bool ContractsAreValueOnly(Program program, Method goal, Method generator, out string failure) {
    failure = "";
    foreach (var expression in goal.Req.Select(requirement => requirement.E).Concat(generator.Ens.Select(ensure => ensure.E))) {
      if (expression.DescendantsAndSelf.OfType<IdentifierExpr>().Any(identifier => generator.Ins.Contains(identifier.Var))) {
        failure = "Generator postconditions depending on the random-source input are outside the value-only bridge scope.";
        return false;
      }
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
    private readonly Method goal;
    private readonly Method generator;
    private readonly ContractGeneratorInputBinding originalBinding;
    private readonly Program proofProgram;
    private readonly IReadOnlyList<ContractSource> proofSources;
    private readonly ContractGeneratorInputBinding proofBinding;
    private readonly HashSet<string> requiredChecks;

    internal Program RuntimeProgram => originalProgram;
    internal Method RuntimeGoal => goal;
    internal Method RuntimeGenerator => generator;

    internal Certificate(Program originalProgram, Method goal, Method generator, ContractGeneratorInputBinding originalBinding,
      Program proofProgram, IReadOnlyList<ContractSource> proofSources, ContractGeneratorInputBinding proofBinding,
      IReadOnlySet<string> requiredChecks) {
      this.originalProgram = originalProgram;
      this.goal = goal;
      this.generator = generator;
      this.originalBinding = originalBinding;
      this.proofProgram = proofProgram;
      this.proofSources = proofSources;
      this.proofBinding = proofBinding;
      this.requiredChecks = requiredChecks.ToHashSet(StringComparer.Ordinal);
    }

    internal bool Matches(Program program, IReadOnlyList<ContractSource> sources, Method selectedGoal, Method selectedGenerator,
      DafnyOptions options, IReadOnlySet<string> checks) => requiredChecks.SetEquals(checks) && ReferenceEquals(originalProgram, program) && ReferenceEquals(goal, selectedGoal) &&
      ReferenceEquals(generator, selectedGenerator) && ReferenceEquals(program.Options, options) &&
      requiredChecks.Count != 0 && ProofOptionFailure(options) == null && originalBinding.Matches(program, sources) &&
      proofBinding.Matches(proofProgram, proofSources);
  }
}

// The analyzer's translated identities include all retained ambient theory and each method's own implementation.
// Keep the complete provider injectable only internally so development tests never hash installed assemblies.
internal sealed record ContractGeneratorDefinitionIdentity(string SourcePath, string FullName) {
  internal static ContractGeneratorDefinitionIdentity For(MethodOrFunction callable) =>
    new(Path.GetFullPath(callable.StartToken.ActualFilename), callable.FullDafnyName);
}

internal sealed record ContractGeneratorInputBinding(string Sources, string ProofInputs,
  IReadOnlyList<ContractGeneratorDefinitionIdentity> RequiredDefinitions) {
  internal static ContractGeneratorInputBinding? Capture(Program program, IReadOnlyList<ContractSource> sources,
    IReadOnlyList<ContractGeneratorDefinitionIdentity> requiredDefinitions,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze = null) =>
    Capture(program, sources, requiredDefinitions, out _, analyze);

  private static ContractGeneratorInputBinding? Capture(Program program, IReadOnlyList<ContractSource> sources,
    IReadOnlyList<ContractGeneratorDefinitionIdentity> requiredDefinitions, out string? failure,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze) {
    failure = null;
    ContractSourceSnapshot.ValidateTrustedSources(sources, null);
    var uris = sources.Select(source => ContractSourceSnapshot.UriFor(source.Path)).ToHashSet();
    var inputs = (analyze ?? Analyze)(program, uris);
    if (inputs == null) { failure = "Analyzer proof inputs are unavailable."; return null; }
    if (inputs.SchemaVersion != 1) { failure = "Analyzer proof-input schema is unsupported."; return null; }
    if (!Digest(inputs.ToolchainSha256) || !Digest(inputs.OptionsSha256)) {
      failure = "Analyzer toolchain/options identity is incomplete or malformed.";
      return null;
    }
    if (inputs.Definitions.Count == 0 || requiredDefinitions.Count == 0) {
      failure = "Analyzer definition coverage is empty or incomplete.";
      return null;
    }
    var paths = sources.Select(source => Path.GetFullPath(source.Path)).ToHashSet(StringComparer.Ordinal);
    var identities = new HashSet<ContractGeneratorDefinitionIdentity>();
    foreach (var definition in inputs.Definitions) {
      if (!paths.Contains(definition.SourcePath) || string.IsNullOrWhiteSpace(definition.FullName) ||
          !Digest(definition.Sha256) || !identities.Add(new(definition.SourcePath, definition.FullName))) {
        failure = "Analyzer definition identity is malformed, duplicated or outside the source snapshots: " + Identity(definition.SourcePath, definition.FullName);
        return null;
      }
    }
    if (requiredDefinitions.Distinct().Count() != requiredDefinitions.Count) {
      failure = "Required analyzer definition identities are duplicated.";
      return null;
    }
    if (requiredDefinitions.Any(identity => !identities.Contains(identity))) {
      var missing = requiredDefinitions.First(identity => !identities.Contains(identity));
      failure = "Analyzer required definition is missing: " + Identity(missing?.SourcePath, missing?.FullName);
      return null;
    }
    var regions = sources.Select(source => new SourceFingerprintRegion(ContractSourceSnapshot.UriFor(source.Path).AbsoluteUri,
      source.Path, null, [])).ToArray();
    var document = SourceFingerprint.Compute(program.Options, new(regions),
      sources.ToDictionary(source => source.Path, source => source.Content, StringComparer.Ordinal), out _);
    if (document == null) { failure = "Source fingerprint is unavailable."; return null; }
    return new(JsonSerializer.Serialize(document), JsonSerializer.Serialize(inputs), requiredDefinitions.ToArray());
  }

  internal bool Matches(Program program, IReadOnlyList<ContractSource> sources,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze = null) => Mismatch(program, sources, analyze) == null;

  internal string? Mismatch(Program program, IReadOnlyList<ContractSource> sources,
    Func<Program, IReadOnlySet<Uri>, DafnyProofInputs?>? analyze = null) {
    var candidate = Capture(program, sources, RequiredDefinitions, out var failure, analyze);
    if (candidate == null) { return failure ?? "Analyzer binding is unavailable."; }
    if (Sources != candidate.Sources) { return "Source fingerprint changed."; }
    if (ProofInputs == candidate.ProofInputs) { return null; }

    // These JSON values were serialized by Capture, never supplied by request metadata. Exact serialized
    // equality above remains authoritative; the comparisons below only explain an already rejected result.
    var before = JsonSerializer.Deserialize<DafnyProofInputs>(ProofInputs)!;
    var after = JsonSerializer.Deserialize<DafnyProofInputs>(candidate.ProofInputs)!;
    if (before.ToolchainSha256 != after.ToolchainSha256) { return "Analyzer toolchain identity changed."; }
    if (before.OptionsSha256 != after.OptionsSha256) { return "Analyzer verifier-options identity changed."; }
    var remaining = after.Definitions.ToDictionary(definition => (definition.SourcePath, definition.FullName));
    foreach (var definition in before.Definitions) {
      if (!remaining.Remove((definition.SourcePath, definition.FullName), out var current)) {
        return "Analyzer definition is missing: " + Identity(definition.SourcePath, definition.FullName);
      }
      if (definition.Sha256 != current.Sha256) {
        return "Analyzer definition input changed: " + Identity(definition.SourcePath, definition.FullName);
      }
    }
    if (remaining.Values.FirstOrDefault() is { } added) {
      return "Analyzer definition was added: " + Identity(added.SourcePath, added.FullName);
    }
    return "Analyzer serialized definition ordering or metadata changed.";
  }

  private static string Identity(string? path, string? name) => "'" + Bounded(path) + "::" + Bounded(name) + "'.";
  private static string Bounded(string? value) => value == null ? "<null>" : new string(value.Take(160).Select(character => char.IsControl(character) ? '?' : character).ToArray()) +
    (value.Length > 160 ? "..." : "");

  private static bool Digest(string value) => value is { Length: 64 } && value.All(character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

  private static DafnyProofInputs? Analyze(Program program, IReadOnlySet<Uri> uris) =>
    DefinitionAnalysis.AnalyzeDocument(program, uris, includeSemanticFacts: false, includeProofInputs: true).SourceFacts.ProofInputs;
}
