#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.Auditor;
using Declaration = Microsoft.Dafny.Declaration;
using Function = Microsoft.Dafny.Function;
using Program = Microsoft.Dafny.Program;
using Type = Microsoft.Dafny.Type;

[assembly: InternalsVisibleTo("DafnyTestGeneration.Test")]

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Distinguishes logical proof from evidence usable for execution and construction.</summary>
public enum ContractSpecificationRole { Execution, Logical }

internal enum ContractNativeProofRole { WellFormedness, Correctness, Override }
internal sealed record ContractSpecificationCheck(Declaration Declaration, ContractNativeProofRole Role) {
  internal string VerboseName => ContractSpecificationChecker.Name(Declaration) + " (" + (Role switch {
    ContractNativeProofRole.WellFormedness => "well-formedness",
    ContractNativeProofRole.Correctness => "correctness",
    _ => "override check"
  }) + ")";
}

/// <summary>A closed set of original declarations whose contracts need native validation.</summary>
public sealed class ContractSpecificationScope {
  internal HashSet<Declaration> Declarations { get; }
  internal ContractGeneratorProofAudit? ProofAudit { get; }
  internal string CurrentIdentity(string context) => context + "\n" + Role + "\n" + string.Join("\n", Symbols.Concat(RequiredNativeChecks));
  internal ContractSpecificationChecker Owner { get; }
  internal HashSet<ContractSpecificationCheck> Checks { get; }
  public ContractSpecificationRole Role { get; }
  public string CacheIdentity { get; }
  public IReadOnlyList<string> RequiredNativeChecks => Checks.Select(check => check.VerboseName).Distinct()
    .OrderBy(name => name, StringComparer.Ordinal).ToList();
  public string? Failure { get; }
  public IReadOnlyList<string> Symbols => Declarations.Select(declaration => declaration.GetType().Name + ":" +
    ContractSpecificationChecker.Name(declaration)).OrderBy(name => name, StringComparer.Ordinal).ToList();

  /// <summary>Tests membership by original declaration identity, without accepting a same-named detached declaration.</summary>
  public bool ContainsDeclaration(Declaration declaration) => Declarations.Contains(declaration);

  internal ContractSpecificationScope(ContractSpecificationChecker owner, string context, ContractSpecificationRole role,
    HashSet<Declaration> declarations, HashSet<ContractSpecificationCheck> checks, string? failure,
    ContractGeneratorProofAudit? proofAudit = null) {
    Owner = owner;
    ProofAudit = proofAudit;
    Role = role;
    Declarations = declarations;
    Checks = checks;
    Failure = failure;
    CacheIdentity = CurrentIdentity(context);
  }
}

/// <summary>Internal native proof evidence; this is not part of the public campaign JSON schema.</summary>
public sealed record ContractSpecificationResult(bool Verified, string Diagnostics,
  IReadOnlyList<string> Implementations, IReadOnlyList<string> AssertionFreeDeclarations,
  int VerifiedCount = 0, int ErrorCount = 0) {
  public string? SourceSetHash { get; init; }
  public string? TrustSetHash { get; init; }
  public ContractSequenceRefinementResult? SequenceRefinement { get; init; }
  public ContractSpecificationRole? Role { get; init; }
  internal IReadOnlyList<string> CoveredNativeChecks { get; init; } = [];
  internal IReadOnlyList<string> VerifiedImplementationChecks { get; init; } = [];
}

/// <summary>Source- and trust-bound independent global inhabitance evidence, separate from any captured state.</summary>
public sealed record ContractGlobalInhabitationCertificate(string SourceSetHash,
  IReadOnlyList<string> Symbols, string ProofContext) {
  public string? TrustSetHash { get; init; }
}

/// <summary>Validates original specification closures under exact source trust, with separately budgeted native checks.</summary>
public sealed class ContractSpecificationChecker {
  private readonly Program original;
  private readonly IReadOnlyList<ContractSource> sources;
  private readonly DafnyOptions options;
  private readonly HashSet<ContractSpecificationCheck> checkedChecks = [];
  private readonly HashSet<Declaration> acceptedDeclarations = [];
  private readonly HashSet<ModuleDefinition> originalModules;
  private readonly HashSet<Uri> trustedSourceUris;
  private Program? verificationProgram;
  private BatchErrorReporter? reporter;
  private readonly string sourceSetHash;
  private readonly string trustSetHash;
  private ContractGlobalInhabitationCertificate? independentGlobals;
  private readonly ContractPinnedSolverIdentity? proofSolver;
  internal string? FinalNativeOptionsFingerprint { get; private set; }

  // Every scope is certified against the original sources with abstract-global axioms removed.
  private string ScopeContext => sourceSetHash + "/trusted-sources:" + trustSetHash +
    "/original-native-with-abstract-global-axioms-removed";

  /// <summary>Creates a campaign-local checker bound to one immutable original source program.</summary>
  public ContractSpecificationChecker(Program original, IReadOnlyList<ContractSource> sources, DafnyOptions options,
    IReadOnlyList<ContractDependency>? trustedSources = null) : this(original, sources, options, null, trustedSources) {
  }

  internal ContractSpecificationChecker(Program original, IReadOnlyList<ContractSource> sources, DafnyOptions options,
    ContractPinnedSolverIdentity? proofSolver, IReadOnlyList<ContractDependency>? trustedSources = null) {
    ContractSourceSnapshot.ValidateTrustedSources(sources, trustedSources);
    this.original = original;
    originalModules = original.RawModules().ToHashSet();
    this.sources = sources;
    this.proofSolver = proofSolver;
    sourceSetHash = ContractRuntimeTypeEvidence.SourceSetHash(sources);
    trustSetHash = TrustSetHash(trustedSources);
    trustedSourceUris = (trustedSources ?? []).Select(source => ContractSourceSnapshot.UriFor(source.Path)).ToHashSet();
    this.options = new DafnyOptions(options, useNullWriters: true) {
      Compile = false,
      RunningBoogieFromCommandLine = true,
      ProcsToCheck = ["*"],
      ProcsToIgnore = [],
      VerifyAllModules = true
    };
    this.options.Printer = new DafnyConsolePrinter(this.options);
  }

  /// <summary>Discovers original bodies, proof callees, type constraints and witnesses, rejecting unproved trust.</summary>
  public ContractSpecificationScope Scope(IEnumerable<MethodOrFunction> roots, IEnumerable<Type>? types = null,
    IEnumerable<ConstantField>? constants = null) => CreateScope(ContractSpecificationRole.Execution, roots, types, constants);

  /// <summary>Collects logical definitions and invoked proof methods without claiming compiled by-method correctness.</summary>
  public ContractSpecificationScope LogicalScope(IEnumerable<MethodOrFunction> roots, IEnumerable<Type>? types = null,
    IEnumerable<ConstantField>? constants = null) => CreateScope(ContractSpecificationRole.Logical, roots, types, constants);

  internal ContractSpecificationScope AuditedProofScope(ContractSpecificationRole role,
    IEnumerable<MethodOrFunction> roots, IEnumerable<Type>? types, IEnumerable<ConstantField>? constants,
    ContractGeneratorProofAudit audit) {
    if (audit.Failure != null) {
      return UnsupportedScope(audit.Failure);
    }
    if (!audit.IsBoundTo(original, sources)) {
      return UnsupportedScope("The proof audit is not bound to this exact resolved program and source set.");
    }
    return CreateScope(role, roots, types, constants, audit);
  }

  internal ContractSpecificationScope UnsupportedScope(string reason) => new(this,
    ScopeContext, ContractSpecificationRole.Execution, [], [], reason);

  private ContractSpecificationScope CreateScope(ContractSpecificationRole role, IEnumerable<MethodOrFunction> roots,
    IEnumerable<Type>? types, IEnumerable<ConstantField>? constants, ContractGeneratorProofAudit? audit = null) {
    var declarations = new HashSet<Declaration>();
    if (role == ContractSpecificationRole.Execution) {
      ContractRuntimeObligationTransformer.ExecutionReachable(original, roots, types, declarations, constants);
    } else {
      ContractRuntimeObligationTransformer.LogicalReachable(original, roots, types, declarations, constants);
    }
    if (audit != null && !audit.IsBoundTo(original, sources)) {
      return new(this, ScopeContext, role, [], [], "The exact embedded RNG audit no longer matches the proof program.");
    }
    if (audit != null) {
      declarations.RemoveWhere(audit.IsPinnedRngDeclaration);
    }
    declarations.RemoveWhere(declaration => Module(declaration) == original.SystemModuleManager.SystemModule ||
      declaration is not (MethodOrFunction or ConstantField or SubsetTypeDecl or NewtypeDecl) || declaration is NonNullTypeDecl ||
      declaration is ConstantField { Rhs: null, IsStatic: false });
    // Re-enable source-level verification skips in the detached proof program;
    // only the exact host trust set may omit original declaration audits and obligations.
    var trust = TrustDependencies(declarations.OfType<MethodOrFunction>().Where(callable => !IsTrusted(callable))
        .Where(callable => role != ContractSpecificationRole.Logical || callable is not Function))
      .Where(dependency => dependency.Kind != "verify_false").ToList();
    var failure = trust.Count == 0 ? null : string.Join(", ", trust.Select(item => item.Symbol + ":" + item.Kind));
    foreach (var declaration in declarations) {
      if (!Owns(declaration)) { failure ??= "Declaration is not from the original resolved program: " + Name(declaration); }
      if (audit != null) {
        var retainedNodes = role == ContractSpecificationRole.Logical && declaration is MethodOrFunction callable
          ? ContractRuntimeObligationTransformer.LogicalNodes(callable)
          : declaration.Descendants();
        if (retainedNodes.OfType<ExpectStmt>().Any()) {
          failure ??= "unchecked expect statement in retained proof closure: " + Name(declaration);
        }
      }
      if (IsTrusted(declaration)) { continue; }
      if (role == ContractSpecificationRole.Logical && declaration is Function function) {
        if (function.Body == null) { failure ??= "bodyless logical function: " + Name(function); }
        if (Attributes.Contains(function.Attributes, "only")) { failure ??= "verify_only: " + Name(function); }
        foreach (var assumption in ContractRuntimeObligationTransformer.LogicalNodes(function).OfType<Node>()
                   .SelectMany(node => node.Assumptions(function))) {
          if (TrustKind(assumption.desc) is { } kind) { failure ??= Name(function) + ":" + kind; }
        }
      }
      var ancestors = new List<Declaration> { declaration };
      if (declaration is MemberDecl member) { ancestors.Add(member.EnclosingClass); }
      if (ancestors.Any(item => item.HasAxiomAttribute || item.HasExternAttribute) ||
          !declaration.ShouldVerify(original.Compilation) || Module(declaration).IsFacade) {
        failure ??= "unverified declaration or owner: " + Name(declaration);
      }
      for (var owner = Module(declaration); owner != null; owner = owner.EnclosingModule) {
        if (Attributes.Contains(owner.Attributes, "axiom") || Attributes.Contains(owner.Attributes, "extern")) {
          failure ??= "unverified module: " + owner.FullDafnyName;
        }
      }
      if (declaration is not MethodOrFunction) {
        foreach (var assumption in declaration.Descendants().Prepend((INode)declaration).OfType<Node>().SelectMany(node => node.Assumptions(declaration))) {
          if (TrustKind(assumption.desc) is { } kind) {
            failure ??= Name(declaration) + ":" + kind;
          }
        }
      }
      if (declaration is ConstantField { Rhs: null }) { failure ??= "bodyless constant: " + Name(declaration); }
    }
    return new(this, ScopeContext, role, declarations,
      declarations.Where(declaration => !IsTrusted(declaration)).SelectMany(NativeChecks).ToHashSet(), failure, audit);
  }

  private bool IsTrusted(Declaration declaration) => trustedSourceUris.Contains(declaration.Origin.Uri);

  private static string TrustSetHash(IReadOnlyList<ContractDependency>? trustedSources) => ContractHarnessBuilder.Hash(
    JsonSerializer.Serialize((trustedSources ?? []).OrderBy(source => source.Path, StringComparer.Ordinal)
      .ThenBy(source => source.Sha256, StringComparer.Ordinal).Select(source => new { source.Path, source.Sha256 })));

  private sealed record TrustDependency(string Symbol, string Kind, string Reason);

  private static IReadOnlyList<TrustDependency> TrustDependencies(IEnumerable<MethodOrFunction> callables) {
    var result = new List<TrustDependency>();
    foreach (var callable in callables) {
      var symbol = callable.FullDafnyName;
      var isExtern = Attributes.Contains(callable.Attributes, "extern");
      if (isExtern) {
        result.Add(new TrustDependency(symbol, "extern_contract",
          "The external implementation was not checked; callers use its original contract and frame."));
      }
      if (callable.HasAxiomAttribute) {
        result.Add(new TrustDependency(symbol, "axiom", "The declaration carries {:axiom}."));
      }
      if (callable.HasVerifyFalseAttribute) {
        result.Add(new TrustDependency(symbol, "verify_false", "The declaration carries {:verify false}."));
      }
      var hasBody = callable switch {
        Method method => method.Body != null,
        Function function => function.ByMethodBody != null || function.Body != null,
        _ => false
      };
      if (!isExtern && !hasBody) {
        result.Add(new TrustDependency(symbol, "bodyless_contract",
          "The declaration has no implementation and is used through its contract."));
      }
      foreach (var assumption in callable.Assumptions(callable)) {
        var kind = TrustKind(assumption.desc);
        if (kind != null) {
          result.Add(new TrustDependency(symbol, kind, assumption.desc.Issue));
        }
      }
    }
    return result.Distinct().OrderBy(item => item.Symbol, StringComparer.Ordinal)
      .ThenBy(item => item.Kind, StringComparer.Ordinal).ToList();
  }

  private static string? TrustKind(AssumptionDescription description) {
    if (description == AssumptionDescription.MayNotTerminate) {
      return "nontermination";
    }
    if (description == AssumptionDescription.ForallWithoutBody) {
      return "forall_without_body";
    }
    if (description == AssumptionDescription.LoopWithoutBody) {
      return "loop_without_body";
    }
    if (description == AssumptionDescription.AssertOnly) {
      return "assert_only";
    }
    if (description == AssumptionDescription.MemberOnly) {
      return "verify_only";
    }
    if (description.Issue.Contains("[assume", StringComparison.Ordinal)) {
      return "assume";
    }
    if (description.Issue.Contains("assume_concurrent", StringComparison.Ordinal)) {
      return "assume_concurrent";
    }
    return null;
  }

  /// <summary>Collects the original function and type dependencies of a resolved contract expression.</summary>
  public ContractSpecificationScope Scope(Expression expression) => Scope(
    ContractRuntimeObligationTransformer.FunctionReferences(expression),
    expression.DescendantsAndSelf.OfType<Expression>().Where(node => node.Type != null).Select(node => node.Type));

  /// <summary>Collects logical dependencies, including proof statements and constants directly in a contract.</summary>
  public ContractSpecificationScope LogicalScope(Expression expression) {
    var nodes = ContractRuntimeObligationTransformer.LogicalNodes(expression).Prepend(expression).ToList();
    var roots = nodes.OfType<Expression>().Select(node => ContractRuntimeObligationTransformer.FunctionReference(node.Resolved))
      .OfType<MethodOrFunction>().Concat(nodes.OfType<CallStmt>().Select(call => call.Method)).Distinct().ToList();
    var scope = LogicalScope(roots, nodes.OfType<Expression>().Where(node => node.Type != null).Select(node => node.Type),
      nodes.OfType<MemberSelectExpr>().Select(select => select.Member).OfType<ConstantField>());
    // This declaration supplies diagnostic ownership only; direct proof-statement assumptions
    // must be audited even when the expression contains no callable or constant references.
    var diagnosticOwner = (Declaration?)roots.FirstOrDefault() ?? original.DefaultModuleDef.TopLevelDecls.First();
    var failure = nodes.OfType<Node>().SelectMany(node => node.Assumptions(diagnosticOwner))
      .Select(assumption => TrustKind(assumption.desc)).FirstOrDefault(kind => kind != null);
    return failure == null ? scope : new(this, ScopeContext,
      ContractSpecificationRole.Logical, scope.Declarations, scope.Checks, scope.Failure ?? "contract expression:" + failure);
  }

  /// <summary>Returns owner modules that still contain unchecked declarations in this exact scope.</summary>
  public IReadOnlyList<string> PendingModules(ContractSpecificationScope scope) => !BoundScope(scope) ? [] : scope.Checks
    .Where(check => !checkedChecks.Contains(check)).Select(check => Module(check.Declaration).FullDafnyName)
    .Distinct().OrderBy(name => name, StringComparer.Ordinal).ToList();

  /// <summary>Accepts a closure after every untrusted declaration was checked and every trusted source was bound.</summary>
  public bool Accept(ContractSpecificationScope scope) {
    if (!BoundScope(scope) || scope.Failure != null || !scope.Checks.IsSubsetOf(checkedChecks)) { return false; }
    if (scope.Role == ContractSpecificationRole.Execution) { acceptedDeclarations.UnionWith(scope.Declarations); }
    return true;
  }

  /// <summary>Checks accepted or trusted status by original declaration identity, not spelling alone.</summary>
  public bool IsValidated(Declaration declaration) => acceptedDeclarations.Contains(declaration);

  internal bool IsBoundTo(Program program, IReadOnlyList<ContractSource> snapshots) => ReferenceEquals(original, program) &&
    sourceSetHash == ContractRuntimeTypeEvidence.SourceSetHash(snapshots);

  internal bool IsBoundTo(Program program, IReadOnlyList<ContractSource> snapshots,
    IReadOnlyList<ContractDependency>? trustedSources) => IsBoundTo(program, snapshots) &&
    trustSetHash == TrustSetHash(trustedSources);

  internal ContractGlobalInhabitationCertificate? IndependentGlobals(Program program,
    IReadOnlyList<ContractSource> snapshots) {
    if (!IsBoundTo(program, snapshots)) { return null; }
    if (independentGlobals != null) { return independentGlobals; }
    var scope = ContractInitialTypeProof.RequiredGlobalScope(program, this);
    if (!Accept(scope) || !ContractRuntimeHeapChecking.IndependentCertifiedGlobalsInhabited(program, this)) { return null; }
    return independentGlobals = new(sourceSetHash, scope.Symbols,
      "original-native-wd-with-abstract-global-axioms-removed; independent-finite-inhabitants") {
      TrustSetHash = trustSetHash
    };
  }

  /// <summary>Verifies every emitted native obligation for the selected declarations in one owner module.</summary>
  public async Task<ContractSpecificationResult> CheckModuleAsync(ContractSpecificationScope scope, string moduleName,
    CancellationToken cancellationToken, Action<string, string>? phaseObserver = null, long? deadlineTimestamp = null) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    if (proofSolver != null && !ContractGeneratorProof.HasExactTrustedVerifierFactory(options)) {
      return new(false, "The proof checker does not carry the exact captured trusted Boogie verifier factory.", [], []);
    }
    if (!BoundScope(scope)) { return new(false, "Specification scope is not bound to this original checker/source context.", [], []); }
    if (scope.Failure != null) { return new(false, scope.Failure, [], []); }
    var selected = scope.Checks.Where(check => Module(check.Declaration).FullDafnyName == moduleName &&
      !checkedChecks.Contains(check)).ToList();
    if (selected.Count == 0) { return new(true, "No remaining declarations in this module.", [], []); }
    if (verificationProgram == null) {
      reporter = new BatchErrorReporter(options);
      var parsed = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken, phaseObserver: phaseObserver);
      if (reporter.ErrorCount != 0) {
        return new(false, string.Join("\n", reporter.AllMessages.Select(message => message.Message)), [], []);
      }
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      // Only this private parse is changed. A skipped body must pass the same native
      // well-formedness/correctness checks as a normally verified source declaration.
      foreach (var owner in parsed.RawModules()) {
        owner.Attributes = EnableVerification(owner.Attributes);
        foreach (var declaration in owner.Descendants().OfType<Declaration>()) {
          declaration.Attributes = EnableVerification(declaration.Attributes);
        }
      }
      verificationProgram = parsed;
      if (proofSolver == null) {
        options.ProcessSolverOptions(reporter, Microsoft.Dafny.Token.NoToken);
      } else {
        var proverPaths = options.ProverOptions.Where(option => option.StartsWith("PROVER_PATH=", StringComparison.Ordinal))
          .Select(option => option["PROVER_PATH=".Length..]).Distinct(StringComparer.Ordinal).ToList();
        if (!StringComparer.Ordinal.Equals(proofSolver.Path, "/usr/bin/z3") || proverPaths.Count != 1 ||
            !StringComparer.Ordinal.Equals(proverPaths[0], proofSolver.Path) ||
            !Version.TryParse(proofSolver.Version, out var pinnedVersion) ||
            options.SolverIdentifier is not (null or "Z3") || options.SolverVersion is not null && options.SolverVersion != pinnedVersion) {
          verificationProgram = null;
          return new(false, "The proof checker options do not match the exact pinned system Z3 identity.", [], []);
        }
        options.SetZ3Options(pinnedVersion);
        if (!ContractGeneratorProof.HasExactTrustedVerifierFactory(options)) {
          verificationProgram = null;
          return new(false, "The proof checker verifier factory changed before native verification.", [], []);
        }
        if (!ContractGeneratorProof.TryOptionsFingerprint(options, out var nativeOptionsFingerprint)) {
          verificationProgram = null;
          return new(false, "The proof checker native options have no complete supported fingerprint.", [], []);
        }
        FinalNativeOptionsFingerprint = nativeOptionsFingerprint;
      }
      if (reporter.ErrorCount != 0) {
        verificationProgram = null;
        return new(false, string.Join("\n", reporter.AllMessages.Select(message => message.Message)), [], []);
      }
    }
    var module = BoogieGenerator.VerifiableModules(verificationProgram).SingleOrDefault(candidate => candidate.FullDafnyName == moduleName);
    if (module == null) { return new(false, "Native verification owner unavailable: " + moduleName, [], []); }
    var verboseNames = selected.Select(check => check.VerboseName).ToHashSet(StringComparer.Ordinal);
    var translated = ContractPhaseRecorder.Measure(phaseObserver, "translation:" + moduleName, cancellationToken, () => {
      Type.ResetScopes();
      return new BoogieGenerator(reporter!, verificationProgram.ProofDependencyManager).DoTranslation(verificationProgram, module);
    });
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var globalContext = ContractGlobalAssumptions.RemoveAbstractConstantAxioms(verificationProgram, translated);
    var selectedImplementations = translated.Implementations.Where(implementation => verboseNames.Contains(implementation.VerboseName)).ToList();
    var procedures = translated.TopLevelDeclarations.OfType<Procedure>().Select(procedure => procedure.VerboseName).ToHashSet();
    // Native function/type/constant checks always emit a procedure, even when there are no assertions.
    // By-method declarations instead emit their correctness procedure and are also covered here.
    var missing = selected.Where(check => !procedures.Contains(check.VerboseName)).ToList();
    if (missing.Count != 0) {
      return new(false, "Missing native declaration coverage: " + string.Join(", ", missing.Select(check => check.VerboseName)),
        selectedImplementations.Select(implementation => implementation.Name).ToList(), []);
    }
    var assertionFree = selected.Where(check => !selectedImplementations.Any(implementation =>
      implementation.VerboseName == check.VerboseName)).Select(check => Name(check.Declaration)).Distinct().ToList();
    // Restrict verification bodies only: retain all original procedures, definitions, axioms and imported declarations.
    // This avoids Boogie's user-facing wildcard routine filter and its source-name matching ambiguities.
    translated.RemoveTopLevelDeclarations(declaration => declaration is Implementation implementation && !selectedImplementations.Contains(implementation));
    var implementationNames = selectedImplementations.Select(implementation => implementation.Name).ToList();
    var sequenceProof = ContractPhaseRecorder.Measure(phaseObserver, "sequence_refinement:" + moduleName, cancellationToken,
      () => ContractSequenceRefinementProof.Apply(translated, selectedImplementations, cancellationToken, deadlineTimestamp));
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    if (!sequenceProof.Preserved) {
      return Evidence(new(false, sequenceProof.Failure ?? "Original native assertion preservation failed.", implementationNames, []));
    }
    if (selectedImplementations.Count == 0) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      checkedChecks.UnionWith(selected);
      return Evidence(new ContractSpecificationResult(true, globalContext + "\nNative declarations contain no assertions.", [], assertionFree) with {
        CoveredNativeChecks = selected.Select(check => check.VerboseName).ToList()
      });
    }
    if (proofSolver != null && !ContractGeneratorProof.IsPinnedSolverFileCurrent(proofSolver,
          deadlineTimestamp, cancellationToken)) {
      return Evidence(new(false, "The pinned Z3 executable changed before native verification.", implementationNames, []));
    }
    if (proofSolver != null && !ContractGeneratorProof.HasExactTrustedVerifierFactory(options)) {
      return Evidence(new(false, "The proof checker verifier factory changed before native verification.", implementationNames, []));
    }
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var log = new StringWriter();
    var (outcome, stats) = await ContractPhaseRecorder.MeasureAsync(phaseObserver, "boogie:" + moduleName,
      cancellationToken, () => DafnyMain.BoogieOnce(reporter!, options, log, engine,
        "contract-specification", module.SanitizedName, translated, null, cancellationToken));
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var solverStillPinned = proofSolver == null || ContractGeneratorProof.IsPinnedSolverFileCurrent(proofSolver,
      deadlineTimestamp, cancellationToken);
    var success = outcome is PipelineOutcome.Done or PipelineOutcome.VerificationCompleted &&
      solverStillPinned && BoundScope(scope) &&
      stats.ErrorCount + stats.TimeoutCount + stats.InconclusiveCount + stats.OutOfResourceCount + stats.OutOfMemoryCount + stats.SolverExceptionCount == 0 &&
      stats.VerifiedCount == selectedImplementations.Count;
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    if (success) { checkedChecks.UnionWith(selected); }
    return Evidence(new ContractSpecificationResult(success, globalContext + "\n" + log, implementationNames, assertionFree,
      stats.VerifiedCount, stats.ErrorCount) with {
      CoveredNativeChecks = success ? selected.Select(check => check.VerboseName).ToList() : [],
      VerifiedImplementationChecks = success ? selected.Where(check => selectedImplementations.Any(implementation =>
        implementation.VerboseName == check.VerboseName)).Select(check => check.VerboseName).ToList() : []
    });

    ContractSpecificationResult Evidence(ContractSpecificationResult result) => result with {
      SourceSetHash = sourceSetHash,
      TrustSetHash = trustSetHash,
      SequenceRefinement = sequenceProof,
      Role = scope.Role
    };
  }

  internal string? ResolvedSolverVersion(string expectedPath) {
    if (proofSolver == null || !StringComparer.Ordinal.Equals(proofSolver.Path, expectedPath) ||
        !ContractGeneratorProof.HasExactTrustedVerifierFactory(options) ||
        !StringComparer.Ordinal.Equals(expectedPath, "/usr/bin/z3") ||
        !StringComparer.Ordinal.Equals(options.SolverIdentifier, "Z3") ||
        !Version.TryParse(proofSolver.Version, out var pinnedVersion) || options.SolverVersion != pinnedVersion ||
        FinalNativeOptionsFingerprint == null ||
        !ContractGeneratorProof.TryOptionsFingerprint(options, out var currentFingerprint) ||
        !StringComparer.Ordinal.Equals(FinalNativeOptionsFingerprint, currentFingerprint)) {
      return null;
    }
    var proverPaths = options.ProverOptions.Where(option => option.StartsWith("PROVER_PATH=", StringComparison.Ordinal))
      .Select(option => option["PROVER_PATH=".Length..]).Distinct(StringComparer.Ordinal).ToList();
    return proverPaths.Count == 1 && StringComparer.Ordinal.Equals(proverPaths[0], expectedPath)
      ? options.SolverVersion.ToString() : null;
  }

  private bool BoundScope(ContractSpecificationScope scope) => ReferenceEquals(scope.Owner, this) &&
    sourceSetHash == ContractRuntimeTypeEvidence.SourceSetHash(sources) &&
    scope.CacheIdentity == scope.CurrentIdentity(ScopeContext) &&
    (scope.ProofAudit == null || scope.ProofAudit.IsBoundTo(original, sources));

  private bool Owns(Declaration declaration) => originalModules.Contains(Module(declaration)) && (declaration switch {
    Method { FunctionFromWhichThisIsByMethodDecl: { } function } method =>
      ReferenceEquals(function.ByMethodDecl, method) && function.EnclosingClass is TopLevelDeclWithMembers owner && owner.Members.Contains(function),
    MemberDecl member => member.EnclosingClass is TopLevelDeclWithMembers owner && owner.Members.Contains(member),
    TopLevelDecl type => type.EnclosingModuleDefinition.TopLevelDecls.Contains(type),
    _ => false
  });

  private static IEnumerable<ContractSpecificationCheck> NativeChecks(Declaration declaration) {
    if (declaration is not Method { FunctionFromWhichThisIsByMethodDecl: not null }) {
      yield return new(declaration, ContractNativeProofRole.WellFormedness);
    }
    if (declaration is Method) { yield return new(declaration, ContractNativeProofRole.Correctness); }
    if (declaration is Function { OverriddenFunction: not null } or Method { OverriddenMethod: not null }) {
      yield return new(declaration, ContractNativeProofRole.Override);
    }
  }

  private static Attributes? EnableVerification(Attributes? attributes) {
    if (attributes == null) { return null; }
    var previous = EnableVerification(attributes.Prev);
    if (attributes.Name == "verify" && attributes.Args.Count == 1 && Microsoft.Dafny.LiteralExpr.IsFalse(attributes.Args[0])) {
      return previous;
    }
    attributes.Prev = previous;
    return attributes;
  }

  private static ModuleDefinition Module(Declaration declaration) => declaration switch {
    MemberDecl member => member.EnclosingClass.EnclosingModuleDefinition,
    TopLevelDecl topLevel => topLevel.EnclosingModuleDefinition,
    _ => throw new ArgumentException("Unexpected specification declaration.", nameof(declaration))
  };

  internal static string Name(Declaration declaration) => declaration switch {
    MemberDecl member => member.FullDafnyName,
    TopLevelDecl topLevel => topLevel.FullDafnyName,
    _ => throw new ArgumentException("Unexpected specification declaration.", nameof(declaration))
  };
}
