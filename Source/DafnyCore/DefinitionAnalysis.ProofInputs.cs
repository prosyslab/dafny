#nullable enable
using System;
using System.Collections.Generic;
using System.Collections;
using System.CommandLine;
using System.CommandLine.Binding;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>Identifies the complete conservative translated input for a source definition.</summary>
public sealed record DafnyDefinitionProofInput(string SourcePath, string FullName, string Sha256);

/// <summary>Binds translated definition inputs to their producer and verification options.</summary>
public sealed record DafnyProofInputs(
  int SchemaVersion,
  string ToolchainSha256,
  string OptionsSha256,
  IReadOnlyList<DafnyDefinitionProofInput> Definitions);

public static partial class DefinitionAnalysis {
  private static readonly Lazy<string?> ProofToolchainIdentity = new(ProofToolchainHash);
  /// <summary>Identifies the bounded native producer assemblies without granting proof-input evidence.</summary>
  public static string? ContextToolchainIdentity() => ProofToolchainIdentity.Value;

  /// <summary>Identifies effective resolver and verifier settings, including native solver options.</summary>
  public static string ContextOptionsIdentity(DafnyOptions options) => ProofOptionsHash(options);

  public static string ResolutionOptionsIdentity(DafnyOptions options) => ProofHash(JsonSerializer.Serialize(new {
    Arguments = DafnyCommands.ResolverOptions.Concat(new Option[] {
      CommonOptionBag.UnrollBoundedQuantifiers, CommonOptionBag.RelaxDefiniteAssignment,
      CommonOptionBag.VerifyIncludedFiles, CommonOptionBag.ManualLemmaInduction,
      CommonOptionBag.DefaultFunctionOpacity, CommonOptionBag.ManualTriggerOption,
      BoogieOptionBag.VerificationTimeLimit, BoogieOptionBag.SolverResourceLimit
    }).Distinct().Where(option => option != CommonOptionBag.LogLocation &&
      option != CommonOptionBag.LogLevelOption && option != BoogieOptionBag.Cores &&
      option != CommonOptionBag.Libraries)
      .OrderBy(option => option.Name, StringComparer.Ordinal)
      .Select(option => new { option.Name, Value = EffectiveOption(options, option) }).ToList(),
    options.TimeLimit,
    options.ResourceLimit,
    options.AutoTriggers
  }));

  private static object? EffectiveOption(DafnyOptions options, Option option) {
    if (!options.Options.OptionArguments.TryGetValue(option, out var value)) {
      var descriptor = (IValueDescriptor)option;
      value = descriptor.HasDefaultValue ? descriptor.GetDefaultValue() :
        option.ValueType == typeof(bool) ? false : option.ValueType == typeof(uint) ? 0U :
        option.ValueType == typeof(int) ? 0 : null;
    }
    if (value is IEnumerable sequence and not string) {
      return sequence.Cast<object>().ToArray();
    }
    if (value == null && (option.ValueType == typeof(IEnumerable<string>) || option.ValueType == typeof(IList<string>))) {
      return Array.Empty<string>();
    }
    return value is FileSystemInfo file ? file.FullName : value;
  }

  /// <summary>Rejects transformations whose dependency semantics are outside native diagnostic binding.</summary>
  public static bool SupportsDiagnosticContext(DafnyOptions options, bool allowSourceLibraries = false) =>
    !(options.Get(CommonOptionBag.PluginOption)?.Count is > 0 ||
      options.AdditionalPlugins.Count > 0 || options.AdditionalPluginArguments.Count > 0 ||
      !options.Plugins.SequenceEqual(DafnyOptions.DefaultPlugins) ||
      !SupportedProofBoogieArguments(options) ||
      options.InlineDepth != DafnyOptions.Default.InlineDepth ||
      options.StratifiedInlining != DafnyOptions.Default.StratifiedInlining ||
      options.ProcedureInlining != DafnyOptions.Default.ProcedureInlining || options.InferModifies ||
      options.LoopUnrollCount != DafnyOptions.Default.LoopUnrollCount ||
      options.SoundLoopUnrolling != DafnyOptions.Default.SoundLoopUnrolling ||
      !allowSourceLibraries && options.Get(CommonOptionBag.Libraries)?.Any() == true || options.Get(CommonOptionBag.Prelude) != null);

  private static bool SupportedProofBoogieArguments(DafnyOptions options) {
    var arguments = options.Get(BoogieOptionBag.BoogieArguments)?.ToList() ?? new List<string>();
    return arguments.Count == 0 || arguments.Count == 1 &&
      arguments[0].StartsWith("/randomSeed:", StringComparison.Ordinal) &&
      int.TryParse(arguments[0]["/randomSeed:".Length..], out var seed) && seed == options.RandomSeed;
  }
  private sealed record TranslatedProofDeclaration(
    string Module,
    string Sha256,
    DefinitionNode? Owner,
    bool ExcludableImplementation);

  private static DafnyProofInputs? ProofInputsFor(Program program, IReadOnlySet<Uri> analysisSourceUris) =>
    ProofInputsFor(program, analysisSourceUris,
      input => BoogieGenerator.Translate(input, input.Reporter), () => ProofToolchainIdentity.Value);

  /// <summary>Hash fresh native translations before Boogie prepares mutable verification tasks.</summary>
  public static DafnyProofInputs? ProofInputsFromTranslations(Program program,
    IReadOnlySet<Uri> analysisSourceUris, IReadOnlyList<Tuple<string, Bpl.Program>> translations) =>
    ProofInputsFor(program, analysisSourceUris, _ => translations, () => ProofToolchainIdentity.Value);

  /// <summary>Bind native result-cache checksums to the complete existing translated input identity.</summary>
  /// <remarks>
  /// The key is position-free: the base checksum is an MD5 of the printed declaration, the fingerprint hashes
  /// the printed translation, and <see cref="AssertionShape"/> guards the ordered assertion sequence. Cached
  /// results are rebased onto the current split assertions when they are replayed, so reports use current tokens.
  /// </remarks>
  public static void BindNativeVerificationChecksums(IReadOnlyList<Tuple<string, Bpl.Program>> translations,
    DafnyProofInputs? proofInputs) {
    var fingerprints = proofInputs?.Definitions.GroupBy(definition => (definition.SourcePath, definition.FullName))
      .Where(group => group.Count() == 1).ToDictionary(group => group.Key, group => group.Single().Sha256);
    foreach (var (_, translation) in translations) {
      var procedures = translation.Procedures.GroupBy(procedure => procedure.Name, StringComparer.Ordinal)
        .Where(group => group.Count() == 1).ToDictionary(group => group.Key, group => group.Single(), StringComparer.Ordinal);
      foreach (var implementation in translation.Implementations) {
        string? fingerprint = null;
        if (implementation.tok is CanVerifyOrigin { CanVerify: INode node } origin) {
          fingerprints?.TryGetValue((SourcePath(node), origin.CanVerify.FullDafnyName), out fingerprint);
        }
        // Boogie's dependency collector covers functions and procedures, but arbitrary
        // translated axioms can also affect a VC. Unsupported certificate owners retain
        // same-state task reuse, with a fresh checksum preventing cross-state cache replay.
        var checksum = ProofHash(implementation.Checksum + "\0" + (fingerprint != null
          ? fingerprint + "\0" + AssertionShape(implementation, procedures) : Guid.NewGuid().ToString("N")));
        implementation.Attributes = new Bpl.QKeyValue(implementation.tok, "checksum", new List<object> { checksum },
          implementation.Attributes);
      }
    }
  }

  /// <summary>
  /// Hash the ordered proof obligations of a fresh translation without any token or position. Native cached
  /// results retain assertion objects; the same shape lets a reused result be mapped onto the current assertions
  /// by ordinal. Boogie later desugars non-free call preconditions and procedure postconditions into assertions,
  /// so those are listed from the contracts they come from, in the order of the commands that use them.
  /// A fresh translation has unresolved callee and procedure references, so contracts are found by name.
  /// </summary>
  internal static string AssertionShape(Bpl.Implementation implementation, IReadOnlyDictionary<string, Bpl.Procedure> procedures) {
    var shape = new List<object>();
    void Add(string kind, Bpl.ProofObligationDescription? description) =>
      shape.Add(new { Kind = kind, Ordinal = shape.Count, Success = description?.SuccessDescription, Failure = description?.FailureDescription });
    void Visit(IEnumerable<Bpl.Cmd> commands) {
      foreach (var command in commands) {
        switch (command) {
          case Bpl.AssertCmd assert:
            Add(assert.GetType().Name, assert.Description);
            break;
          case Bpl.CallCmd call:
            // An unknown callee still contributes its name, so the key cannot ignore the call.
            Add("Call:" + call.callee, null);
            if (procedures.TryGetValue(call.callee, out var callee)) {
              foreach (var requires in callee.Requires.Where(requires => !requires.Free)) {
                Add("CallRequires", requires.Description);
              }
            }
            break;
          case Bpl.StateCmd state:
            Visit(state.Cmds);
            break;
        }
      }
    }
    foreach (var block in implementation.Blocks) {
      Visit(block.Cmds);
    }
    if (procedures.TryGetValue(implementation.Name, out var own)) {
      foreach (var ensures in own.Ensures.Where(ensures => !ensures.Free)) {
        Add("ProcedureEnsures", ensures.Description);
      }
    }
    return ProofHash(JsonSerializer.Serialize(shape));
  }

  // Let memory tests supply the translation environment and toolchain identity; keep fingerprinting here.
  internal static DafnyProofInputs? ProofInputsFor(Program program, IReadOnlySet<Uri> analysisSourceUris,
    Func<Program, IEnumerable<Tuple<string, Bpl.Program>>> translate, Func<string?> toolchainIdentity) {
    var options = program.Options;
    // Plugins and arbitrary Boogie arguments may install transformations that consume
    // implementation bodies. Their dependency semantics are outside this schema.
    if (options.Get(CommonOptionBag.PluginOption)?.Count is > 0 ||
        options.AdditionalPlugins.Count > 0 || options.AdditionalPluginArguments.Count > 0 ||
        !options.Plugins.SequenceEqual(DafnyOptions.DefaultPlugins) ||
        !SupportedProofBoogieArguments(options) ||
        options.InlineDepth != DafnyOptions.Default.InlineDepth ||
        options.StratifiedInlining != DafnyOptions.Default.StratifiedInlining ||
        options.ProcedureInlining != DafnyOptions.Default.ProcedureInlining ||
        options.InferModifies ||
        options.LoopUnrollCount != DafnyOptions.Default.LoopUnrollCount ||
        options.SoundLoopUnrolling != DafnyOptions.Default.SoundLoopUnrolling) {
      return null;
    }

    var sourceDefinitions = SourceDefinitions(program, spansOnly: false, analysisSourceUris, identitiesOnly: true);
    var declarationIndex = SourceDeclarationIndex(program, sourceDefinitions);
    var printOptions = new DafnyOptions(options) {
      PrintInstrumented = true,
      PrintInlined = true,
      PrintWithUniqueASTIds = false,
      PrintDesugarings = false,
      PrintUnstructured = 0,
      PrintFile = "-"
    };
    var translated = new List<TranslatedProofDeclaration>();
    var errorCount = program.Reporter.ErrorCount;
    foreach (var (moduleName, boogieProgram) in translate(program)) {
      // Serialize the fresh translation without resolving it or invoking a solver.
      var procedures = boogieProgram.TopLevelDeclarations.OfType<Bpl.Procedure>()
        .GroupBy(procedure => procedure.Name, StringComparer.Ordinal)
        .ToDictionary(group => group.Key, group => group.ToList(), StringComparer.Ordinal);
      var declarations = new List<(Bpl.Declaration Declaration, DefinitionNode? Owner, bool Excludable)>();
      foreach (var declaration in boogieProgram.TopLevelDeclarations) {
        DefinitionNode? owner = null;
        var excludable = false;
        if (declaration is Bpl.Implementation or Bpl.Procedure &&
            declaration.tok is CanVerifyOrigin origin &&
            origin.CanVerify is INode sourceNode &&
            declarationIndex.TryGetValue(sourceNode, out owner)) {
          if (declaration is Bpl.Implementation implementation) {
            // A modular ordinary method/lemma call consumes its procedure contract. An
            // inline implementation can instead become part of another VC, so keep it.
            var modularMethod = origin.CanVerify is Method { IsByMethod: false } method &&
              (method.GetType() == typeof(Method) || method.GetType() == typeof(Lemma));
            excludable = modularMethod &&
              !HasInlineAttribute(implementation.Attributes) &&
              procedures.TryGetValue(implementation.Name, out var matches) && matches.Count == 1 &&
              !HasInlineAttribute(matches[0].Attributes);
          }
        }
        declarations.Add((declaration, owner, excludable));
      }
      foreach (var declaration in declarations) {
        translated.Add(new TranslatedProofDeclaration(moduleName,
          ProofDeclarationHash(printOptions, declaration.Declaration), declaration.Owner, declaration.Excludable));
      }
    }
    if (program.Reporter.ErrorCount != errorCount || translated.Count == 0) {
      return null;
    }

    var toolchain = toolchainIdentity();
    if (toolchain == null) {
      return null;
    }
    var optionsHash = ProofOptionsHash(options);
    var results = new List<DafnyDefinitionProofInput>();
    foreach (var definition in sourceDefinitions) {
      // By-method and generated/extreme declarations require more than one logical
      // source identity. Do not issue a partial certificate for them.
      if (definition.Declaration is not MethodOrConstructor and not Function ||
          definition.Declaration is Function { ByMethodBody: not null } or ExtremeLemma ||
          definition.Declaration is MethodOrFunction { HasVerifyFalseAttribute: true } ||
          definition.Declaration is MethodOrConstructor { Body: null } or Function { Body: null } ||
          definition.BodyKind == DefinitionBodyKind.FunctionByMethod ||
          !translated.Any(item => ReferenceEquals(item.Owner, definition))) {
        continue;
      }
      var sourcePath = SourcePath(definition.Declaration);
      if (sourcePath.Length == 0 || sourceDefinitions.Count(other => SourcePath(other.Declaration) == sourcePath &&
            other.ReportFullName == definition.ReportFullName) != 1) {
        continue;
      }
      var inputs = translated.Where(item => !item.ExcludableImplementation || ReferenceEquals(item.Owner, definition))
        .Select(item => new { item.Module, item.Sha256 }).ToList();
      results.Add(new DafnyDefinitionProofInput(sourcePath, definition.ReportFullName,
        ProofHash(JsonSerializer.Serialize(new { toolchain, optionsHash, inputs }))));
    }
    return new DafnyProofInputs(1, toolchain, optionsHash, results);
  }

  private static bool HasInlineAttribute(Bpl.QKeyValue? attributes) {
    for (var attribute = attributes; attribute != null; attribute = attribute.Next) {
      if (attribute.Key == "inline") {
        return true;
      }
    }
    return false;
  }

  private static string ProofDeclarationHash(DafnyOptions options, Bpl.Declaration declaration) {
    using var text = new StringWriter();
    // The short constructor changes source tokens. Keep task ownership and diagnostics
    // intact when this translation will subsequently be prepared for verification.
    using (var writer = new Bpl.TokenTextWriter("proof-input", text, false, false, options)) {
      declaration.Emit(writer, 0);
    }
    // Boogie's own lexer drops whitespace and comments without touching string
    // literals or semantic attributes. Length framing avoids token concatenation.
    using var stream = new MemoryStream(Encoding.UTF8.GetBytes(text.ToString()), writable: false);
    var scanner = new Bpl.Scanner(stream, new Bpl.Errors(), "proof-input", false);
    var tokens = new List<string>();
    for (var token = scanner.Scan(); token.kind != 0; token = scanner.Scan()) {
      tokens.Add(token.val);
    }
    using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
    for (var index = 0; index < tokens.Count; index++) {
      // Dependency IDs label diagnostic/unsat-core records; captureState labels
      // model-view snapshots. Their counters/locations change after unrelated
      // edits. Recognize complete Boogie attributes using lexical tokens only.
      if (index + 3 < tokens.Count && tokens[index] == "{" && tokens[index + 1] == ":" &&
          tokens[index + 2] is "id" or "captureState") {
        var depth = 1;
        var end = index + 3;
        for (; end < tokens.Count && depth != 0; end++) {
          if (tokens[end] == "{") {
            depth++;
          } else if (tokens[end] == "}") {
            depth--;
          }
        }
        if (depth == 0) {
          index = end - 1;
          continue;
        }
      }
      var bytes = Encoding.UTF8.GetBytes(tokens[index]);
      hash.AppendData(BitConverter.GetBytes(bytes.Length));
      hash.AppendData(bytes);
    }
    return Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
  }

  private static string? ProofToolchainHash() {
    var assemblies = new[] {
      typeof(DefinitionAnalysis).Assembly,
      typeof(Bpl.Program).Assembly,
      typeof(Bpl.ExecutionEngine).Assembly,
      typeof(Microsoft.Boogie.VCExprAST.VCExpr).Assembly,
      typeof(VCGeneration.TokenWrapper).Assembly,
      typeof(Microsoft.BaseTypes.BigNum).Assembly
    };
    var identities = new SortedDictionary<string, string>(StringComparer.Ordinal);
    foreach (var assembly in assemblies.Distinct()) {
      try {
        using var stream = File.OpenRead(assembly.Location);
        identities.Add(assembly.GetName().Name!, Convert.ToHexString(SHA256.HashData(stream)));
      } catch (IOException) {
        return null;
      } catch (UnauthorizedAccessException) {
        return null;
      }
    }
    return ProofHash(JsonSerializer.Serialize(identities));
  }

  private static string ProofOptionsHash(DafnyOptions options) {
    var arguments = DafnyCommands.VerificationOptions.Concat(DafnyCommands.ResolverOptions).Distinct()
      .Where(option => option != CommonOptionBag.Libraries && option != CommonOptionBag.Prelude &&
        option != CommonOptionBag.VerificationLogFormat && option != CommonOptionBag.ProgressOption &&
        option != CommonOptionBag.VerificationCoverageReport && option != CommonOptionBag.NoTimeStampForCoverageReport &&
        option != CommonOptionBag.JsonOutput && option != CommonOptionBag.JsonDiagnostics &&
        option != CommonOptionBag.LogLocation && option != CommonOptionBag.LogLevelOption)
      .OrderBy(option => option.Name, StringComparer.Ordinal)
      .Select(option => {
        var value = EffectiveOption(options, option);
        return new {
          option.Name,
          Value = value is FileSystemInfo file ? file.FullName : value
        };
      }).ToList();
    // Include the effective Boogie settings as well as their modern CLI bindings.
    // Paths to libraries/prelude are represented by their translated declarations.
    return ProofHash(JsonSerializer.Serialize(new {
      arguments,
      options.ProcedureInlining,
      options.InlineDepth,
      options.StratifiedInlining,
      options.LoopUnrollCount,
      options.SoundLoopUnrolling,
      options.TypeEncodingMethod,
      options.UseArrayTheory,
      options.UseSubsumption,
      options.Prune,
      options.PruneInfeasibleEdges,
      options.InferModifies,
      options.FreeVarLambdaLifting,
      options.KeepQuantifier,
      options.VcsSplitOnEveryAssert,
      options.RelaxFocus,
      options.RandomSeed,
      options.TimeLimit,
      options.ResourceLimit,
      options.AutoTriggers,
      options.RandomizeVcIterations,
      options.ProverOptions,
      options.VerifySnapshots
    }));
  }

  private static string ProofHash(string value) {
    return Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(value))).ToLowerInvariant();
  }

}
