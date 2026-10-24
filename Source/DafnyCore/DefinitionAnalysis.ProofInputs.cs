#nullable enable
using System;
using System.Collections.Generic;
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

  /// <summary>Rejects transformations whose dependency semantics are outside native diagnostic binding.</summary>
  public static bool SupportsDiagnosticContext(DafnyOptions options) =>
    !(options.Get(CommonOptionBag.PluginOption)?.Count is > 0 ||
      options.AdditionalPlugins.Count > 0 || options.AdditionalPluginArguments.Count > 0 ||
      !options.Plugins.SequenceEqual(DafnyOptions.DefaultPlugins) ||
      options.Get(BoogieOptionBag.BoogieArguments)?.Any() == true ||
      options.InlineDepth != DafnyOptions.Default.InlineDepth ||
      options.StratifiedInlining != DafnyOptions.Default.StratifiedInlining ||
      options.ProcedureInlining != DafnyOptions.Default.ProcedureInlining || options.InferModifies ||
      options.LoopUnrollCount != DafnyOptions.Default.LoopUnrollCount ||
      options.SoundLoopUnrolling != DafnyOptions.Default.SoundLoopUnrolling ||
      options.Get(CommonOptionBag.Libraries)?.Any() == true || options.Get(CommonOptionBag.Prelude) != null);
  private sealed record TranslatedProofDeclaration(
    string Module,
    string Sha256,
    DefinitionNode? Owner,
    bool ExcludableImplementation);

  private static DafnyProofInputs? ProofInputsFor(Program program, IReadOnlySet<Uri> analysisSourceUris) =>
    ProofInputsFor(program, analysisSourceUris,
      input => BoogieGenerator.Translate(input, input.Reporter), () => ProofToolchainIdentity.Value);

  // Let memory tests supply the translation environment and toolchain identity; keep fingerprinting here.
  internal static DafnyProofInputs? ProofInputsFor(Program program, IReadOnlySet<Uri> analysisSourceUris,
    Func<Program, IEnumerable<Tuple<string, Bpl.Program>>> translate, Func<string?> toolchainIdentity) {
    var options = program.Options;
    // Plugins and arbitrary Boogie arguments may install transformations that consume
    // implementation bodies. Their dependency semantics are outside this schema.
    if (options.Get(CommonOptionBag.PluginOption)?.Count is > 0 ||
        options.AdditionalPlugins.Count > 0 || options.AdditionalPluginArguments.Count > 0 ||
        !options.Plugins.SequenceEqual(DafnyOptions.DefaultPlugins) ||
        options.Get(BoogieOptionBag.BoogieArguments)?.Any() == true ||
        options.InlineDepth != DafnyOptions.Default.InlineDepth ||
        options.StratifiedInlining != DafnyOptions.Default.StratifiedInlining ||
        options.ProcedureInlining != DafnyOptions.Default.ProcedureInlining ||
        options.InferModifies ||
        options.LoopUnrollCount != DafnyOptions.Default.LoopUnrollCount ||
        options.SoundLoopUnrolling != DafnyOptions.Default.SoundLoopUnrolling) {
      return null;
    }

    var sourceDefinitions = SourceDefinitions(program, spansOnly: false, analysisSourceUris);
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
      foreach (var declaration in boogieProgram.TopLevelDeclarations) {
        DefinitionNode? owner = null;
        var excludable = false;
        if (declaration is Bpl.Implementation implementation &&
            implementation.tok is CanVerifyOrigin origin &&
            origin.CanVerify is INode sourceNode &&
            declarationIndex.TryGetValue(sourceNode, out owner)) {
          // A modular ordinary method/lemma call consumes its procedure contract. An
          // inline implementation can instead become part of another VC, so keep it.
          var modularMethod = origin.CanVerify is Method { IsByMethod: false } method &&
            (method.GetType() == typeof(Method) || method.GetType() == typeof(Lemma));
          excludable = modularMethod &&
            !HasInlineAttribute(implementation.Attributes) &&
            procedures.TryGetValue(implementation.Name, out var matches) && matches.Count == 1 &&
            !HasInlineAttribute(matches[0].Attributes);
        }
        translated.Add(new TranslatedProofDeclaration(moduleName,
          ProofDeclarationHash(printOptions, declaration), owner, excludable));
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
    using (var writer = new Bpl.TokenTextWriter(text, options)) {
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
      .Where(option => option != CommonOptionBag.Libraries && option != CommonOptionBag.Prelude)
      .OrderBy(option => option.Name, StringComparer.Ordinal)
      .Select(option => {
        var value = options.Options.OptionArguments.GetValueOrDefault(option);
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
      options.RandomizeVcIterations,
      options.ProverOptions,
      options.VerifySnapshots
    }));
  }

  private static string ProofHash(string value) {
    return Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(value))).ToLowerInvariant();
  }

}
