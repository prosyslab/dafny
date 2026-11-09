#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections;
using System.CommandLine;
using System.CommandLine.Binding;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>
/// Identifies the solver input of a source definition: from schema 2 on, a digest over the modular keys of the Boogie
/// implementations it owns. An empty implementation list is a certified zero-obligation target.
/// </summary>
public sealed record DafnyDefinitionProofInput(string SourcePath, string FullName, string Sha256) {
  /// <summary>Number of owned Boogie implementations (schema 2 and later).</summary>
  [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  public int? Implementations { get; init; }
  /// <summary>Where the declarations of the owned keys come from (schema 2 and later). Not part of any key.</summary>
  [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  public DafnyProofClosureOrigins? ClosureOrigins { get; init; }
}

/// <summary>A half-open source range of one closure declaration, in the offsets definitions report.</summary>
public sealed record DafnyProofOriginSpan(int Start, int End);

/// <summary>Merged closure origin ranges in one source.</summary>
public sealed record DafnyProofOriginSource(string SourcePath, IReadOnlyList<DafnyProofOriginSpan> Spans);

/// <summary>
/// Dafny origins of an owned implementation, its own and called procedures and its live solver declarations.
/// <see cref="Toolchain"/> counts the declarations without a source origin (prelude, generated, no token).
/// </summary>
public sealed record DafnyProofClosureOrigins(IReadOnlyList<DafnyProofOriginSource> Sources, int Toolchain);

/// <summary>Binds translated definition inputs to their producer and verification options.</summary>
public sealed record DafnyProofInputs(
  int SchemaVersion,
  string ToolchainSha256,
  string OptionsSha256,
  IReadOnlyList<DafnyDefinitionProofInput> Definitions);

public static partial class DefinitionAnalysis {
  private static readonly Lazy<string?> AssemblyToolchainIdentity = new(AssemblyToolchainHash);
  /// <summary>Identifies the bounded native producer assemblies without granting proof-input evidence.</summary>
  public static string? ContextToolchainIdentity() => AssemblyToolchainIdentity.Value;

  /// <summary>
  /// The toolchain a proof input is bound to: the producer assemblies and the solver binary that would run
  /// with these options. Null (no proof inputs) when either cannot be identified.
  /// </summary>
  internal static string? ProofToolchainIdentity(DafnyOptions options, Func<string, string?>? contentHash = null) =>
    ProofToolchainHash(AssemblyToolchainIdentity.Value, SolverIdentity(options, contentHash ?? FileContentHash));

  internal static string? ProofToolchainHash(string? assemblies, string? solver) =>
    assemblies == null || solver == null ? null : ProofHash(JsonSerializer.Serialize(new { assemblies, solver }));

  /// <summary>
  /// Identifies effective resolver and verifier settings for a context that owns a verification engine, including
  /// native solver options. Every configured solver enters by its effective absolute path and by its content: the
  /// engine starts that path, so a request naming another path never shares a context (state, engine or result
  /// cache) with it, even for equal bytes, and other bytes at the same path give another context. A path that is not
  /// <see cref="DafnyOptions.IsExactSolverPath"/> is never read (the started file need not be the read one). Proof
  /// keys use the path-free <see cref="ProofOptionsHash"/> and bind the solver by content in the toolchain.
  /// </summary>
  public static string ContextOptionsIdentity(DafnyOptions options) => ContextOptionsIdentity(options, FileContentHash);

  /// <summary><see cref="ContextOptionsIdentity(DafnyOptions)"/> with the solver content hash supplied (test seam).</summary>
  public static string ContextOptionsIdentity(DafnyOptions options, Func<string, string?> contentHash) {
    var solvers = SolverPaths(options).Select(path => DafnyOptions.IsExactSolverPath(path)
      ? new { path, content = contentHash(path) is { } hash ? "sha256:" + hash : "unhashable" }
      : new { path, content = "inexact" }).ToList();
    return solvers.Count == 0 ? ProofOptionsHash(options)
      : ProofHash(JsonSerializer.Serialize(new { options = ProofOptionsHash(options), solvers }));
  }

  /// <summary>
  /// The configured solver paths (<c>PROVER_PATH</c> in every form), as given, each once at its last position.
  /// Boogie applies the last entry, so equal lists start the same solver; repeated entries (the
  /// <c>--solver-path</c> binding and <see cref="DafnyOptions.ProcessSolverOptions"/> add the same one) collapse.
  /// </summary>
  internal static IReadOnlyList<string> SolverPaths(DafnyOptions options) {
    var paths = options.ProverOptions.Select(DafnyOptions.ProverPathValue).Where(path => path != null)
      .Select(path => path!).ToList();
    return paths.Where((path, index) => paths.LastIndexOf(path) == index).ToList();
  }

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
      int.TryParse(arguments[0]["/randomSeed:".Length..], out var seed) &&
      seed == (options.StableRandomSeed ?? options.RandomSeed);
  }
  private static DafnyProofInputs? ProofInputsFor(Program program, IReadOnlySet<Uri> analysisSourceUris) =>
    ProofInputsFor(program, analysisSourceUris,
      input => BoogieGenerator.Translate(input, input.Reporter), () => ProofToolchainIdentity(program.Options));

  /// <summary>
  /// Key the session's own translations. This lifts their lambdas (once, as the engine path would) and computes
  /// the per-implementation keys on the program that the engine will verify.
  /// </summary>
  public static DafnyProofInputs? ProofInputsFromTranslations(Program program,
    IReadOnlySet<Uri> analysisSourceUris, IReadOnlyList<Tuple<string, Bpl.Program>> translations) =>
    ProofInputsFor(program, analysisSourceUris, _ => translations, () => ProofToolchainIdentity(program.Options));

  /// <summary>Bind native result-cache checksums to the modular key of each implementation.</summary>
  /// <remarks>
  /// The key covers the implementation text, its own and called procedures, the ordered superset of its pruned
  /// solver declarations, the effective options and the toolchain; <see cref="AssertionShape"/> guards the
  /// ordered assertion sequence that cached results are rebased onto. An implementation without a key (no proof
  /// inputs for these options, or an unsupported implementation) gets a fresh checksum, which keeps same-state
  /// task reuse and disables cross-compilation replay.
  ///
  /// For an implementation with a key, Boogie's dependency identity (<c>MD5DependencyChecksum_</c>, which its
  /// result cache compares next to the checksum) is set to a digest of the bound checksum. Otherwise Boogie
  /// combines the Dafny <c>{:checksum}</c> of every transitively mentioned function, which is much wider than
  /// the pruned solver input and misses after unrelated edits. The key already covers a superset of every
  /// split's solver input, the options and the toolchain, so lookup then succeeds exactly when key and
  /// assertion shape match. Implementations without a key keep Boogie's own dependency identity.
  /// </remarks>
  public static void BindNativeVerificationChecksums(IReadOnlyList<Tuple<string, Bpl.Program>> translations,
    DafnyProofInputs? proofInputs) {
    foreach (var (_, translation) in translations) {
      var keys = proofInputs is { SchemaVersion: ModularProofKeys.SchemaVersion } ? ModularProofKeys.Existing(translation) : null;
      var procedures = translation.Procedures.GroupBy(procedure => procedure.Name, StringComparer.Ordinal)
        .Where(group => group.Count() == 1).ToDictionary(group => group.Key, group => group.Single(), StringComparer.Ordinal);
      foreach (var implementation in translation.Implementations) {
        string? key = null;
        if (keys?.Unsupported == null && keys?.Implementations.TryGetValue(implementation, out var content) == true &&
            content.Content != null) {
          key = ModularProofKeys.Key(proofInputs!.ToolchainSha256, proofInputs.OptionsSha256, content.Content);
        }
        var checksum = ProofHash(key != null
          ? key + "\0" + AssertionShape(implementation, procedures) : Guid.NewGuid().ToString("N"));
        implementation.Attributes = new Bpl.QKeyValue(implementation.tok, "checksum", new List<object> { checksum },
          implementation.Attributes);
        if (key != null) {
          implementation.MD5DependencyChecksum_ = KeyDependencyIdentity(checksum);
        }
      }
    }
  }

  /// <summary>The dependency identity of a key-bound implementation: a function of its bound checksum only.</summary>
  internal static byte[] KeyDependencyIdentity(string checksum) =>
    SHA256.HashData(Encoding.UTF8.GetBytes("modular-proof-key-dependency\0" + checksum));

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
        // Boogie's per-iteration seeds shuffle the whole pruned list (see ModularProofKeys).
        options.RandomizeVcIterations > 1 ||
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
    var errorCount = program.Reporter.ErrorCount;
    var modules = new List<(Bpl.Program Program, ModularProofKeys.ProgramKeys Keys)>();
    foreach (var (_, boogieProgram) in translate(program)) {
      modules.Add((boogieProgram, ModularProofKeys.Compute(options, boogieProgram)));
    }
    if (program.Reporter.ErrorCount != errorCount || modules.Count == 0) {
      return null;
    }

    var toolchain = toolchainIdentity();
    if (toolchain == null) {
      return null;
    }
    var optionsHash = ProofOptionsHash(options);
    // Ownership follows the session's verification-task owner (the implementation's CanVerifyOrigin).
    var owned = new Dictionary<DefinitionNode, List<ModularProofKeys.ImplementationKey?>>();
    var unattributed = false;
    var procedureNames = new HashSet<string>(StringComparer.Ordinal);
    foreach (var (boogieProgram, keys) in modules) {
      procedureNames.UnionWith(boogieProgram.TopLevelDeclarations.OfType<Bpl.Procedure>().Select(procedure => procedure.Name));
      foreach (var implementation in boogieProgram.TopLevelDeclarations.OfType<Bpl.Implementation>()) {
        if (implementation.tok is not CanVerifyOrigin { CanVerify: INode node }) {
          unattributed = true;
          continue;
        }
        if (!declarationIndex.TryGetValue(node, out var owner)) {
          continue;
        }
        if (!owned.TryGetValue(owner, out var list)) {
          owned[owner] = list = new List<ModularProofKeys.ImplementationKey?>();
        }
        list.Add(keys.Unsupported == null && keys.Implementations.TryGetValue(implementation, out var key) ? key : null);
      }
    }

    var results = new List<DafnyDefinitionProofInput>();
    foreach (var definition in sourceDefinitions) {
      // By-method and generated/extreme declarations require more than one logical
      // source identity. Do not issue a partial certificate for them.
      if (definition.Declaration is not MethodOrConstructor and not Function ||
          definition.Declaration is Function { ByMethodBody: not null } or ExtremeLemma ||
          definition.Declaration is MethodOrFunction { HasVerifyFalseAttribute: true } ||
          definition.Declaration is MethodOrConstructor { Body: null } or Function { Body: null } ||
          definition.BodyKind == DefinitionBodyKind.FunctionByMethod) {
        continue;
      }
      var implementations = owned.GetValueOrDefault(definition) ?? new List<ModularProofKeys.ImplementationKey?>();
      if (implementations.Count == 0) {
        // Dafny emits no implementation for a declaration without proof obligations. Certify that only when
        // every implementation has a known owner and the translation shows the declaration in verification
        // scope: its correctness or well-formedness procedure is emitted exactly when it is checked.
        var marker = definition.Declaration switch {
          Function function => "CheckWellformed" + BoogieGenerator.NameSeparator + function.FullSanitizedName,
          MethodOrConstructor method => "Impl" + BoogieGenerator.NameSeparator + method.FullSanitizedName,
          _ => null
        };
        if (unattributed || marker == null || !procedureNames.Contains(marker)) {
          continue;
        }
      } else if (implementations.Any(key => key?.Content == null)) {
        continue;
      }
      var sourcePath = SourcePath(definition.Declaration);
      if (sourcePath.Length == 0 || sourceDefinitions.Count(other => SourcePath(other.Declaration) == sourcePath &&
            other.ReportFullName == definition.ReportFullName) != 1) {
        continue;
      }
      var keyed = implementations.Select(key => new[] {
        key!.Implementation.Name, ModularProofKeys.Key(toolchain, optionsHash, key.Content!)
      }).OrderBy(pair => pair[0], StringComparer.Ordinal).ThenBy(pair => pair[1], StringComparer.Ordinal).ToList();
      results.Add(new DafnyDefinitionProofInput(sourcePath, definition.ReportFullName,
        ProofHash(JsonSerializer.Serialize(new {
          Schema = ModularProofKeys.SchemaVersion,
          toolchain,
          optionsHash,
          implementations = keyed
        }))) {
        Implementations = implementations.Count,
        ClosureOrigins = ClosureOrigins(implementations.SelectMany(key => key!.Closure))
      });
    }
    return new DafnyProofInputs(ModularProofKeys.SchemaVersion, toolchain, optionsHash, results);
  }

  /// <summary>Merge the source ranges of closure declarations; declarations without a source are counted.</summary>
  private static DafnyProofClosureOrigins ClosureOrigins(IEnumerable<Bpl.Declaration> declarations) {
    var spans = new SortedDictionary<string, List<(int Start, int End)>>(StringComparer.Ordinal);
    var toolchain = 0;
    foreach (var declaration in declarations.Distinct(ReferenceEqualityComparer.Instance).Cast<Bpl.Declaration>()) {
      if (OriginSpan(declaration.tok) is not { } span) {
        toolchain++;
        continue;
      }
      if (!spans.TryGetValue(span.Path, out var list)) {
        spans[span.Path] = list = new List<(int, int)>();
      }
      list.Add((span.Start, span.End));
    }
    var sources = new List<DafnyProofOriginSource>();
    foreach (var (path, list) in spans) {
      var merged = new List<DafnyProofOriginSpan>();
      foreach (var (start, end) in list.OrderBy(item => item.Start).ThenBy(item => item.End)) {
        if (merged.Count > 0 && start <= merged[^1].End) {
          merged[^1] = merged[^1] with { End = Math.Max(merged[^1].End, end) };
        } else {
          merged.Add(new DafnyProofOriginSpan(start, end));
        }
      }
      sources.Add(new DafnyProofOriginSource(path, merged));
    }
    return new DafnyProofClosureOrigins(sources, toolchain);
  }

  /// <summary>The whole source range of a Dafny origin, or null for Boogie and missing tokens.</summary>
  private static (string Path, int Start, int End)? OriginSpan(Bpl.IToken token) {
    if (token is not IOrigin origin || !token.IsValid || origin.Uri is not { } uri) {
      return null;
    }
    var range = origin.EntireRange ?? origin.ReportingRange;
    var first = range.StartToken;
    var last = range.EndToken ?? first;
    if (first.Uri == null || !first.IsValid) {
      return null;
    }
    var path = uri.IsFile ? Path.GetFullPath(uri.LocalPath) : uri.ToString();
    var start = Math.Min(first.pos, last.pos);
    return (path, start, Math.Max(TokenEnd(first), TokenEnd(last)));
  }

  private static bool HasInlineAttribute(Bpl.QKeyValue? attributes) {
    for (var attribute = attributes; attribute != null; attribute = attribute.Next) {
      if (attribute.Key == "inline") {
        return true;
      }
    }
    return false;
  }

  private static DafnyOptions ProofPrintOptions(DafnyOptions options) => new(options) {
    PrintInstrumented = true,
    PrintInlined = true,
    PrintWithUniqueASTIds = false,
    PrintDesugarings = false,
    PrintUnstructured = 0,
    PrintFile = "-"
  };

  /// <summary>
  /// Hash one declaration's printed Boogie text by lexical token, without positions, comments, labels of
  /// diagnostics or checksums. <paramref name="rename"/> maps identifier tokens (lifted lambda names). Semantic
  /// flags the printer omits are appended.
  /// </summary>
  internal static string ProofDeclarationHash(DafnyOptions options, Bpl.Declaration declaration,
    Func<string, string>? rename = null) {
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
    void Append(string value) {
      var bytes = Encoding.UTF8.GetBytes(value);
      hash.AppendData(BitConverter.GetBytes(bytes.Length));
      hash.AppendData(bytes);
    }
    for (var index = 0; index < tokens.Count; index++) {
      // Dependency IDs label diagnostic/unsat-core records; captureState labels
      // model-view snapshots; checksums key Boogie's result cache. Their values change
      // after unrelated edits and none reaches the solver (Dafny disables debug
      // information). Recognize complete Boogie attributes using lexical tokens only.
      if (index + 3 < tokens.Count && tokens[index] == "{" && tokens[index + 1] == ":" &&
          tokens[index + 2] is "id" or "captureState" or "checksum") {
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
      Append(rename == null ? tokens[index] : rename(tokens[index]));
    }
    // Not printed, but they change which axioms a split declares (hidden CanHide axioms are pruned) and
    // which axiom Boogie treats as a function's definition.
    switch (declaration) {
      case Bpl.Axiom axiom:
        Append("\u0001canHide:" + axiom.CanHide);
        break;
      case Bpl.Function function:
        Append("\u0001definition:" + (function.DefinitionAxiom != null));
        Append("\u0001canHide:" + string.Join(",", function.DefinitionAxioms.Select(axiom => axiom.CanHide)));
        break;
      case Bpl.Constant constant:
        Append("\u0001canHide:" + string.Join(",", constant.DefinitionAxioms.Select(axiom => axiom.CanHide)));
        break;
    }
    return Convert.ToHexString(hash.GetHashAndReset()).ToLowerInvariant();
  }

  /// <summary>SHA-256 of the solver executable's bytes; only Z3 is supported.</summary>
  private static string? SolverIdentity(DafnyOptions options, Func<string, string?> contentHash) {
    if (!options.IsUsingZ3() || options.ResolveZ3ExecutablePath() is not { } path) {
      return null;
    }
    return contentHash(path) is { } hash ? "z3:" + hash : null;
  }

  /// <summary>SHA-256 of a file's bytes after following links; null when the file cannot be read.</summary>
  internal static string? FileContentHash(string path) => ToolFileHashes.Shared.Hash(path);

  /// <summary>
  /// What says a file is unchanged without reading it: size, write time, change time and, where the platform reports
  /// it, the device and inode. Rewriting a file in place (even keeping size and write time) changes its change time;
  /// replacing it by another file changes its inode.
  /// </summary>
  internal sealed record FileStamp(long Length, DateTime Written, DateTime Changed, string? Node) {
    public DateTime Latest => Written > Changed ? Written : Changed;
  }

  /// <summary>
  /// Content hashes of tool files (solver binary, solver plugin), cached per resolved path while the file's stamp is
  /// unchanged. A file changed within <see cref="RacyWindow"/> is hashed but not cached, because a second change in
  /// the same timestamp tick would keep its stamp; a file whose stamp changes while it is read has no hash.
  /// </summary>
  internal sealed class ToolFileHashes(Func<string, FileStamp?> stamp, Func<string, string> read, Func<DateTime> now) {
    internal static readonly TimeSpan RacyWindow = TimeSpan.FromSeconds(2);
    internal static ToolFileHashes Shared { get; } = new(ReadStamp, ReadHash, () => DateTime.UtcNow);
    private readonly ConcurrentDictionary<string, (FileStamp Stamp, string Hash)> entries = new(StringComparer.Ordinal);

    internal string? Hash(string path) {
      try {
        var file = new FileInfo(Path.GetFullPath(path));
        var resolved = (file.ResolveLinkTarget(returnFinalTarget: true) as FileInfo ?? file).FullName;
        if (stamp(resolved) is not { } before) {
          return null;
        }
        if (entries.TryGetValue(resolved, out var entry) && entry.Stamp == before) {
          return entry.Hash;
        }
        var hash = read(resolved);
        if (stamp(resolved) != before) {
          return null;
        }
        if (now() - before.Latest >= RacyWindow) {
          entries[resolved] = (before, hash);
        }
        return hash;
      } catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or
                                             ArgumentException or NotSupportedException) {
        return null;
      }
    }

    private static string ReadHash(string path) {
      using var stream = File.OpenRead(path);
      return Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
    }

    internal static FileStamp? ReadStamp(string path) {
      var info = new FileInfo(path);
      if (!info.Exists) {
        return null;
      }
      var status = LinuxStatus(path);
      return new FileStamp(info.Length, info.LastWriteTimeUtc, status?.Changed ?? info.CreationTimeUtc, status?.Node);
    }

    private const int AtCurrentDirectory = -100;
    private const uint StatxInode = 0x100;
    private const uint StatxChangeTime = 0x80;
    private const uint StatxBasicStats = 0x7ff;
    private static volatile bool statxUnavailable;

    [DllImport("libc", EntryPoint = "statx", SetLastError = true)]
    private static extern int Statx(int directory, [MarshalAs(UnmanagedType.LPUTF8Str)] string path, int flags,
      uint mask, [Out] byte[] buffer);

    /// <summary>
    /// Change time and device:inode from Linux <c>statx</c> (its 256-byte layout is the same on every architecture),
    /// following links; null on other platforms or when the call is unavailable or fails.
    /// </summary>
    private static (DateTime Changed, string Node)? LinuxStatus(string path) {
      if (!OperatingSystem.IsLinux() || statxUnavailable) {
        return null;
      }
      try {
        var buffer = new byte[256];
        if (Statx(AtCurrentDirectory, path, 0, StatxBasicStats, buffer) != 0 ||
            (BitConverter.ToUInt32(buffer, 0) & (StatxInode | StatxChangeTime)) != (StatxInode | StatxChangeTime)) {
          return null;
        }
        var changed = DateTime.UnixEpoch.AddTicks(BitConverter.ToInt64(buffer, 96) * TimeSpan.TicksPerSecond +
                                                  BitConverter.ToUInt32(buffer, 104) / 100);
        return (changed, $"{BitConverter.ToUInt32(buffer, 136)}:{BitConverter.ToUInt32(buffer, 140)}:{BitConverter.ToUInt64(buffer, 32)}");
      } catch (Exception exception) when (exception is DllNotFoundException or EntryPointNotFoundException) {
        statxUnavailable = true;
        return null;
      }
    }
  }

  /// <summary>
  /// A tool file (solver binary, solver plugin) by content. Only a file that cannot be read keeps its path, so two
  /// unreadable tools never share an identity.
  /// </summary>
  private static string ContentIdentity(string path) =>
    FileContentHash(path) is { } hash ? "sha256:" + hash : "unhashable:" + path;

  /// <summary>
  /// Prover options that name a host location instead of a semantic setting, in every form Boogie parses
  /// (<c>NAME=v</c>, <c>NAME:v</c>, bare): the solver binary (bound by content in the toolchain identity), the SMT
  /// log file and the inspector process, which only receives statistics.
  /// </summary>
  internal static bool IsLocationProverOption(string proverOption) =>
    new[] { "PROVER_PATH", "LOG_FILE", "INSPECTOR" }.Any(name => proverOption.StartsWith(name, StringComparison.Ordinal) &&
      (proverOption.Length == name.Length || proverOption[name.Length] is '=' or ':'));

  /// <summary>
  /// The command-line options whose effective values enter <see cref="ProofOptionsHash"/>. Libraries and the prelude
  /// are represented by their translated declarations, the solver binary by content in the toolchain identity;
  /// report, log and progress destinations do not change what is proved.
  /// </summary>
  internal static IReadOnlyList<Option> ProofOptionArguments => DafnyCommands.VerificationOptions
    .Concat(DafnyCommands.ResolverOptions).Distinct()
    .Where(option => option != CommonOptionBag.Libraries && option != CommonOptionBag.Prelude &&
      option != BoogieOptionBag.SolverPath && option != BoogieOptionBag.SolverLog &&
      option != CommonOptionBag.VerificationLogFormat && option != CommonOptionBag.ProgressOption &&
      option != CommonOptionBag.VerificationCoverageReport && option != CommonOptionBag.NoTimeStampForCoverageReport &&
      option != CommonOptionBag.JsonOutput && option != CommonOptionBag.JsonDiagnostics &&
      option != CommonOptionBag.LogLocation && option != CommonOptionBag.LogLevelOption)
    .OrderBy(option => option.Name, StringComparer.Ordinal).ToList();

  private static string? AssemblyToolchainHash() =>
    ToolchainAssemblyFiles() is { } files ? ToolchainAssemblyHash(files, FileContentHash) : null;

  private static bool IsToolchainAssemblyName(string? name) => name != null &&
    (name.StartsWith("Boogie", StringComparison.Ordinal) || name.StartsWith("Dafny", StringComparison.Ordinal));

  /// <summary>
  /// The producer assembly files whose code can change translation, VC generation, SMT emission, solver interaction
  /// or result parsing: the Boogie and Dafny assemblies statically reachable from DafnyCore and Boogie's execution
  /// engine (this loads them), plus every <c>Boogie*.dll</c> and <c>Dafny*.dll</c> in the directories they were
  /// loaded from (the driver, language server and pipeline assemblies of an install). Each file is named by its file
  /// name, never its directory. Null when an assembly cannot be loaded or has no file.
  /// </summary>
  public static IReadOnlyList<(string Name, string Path)>? ToolchainAssemblyFiles() {
    try {
      var reached = new Dictionary<string, System.Reflection.Assembly>(StringComparer.Ordinal);
      var pending = new Stack<System.Reflection.Assembly>(new[] {
        typeof(DefinitionAnalysis).Assembly, typeof(Bpl.Program).Assembly, typeof(Bpl.ExecutionEngine).Assembly,
        typeof(Microsoft.Boogie.VCExprAST.VCExpr).Assembly, typeof(VCGeneration.TokenWrapper).Assembly,
        typeof(Microsoft.BaseTypes.BigNum).Assembly
      });
      while (pending.TryPop(out var assembly)) {
        if (!reached.TryAdd(assembly.GetName().Name!, assembly)) {
          continue;
        }
        foreach (var reference in assembly.GetReferencedAssemblies()) {
          if (IsToolchainAssemblyName(reference.Name) && !reached.ContainsKey(reference.Name!)) {
            pending.Push(System.Reflection.Assembly.Load(reference));
          }
        }
      }
      var paths = new HashSet<string>(StringComparer.Ordinal);
      foreach (var assembly in reached.Values) {
        if (string.IsNullOrEmpty(assembly.Location)) {
          return null;
        }
        paths.Add(Path.GetFullPath(assembly.Location));
      }
      foreach (var directory in paths.Select(Path.GetDirectoryName).Distinct().ToList()) {
        paths.UnionWith(Directory.EnumerateFiles(directory!, "*.dll")
          .Where(file => IsToolchainAssemblyName(Path.GetFileName(file))).Select(Path.GetFullPath));
      }
      return paths.Select(path => (Name: Path.GetFileName(path), Path: path))
        .OrderBy(file => file.Name, StringComparer.Ordinal).ThenBy(file => file.Path, StringComparer.Ordinal).ToList();
    } catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or
                                           BadImageFormatException or ArgumentException or NotSupportedException) {
      return null;
    }
  }

  /// <summary>
  /// Identity of producer assembly files by file name and content, independent of their order and directories.
  /// Null when one cannot be read.
  /// </summary>
  internal static string? ToolchainAssemblyHash(IEnumerable<(string Name, string Path)> files,
    Func<string, string?> contentHash) {
    var identities = new List<string>();
    foreach (var (name, path) in files) {
      if (contentHash(path) is not { } hash) {
        return null;
      }
      identities.Add(name + ":" + hash);
    }
    return ProofHash(JsonSerializer.Serialize(identities.Distinct().OrderBy(identity => identity, StringComparer.Ordinal)));
  }

  /// <summary>
  /// The effective semantic options a proof depends on. It names no host location, so the same options give the
  /// same hash wherever the toolchain is installed.
  /// </summary>
  internal static string ProofOptionsHash(DafnyOptions options) {
    var arguments = ProofOptionArguments.Select(option => {
      var value = EffectiveOption(options, option);
      if (option == BoogieOptionBag.SolverOption && value is object[] solverOptions) {
        value = solverOptions.Where(entry => entry is not string text || !IsLocationProverOption(text)).ToArray();
      } else if (option == BoogieOptionBag.SolverPlugin && value is string plugin) {
        value = ContentIdentity(plugin);
      }
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
      ProverOptions = options.ProverOptions.Where(option => !IsLocationProverOption(option)).ToList(),
      options.VerifySnapshots
    }));
  }

  private static string ProofHash(string value) {
    return Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(value))).ToLowerInvariant();
  }

}
