#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class DefinitionAnalysisCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Format,
    SpansOnly,
    IncludeSourceFacts,
    IncludeSemanticFacts,
    IncludeVerificationFacts,
    IncludeProofInputs,
    IncludeStatements,
    AnalysisSources
  }.Concat(DafnyCommands.ConsoleOutputOptions)
    .Concat(DafnyCommands.ResolverOptions)
    .Concat(DafnyCommands.VerificationOptions).Distinct();

  private static readonly Option<string> Format = new("--format", () => "json",
    "Output format. Only 'json' is currently supported.");
  internal static readonly Option<bool> SpansOnly = new("--spans-only",
    "Report parse-level source spans without requiring name or type resolution.");
  internal static readonly Option<bool> IncludeSourceFacts = new("--include-source-facts",
    "Wrap definitions and resolved source structure in a JSON document.");
  internal static readonly Option<bool> IncludeSemanticFacts = new("--include-semantic-facts",
    "Include deterministic source and definition semantic fingerprints.");
  internal static readonly Option<bool> IncludeVerificationFacts = new("--include-verification-facts",
    "Include native resolved verification targets and their authored declaration attributes.");
  internal static readonly Option<bool> IncludeStatements = new("--include-statements",
    "Report resolved statement spans, kinds, and direct call targets.");
  internal static readonly Option<bool> IncludeProofInputs = new("--include-proof-inputs",
    "Include conservative translated per-definition proof-input fingerprints without running a solver.");

  internal static readonly Option<IList<FileInfo>> AnalysisSources = new("--analysis-source", () => new List<FileInfo>(),
    "Report facts for this verified source of the compilation instead of only the root sources. " +
    "Repeat to report several sources; every analyzed root must be listed. Roots, includes and libraries are unchanged.") {
    ArgumentHelpName = "file"
  };

  static DefinitionAnalysisCommand() {
    OptionRegistry.RegisterOption(AnalysisSources, OptionScope.Cli);
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(SpansOnly, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeSourceFacts, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeSemanticFacts, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeVerificationFacts, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeProofInputs, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeStatements, OptionScope.Cli);
  }

  public static Command Create() {
    var result = new Command("definition-analysis",
      "Report resolved Dafny declaration dependencies, source spans, paths, and local includes.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(Format) != "json") {
      await options.ErrorWriter.WriteLineAsync("definition-analysis only supports --format json.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    if (options.Get(SpansOnly)) {
      if (options.Get(IncludeProofInputs)) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --include-proof-inputs with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (options.Get(IncludeSourceFacts)) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --include-source-facts with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (options.Get(IncludeStatements)) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --include-statements with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (options.Get(IncludeSemanticFacts)) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --include-semantic-facts with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (options.Get(IncludeVerificationFacts)) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --include-verification-facts with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (options.Get(AnalysisSources)?.Any() == true) {
        await options.ErrorWriter.WriteLineAsync(
          "definition-analysis does not support --analysis-source with --spans-only.");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      return await ExecuteSpansOnly(options);
    }

    var certificateOutput = options.BaseOutputWriter;
    if (options.Get(IncludeProofInputs)) {
      // Keep the optional certificate document independently parseable while
      // preserving all existing qualification diagnostics for the caller.
      ((Microsoft.Boogie.CommandLineOptions)options).OutputWriter = options.ErrorWriter;
    }
    var compilation = CliCompilation.Create(options);
    if (options.Get(IncludeProofInputs)) {
      // Translation consumes declared solver settings, not the executable's
      // discovered version. Certificate generation must not launch the solver.
      compilation.Compilation.ShouldProcessSolverOptions = false;
    }
    compilation.Start();
    var rootSourceUris = AnalysisSourceUris(await compilation.Compilation.RootFiles);
    var resolution = await compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      return await compilation.GetAndReportExitCode();
    }
    var analysisSourceUris = SelectAnalysisSources(options, rootSourceUris, resolution.ResolvedProgram, out var selectionError);
    if (analysisSourceUris == null) {
      await options.ErrorWriter.WriteLineAsync(selectionError);
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var includeSourceFacts = options.Get(IncludeSourceFacts) || options.Get(IncludeSemanticFacts) || options.Get(IncludeProofInputs) || options.Get(IncludeVerificationFacts);
    object results;
    if (includeSourceFacts) {
      DefinitionAnalysisDocument AnalyzeDocument() => DefinitionAnalysis.AnalyzeDocument(
        resolution.ResolvedProgram,
        analysisSourceUris,
        options.Get(IncludeStatements),
        options.Get(IncludeSemanticFacts),
        options.Get(IncludeProofInputs),
        verificationTargets: options.Get(IncludeVerificationFacts)
          ? resolution.CanVerifies!.Values.SelectMany(tree => tree.Values)
          : null);
      results = await DafnyMain.LargeStackFactory.StartNew(AnalyzeDocument);
    } else {
      results = await DafnyMain.LargeStackFactory.StartNew(() => DefinitionAnalysis.Analyze(
        resolution.ResolvedProgram,
        analysisSourceUris,
        options.Get(IncludeStatements)));
    }
    var json = JsonSerializer.Serialize(results, new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      WriteIndented = true
    });
    if (options.Get(IncludeProofInputs)) {
      await certificateOutput.WriteLineAsync(json);
    } else {
      await options.OutputWriter.Code(json + "\n");
    }

    return await compilation.GetAndReportExitCode();
  }

  private static async Task<int> ExecuteSpansOnly(DafnyOptions options) {
    var (code, dafnyFiles, _) = await SynchronousCliCompilation.GetDafnyFiles(options);
    if (code != ExitValue.SUCCESS) {
      return (int)code;
    }

    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);
    var programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";
    var (program, parseError) = await DafnyMain.Parse(dafnyFiles, programName, options);
    if (parseError != null) {
      await options.ErrorWriter.WriteLineAsync(parseError);
      return (int)ExitValue.DAFNY_ERROR;
    }

    var analysisSourceUris = AnalysisSourceUris(dafnyFiles);
    var json = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeSpans(program, analysisSourceUris), new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      WriteIndented = true
    });
    await options.OutputWriter.Code(json + "\n");
    return (int)ExitValue.SUCCESS;
  }

  /// <summary>
  /// Choose the reported sources without changing the compilation. A selection must
  /// keep every analyzed root and may add only sources this compilation verifies.
  /// Root status decides which included declarations are translated unless
  /// --verify-included-files is set, so proof and verification facts of a non-root
  /// source require it. Returns null with an error message for an invalid selection.
  /// </summary>
  internal static IReadOnlySet<Uri>? SelectAnalysisSources(DafnyOptions options, IReadOnlySet<Uri> rootSourceUris,
    Program program, out string? error) {
    error = null;
    var requested = options.Get(AnalysisSources);
    if (requested == null || !requested.Any()) {
      return rootSourceUris;
    }
    var selected = requested.Select(file => new Uri(Path.GetFullPath(file.FullName))).ToHashSet();
    var missingRoot = rootSourceUris.FirstOrDefault(uri => !selected.Contains(uri));
    if (missingRoot != null) {
      error = $"--analysis-source must list every analyzed root; {missingRoot.LocalPath} is missing.";
      return null;
    }
    var verified = program.Compilation.VerifiedUris();
    var parsed = program.Compilation.RootSourceUris.Concat(program.Compilation.Includes.Select(include => include.IncludedFilename))
      .ToHashSet();
    foreach (var uri in selected.Where(uri => !rootSourceUris.Contains(uri))) {
      if (!uri.IsFile || Path.GetExtension(uri.LocalPath) != DafnyFile.DafnyFileExtension || !parsed.Contains(uri) ||
          !verified.Contains(uri)) {
        error = $"--analysis-source {uri.LocalPath} is not a verified Dafny source of this compilation.";
        return null;
      }
      if (!options.VerifyAllModules && (options.Get(IncludeProofInputs) || options.Get(IncludeVerificationFacts))) {
        error = $"--analysis-source {uri.LocalPath} is an included source; its proof and verification facts require --verify-included-files.";
        return null;
      }
    }
    return selected;
  }

  internal static IReadOnlySet<Uri> AnalysisSourceUris(IEnumerable<DafnyFile> rootFiles) {
    return rootFiles
      .Where(file =>
        !file.ShouldNotVerify &&
        (file.Uri == DafnyFile.StdInUri ||
         file.Uri.IsFile && file.Extension == DafnyFile.DafnyFileExtension))
      .Select(file => file.Uri)
      .ToHashSet();
  }
}
