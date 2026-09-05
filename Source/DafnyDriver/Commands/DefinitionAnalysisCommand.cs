#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
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
    IncludeStatements
  }.Concat(DafnyCommands.ConsoleOutputOptions)
    .Concat(DafnyCommands.ResolverOptions);

  private static readonly Option<string> Format = new("--format", () => "json",
    "Output format. Only 'json' is currently supported.");
  private static readonly Option<bool> SpansOnly = new("--spans-only",
    "Report parse-level source spans without requiring name or type resolution.");
  private static readonly Option<bool> IncludeSourceFacts = new("--include-source-facts",
    "Wrap definitions and resolved source structure in a JSON document.");
  private static readonly Option<bool> IncludeSemanticFacts = new("--include-semantic-facts",
    "Include deterministic source and definition semantic fingerprints.");
  private static readonly Option<bool> IncludeStatements = new("--include-statements",
    "Report resolved statement spans, kinds, and direct call targets.");

  static DefinitionAnalysisCommand() {
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(SpansOnly, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeSourceFacts, OptionScope.Cli);
    OptionRegistry.RegisterOption(IncludeSemanticFacts, OptionScope.Cli);
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
      return await ExecuteSpansOnly(options);
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();
    var analysisSourceUris = AnalysisSourceUris(await compilation.Compilation.RootFiles);
    var resolution = await compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      return await compilation.GetAndReportExitCode();
    }

    var includeSourceFacts = options.Get(IncludeSourceFacts) || options.Get(IncludeSemanticFacts);
    var results = includeSourceFacts
      ? (object)DefinitionAnalysis.AnalyzeDocument(
        resolution.ResolvedProgram,
        analysisSourceUris,
        options.Get(IncludeStatements),
        options.Get(IncludeSemanticFacts))
      : DefinitionAnalysis.Analyze(
        resolution.ResolvedProgram,
        analysisSourceUris,
        options.Get(IncludeStatements));
    var json = JsonSerializer.Serialize(results, new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      WriteIndented = true
    });
    await options.OutputWriter.Code(json + "\n");

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

  private static IReadOnlySet<Uri> AnalysisSourceUris(IEnumerable<DafnyFile> rootFiles) {
    return rootFiles
      .Where(file =>
        !file.ShouldNotVerify &&
        (file.Uri == DafnyFile.StdInUri ||
         file.Uri.IsFile && file.Extension == DafnyFile.DafnyFileExtension))
      .Select(file => file.Uri)
      .ToHashSet();
  }
}
