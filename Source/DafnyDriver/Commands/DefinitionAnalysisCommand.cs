#nullable enable
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
    SpansOnly
  }.Concat(DafnyCommands.ConsoleOutputOptions)
    .Concat(DafnyCommands.ResolverOptions);

  private static readonly Option<string> Format = new("--format", () => "json",
    "Output format. Only 'json' is currently supported.");
  private static readonly Option<bool> SpansOnly = new("--spans-only",
    "Report parse-level source spans without requiring name or type resolution.");

  static DefinitionAnalysisCommand() {
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(SpansOnly, OptionScope.Cli);
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
      return await ExecuteSpansOnly(options);
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();
    var resolution = await compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      return await compilation.GetAndReportExitCode();
    }

    var results = DefinitionAnalysis.Analyze(resolution.ResolvedProgram);
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

    var json = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeSpans(program), new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      WriteIndented = true
    });
    await options.OutputWriter.Code(json + "\n");
    return (int)ExitValue.SUCCESS;
  }
}
