#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class WpContextCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Format,
    TargetLine,
    TargetColumn,
    CodeFromLine,
    CodeToLine
  }.Concat(DafnyCommands.ConsoleOutputOptions)
    .Concat(DafnyCommands.ResolverOptions);

  private static readonly Option<string> Format = new("--format", () => "json",
    "Output format. Only 'json' is currently supported.");
  private static readonly Option<int> TargetLine = new("--target-line",
    "1-based line containing the target assert statement.");
  private static readonly Option<int> TargetColumn = new("--target-column", () => 1,
    "1-based column inside the target assert statement.");
  private static readonly Option<int> CodeFromLine = new("--code-from-line",
    "1-based first line of the code prefix P.");
  private static readonly Option<int> CodeToLine = new("--code-to-line",
    "1-based last line of the code prefix P.");

  static WpContextCommand() {
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(TargetLine, OptionScope.Cli);
    OptionRegistry.RegisterOption(TargetColumn, OptionScope.Cli);
    OptionRegistry.RegisterOption(CodeFromLine, OptionScope.Cli);
    OptionRegistry.RegisterOption(CodeToLine, OptionScope.Cli);
  }

  public static Command Create() {
    var result = new Command("wp-context",
      "Report AST-derived context for weakest-precondition candidate generation.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(Format) != "json") {
      await options.ErrorWriter.WriteLineAsync("wp-context only supports --format json.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    if (options.CliRootSourceUris.Count != 1 || !options.CliRootSourceUris[0].IsFile) {
      await options.ErrorWriter.WriteLineAsync("wp-context requires exactly one Dafny source file.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var sourcePath = options.CliRootSourceUris[0].LocalPath;
    string sourceText;
    try {
      sourceText = await File.ReadAllTextAsync(sourcePath);
    } catch (IOException exception) {
      await options.ErrorWriter.WriteLineAsync($"could not read source file: {exception.Message}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();
    var resolution = await compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      return await compilation.GetAndReportExitCode();
    }

    try {
      var result = WpContextAnalysis.Analyze(
        resolution.ResolvedProgram,
        sourcePath,
        sourceText,
        options.Get(TargetLine),
        options.Get(TargetColumn),
        options.Get(CodeFromLine),
        options.Get(CodeToLine),
        options);
      var json = JsonSerializer.Serialize(result, new JsonSerializerOptions {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
        WriteIndented = true
      });
      await options.OutputWriter.Code(json + "\n");
    } catch (WpContextAnalysisException exception) {
      await options.ErrorWriter.WriteLineAsync(exception.Message);
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    return await compilation.GetAndReportExitCode();
  }
}
