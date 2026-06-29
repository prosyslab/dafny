#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class MethodSegmentContextCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Format,
    MethodName
  }.Concat(DafnyCommands.ConsoleOutputOptions)
    .Concat(DafnyCommands.ResolverOptions);

  private static readonly Option<string> Format = new("--format", () => "json",
    "Output format. Only 'json' is currently supported.");
  private static readonly Option<string> MethodName = new("--method-name",
    "Method name or full Dafny name to inspect.");

  static MethodSegmentContextCommand() {
    OptionRegistry.RegisterOption(Format, OptionScope.Cli);
    OptionRegistry.RegisterOption(MethodName, OptionScope.Cli);
  }

  public static Command Create() {
    var result = new Command("method-segment-context",
      "Report AST-derived method body context for Hoare segment planning.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(Format) != "json") {
      await options.ErrorWriter.WriteLineAsync("method-segment-context only supports --format json.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    if (options.CliRootSourceUris.Count != 1 || !options.CliRootSourceUris[0].IsFile) {
      await options.ErrorWriter.WriteLineAsync("method-segment-context requires exactly one Dafny source file.");
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
      var result = MethodSegmentContextAnalysis.Analyze(
        resolution.ResolvedProgram,
        sourcePath,
        sourceText,
        options.Get(MethodName));
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
