using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

public static class AstDumpCommand {

  public static readonly Option<FileInfo> Output = new("--output",
    "Path to the JSON file that will receive the resolved AST dump");

  static AstDumpCommand() {
    OptionRegistry.RegisterOption(Output, OptionScope.Cli);
  }

  public static IEnumerable<Option> Options => new Option[] { Output }
    .Concat(DafnyCommands.ResolverOptions)
    .Concat(DafnyCommands.ConsoleOutputOptions);

  public static Command Create() {
    var result = new Command("ast-dump", @"Ast dump the dafny file.");
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, _) => {
      options.AllowSourceFolders = true;
      var exitValue = await DoDumping(options);
      return (int)exitValue;
    });

    return result;
  }

  public static async Task<ExitValue> DoDumping(DafnyOptions options) {
    options.AllowSourceFolders = true;
    var outputFile = options.Get(Output) ?? GetDefaultOutputFile(options);

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    var exitValue = await compilation.GetAndReportExitValue();
    if (resolution is not { HasErrors: false }) {
      return exitValue;
    }

    try {
      if (outputFile.DirectoryName is { Length: > 0 }) {
        Directory.CreateDirectory(outputFile.DirectoryName);
      }

      var json = ResolvedAstJsonSerializer.Serialize(resolution.ResolvedProgram);
      var serialized = json.ToJsonString(new JsonSerializerOptions { WriteIndented = true });
      await File.WriteAllTextAsync(outputFile.FullName, serialized);
      if (options.Verbose || options.Get(Output) == null) {
        await options.OutputWriter.Status($"Resolved AST JSON written to {outputFile.FullName}");
      }
      return exitValue;
    } catch (Exception exception) {
      await options.OutputWriter.Status($"Failed to write AST dump: {exception.Message}");
      return ExitValue.DAFNY_ERROR;
    }
  }

  private static FileInfo GetDefaultOutputFile(DafnyOptions options) {
    if (options.CliRootSourceUris.Count == 1 && options.CliRootSourceUris[0].IsFile) {
      var inputPath = options.CliRootSourceUris[0].LocalPath;
      var directory = Path.GetDirectoryName(inputPath) ?? Directory.GetCurrentDirectory();
      var fileNameWithoutExtension = Path.GetFileNameWithoutExtension(inputPath);
      return new FileInfo(Path.Combine(directory, fileNameWithoutExtension + ".ast.json"));
    }

    return new FileInfo(Path.Combine(Directory.GetCurrentDirectory(), "dafny-ast.json"));
  }
}
