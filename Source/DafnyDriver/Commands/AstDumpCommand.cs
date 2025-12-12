using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny;

public static class AstDumpCommand {

  static AstDumpCommand() { }

  public static IEnumerable<Option> Options => new Option[] { }.Concat(DafnyCommands.ParserOptions);

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
    var (code, dafnyFiles, _) = await SynchronousCliCompilation.GetDafnyFiles(options);
    if (code != 0) {
      return code;
    }
    var errorWriter = options.ErrorWriter;
    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);
    string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";

    var exitValue = ExitValue.SUCCESS;
    Contract.Assert(dafnyFiles.Count > 0 || options.SourceFolders.Count > 0);
    var folderFiles = options.SourceFolders.Select(folderPath => GetFilesForFolder(options, folderPath)).SelectMany(x => x);
    dafnyFiles = dafnyFiles.Concat(folderFiles).ToList();

    var failedToParseFiles = new List<string>();
    var emptyFiles = new List<string>();

    foreach (var file in dafnyFiles) {
      var dafnyFile = file;
      var content = dafnyFile.GetContent();
      var originalText = await content.Reader.ReadToEndAsync();
      content.Reader.Close(); // Manual closing because we want to overwrite
      dafnyFile.GetContent = () => content with { Reader = new StringReader(originalText) };
      // Might not be totally optimized but let's do that for now
      var (dafnyProgram, err) = await DafnyMain.Parse(new List<DafnyFile> { dafnyFile }, programName, options);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        await errorWriter.WriteLineAsync(err);
        failedToParseFiles.Add(dafnyFile.BaseName);
      } else {
        var firstToken = dafnyProgram.GetFirstTokenForUri(file.Uri);
        var result = originalText;
        TextWriter tw = Console.Out;
        JsonNode json = new JsonObject();
        AstPrinter pr = new AstPrinter(tw, json, dafnyProgram.Options);
        pr.PrintProgram(dafnyProgram, false);
        if (firstToken != null) {
          result = Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, file.Uri));
        } else {
          // TODO: is this necessary? there already is a warning about files containing no code
          if (options.Verbose) {
            await options.ErrorWriter.WriteLineAsync(dafnyFile.BaseName + " was empty.");
          }

          emptyFiles.Add(options.GetPrintPath(dafnyFile.FilePath));
        }
      }
    }
    return exitValue;
  }

  public static IEnumerable<DafnyFile> GetFilesForFolder(DafnyOptions options, string folderPath) {
    return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
      .Select(name => DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance,
        new ConsoleErrorReporter(options), options, new Uri(name), Token.Cli));
  }
}
