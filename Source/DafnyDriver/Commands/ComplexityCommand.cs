#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Threading.Tasks;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class ComplexityCommand {
  public static IEnumerable<Option> Options => new Option[] {
    MaxScore
  }.Concat(DafnyCommands.ConsoleOutputOptions).
    Concat(DafnyCommands.ResolverOptions);

  static ComplexityCommand() {
    OptionRegistry.RegisterOption(MaxScore, OptionScope.Cli);
  }

  private static readonly Option<uint?> MaxScore = new("--max-score", () => null,
    "Fail if any executable method or function-by-method body has a complexity score greater than this value.");

  public static Command Create() {
    var result = new Command("complexity", "Report implementation-focused complexity scores for Dafny executable bodies.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution == null || resolution.HasErrors) {
      return await compilation.GetAndReportExitCode();
    }

    var results = ImplementationComplexity.Analyze(resolution.ResolvedProgram);
    await using (var writer = options.OutputWriter.StatusWriter()) {
      foreach (var result in results) {
        await writer.WriteLineAsync(
          $"{result.Origin.OriginToString(options)}: {result.Kind} {result.FullDafnyName} score={result.Score}");
      }
    }

    var maxScore = options.Get(MaxScore);
    if (maxScore is { } limit) {
      var failures = results.Where(result => result.Score > limit).ToList();
      if (failures.Any()) {
        await using var writer = options.OutputWriter.StatusWriter();
        foreach (var failure in failures) {
          await writer.WriteLineAsync(
            $"complexity score exceeded: {failure.Kind} {failure.FullDafnyName} score={failure.Score} max={limit}");
        }

        return (int)ExitValue.DAFNY_ERROR;
      }
    }

    return await compilation.GetAndReportExitCode();
  }
}
