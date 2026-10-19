using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;

namespace Microsoft.Dafny;

static class MeasureComplexityCommand {
  public static IEnumerable<Option> Options => new Option[] {
    Mutations,
    RandomSeed,
    VerifyCommand.FilterSymbol,
    VerifyCommand.FilterPosition,
  }.Concat(DafnyCommands.VerificationOptions).
    Concat(DafnyCommands.ResolverOptions).
    Concat(DafnyCommands.ConsoleOutputOptions);

  static MeasureComplexityCommand() {
    DafnyOptions.RegisterLegacyBinding(Mutations, (o, v) => o.RandomizeVcIterations = (int)v);
    DafnyOptions.RegisterLegacyBinding(RandomSeed, (o, v) => o.RandomSeed = (int)v);

    OptionRegistry.RegisterOption(Mutations, OptionScope.Cli);
    OptionRegistry.RegisterOption(RandomSeed, OptionScope.Cli);
  }

  private static readonly Option<uint> RandomSeed = new("--random-seed", () => 0U,
    $"Turn on randomization of the input that Dafny passes to the SMT solver and turn on randomization in the SMT solver itself. Certain Dafny proofs are complex in the sense that changes to the proof that preserve its meaning may cause its verification result to change. This option simulates meaning-preserving changes to the proofs without requiring the user to actually make those changes. The proof changes are renaming variables and reordering declarations in the SMT input passed to the solver, and setting solver options that have similar effects.");

  private static readonly Option<uint> Mutations = new("--mutations", () => 1U,
    $"Attempt to verify each proof n times with n random seeds, each seed derived from the previous one. {RandomSeed.Name} can be used to specify the first seed, which will otherwise be 0.") {
    ArgumentHelpName = "n"
  };

  public static Command Create() {
    var result = new Command("measure-complexity", "(Experimental) Measure the complexity of verifying the program.");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in Options) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => Execute(options));
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;
    if (resolution != null) {
      Subject<CanVerifyResult> verificationResults = new();

      VerifyCommand.ReportVerificationDiagnostics(compilation, verificationResults);
      var proofDependenciesReported = VerifyCommand.ReportProofDependencies(compilation, resolution, verificationResults);
      var verificationResultsLogged = VerifyCommand.LogVerificationResults(compilation, resolution, verificationResults);

      await RunVerificationIterations(options, compilation, verificationResults);
      await verificationResultsLogged;
      await proofDependenciesReported;
    }

    return await compilation.GetAndReportExitCode();
  }

  internal static async Task RunVerificationIterations(DafnyOptions options, CliCompilation compilation,
    IObserver<CanVerifyResult> verificationResultsObserver) {
    int iterationSeed = (int)options.Get(RandomSeed);
    var random = new Random(iterationSeed);
    var iterations = (int)options.Get(Mutations);
    foreach (var mutation in Enumerable.Range(0, iterations)) {
      await options.OutputWriter.Status(
        $"Starting verification of mutation {mutation + 1}/{iterations} with seed {iterationSeed}");
      try {
        await foreach (var result in compilation.VerifyAllLazily(iterationSeed)) {
          verificationResultsObserver.OnNext(result);
        }
      } catch (Exception e) {
        verificationResultsObserver.OnError(e);
        return;
      }
      iterationSeed = random.Next();
    }
    verificationResultsObserver.OnCompleted();
  }
}
