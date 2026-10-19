using System.CommandLine;
using System.CommandLine.IO;
using System.CommandLine.Parsing;
using System.Reactive;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging.Abstractions;

namespace DafnyDriver.Test;

public class InternalErrorExitTests {
  // An unexpected handler exception retains its diagnostic and receives the native internal-error code.
  [Fact]
  public async Task HandlerExceptionHasDistinctExitCode() {
    var command = new RootCommand();
    command.SetHandler(() => throw new InvalidOperationException("injected compiler failure"));
    var console = new TestConsole();

    var exitCode = await DafnyNewCli.CreateParser(command).InvokeAsync(Array.Empty<string>(), console);

    Assert.Equal((int)ExitValue.INTERNAL_ERROR, exitCode);
    Assert.Contains("injected compiler failure", console.Error.ToString());
  }

  // A malformed command line remains a preprocessing rejection rather than an internal exception.
  [Fact]
  public async Task InvalidCommandLineKeepsPreprocessingExitCode() {
    var console = new TestConsole();
    var exitCode = await DafnyNewCli.CreateParser(new RootCommand()).InvokeAsync(["--unknown-option"], console);

    Assert.Equal((int)ExitValue.PREPROCESSING_ERROR, exitCode);
  }

  // A verifier exception terminates mutation scheduling and outranks candidate diagnostics at the exit boundary.
  [Fact]
  public async Task InternalVerificationErrorStopsMutationsWithoutCompletion() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AllowWarnings, true);
    options.Set(MeasureComplexityCommand.Options.OfType<Option<uint>>().Single(option => option.HasAlias("--mutations")), 3U);
    var uri = new Uri("file:///workspace/tmp/dafny-internal-exit-contract/injected.dfy");
    options.CliRootSourceUris.Add(uri);
    var fileSystem = new InMemoryFileSystem(new Dictionary<Uri, string> {
      [uri] = "method Check() { assert true; }"
    });
    var verifier = new FailingVerifier();
    var telemetry = new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance);
    var loader = new TextDocumentLoader(NullLogger<ITextDocumentLoader>.Instance,
      new DafnyLangParser(options, fileSystem, telemetry,
        NullLogger<DafnyLangParser>.Instance, NullLogger<CachingParser>.Instance),
      new DafnyLangSymbolResolver(NullLogger<DafnyLangSymbolResolver>.Instance,
        NullLogger<CachingResolver>.Instance, telemetry));
    var compilation = new CliCompilation((engine, input) =>
      new Compilation(NullLogger<Compilation>.Instance, fileSystem, loader, verifier, engine, input), options);
    using var ownedCompilation = compilation.Compilation;
    compilation.Start();
    var resolution = await compilation.Resolution.WaitAsync(TimeSpan.FromSeconds(15));
    Assert.NotNull(resolution);
    Assert.False(resolution!.HasErrors);

    var results = new List<CanVerifyResult>();
    var errors = new List<Exception>();
    var completions = 0;
    var observer = Observer.Create<CanVerifyResult>(results.Add, errors.Add, () => completions++);
    await MeasureComplexityCommand.RunVerificationIterations(options, compilation, observer)
      .WaitAsync(TimeSpan.FromSeconds(15));

    Assert.Equal(1, verifier.Calls);
    Assert.Empty(results);
    Assert.Same(verifier.Failure, Assert.Single(errors));
    Assert.Equal(0, completions);
    compilation.Compilation.Reporter.Error(MessageSource.Project, Microsoft.Dafny.Token.Cli, "candidate project error");
    Assert.Equal(ExitValue.INTERNAL_ERROR, await compilation.GetAndReportExitValue());
  }

  private sealed class FailingVerifier : IProgramVerifier {
    public int Calls { get; private set; }
    public InvalidOperationException Failure { get; } = new("injected verifier failure");

    public Task<IReadOnlyList<IVerificationTask>> GetVerificationTasksAsync(ExecutionEngine engine,
      ResolutionResult resolution, ModuleDefinition moduleDefinition, CancellationToken cancellationToken) {
      Calls++;
      throw Failure;
    }
  }
}
