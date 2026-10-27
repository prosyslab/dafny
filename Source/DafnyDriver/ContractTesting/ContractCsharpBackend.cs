#nullable enable
using System;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

internal sealed class ContractCsharpBackend : CsharpBackend {
  private Action<string, string>? phaseObserver;
  private CancellationToken cancellationToken;

  internal ContractCsharpBackend(DafnyOptions options) : base(options) {
  }

  internal void ObserveCompilationPhases(Action<string, string>? observer, CancellationToken token) {
    phaseObserver = observer;
    cancellationToken = token;
  }

  internal string ProjectFileForTesting(string outputType, string sourcePath,
    ReadOnlyCollection<string> otherFileNames) => CreateProjectFile(outputType, sourcePath, otherFileNames);

  protected override bool EmitTranslationRecord => false;
  protected override bool IncludeFrameworkPackageReferences => false;

  protected override SinglePassCodeGenerator CreateCodeGenerator() =>
    new ContractCsharpCodeGenerator(Options, Reporter!);

  protected override Task WriteTargetProgram(string sourcePath, string source) =>
    MeasureAsync("target_source_write", () => base.WriteTargetProgram(sourcePath, source));

  protected override Task WriteProjectFile(string projectPath, string project) =>
    MeasureAsync("target_project_write", () => base.WriteProjectFile(projectPath, project));

  protected override Task<int> RunDotnetBuild(ProcessStartInfo startInfo, TextWriter outputWriter,
    TextWriter errorWriter) =>
    MeasureAsync("dotnet_build", () => base.RunDotnetBuild(startInfo, outputWriter, errorWriter));

  private Task MeasureAsync(string phase, Func<Task> operation) {
    cancellationToken.ThrowIfCancellationRequested();
    return ContractPhaseRecorder.MeasureAsync(phaseObserver, phase, cancellationToken, operation);
  }

  private Task<T> MeasureAsync<T>(string phase, Func<Task<T>> operation) {
    cancellationToken.ThrowIfCancellationRequested();
    return ContractPhaseRecorder.MeasureAsync(phaseObserver, phase, cancellationToken, operation);
  }

  private sealed class ContractCsharpCodeGenerator : CsharpCodeGenerator {
    internal ContractCsharpCodeGenerator(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
    }

    protected override bool EmitSerializedDafnySource => false;
  }
}
