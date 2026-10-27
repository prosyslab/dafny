using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using DafnyTestGeneration;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public static class ContractCompilerWorker {
  internal sealed record CompilationResolution(ContractRuntimeTransformation Transformation, Program Program,
    DafnyOptions Options, BatchErrorReporter Reporter);

  internal sealed record CompilationInput(Program Program, Method Main);

  private sealed record CompilationStaging(string DiagnosticPath, string ObservationPath,
    ReadOnlyCollection<string> Dependencies);

  internal static void ApplyCompilationOptions(DafnyOptions options, string mainName) {
    options.Set(CommonOptionBag.OptimizeErasableDatatypeWrapper, false);
    options.MainMethod = mainName;
    options.Compile = true;
    options.RunAfterCompile = false;
    options.ForceCompile = true;
    options.IncludeRuntime = false;
    options.Backend = new ContractCsharpBackend(options);
    options.SpillTargetCode = 1;
  }

  internal static async Task<CompilationResolution> ResolveRuntimeAsync(ContractRuntimeTransformation transformation,
    DafnyOptions sharedOptions, CancellationToken cancellationToken, Action<string, string>? phaseObserver = null) {
    cancellationToken.ThrowIfCancellationRequested();
    var options = new DafnyOptions(sharedOptions);
    ApplyCompilationOptions(options, transformation.MainName);
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, transformation.Sources, cancellationToken,
      phaseObserver: phaseObserver);
    return new CompilationResolution(transformation, program, options, reporter);
  }

  internal static CompilationInput? PrepareCompilation(CompilationResolution resolution,
    CancellationToken cancellationToken, out ContractCompileResult? rejection) {
    cancellationToken.ThrowIfCancellationRequested();
    var location = resolution.Transformation.Prepared.Location;
    if (!ReferenceEquals(resolution.Program.Options, resolution.Options) ||
        !ReferenceEquals(resolution.Program.Reporter, resolution.Reporter) ||
        resolution.Options.MainMethod != resolution.Transformation.MainName ||
        resolution.Options.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper) ||
        !resolution.Options.Compile || resolution.Options.RunAfterCompile || !resolution.Options.ForceCompile ||
        resolution.Options.IncludeRuntime || resolution.Options.Backend is not ContractCsharpBackend ||
        resolution.Options.SpillTargetCode != 1) {
      rejection = new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler resolution state is inconsistent.", Entry: location);
      return null;
    }
    if (resolution.Reporter.ErrorCount > 0) {
      rejection = new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        Diagnostics(resolution.Reporter), Entry: location);
      return null;
    }
    if (!SinglePassCodeGenerator.HasMain(resolution.Program, out var main) ||
        main.FullDafnyName != resolution.Options.MainMethod) {
      rejection = new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not select the diagnostic main.", Entry: location);
      return null;
    }
    rejection = null;
    return new CompilationInput(resolution.Program, main);
  }

  internal static async Task<ContractCompileResult> CompileRuntimeAsync(CompilationResolution resolution,
    ContractRuntimeCampaignRequest request, string outputDirectory, CancellationToken cancellationToken,
    Action<string, string>? phaseObserver = null) {
    var input = PrepareCompilation(resolution, cancellationToken, out var rejection);
    if (input == null) {
      return rejection!;
    }
    var backend = (ContractCsharpBackend)resolution.Options.Backend;
    backend.ObserveCompilationPhases(phaseObserver, cancellationToken);
    CompilationStaging staging;
    try {
      staging = await ContractPhaseRecorder.MeasureAsync(phaseObserver, "staging", cancellationToken,
        () => StageAsync(resolution.Transformation, request.Dependencies, outputDirectory, cancellationToken));
    } catch (ArgumentException error) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Diagnostic dependency staging failed: " + error.Message,
        Entry: resolution.Transformation.Prepared.Location);
    }
    cancellationToken.ThrowIfCancellationRequested();
    using var compilerOutput = new StringWriter();
    var compilerWriter = new DafnyOptions(TextReader.Null, compilerOutput, compilerOutput).OutputWriter;
    var compiled = await ContractPhaseRecorder.MeasureAsync(phaseObserver, "target_compile", cancellationToken,
      () => SynchronousCliCompilation.CompileDafnyProgram(input.Program, staging.DiagnosticPath,
        staging.Dependencies, true, compilerWriter,
        new SynchronousCliCompilation.CompilationSettings(phaseObserver, cancellationToken, false)));
    cancellationToken.ThrowIfCancellationRequested();
    if (!compiled) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Diagnostic compilation failed: " + compilerOutput + "\n" +
        string.Join("\n", resolution.Reporter.AllMessages.Where(message => message.Level == ErrorLevel.Error)
          .Select(message => message.Message)), Entry: resolution.Transformation.Prepared.Location);
    }
    var assemblyPath = Path.Combine(outputDirectory, "diagnostic.dll");
    if (!File.Exists(assemblyPath) || !File.Exists(Path.Combine(outputDirectory, "diagnostic.runtimeconfig.json"))) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not emit an executable assembly and runtime configuration.",
        Entry: resolution.Transformation.Prepared.Location);
    }
    var assemblyHash = Convert.ToHexString(
      SHA256.HashData(await File.ReadAllBytesAsync(assemblyPath, cancellationToken))).ToLowerInvariant();
    return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Passed, "Compiled diagnostic copy.",
      assemblyPath, assemblyHash, staging.ObservationPath, resolution.Transformation.Prepared.Location);
  }

  private static async Task<CompilationStaging> StageAsync(ContractRuntimeTransformation transformation,
    IReadOnlyList<ContractDependency>? sourceDependencies, string outputDirectory,
    CancellationToken cancellationToken) {
    cancellationToken.ThrowIfCancellationRequested();
    Directory.CreateDirectory(outputDirectory);
    await File.WriteAllTextAsync(Path.Combine(outputDirectory, "NuGet.Config"),
      "<configuration><packageSources><clear /></packageSources></configuration>", cancellationToken);
    await File.WriteAllTextAsync(Path.Combine(outputDirectory, "Directory.Build.props"),
      "<Project><PropertyGroup><UseSharedCompilation>false</UseSharedCompilation></PropertyGroup></Project>",
      cancellationToken);
    var observationPath = Path.Combine(outputDirectory, "observations.jsonl");
    var runtimePath = Path.Combine(outputDirectory, "ContractRuntime.cs");
    await File.WriteAllTextAsync(runtimePath,
      ContractRuntimeInstrumentation.RuntimeSource(observationPath, transformation), cancellationToken);
    var dependencies = new List<string> { runtimePath };
    var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "ContractRuntime.cs", "diagnostic.dll", "DafnyRuntime.dll" };
    foreach (var dependency in sourceDependencies ?? []) {
      var name = Path.GetFileName(dependency.Path);
      if (Path.GetExtension(name) is not (".cs" or ".dll") || !names.Add(name)) {
        throw new ArgumentException("Unsupported or conflicting dependency file name: " + name);
      }
      var content = await File.ReadAllBytesAsync(dependency.Path, cancellationToken);
      if (Convert.ToHexString(SHA256.HashData(content)).ToLowerInvariant() != dependency.Sha256) {
        throw new ArgumentException("Dependency hash mismatch: " + name);
      }
      var staged = Path.Combine(outputDirectory, name);
      await File.WriteAllBytesAsync(staged, content, cancellationToken);
      dependencies.Add(staged);
    }
    var diagnosticPath = Path.Combine(outputDirectory, "diagnostic.dfy");
    var source = ContractSourceSnapshot.Find(transformation.Sources, transformation.Prepared.Method.Origin.Uri).Content;
    await File.WriteAllTextAsync(diagnosticPath, source, cancellationToken);
    return new CompilationStaging(diagnosticPath, observationPath,
      new ReadOnlyCollection<string>(dependencies));
  }

  private static string Diagnostics(BatchErrorReporter reporter) =>
    string.Join("\n", reporter.AllMessages.Select(message => message.Message));
}
