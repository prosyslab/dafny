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
  public static async Task<ContractCompileResult> CompileAsync(ContractCompileRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    if (request.SchemaVersion != ContractJson.SchemaVersion) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.InvalidInput, "Unsupported compile schema version.");
    }
    ContractHarnessBuilder.ValidateRequest(request.Test);
    options.Backend = new CsharpBackend(options);
    options.Set(CommonOptionBag.OptimizeErasableDatatypeWrapper, false);
    Directory.CreateDirectory(request.OutputDirectory);
    // Diagnostic builds use only the already-installed compiler/runtime packages.
    // Missing cached prerequisites remain build errors; no package source is contacted.
    await File.WriteAllTextAsync(Path.Combine(request.OutputDirectory, "NuGet.Config"),
      "<configuration><packageSources><clear /></packageSources></configuration>", cancellationToken);
    await File.WriteAllTextAsync(Path.Combine(request.OutputDirectory, "Directory.Build.props"),
      "<Project><PropertyGroup><UseSharedCompilation>false</UseSharedCompilation></PropertyGroup></Project>", cancellationToken);
    var prepared = await ParseAsync(request.Test, options, cancellationToken);
    var sources = ContractHarnessBuilder.RuntimeSources(prepared, request.Test);
    var source = ContractSourceSnapshot.Find(sources, prepared.Method.Origin.Uri).Content;
    var observationPath = Path.Combine(request.OutputDirectory, "observations.jsonl");
    await File.WriteAllTextAsync(observationPath, "", cancellationToken);
    var bridgePath = Path.Combine(request.OutputDirectory, "ContractBridge.cs");
    await File.WriteAllTextAsync(bridgePath, ContractStubRuntime.BridgeSource(observationPath, prepared), cancellationToken);
    return await CompileSourcesAsync(sources, source, request.Test.Dependencies, request.OutputDirectory,
      bridgePath, observationPath, prepared.Location,
      ContractHarnessBuilder.QualifiedDiagnosticName(prepared, ContractHarnessBuilder.MainName), options, cancellationToken);
  }

  public static async Task<ContractCompileResult> CompileRuntimeAsync(ContractRuntimeTransformation transformation,
    ContractRuntimeCampaignRequest request, string outputDirectory, DafnyOptions options, CancellationToken cancellationToken) {
    Directory.CreateDirectory(outputDirectory);
    await File.WriteAllTextAsync(Path.Combine(outputDirectory, "NuGet.Config"),
      "<configuration><packageSources><clear /></packageSources></configuration>", cancellationToken);
    await File.WriteAllTextAsync(Path.Combine(outputDirectory, "Directory.Build.props"),
      "<Project><PropertyGroup><UseSharedCompilation>false</UseSharedCompilation></PropertyGroup></Project>", cancellationToken);
    options.Set(CommonOptionBag.OptimizeErasableDatatypeWrapper, false);
    var observationPath = Path.Combine(outputDirectory, "observations.jsonl");
    var bridgePath = Path.Combine(outputDirectory, "ContractBridge.cs");
    await File.WriteAllTextAsync(bridgePath,
      ContractRuntimeInstrumentation.BridgeSource(observationPath, transformation), cancellationToken);
    var source = ContractSourceSnapshot.Find(transformation.Sources, transformation.Prepared.Method.Origin.Uri).Content;
    return await CompileSourcesAsync(transformation.Sources, source, request.Dependencies, outputDirectory,
      bridgePath, observationPath, transformation.Prepared.Location, transformation.MainName, options, cancellationToken);
  }

  private static async Task<ContractCompileResult> CompileSourcesAsync(IReadOnlyList<ContractSource> sources,
    string source, IReadOnlyList<ContractDependency> sourceDependencies, string outputDirectory,
    string bridgePath, string observationPath, ContractSourceLocation location, string mainName,
    DafnyOptions options, CancellationToken cancellationToken) {
    var dependencies = new List<string> { bridgePath };
    var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "ContractBridge.cs", "diagnostic.dll", "DafnyRuntime.dll" };
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
    await File.WriteAllTextAsync(diagnosticPath, source, cancellationToken);
    options.MainMethod = mainName;
    options.Compile = true;
    options.RunAfterCompile = false;
    options.ForceCompile = true;
    options.Backend = new CsharpBackend(options);
    options.SpillTargetCode = 1;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken);
    if (reporter.ErrorCount > 0) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)), Entry: location);
    }
    if (!SinglePassCodeGenerator.HasMain(program, out var main) || main.FullDafnyName != options.MainMethod) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not select the diagnostic main.", Entry: location);
    }
    using var compilerOutput = new StringWriter();
    var compilerWriter = new DafnyOptions(TextReader.Null, compilerOutput, compilerOutput).OutputWriter;
    if (!await SynchronousCliCompilation.CompileDafnyProgram(program, diagnosticPath,
          new ReadOnlyCollection<string>(dependencies), true, compilerWriter)) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Diagnostic compilation failed: " + compilerOutput + "\n" +
        string.Join("\n", reporter.AllMessages.Where(message => message.Level == ErrorLevel.Error).Select(message => message.Message)), Entry: location);
    }
    var assemblyPath = Path.Combine(outputDirectory, "diagnostic.dll");
    if (!File.Exists(assemblyPath) || !File.Exists(Path.Combine(outputDirectory, "diagnostic.runtimeconfig.json"))) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not emit an executable assembly and runtime configuration.", Entry: location);
    }
    var assemblyHash = Convert.ToHexString(SHA256.HashData(await File.ReadAllBytesAsync(assemblyPath, cancellationToken))).ToLowerInvariant();
    return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Passed, "Compiled diagnostic copy.",
      assemblyPath, assemblyHash, observationPath, location);
  }

  public static async Task<ContractPreparedProgram> ParseAsync(ContractTestRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    ContractHarnessBuilder.ValidateRequest(request);
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, cancellationToken);
    if (reporter.ErrorCount > 0) {
      throw new ArgumentException(string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    return ContractHarnessBuilder.Prepare(program, request);
  }
}
