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
    var dependencies = new List<string> { bridgePath };
    var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "ContractBridge.cs", "diagnostic.dll", "DafnyRuntime.dll" };
    foreach (var dependency in request.Test.Dependencies ?? []) {
      var name = Path.GetFileName(dependency.Path);
      if (Path.GetExtension(name) is not (".cs" or ".dll") || !names.Add(name)) {
        throw new ArgumentException("Unsupported or conflicting dependency file name: " + name);
      }
      var content = await File.ReadAllBytesAsync(dependency.Path, cancellationToken);
      if (Convert.ToHexString(SHA256.HashData(content)).ToLowerInvariant() != dependency.Sha256) {
        throw new ArgumentException("Dependency hash mismatch: " + name);
      }
      var staged = Path.Combine(request.OutputDirectory, name);
      await File.WriteAllBytesAsync(staged, content, cancellationToken);
      dependencies.Add(staged);
    }
    var diagnosticPath = Path.Combine(request.OutputDirectory, "diagnostic.dfy");
    await File.WriteAllTextAsync(diagnosticPath, source, cancellationToken);
    options.MainMethod = ContractHarnessBuilder.QualifiedDiagnosticName(prepared, ContractHarnessBuilder.MainName);
    options.Compile = true;
    options.RunAfterCompile = false;
    options.ForceCompile = true;
    options.Backend = new CsharpBackend(options);
    options.SpillTargetCode = 1;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken);
    if (reporter.ErrorCount > 0) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)), Entry: prepared.Location);
    }
    if (!SinglePassCodeGenerator.HasMain(program, out var main) || main.FullDafnyName != options.MainMethod) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not select the diagnostic main.", Entry: prepared.Location);
    }
    if (!await SynchronousCliCompilation.CompileDafnyProgram(program, diagnosticPath,
          new ReadOnlyCollection<string>(dependencies), true)) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Diagnostic compilation failed: " + string.Join("\n", reporter.AllMessages.Select(message => message.Message)), Entry: prepared.Location);
    }
    var assemblyPath = Path.Combine(request.OutputDirectory, "diagnostic.dll");
    if (!File.Exists(assemblyPath) || !File.Exists(Path.Combine(request.OutputDirectory, "diagnostic.runtimeconfig.json"))) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler did not emit an executable assembly and runtime configuration.", Entry: prepared.Location);
    }
    var assemblyHash = Convert.ToHexString(SHA256.HashData(await File.ReadAllBytesAsync(assemblyPath, cancellationToken))).ToLowerInvariant();
    return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Passed, "Compiled diagnostic copy.",
      assemblyPath, assemblyHash, observationPath, prepared.Location);
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
