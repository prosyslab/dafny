#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

public class CompilationResolutionTests {
  // Resolution uses a configured clone, compilation reuses its exact program, and late caller mutation stays explicit.
  [Fact]
  public async Task ConfiguresDetachedResolutionAndPreservesCallerUntilCompilationBoundary() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Main");
    var sharedOptions = MemoryOptions();
    sharedOptions.Set(CommonOptionBag.OptimizeErasableDatatypeWrapper, true);
    sharedOptions.DisableScopes = true;
    sharedOptions.DisallowIncludes = true;
    sharedOptions.MainMethod = "Caller.Main";
    sharedOptions.Compile = false;
    sharedOptions.RunAfterCompile = true;
    sharedOptions.ForceCompile = false;
    sharedOptions.IncludeRuntime = true;
    sharedOptions.SpillTargetCode = 4;
    var sharedBackend = sharedOptions.Backend;

    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, sharedOptions,
      CancellationToken.None);

    Assert.NotSame(sharedOptions, resolution.Options);
    Assert.Same(transformation, resolution.Transformation);
    Assert.Same(resolution.Options, resolution.Program.Options);
    Assert.Same(resolution.Reporter, resolution.Program.Reporter);
    Assert.IsType<ContractCsharpBackend>(resolution.Options.Backend);
    Assert.NotSame(sharedBackend, resolution.Options.Backend);
    Assert.False(resolution.Options.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper));
    Assert.Equal("M.Main", resolution.Options.MainMethod);
    Assert.True(resolution.Options.Compile);
    Assert.False(resolution.Options.RunAfterCompile);
    Assert.True(resolution.Options.ForceCompile);
    Assert.False(resolution.Options.IncludeRuntime);
    Assert.Equal((uint)1, resolution.Options.SpillTargetCode);
    Assert.True(resolution.Options.DisableScopes);
    Assert.False(resolution.Options.DisallowIncludes);
    Assert.True(sharedOptions.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper));
    Assert.Equal("Caller.Main", sharedOptions.MainMethod);
    Assert.False(sharedOptions.Compile);
    Assert.True(sharedOptions.RunAfterCompile);
    Assert.False(sharedOptions.ForceCompile);
    Assert.True(sharedOptions.IncludeRuntime);
    Assert.Equal((uint)4, sharedOptions.SpillTargetCode);
    Assert.True(sharedOptions.DisallowIncludes);
    Assert.Same(sharedBackend, sharedOptions.Backend);

    var input = ContractCompilerWorker.PrepareCompilation(resolution, CancellationToken.None, out var rejection);
    Assert.Null(rejection);
    Assert.NotNull(input);
    Assert.Same(resolution.Program, input!.Program);
    Assert.Same(input.Main, ContractCallableSelector.SelectMethod(resolution.Program, new("M.Main"),
      requireConcreteReceiver: false));

    ContractCompilerWorker.ApplyCompilationOptions(sharedOptions, transformation.MainName);
    Assert.False(sharedOptions.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper));
    Assert.Equal("M.Main", sharedOptions.MainMethod);
    Assert.IsType<ContractCsharpBackend>(sharedOptions.Backend);
    Assert.NotSame(sharedBackend, sharedOptions.Backend);
    Assert.False(sharedOptions.IncludeRuntime);
  }

  // The diagnostic backend omits source serialization, embedded runtime code, and translation-record output only for PBT.
  [Fact]
  public async Task DiagnosticBackendOmitsReusableCompilerArtifacts() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Main");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);

    var (diagnosticText, diagnosticFiles) = Render(resolution.Program,
      Assert.IsType<ContractCsharpBackend>(resolution.Options.Backend));

    Assert.DoesNotContain("DafnySourceAttribute(@\"", diagnosticText);
    Assert.DoesNotContain("public class DafnySourceAttribute", diagnosticText);
    Assert.Contains("class __CallToMain", diagnosticText);
    Assert.Contains("public static void Main(string[] args)", diagnosticText);
    Assert.Empty(diagnosticFiles);

    var ordinaryOptions = MemoryOptions();
    ordinaryOptions.Set(CommonOptionBag.OptimizeErasableDatatypeWrapper, false);
    ordinaryOptions.IncludeRuntime = true;
    var ordinaryBackend = new CsharpBackend(ordinaryOptions);
    ordinaryOptions.Backend = ordinaryBackend;
    var ordinaryReporter = new BatchErrorReporter(ordinaryOptions);
    var ordinaryProgram = await ContractSourceSnapshot.ParseAsync(ordinaryReporter, transformation.Sources,
      CancellationToken.None);
    Assert.Equal(0, ordinaryReporter.ErrorCount);

    var (ordinaryText, ordinaryFiles) = Render(ordinaryProgram, ordinaryBackend);

    Assert.Contains("DafnySourceAttribute(@\"", ordinaryText);
    Assert.Contains("public class DafnySourceAttribute", ordinaryText);
    Assert.Contains(ordinaryFiles, file => file.Filename.EndsWith("-cs.dtr", StringComparison.Ordinal));
  }

  // The diagnostic project keeps runtime and caller dependencies while relying on net8 framework references.
  [Fact]
  public void DiagnosticProjectUsesTrustedRuntimeWithoutRedundantPackages() {
    var diagnosticOptions = MemoryOptions();
    ContractCompilerWorker.ApplyCompilationOptions(diagnosticOptions, "M.Main");
    var diagnosticBackend = Assert.IsType<ContractCsharpBackend>(diagnosticOptions.Backend);
    var dependencies = new ReadOnlyCollection<string>([
      "/workspace/ContractRuntime.cs",
      "/workspace/NativeDependency.dll"
    ]);

    var diagnosticProject = diagnosticBackend.ProjectFileForTesting("Exe", "/workspace/diagnostic.cs",
      dependencies);

    Assert.Contains("<TargetFramework>net8.0</TargetFramework>", diagnosticProject);
    Assert.Contains("<Reference Include=\"DafnyRuntime\">", diagnosticProject);
    Assert.Contains("<Compile Include=\"/workspace/ContractRuntime.cs\" />", diagnosticProject);
    Assert.Contains("<Reference Include=\"NativeDependency\">", diagnosticProject);
    Assert.DoesNotContain("<PackageReference", diagnosticProject);

    var ordinaryOptions = MemoryOptions();
    ordinaryOptions.IncludeRuntime = true;
    var ordinaryBackend = new InspectableCsharpBackend(ordinaryOptions);
    var ordinaryProject = ordinaryBackend.ProjectFile("Exe", "/workspace/diagnostic.cs", dependencies);

    Assert.Contains("<PackageReference Include=\"System.Runtime.Numerics\"", ordinaryProject);
    Assert.Contains("<PackageReference Include=\"System.Collections.Immutable\"", ordinaryProject);
    Assert.DoesNotContain("<Reference Include=\"DafnyRuntime\">", ordinaryProject);
  }

  // The memory-only diagnostic compilation reports code generation and rendering without spilling generated files.
  [Fact]
  public async Task ObservesMemoryCompilationPhasesAndSkipsPreliminaryWrite() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Main");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);
    var phases = new List<(string Phase, string State)>();
    var dependencies = new ReadOnlyCollection<string>(["/workspace/ContractRuntime.cs"]);

    var compiled = await SynchronousCliCompilation.CompileDafnyProgram(resolution.Program,
      "/workspace/diagnostic.dfy", dependencies, false,
      new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null).OutputWriter,
      new SynchronousCliCompilation.CompilationSettings(
        (phase, state) => phases.Add((phase, state)), CancellationToken.None, false));

    Assert.True(compiled);
    Assert.Equal([
      ("code_generation", "started"),
      ("code_generation", "completed"),
      ("target_render", "started"),
      ("target_render", "completed")
    ], phases);
    Assert.False(SynchronousCliCompilation.ShouldWriteGeneratedTargetFiles(resolution.Options,
      resolution.Options.Backend, dependencies, true, false));
    Assert.True(SynchronousCliCompilation.ShouldWriteGeneratedTargetFiles(resolution.Options,
      resolution.Options.Backend, dependencies, true, true));
  }

  // Compiler options are applied before resolution so a ghost tuple with one runtime field retains its unary wrapper.
  [Fact]
  public async Task ResolvesGhostTupleWithCompilationPhysicalRepresentation() {
    const string source = "module M { function Tuple(): (ghost int, int) { (ghost 1, 2) } method Main() {} }";
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(await Transformation(source, "M.Main"),
      MemoryOptions(), CancellationToken.None);

    Assert.Equal(0, resolution.Reporter.ErrorCount);
    var tuple = Assert.Single(resolution.Program.SystemModuleManager.SystemModule.SourceDecls
      .OfType<TupleTypeDecl>().Where(declaration => declaration.ArgumentGhostness.SequenceEqual([true, false])));
    Assert.NotNull(tuple.NonGhostTupleTypeDecl);
    Assert.Equal(1, tuple.NonGhostTupleTypeDecl!.Dims);
  }

  // Parse or resolution errors are rejected by the pure preparation gate.
  [Fact]
  public async Task RejectsResolutionErrorsBeforeCompilation() {
    var transformation = await Transformation("module M { method Main() { var value: MissingType; } }", "M.Main");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);

    var input = ContractCompilerWorker.PrepareCompilation(resolution, CancellationToken.None, out var rejection);

    Assert.Null(input);
    Assert.NotNull(rejection);
    Assert.Equal(ContractTestStatus.Error, rejection!.Status);
  }

  // A stipulated main mismatch is rejected by the pure preparation gate.
  [Fact]
  public async Task RejectsWrongMainBeforeCompilation() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Missing");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);

    var input = ContractCompilerWorker.PrepareCompilation(resolution, CancellationToken.None, out var rejection);

    Assert.Null(input);
    Assert.NotNull(rejection);
    Assert.Equal(ContractTestStatus.Error, rejection!.Status);
    Assert.Contains("diagnostic main", rejection.Reason);
  }

  // Mixing a program with another configured option instance is rejected by the pure preparation gate.
  [Fact]
  public async Task RejectsMixedResolutionIdentityBeforeCompilation() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Main");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);
    var otherOptions = MemoryOptions();
    ContractCompilerWorker.ApplyCompilationOptions(otherOptions, transformation.MainName);
    var mixed = new ContractCompilerWorker.CompilationResolution(transformation, resolution.Program,
      otherOptions, resolution.Reporter);

    var input = ContractCompilerWorker.PrepareCompilation(mixed, CancellationToken.None, out var rejection);

    Assert.Null(input);
    Assert.NotNull(rejection);
    Assert.Equal(ContractTestStatus.Error, rejection!.Status);
    Assert.Contains("inconsistent", rejection.Reason);
  }

  // Cancellation is observed by the pure preparation gate before compilation can begin.
  [Fact]
  public async Task RejectsCancellationBeforeCompilation() {
    var transformation = await Transformation("module M { method Main() {} }", "M.Main");
    var resolution = await ContractCompilerWorker.ResolveRuntimeAsync(transformation, MemoryOptions(),
      CancellationToken.None);
    using var cancelled = new CancellationTokenSource();
    cancelled.Cancel();

    Assert.ThrowsAny<OperationCanceledException>(() =>
      ContractCompilerWorker.PrepareCompilation(resolution, cancelled.Token, out _));
  }

  private static async Task<ContractRuntimeTransformation> Transformation(string transformedSource, string mainName) {
    const string path = "/workspace/CompilationResolution.dfy";
    const string originalSource = "module M { method Main() {} }";
    var original = new ContractSource(path, originalSource, ContractHarnessBuilder.Hash(originalSource));
    var reporter = new BatchErrorReporter(MemoryOptions());
    var program = await ContractSourceSnapshot.ParseAsync(reporter, [original], CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Main"), requireConcreteReceiver: false);
    var prepared = new ContractPreparedProgram(program, goal, original,
      new(path, goal.Origin.line, goal.Origin.col, goal.FullDafnyName, original.Sha256), Sources: [original]);
    var transformed = new ContractSource(path, transformedSource, ContractHarnessBuilder.Hash(transformedSource));
    return new ContractRuntimeTransformation([transformed], [], [], mainName, prepared, new HashSet<Field>());
  }

  private static DafnyOptions MemoryOptions() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null) {
      TheProverFactory = new NoProverFactory()
    };
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.XmlSink = null;
    options.DafnyPrintFile = null;
    options.DafnyPrintResolvedFile = null;
    options.AutoReqPrintFile = null;
    options.DafnyPrintExportedViews = [];
    options.AdditionalPlugins = [];
    options.AdditionalPluginArguments = [];
    options.PrintIncludesMode = DafnyOptions.IncludesModes.None;
    options.PrintStats = false;
    options.PrintFunctionCallGraph = false;
    return options;
  }

  private static (string Text, Queue<FileSyntax> Files) Render(Program program, CsharpBackend backend) {
    backend.OnPreCompile(program.Reporter, new ReadOnlyCollection<string>([]));
    var output = new ConcreteSyntaxTree();
    backend.Compile(program, "/workspace/diagnostic.dfy", output);
    var writer = new StringWriter();
    var files = new Queue<FileSyntax>();
    output.Render(writer, 0, new WriterState(), files, backend.TargetIndentSize);
    var text = writer.ToString();
    if (SinglePassCodeGenerator.HasMain(program, out var main)) {
      var callToMain = new ConcreteSyntaxTree();
      backend.EmitCallToMain(main, "diagnostic", callToMain);
      text += callToMain.MakeString(backend.TargetIndentSize);
    }
    return (text, files);
  }

  private sealed class InspectableCsharpBackend(DafnyOptions options) : CsharpBackend(options) {
    internal string ProjectFile(string outputType, string sourcePath,
      ReadOnlyCollection<string> otherFileNames) => CreateProjectFile(outputType, sourcePath, otherFileNames);
  }

  private sealed class NoProverFactory : Microsoft.Boogie.ProverFactory {
    public override Microsoft.Boogie.ProverInterface SpawnProver(Microsoft.Boogie.SMTLibOptions libOptions,
      Microsoft.Boogie.ProverOptions options, object ctxt) =>
      throw new InvalidOperationException("Memory tests must not spawn a prover.");

    public override Microsoft.Boogie.ProverContext NewProverContext(Microsoft.Boogie.ProverOptions options) =>
      throw new InvalidOperationException("Memory tests must not create a prover context.");
  }
}
