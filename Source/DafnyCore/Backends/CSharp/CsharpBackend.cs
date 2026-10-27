using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class CsharpBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new CsharpCodeGenerator(Options, Reporter);
  }

  protected virtual bool IncludeFrameworkPackageReferences => true;

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetName => "C#";
  public override bool IsStable => true;
  public override string TargetExtension => "cs";

  // True if the most recently visited AST has a method annotated with {:synthesize}:

  public override string GetCompileName(bool isDefaultModule, string moduleName, string compileName) {
    return isDefaultModule
      ? PublicIdProtect(compileName)
      : base.GetCompileName(isDefaultModule, moduleName, compileName);
  }

  public override bool SupportsInMemoryCompilation => true;
  public override bool TextualTargetIsExecutable => false;

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {

    var outputDir = targetFilename == null ? Directory.GetCurrentDirectory() : Path.GetDirectoryName(Path.GetFullPath(targetFilename));
    var fileNames = Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName));
    var sourcePath = Path.Join(outputDir, fileNames + ".cs");
    var csprojPath = Path.Join(outputDir, fileNames + ".csproj");
    Directory.CreateDirectory(outputDir);

    var source = callToMain == null ? targetProgramText : targetProgramText + callToMain;
    await WriteTargetProgram(sourcePath, source);

    var outputType = callToMain == null ? "Library" : "Exe";

    foreach (var file in otherFileNames) {
      string extension = Path.GetExtension(file);
      if (extension != null) { extension = extension.ToLower(); }
      if (extension == ".cs") {
        var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
        if (!File.Exists(normalizedPath)) {
          await outputWriter.Status($"Errors compiling program: Could not find {file}");
          return (false, null);
        }
      }
    }

    var projectFile = CreateProjectFile(outputType, sourcePath, otherFileNames);
    await WriteProjectFile(csprojPath, projectFile);

    var arguments = new[] { "build", csprojPath, "-o", outputDir };
    var psi = PrepareProcessStartInfo("dotnet", arguments);
    var dotnetOutputWriter = new StringWriter();
    var dotnetErrorWriter = new StringWriter();
    var exitCode = await RunDotnetBuild(psi, dotnetOutputWriter, dotnetErrorWriter);
    var dllPath = Path.Combine(outputDir, fileNames + ".dll");
    if (exitCode != 0 || !File.Exists(dllPath)) {
      await outputWriter.Status($@"Failed to compile C# source code using 'dotnet {string.Join(" ", arguments)}'. Command output was:" +
                                dotnetOutputWriter.ToString() + dotnetErrorWriter.ToString());
    } else {
      if (Options.Verbose) {
        await outputWriter.Status($"Compiled assembly into {Path.GetFileName(dllPath)}");
      }
    }
    return (exitCode == 0, dllPath);
  }

  protected virtual Task WriteTargetProgram(string sourcePath, string source) =>
    File.WriteAllTextAsync(sourcePath, source);

  protected virtual Task WriteProjectFile(string projectPath, string project) =>
    File.WriteAllTextAsync(projectPath, project);

  protected virtual Task<int> RunDotnetBuild(ProcessStartInfo startInfo, TextWriter outputWriter,
    TextWriter errorWriter) => RunProcess(startInfo, outputWriter, errorWriter);

  protected virtual string CreateProjectFile(string outputType, string sourcePath,
    ReadOnlyCollection<string> otherFileNames) {
    var itemGroupExtra = @"";
    if (!Options.IncludeRuntime) {
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      var runtimePath = Path.Join(libPath, "DafnyRuntime.dll");
      itemGroupExtra = @$"
    <Reference Include=""DafnyRuntime"">
      <HintPath>{runtimePath}</HintPath>
    </Reference>";
    }

    var sourceFiles = new StringBuilder();
    sourceFiles.AppendLine(@$"<Compile Include=""{sourcePath}"" />");
    foreach (var file in otherFileNames) {
      var extension = Path.GetExtension(file)?.ToLower();
      if (extension == ".cs") {
        var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
        sourceFiles.AppendLine(@$"<Compile Include=""{normalizedPath}"" />");
      } else if (extension == ".dll") {
        sourceFiles.Append(@$"
    <Reference Include=""{Path.GetFileNameWithoutExtension(file)}"">
      <HintPath>{Path.GetFullPath(file)}</HintPath>
    </Reference>");
      }
    }

    var packageReferences = IncludeFrameworkPackageReferences
      ? @"
      <PackageReference Include=""System.Runtime.Numerics"" Version=""4.3.0"" />
      <PackageReference Include=""System.Collections.Immutable"" Version=""1.7.1"" />"
      : "";
    var itemGroup = @$"
  <ItemGroup>
      {sourceFiles}{packageReferences}
      {itemGroupExtra}
  </ItemGroup>";

    return @$"<Project Sdk=""Microsoft.NET.Sdk"">

  <PropertyGroup>
    <OutputType>{outputType}</OutputType>
    <TargetFramework>net8.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <NoWarn>CS8600;CS8603;CS8604;CS8605;CS8625;CS8629;CS8714;CS8765;CS8769;CS8981</NoWarn>
    <Nullable>enable</Nullable>
    <RollForward>Major</RollForward>
  </PropertyGroup>

  {itemGroup}
</Project>
";
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain,
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, IDafnyOutputWriter outputWriter) {

    var dllPath = (string)compilationResult;
    var dllFolder = Path.GetDirectoryName(dllPath)!;

    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) == ".dll") {
        var destination = Path.Combine(dllFolder, Path.GetFileName(otherFileName));
        if (Path.GetFullPath(otherFileName) != Path.GetFullPath(destination)) {
          File.Copy(otherFileName, destination, true);
        }
      }
    }

    var psi = PrepareProcessStartInfo("dotnet", new[] { dllPath }.Concat(Options.MainArgs));

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return await RunProcess(psi, sw, ew) == 0;
  }

  public override void PopulateCoverageReport(CoverageReport coverageReport) {
    codeGenerator.Coverage.PopulateCoverageReport(coverageReport);
  }

  public CsharpBackend(DafnyOptions options) : base(options) {
  }
}
