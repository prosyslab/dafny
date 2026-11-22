using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny.Compilers;

public class LibraryBackend : ExecutableBackend {
  public LibraryBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { };

  public override string TargetName => "Dafny Library (.doo)";

  /// Some tests still fail when using the lib back-end, for example due to disallowed assumptions being present in the test,
  /// such as empty constructors with ensures clauses, generated from iterators
  public override bool IsStable => false;

  public override string TargetExtension => "doo";
  public override string TargetId => "lib";

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-lib";

  public override bool TextualTargetIsExecutable => false;

  public override bool SupportsInMemoryCompilation => false;

  public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
    Feature.LegacyCLI,
    Feature.RuntimeCoverageReport
  };

  // Necessary since Compiler is null
  public override string ModuleSeparator => ".";

  public string DooPath { get; set; }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return null;
  }

  public override Task<bool> OnPostGenerate(string dafnyProgramName, string targetFilename, IDafnyOutputWriter outputWriter) {
    // Not calling base.OnPostCompile() since it references `compiler`
    return Task.FromResult(true);
  }

  public override string PublicIdProtect(string name) {
    throw new NotSupportedException();
  }

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    if (!Options.UsingNewCli) {
      throw new UnsupportedFeatureException(dafnyProgram.GetStartOfFirstFileToken(), Feature.LegacyCLI);
    }

    var snapshot = dafnyProgram.Options.Get(CommonOptionBag.InferModifiesOption)
      ? WithInferredFrames(dafnyProgram)
      : dafnyProgram.AfterParsingClone;
    var dooFile = new DooFile(snapshot);
    dooFile.Write(output);
  }

  // The parse snapshot preserves prefix module syntax, but predates inference. Copy
  // source-shaped frames into that snapshot so a library keeps its verified contract.
  private static Program WithInferredFrames(Program program) {
    var inferred = program.RawModules()
      .SelectMany(module => module.TopLevelDecls.OfType<TopLevelDeclWithMembers>())
      .SelectMany(decl => decl.Members.OfType<MethodOrConstructor>())
      .Where(method => method.InferredModifiesFromCli)
      .Distinct()
      .GroupBy(SourceKey)
      .ToDictionary(group => group.Key, group => group.ToList());
    if (inferred.Count == 0) {
      return program.AfterParsingClone;
    }

    var snapshot = new Program(new Cloner(true), program.AfterParsingClone);
    var sourceMethods = SourceMethods(snapshot.DefaultModuleDef)
      .GroupBy(SourceKey).ToDictionary(group => group.Key, group => group.ToList());
    // Validate all matches before changing the snapshot.
    foreach (var (key, methods) in inferred) {
      if (methods.Count != 1 || !sourceMethods.TryGetValue(key, out var originals) || originals.Count != 1 ||
          originals[0].Mod.Expressions.Count != 0 || originals[0].Mod.Attributes != null) {
        throw new InvalidOperationException($"Cannot serialize inferred modifies clause for {key.Name} at {key.Uri}:{key.Position}");
      }
    }
    var cloner = new Cloner();
    foreach (var (key, methods) in inferred) {
      sourceMethods[key][0].Mod.Expressions.AddRange(methods[0].Mod.Expressions.Select(cloner.CloneFrameExpr));
    }
    return snapshot;
  }

  private static (Uri Uri, int Position, string Name) SourceKey(MethodOrConstructor method) =>
    (method.Origin.Uri, method.Origin.pos, method.Name);

  private static IEnumerable<MethodOrConstructor> SourceMethods(ModuleDefinition module) {
    foreach (var declaration in module.TopLevelDecls) {
      if (declaration is TopLevelDeclWithMembers withMembers) {
        foreach (var method in withMembers.Members.OfType<MethodOrConstructor>()) {
          yield return method;
        }
      }
      if (declaration is LiteralModuleDecl nested) {
        foreach (var method in SourceMethods(nested.ModuleDef)) {
          yield return method;
        }
      }
    }
    foreach (var prefix in module.PrefixNamedModules) {
      foreach (var method in SourceMethods(prefix.Module.ModuleDef)) {
        yield return method;
      }
    }
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    // No-op
  }

  private string DooFilePath(string dafnyProgramName) {
    return Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, DooFile.Extension));
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, IDafnyOutputWriter outputWriter) {

    var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    DooPath = DooFilePath(dafnyProgramName);

    File.Delete(DooPath);

    try {
      ZipFile.CreateFromDirectory(targetDirectory, DooPath);
    } catch (IOException) {
      if (File.Exists(DooPath)) {
        await outputWriter.Status($"Failed to delete doo file at {Options.GetPrintPath(DooPath)}");
      }

      throw;
    }
    if (Options.Verbose) {
      await outputWriter.Status($"Wrote Dafny library to {Options.GetPrintPath(DooPath)}");
    }

    return (true, null);
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult,
    IDafnyOutputWriter outputWriter) {
    var dooPath = DooFilePath(dafnyProgramName);
    return RunTargetDafnyProgram(dooPath, outputWriter, true);
  }
}
