using System.Text.Json;
using DafnyDriver.Commands;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging.Abstractions;
using Xunit;
using Program = Microsoft.Dafny.Program;

namespace DafnyDriver.Test;

[Collection("Proof input translation")]
public class AnalysisSourceSelectionTests {
  private static readonly Uri Root = new("file:///workspace/analysis-scope/root.dfy");
  private static readonly Uri Helper = new("file:///workspace/analysis-scope/helper.dfy");
  private static readonly Uri Util = new("file:///workspace/analysis-scope/util.dfy");
  private static readonly Uri Outside = new("file:///workspace/analysis-scope/outside.dfy");

  private static MemoryFiles Files() => new(new Dictionary<Uri, string> {
    [Root] = """
      include "helper.dfy"
      module Main {
        import Helper
        function Render(x: int): int
          requires x >= 0
          ensures Render(x) >= x
        { x + Helper.One() }
        lemma Valid(x: int) ensures Render(x) > x { }
      }
      """,
    [Helper] = """
      include "util.dfy"
      module Helper {
        import Util
        function One(): int { Util.Zero() + 1 }
        method Count(n: nat) returns (r: nat) ensures r == n {
          r := 0;
          while r < n invariant r <= n { r := r + 1; }
        }
      }
      """,
    [Util] = "module Util { function Zero(): int { 0 } }\n"
  });

  // Reporting an included file from a fixed compilation equals naming it as a root.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task SelectedIncludedSourceMatchesExpandedRoots(bool proofInputs) {
    var files = Files();
    var (fixedProgram, fixedOptions) = await Compile(files, [Root], verifyIncluded: true, [Root, Helper], proofInputs);
    var (expandedProgram, expandedOptions) = await Compile(files, [Root, Helper], verifyIncluded: true, [], proofInputs);

    var selected = Select(fixedProgram, fixedOptions, [Root]);
    var expanded = Select(expandedProgram, expandedOptions, [Root, Helper]);

    Assert.NotNull(selected);
    Assert.True(selected!.SetEquals(new[] { Root, Helper }));
    Assert.True(expanded!.SetEquals(new[] { Root, Helper }));
    var actual = Analyze(fixedProgram, selected, proofInputs, files);
    var expected = Analyze(expandedProgram, expanded, proofInputs, files);
    Assert.Equal(expected, actual);
    Assert.Contains("\"Util\"", actual);
    Assert.Contains("Helper.Count", actual);
  }

  // Without a selection the reported scope stays the analyzed roots.
  [Fact]
  public async Task AbsentSelectionKeepsRoots() {
    var (program, options) = await Compile(Files(), [Root], verifyIncluded: false, [], proofInputs: true);
    var selected = Select(program, options, [Root]);
    Assert.True(selected!.SetEquals(new[] { Root }));
  }

  // Invalid selections fail instead of silently changing or narrowing the report.
  [Theory]
  [InlineData("missing-root")]
  [InlineData("outside")]
  [InlineData("proof-without-included-verification")]
  public async Task InvalidSelectionsAreRejected(string selection) {
    var files = Files();
    files.Values[Outside] = "module Outside { }\n";
    var (requested, verifyIncluded, proofInputs, message) = selection switch {
      "missing-root" => (new[] { Helper }, true, false, "every analyzed root"),
      "outside" => (new[] { Root, Outside }, true, false, "not a verified Dafny source"),
      _ => (new[] { Root, Helper }, false, true, "--verify-included-files")
    };
    var (program, options) = await Compile(files, [Root], verifyIncluded, requested, proofInputs);
    var selected = DefinitionAnalysisCommand.SelectAnalysisSources(options, new HashSet<Uri> { Root }, program, out var error);
    Assert.Null(selected);
    Assert.Contains(message, error);
  }

  // Structural facts of an included file do not depend on included-file verification.
  [Fact]
  public async Task StructuralSelectionDoesNotRequireIncludedVerification() {
    var files = Files();
    var (fixedProgram, fixedOptions) = await Compile(files, [Root], verifyIncluded: false, [Root, Helper], proofInputs: false);
    var (expandedProgram, expandedOptions) = await Compile(files, [Root, Helper], verifyIncluded: false, [], proofInputs: false);
    var selected = Select(fixedProgram, fixedOptions, [Root])!;
    var expanded = Select(expandedProgram, expandedOptions, [Root, Helper])!;
    var actual = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(fixedProgram, selected, includeStatements: true,
      includeSemanticFacts: true, sourceSnapshots: Snapshots(files)));
    var expected = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(expandedProgram, expanded, includeStatements: true,
      includeSemanticFacts: true, sourceSnapshots: Snapshots(files)));
    Assert.Equal(expected, actual);
  }

  private static IReadOnlySet<Uri>? Select(Program program, DafnyOptions options, IReadOnlyList<Uri> roots) {
    var selected = DefinitionAnalysisCommand.SelectAnalysisSources(options, roots.ToHashSet(), program, out var error);
    Assert.True(selected != null, error);
    return selected;
  }

  private static string Analyze(Program program, IReadOnlySet<Uri> sources, bool proofInputs, MemoryFiles files) {
    var targets = SymbolExtensions.GetSymbolDescendants(program.DefaultModule).OfType<ICanVerify>()
      .Where(target => !target.Origin.IsCopy && target.ShouldVerify).ToList();
    return JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, sources, includeStatements: true,
      includeSemanticFacts: true, includeProofInputs: proofInputs, verificationTargets: targets,
      sourceSnapshots: Snapshots(files)));
  }

  private static Dictionary<string, string> Snapshots(MemoryFiles files) =>
    files.Values.ToDictionary(file => file.Key.LocalPath, file => file.Value);

  private static async Task<(Program Program, DafnyOptions Options)> Compile(MemoryFiles files, IReadOnlyList<Uri> roots,
    bool verifyIncluded, IReadOnlyList<Uri> analysisSources, bool proofInputs) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.VerifyIncludedFiles, verifyIncluded);
    options.ApplyBinding(CommonOptionBag.VerifyIncludedFiles);
    options.Set(DefinitionAnalysisCommand.IncludeProofInputs, proofInputs);
    options.Set(DefinitionAnalysisCommand.IncludeVerificationFacts, proofInputs);
    options.Set(DefinitionAnalysisCommand.AnalysisSources,
      analysisSources.Select(uri => new FileInfo(uri.LocalPath)).ToList());
    var reporter = new BatchErrorReporter(options);
    var rootFiles = roots.Select(uri => DafnyFile.HandleDafnyFile(files, reporter, options, uri, Token.NoToken)!).ToList();
    var parsed = await new ProgramParser(NullLogger<ProgramParser>.Instance, files)
      .ParseFiles(roots[0].ToString(), rootFiles, reporter, CancellationToken.None);
    Microsoft.Dafny.Type.ResetScopes();
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    Assert.Equal(verifyIncluded, options.VerifyAllModules);
    return (parsed.Program, options);
  }

  private sealed class MemoryFiles(Dictionary<Uri, string> values) : IFileSystem {
    public Dictionary<Uri, string> Values { get; } = values;
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(Values[uri]), null);
    public bool Exists(Uri path) => Values.ContainsKey(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }
}
