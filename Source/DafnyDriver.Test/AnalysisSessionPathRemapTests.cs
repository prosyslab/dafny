using System.Text.Json;
using DafnyDriver.Commands;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>
/// A host may bind a snapshot whose logical root differs from its physical directory. Message text that
/// names a file must show the physical path, exactly as a one-shot run in that directory does.
/// </summary>
[Collection("Proof input translation")]
public class AnalysisSessionPathRemapTests : IDisposable {
  private const string Logical = "/logical-snapshot/root";
  private const string Main = """
    module Main {
      lemma Sound(x: int)
        ensures x + 1 > x
      {
        assert x + 1 > x;
      }
    }
    """;
  private const string Library = "module Lib { function One(): int { 1 } }\n";
  private readonly string physical;

  public AnalysisSessionPathRemapTests() {
    physical = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "session-path-remap-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(System.IO.Path.Combine(physical, "lib"));
    File.WriteAllText(System.IO.Path.Combine(physical, "Main.dfy"), Main);
    File.WriteAllText(System.IO.Path.Combine(physical, "lib", "Lib.dfy"), Library);
  }

  public void Dispose() => Directory.Delete(physical, true);

  private static string[] WithRoot(string[] command, string root, params string[] extra) =>
    [.. command, "--library", root + "/lib/Lib.dfy", .. extra, root + "/Main.dfy"];

  private AnalysisSessionCommand.Request Request(string id, string[] arguments, string? sourceRoot, string? logicalRoot,
    string context = "default") => new(id, arguments, logicalRoot ?? physical, context,
    new Dictionary<string, string> {
      [(logicalRoot ?? physical) + "/Main.dfy"] = Main,
      [(logicalRoot ?? physical) + "/lib/Lib.dfy"] = Library
    }, SourceRoot: sourceRoot, LogicalRoot: logicalRoot);

  private static async Task<(int Code, string Stdout, string Stderr)> OneShot(string[] arguments) {
    using var stdout = new StringWriter();
    using var stderr = new StringWriter();
    var code = await DafnyNewCli.Execute(new WritersConsole(TextReader.Null, stdout, stderr), arguments);
    return (code, stdout.ToString(), stderr.ToString());
  }

  private static IEnumerable<string> LibraryWarnings(string text) =>
    text.Split('\n').Select(line => line.TrimEnd('\r')).Where(line => line.Contains("was passed to --library"));

  // The warning of every command and routing shows the physical path and equals the one-shot line.
  [Theory]
  [InlineData("resolve")]
  [InlineData("verify")]
  [InlineData("definition-analysis")]
  [InlineData("definition-analysis-proof-inputs")]
  public async Task LibraryWarningShowsPhysicalPath(string command) {
    var extra = command == "definition-analysis-proof-inputs" ? new[] { "--include-proof-inputs" } : [];
    var name = command.StartsWith("definition-analysis") ? "definition-analysis" : command;
    using var session = new AnalysisSessionCommand.Session();
    var response = await session.Execute(Request("r1", WithRoot([name], Logical, extra), physical, Logical), CancellationToken.None);
    var oneShot = await OneShot(WithRoot([name], physical, extra));

    var sessionText = response.Stdout + response.Stderr;
    // JSON documents keep logical paths; the client maps them (see _remap_analysis). Message text must not.
    Assert.DoesNotContain(sessionText.Split('\n'), line => !line.StartsWith('{') && !line.StartsWith('[') && line.Contains(Logical));
    var warnings = LibraryWarnings(sessionText).ToList();
    Assert.StartsWith($"CLI: Warning: The file '{physical}/lib/Lib.dfy' was passed to --library.", warnings.Single());
    // One-shot resolve reports no library warnings at all (a separate difference); the other commands match.
    if (name != "resolve") {
      Assert.Equal(LibraryWarnings(oneShot.Stdout + oneShot.Stderr).ToList(), warnings);
    }
    if (name != "resolve") {
      Assert.Equal(oneShot.Code, response.Returncode);
    }
  }

  // Without a logical root, or with equal roots, the text is exactly what the request names.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task WithoutDistinctRootsTextIsUnchanged(bool equalRoots) {
    using var session = new AnalysisSessionCommand.Session();
    var request = equalRoots
      ? Request("r1", WithRoot(["verify"], physical), physical, physical)
      : Request("r1", WithRoot(["verify"], physical), null, null);
    var response = await session.Execute(request, CancellationToken.None);
    var oneShot = await OneShot(WithRoot(["verify"], physical));

    Assert.Equal(LibraryWarnings(oneShot.Stdout + oneShot.Stderr).ToList(), LibraryWarnings(response.Stdout + response.Stderr).ToList());
    Assert.Contains($"'{physical}/lib/Lib.dfy'", response.Stdout + response.Stderr);
  }

  // A native State reused by a request with another snapshot directory prints that request's directory.
  [Fact]
  public async Task ReusedStateReportsTheCurrentSourceRoot() {
    var other = physical + "-second";
    using var session = new AnalysisSessionCommand.Session();
    var arguments = WithRoot(["definition-analysis"], Logical);
    var first = await session.Execute(Request("r1", arguments, physical, Logical), CancellationToken.None);
    var second = await session.Execute(Request("r2", arguments, other, Logical), CancellationToken.None);
    var evidence = JsonSerializer.SerializeToElement(second.NativeEvidence, AnalysisSessionCommand.JsonOptions);

    Assert.True(evidence.GetProperty("analysisModuleHits").GetInt32() > 0, evidence.ToString());
    Assert.Contains($"'{physical}/lib/Lib.dfy'", first.Stdout + first.Stderr);
    Assert.Contains($"'{other}/lib/Lib.dfy'", second.Stdout + second.Stderr);
    Assert.DoesNotContain($"'{physical}/", second.Stdout + second.Stderr);
  }

  // A rejected reported scope names the physical file, as the one-shot rejection does.
  [Fact]
  public async Task AnalysisSourceRejectionShowsPhysicalPath() {
    string[] Arguments(string root) => ["definition-analysis", "--analysis-source", root + "/lib/Lib.dfy", "--library", root + "/lib/Lib.dfy", root + "/Main.dfy"];
    using var session = new AnalysisSessionCommand.Session();
    var response = await session.Execute(Request("r1", Arguments(Logical), physical, Logical), CancellationToken.None);
    var oneShot = await OneShot(Arguments(physical));

    Assert.Contains("--analysis-source", response.Stderr);
    Assert.DoesNotContain(Logical, response.Stderr);
    Assert.Equal(oneShot.Stderr.Split('\n').Where(line => line.Contains("--analysis-source")),
      response.Stderr.Split('\n').Where(line => line.Contains("--analysis-source")));
  }

  // Only a root that starts and ends a path is replaced, including inside a format string.
  [Theory]
  [InlineData("/logical-snapshot/root", "/logical-snapshot/root", "/phys")]
  [InlineData("/logical-snapshot/root/a.dfy", "/logical-snapshot/root/a.dfy", "/phys")]
  [InlineData("file /logical-snapshot/root/a.dfy not found", "file /logical-snapshot/root/a.dfy not found", "/phys")]
  [InlineData("in '/logical-snapshot/root'.", "in '/logical-snapshot/root'.", "/phys")]
  [InlineData("/logical-snapshot/root2/a.dfy", "/logical-snapshot/root2/a.dfy", "/phys")]
  [InlineData("/other/logical-snapshot/root/a.dfy", "/other/logical-snapshot/root/a.dfy", "/phys")]
  [InlineData("/logical-snapshot/root.bak", "/logical-snapshot/root.bak", "/phys")]
  public void TextRemapUsesExactRootBoundaries(string text, string unchanged, string to) {
    var request = new AnalysisSessionCommand.Request("r", SourceRoot: to, LogicalRoot: Logical);
    var mapped = AnalysisSessionCommand.RemapOutputText(text, request);
    var expected = text.StartsWith("/logical-snapshot/root2") || text.StartsWith("/other") || text.Contains("root.bak")
      ? unchanged
      : text.Replace(Logical, to);
    Assert.Equal(expected, mapped);
  }

  // An uncatalogued diagnostic's first part is a format string; braces in the physical root stay literal.
  [Fact]
  public void FormatStringPathsRemapWithoutBreakingFormatting() {
    var request = new AnalysisSessionCommand.Request("r", SourceRoot: "/phys{1}", LogicalRoot: Logical);
    var diagnostic = new DafnyDiagnostic(MessageSource.Project, "", new TokenRange(Token.NoToken, Token.NoToken),
      [$"file {Logical}/a.dfy not found, {{0}}", Logical + "/b.dfy"], ErrorLevel.Error, []);

    var mapped = AnalysisSessionCommand.RemapDiagnostic(diagnostic, request);

    Assert.Equal("file /phys{1}/a.dfy not found, /phys{1}/b.dfy", mapped.Message);
    Assert.Same(diagnostic, AnalysisSessionCommand.RemapDiagnostic(diagnostic, request with { LogicalRoot = null }));
  }
}
