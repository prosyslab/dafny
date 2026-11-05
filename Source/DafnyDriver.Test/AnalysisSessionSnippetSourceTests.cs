using System.Text.Json;
using System.Text.RegularExpressions;
using DafnyDriver.Commands;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

/// <summary>
/// The source excerpt Dafny prints under a diagnostic must come from the bytes the request compiled. A host that
/// binds a physical snapshot to a stable logical root must never see the line of a stale file at the logical path.
/// </summary>
[Collection("Proof input translation")]
public class AnalysisSessionSnippetSourceTests : IDisposable {
  private const string ResolveError = "module Main {\n  method M() returns (r: int) {\n    var bogus: int := \"text\";\n    r := 1;\n  }\n}\n";
  private const string VerifyError =
    "module Main {\n  method Weak(x: int) returns (r: int)\n    ensures r > 5\n  {\n    r := 1;\n  }\n  lemma Bad(x: int) {\n    assert x > 0;\n  }\n}\n";
  private readonly List<string> directories = [];

  private string NewDirectory(string name) {
    var directory = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "session-snippet-" + name + "-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    directories.Add(directory);
    return directory;
  }

  public void Dispose() {
    foreach (var directory in directories) {
      Directory.Delete(directory, true);
    }
  }

  private static string Stale(string text) =>
    string.Join("\n", Enumerable.Range(1, text.Split('\n').Length - 1).Select(line => $"// stale logical line {line}")) + "\n";

  private sealed record Layout(string Logical, string Physical, string OneShot);

  /// <summary>A stale file at the logical path, the candidate in a physical directory and in a clean one-shot directory.</summary>
  private Layout Prepare(string name, string source) {
    var layout = new Layout(NewDirectory("logical"), NewDirectory("physical"), NewDirectory("oneshot"));
    File.WriteAllText(System.IO.Path.Combine(layout.Logical, name), Stale(source));
    File.WriteAllText(System.IO.Path.Combine(layout.Physical, name), source);
    File.WriteAllText(System.IO.Path.Combine(layout.OneShot, name), source);
    return layout;
  }

  private static AnalysisSessionCommand.Request Request(string id, string command, Layout layout, string name, string source,
    string? sourceRoot, bool supplied = true, string context = "default") => new(id, [command, layout.Logical + "/" + name],
    layout.Logical, context, supplied ? new Dictionary<string, string> { [layout.Logical + "/" + name] = source } : null,
    SourceRoot: sourceRoot, LogicalRoot: layout.Logical);

  private static async Task<(int Code, string Stdout, string Stderr)> OneShot(string command, Layout layout, string name) {
    using var stdout = new StringWriter();
    using var stderr = new StringWriter();
    var code = await DafnyNewCli.Execute(new WritersConsole(TextReader.Null, stdout, stderr), [command, layout.OneShot + "/" + name]);
    return (code, stdout.ToString(), stderr.ToString());
  }

  // The excerpt lines only: headers show a cwd-relative path that is a separate, unchanged difference.
  private static List<string> Excerpts(string text) =>
    text.Split('\n').Select(line => line.TrimEnd('\r')).Where(line => Regex.IsMatch(line, @"^ *\d* \|")).ToList();

  // Verification order differs between the session and the one-shot CLI, so blocks are compared as a sorted set.
  private static List<string> ExcerptBlocks(string text) => Excerpts(text).Chunk(3).Select(block => string.Join("\n", block))
    .OrderBy(block => block, StringComparer.Ordinal).ToList();

  private static JsonElement Evidence(AnalysisSessionCommand.Response response) =>
    JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions);

  // A resolution error shows the candidate line in every command that prints it.
  [Theory]
  [InlineData("resolve", true)]
  [InlineData("definition-analysis", true)]
  [InlineData("verify", true)]
  [InlineData("resolve", false)]
  [InlineData("definition-analysis", false)]
  [InlineData("verify", false)]
  public async Task ResolutionErrorExcerptComesFromTheRequestBytes(string command, bool supplied) {
    var layout = Prepare("Resolve.dfy", ResolveError);
    using var session = new AnalysisSessionCommand.Session();
    var request = Request("r1", command, layout, "Resolve.dfy", ResolveError, layout.Physical, supplied);
    // A supplied snapshot beats whatever is on disk at the physical path.
    if (supplied) { File.WriteAllText(layout.Physical + "/Resolve.dfy", "// decoy\n"); }

    var response = await session.Execute(request, CancellationToken.None);
    var oneShot = await OneShot(command, layout, "Resolve.dfy");

    var text = response.Stdout + response.Stderr;
    Assert.Contains("Error: string literal \"text\" used as if it had type int", text);
    Assert.DoesNotContain("stale", text);
    Assert.DoesNotContain("decoy", text);
    Assert.Equal(Excerpts(oneShot.Stdout + oneShot.Stderr), Excerpts(text));
    Assert.Equal(["  |", "3 |     var bogus: int := \"text\";", "  | " + new string(' ', 22) + "^^^^^^"], Excerpts(text).Take(3));
  }

  // The main range and the related location of a verification error both read the request bytes.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task VerificationErrorExcerptsComeFromTheRequestBytes(bool supplied) {
    var layout = Prepare("Verify.dfy", VerifyError);
    using var session = new AnalysisSessionCommand.Session();
    var response = await session.Execute(Request("v1", "verify", layout, "Verify.dfy", VerifyError, layout.Physical, supplied),
      CancellationToken.None);
    var oneShot = await OneShot("verify", layout, "Verify.dfy");

    var text = response.Stdout + response.Stderr;
    Assert.Contains("Error: a postcondition could not be proved on this return path", text);
    Assert.Contains("Related location: this is the postcondition that could not be proved", text);
    Assert.Contains("Error: assertion could not be proved", text);
    Assert.DoesNotContain("stale", text);
    Assert.Contains("8 |     assert x > 0;", Excerpts(text));
    Assert.Contains("3 |     ensures r > 5", Excerpts(text));
    Assert.Contains("4 |   {", Excerpts(text));
    Assert.Equal(3, ExcerptBlocks(text).Count);
    Assert.Equal(ExcerptBlocks(oneShot.Stdout + oneShot.Stderr), ExcerptBlocks(text));
  }

  // A State reused by a request with another snapshot directory still renders the candidate.
  [Fact]
  public async Task ReusedStateWithAnotherSourceRootRendersTheCandidate() {
    var layout = Prepare("Verify.dfy", VerifyError);
    var second = NewDirectory("physical-second");
    File.WriteAllText(second + "/Verify.dfy", VerifyError);
    using var session = new AnalysisSessionCommand.Session();
    var first = await session.Execute(Request("v1", "verify", layout, "Verify.dfy", VerifyError, layout.Physical, supplied: false),
      CancellationToken.None);
    var reused = await session.Execute(Request("v2", "verify", layout, "Verify.dfy", VerifyError, second, supplied: false),
      CancellationToken.None);
    var oneShot = await OneShot("verify", layout, "Verify.dfy");

    var evidence = Evidence(reused);
    Assert.True(Evidence(first).GetProperty("solverRunCount").GetInt32() > 0);
    Assert.Equal(0, evidence.GetProperty("solverRunCount").GetInt32());
    Assert.True(evidence.GetProperty("taskCount").GetInt32() > 0);
    Assert.DoesNotContain("stale", reused.Stdout + reused.Stderr);
    Assert.Equal(ExcerptBlocks(oneShot.Stdout + oneShot.Stderr), ExcerptBlocks(reused.Stdout + reused.Stderr));
    Assert.Equal(ExcerptBlocks(first.Stdout + first.Stderr), ExcerptBlocks(reused.Stdout + reused.Stderr));
  }

  // A later request with different bytes builds a new compilation and renders its own line.
  [Fact]
  public async Task ChangedBytesRenderTheNewCandidateLine() {
    var layout = Prepare("Verify.dfy", VerifyError);
    var moved = "// moved\n" + VerifyError;
    var second = NewDirectory("physical-second");
    File.WriteAllText(second + "/Verify.dfy", moved);
    using var session = new AnalysisSessionCommand.Session();
    await session.Execute(Request("v1", "verify", layout, "Verify.dfy", VerifyError, layout.Physical, supplied: false), CancellationToken.None);
    var changed = await session.Execute(Request("v2", "verify", layout, "Verify.dfy", moved, second), CancellationToken.None);

    var excerpts = Excerpts(changed.Stdout + changed.Stderr);
    Assert.DoesNotContain("stale", changed.Stdout + changed.Stderr);
    Assert.Contains("9 |     assert x > 0;", excerpts);
    Assert.Contains("4 |     ensures r > 5", excerpts);
    Assert.DoesNotContain("8 |     assert x > 0;", excerpts);
  }

  // Without a logical root, or with equal roots, the excerpt is what it always was.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task WithoutDistinctRootsTheExcerptIsUnchanged(bool equalRoots) {
    var directory = NewDirectory("plain");
    File.WriteAllText(directory + "/Verify.dfy", VerifyError);
    using var session = new AnalysisSessionCommand.Session();
    var request = new AnalysisSessionCommand.Request("r1", ["verify", directory + "/Verify.dfy"], directory, "default", null,
      SourceRoot: equalRoots ? directory : null, LogicalRoot: equalRoots ? directory : null);
    var response = await session.Execute(request, CancellationToken.None);
    using var stdout = new StringWriter();
    using var stderr = new StringWriter();
    await DafnyNewCli.Execute(new WritersConsole(TextReader.Null, stdout, stderr), ["verify", directory + "/Verify.dfy"]);

    Assert.Contains("8 |     assert x > 0;", Excerpts(response.Stdout + response.Stderr));
    Assert.Equal(ExcerptBlocks(stdout.ToString() + stderr), ExcerptBlocks(response.Stdout + response.Stderr));
  }
}
