using System.Text.Json;
using DafnyCore;
using Microsoft.Dafny;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;

namespace DafnyDriver.Test;

public class AnalysisSessionDiagnosticLocationTests {
  private const string Logical = "/logical-snapshot/root";
  private const string Physical = "/physical-snapshot/first";

  private static AnalysisSessionCommand.Request Request(string physical = Physical) =>
    new("r", SourceRoot: physical, LogicalRoot: Logical);

  private static TokenRange Range(string path, int line = 1, int column = 3, bool inclusive = true) {
    var token = new Token(line, column) { Uri = new Uri(path), pos = column - 1, val = "assert", kind = 7 };
    return new TokenRange(token, inclusive ? token : null);
  }

  // An external range already under the physical root keeps its own bytes even when display paths collide.
  [Fact]
  public void ExternalExcerptIsNotReverseMapped() {
    var external = Range(Physical + "/Main.dfy");
    var cached = Diagnostic() with {
      RelatedInformation = [new DafnyRelatedInformation(external, "", ["external source"])]
    };
    var files = new MemoryFiles(new Dictionary<Uri, string> {
      [new Uri(Logical + "/Main.dfy")] = "  assert false; // logical candidate\n",
      [external.Uri] = "  assert true; // external source\n"
    });
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      SnippetFileSystem = files,
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request())
    };
    options.Set(Snippets.ShowSnippets, true);

    var mapped = AnalysisSessionCommand.RemapDiagnostic(cached, Request());
    options.OutputWriter.WriteDiagnostic(mapped);

    Assert.Same(cached.Range, mapped.Range);
    Assert.Same(external, mapped.RelatedInformation[0].Range);
    Assert.Contains("1 |   assert false; // logical candidate", output.ToString());
    Assert.Contains("1 |   assert true; // external source", output.ToString());
    Assert.Contains(Physical + "/Main.dfy(1,2): Error:", output.ToString());
    Assert.Contains(Physical + "/Main.dfy(1,2): Related location:", output.ToString());
    Assert.Equal(new[] { new Uri(Logical + "/Main.dfy"), external.Uri }, files.Reads);
  }

  // A related location without its own message, as from a NestedOrigin without text, keeps its null part.
  [Fact]
  public void MessagelessRelatedLocationIsRemapped() {
    var cached = Diagnostic() with {
      RelatedInformation = [new DafnyRelatedInformation(Range(Logical + "/Other.dfy"), "", [null!])]
    };
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request())
    };
    options.Set(Snippets.ShowSnippets, false);

    var mapped = AnalysisSessionCommand.RemapDiagnostic(cached, Request());
    options.OutputWriter.WriteDiagnostic(mapped);

    Assert.Null(mapped.RelatedInformation[0].MessageParts[0]);
    Assert.Contains(Physical + "/Main.dfy(1,2): Error: assertion could not be proved", output.ToString());
    Assert.Contains(Physical + "/Other.dfy(1,2): Related location", output.ToString());
  }

  private static DafnyDiagnostic Diagnostic(TokenRange? range = null) => new(MessageSource.Verifier, "",
    range ?? Range(Logical + "/Main.dfy"), ["assertion could not be proved"], ErrorLevel.Error,
    [new DafnyRelatedInformation(Range(Logical + "/Spec.dfy"), "", ["the specification"])]);

  // Both diagnostic locations render the current physical root while cached tokens retain their logical URIs.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public void PrimaryAndRelatedLocationsAreRequestLocal(bool printRanges) {
    var cached = Diagnostic();
    var first = AnalysisSessionCommand.RemapDiagnostic(cached, Request());
    var second = AnalysisSessionCommand.RemapDiagnostic(cached, Request("/physical-snapshot/second"));
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null);
    options.Set(Snippets.ShowSnippets, false);
    options.Set(CommonOptionBag.PrintDiagnosticsRanges, printRanges);
    options.PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request());
    options.OutputWriter.WriteDiagnostic(first);
    options.PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request("/physical-snapshot/second"));
    options.OutputWriter.WriteDiagnostic(second);

    var position = printRanges ? "(1:2-1:8)" : "(1,2)";
    Assert.Contains(Physical + "/Main.dfy" + position + ": Error: assertion could not be proved", output.ToString());
    Assert.Contains(Physical + "/Spec.dfy" + position + ": Related location: the specification", output.ToString());
    Assert.Contains("/physical-snapshot/second/Main.dfy" + position, output.ToString());
    Assert.Contains("/physical-snapshot/second/Spec.dfy" + position, output.ToString());
    Assert.DoesNotContain(Logical, output.ToString());
    Assert.Equal(Logical + "/Main.dfy", cached.Range.Uri.LocalPath);
    Assert.Equal(Logical + "/Spec.dfy", cached.RelatedInformation[0].Range.Uri.LocalPath);
    Assert.Same(cached.Range, first.Range);
    Assert.Equal(cached.Source, second.Source);
    Assert.Equal(cached.Level, second.Level);
    Assert.Equal(cached.ErrorId, second.ErrorId);
    Assert.Equal(cached.Message, second.Message);
    Assert.Equal(cached.Range.ToDafnyRange(), second.Range.ToDafnyRange());
    Assert.Equal(cached.Range.StartToken.kind, second.Range.StartToken.kind);
  }

  // Physical diagnostic headers still read primary and related excerpts from the captured logical snapshot.
  [Theory]
  [InlineData(Physical)]
  [InlineData("/physical-snapshot/second")]
  public void PhysicalLocationsKeepCapturedExcerpts(string physical) {
    var files = new MemoryFiles(new Dictionary<Uri, string> {
      [new Uri(Logical + "/Main.dfy")] = "  assert false; // captured primary\n",
      [new Uri(Logical + "/Spec.dfy")] = "  assert true; // captured related\n",
      [new Uri(physical + "/Main.dfy")] = "// physical decoy\n"
    });
    using var output = new StringWriter();
    var request = Request(physical);
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      SnippetFileSystem = files,
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, request)
    };
    options.Set(Snippets.ShowSnippets, true);

    options.OutputWriter.WriteDiagnostic(AnalysisSessionCommand.RemapDiagnostic(Diagnostic(), request));

    Assert.Contains(physical + "/Main.dfy(1,2)", output.ToString());
    Assert.Contains(physical + "/Spec.dfy(1,2)", output.ToString());
    Assert.Contains("1 |   assert false; // captured primary", output.ToString());
    Assert.Contains("1 |   assert true; // captured related", output.ToString());
    var excerptLines = output.ToString().Split('\n').Select(line => line.TrimEnd('\r'))
      .Where(line => line.Contains('|')).ToArray();
    Assert.Equal(new[] {
      "  |", "1 |   assert false; // captured primary", "  |   ^^^^^^",
      "  |", "1 |   assert true; // captured related", "  |   ^^^^^^"
    }, excerptLines);
    Assert.DoesNotContain("decoy", output.ToString());
    Assert.Equal(new[] { new Uri(Logical + "/Main.dfy"), new Uri(Logical + "/Spec.dfy") }, files.Reads);
  }

  // Mapping a multi-token diagnostic leaves both endpoints and the retained token chain untouched.
  [Fact]
  public void CachedTokenChainIsUnchanged() {
    var start = Range(Logical + "/Main.dfy").StartToken;
    var end = new Token(1, 10) { Uri = start.Uri, pos = 9, val = "false" };
    var after = new Token(1, 15) { Uri = start.Uri, pos = 14, val = ";" };
    start.Next = end;
    end.Prev = start;
    end.Next = after;
    after.Prev = end;
    var cached = Diagnostic(new TokenRange(start, end));

    var mapped = AnalysisSessionCommand.RemapDiagnostic(cached, Request());
    AnalysisSessionCommand.RemapDiagnostic(cached, Request("/physical-snapshot/second"));

    Assert.Same(start, cached.Range.StartToken);
    Assert.Same(end, cached.Range.EndToken);
    Assert.Same(end, start.Next);
    Assert.Same(start, end.Prev);
    Assert.Same(after, end.Next);
    Assert.Same(end, after.Prev);
    Assert.Equal(Logical + "/Main.dfy", start.Uri.LocalPath);
    Assert.Equal(start.Uri, end.Uri);
    Assert.Same(start, mapped.Range.StartToken);
    Assert.Same(end, mapped.Range.EndToken);
    Assert.Equal(Logical + "/Main.dfy", mapped.Range.EndToken.Uri.LocalPath);
    Assert.Equal(cached.Range.ToDafnyRange(), mapped.Range.ToDafnyRange());
  }

  // Locations outside the exact logical root and non-file URIs retain their original ranges.
  [Theory]
  [InlineData("/external/Spec.dfy")]
  [InlineData("/logical-snapshot/root-other/Spec.dfy")]
  [InlineData("/other/logical-snapshot/root/Spec.dfy")]
  [InlineData("file:///external/Spec.dfy?key=value#anchor")]
  [InlineData("stdin:///")]
  public void ExternalLocationsAreUnchanged(string location) {
    var external = Range(location);
    var cached = Diagnostic(external) with {
      RelatedInformation = [new DafnyRelatedInformation(external, "", ["external"])]
    };

    var mapped = AnalysisSessionCommand.RemapDiagnostic(cached, Request());
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request())
    };
    options.Set(CommonOptionBag.JsonOutput, true);
    options.OutputWriter.WriteDiagnostic(mapped);
    using var document = JsonDocument.Parse(output.ToString());
    var value = document.RootElement.GetProperty("value");

    Assert.Same(external, mapped.Range);
    Assert.Same(external, mapped.RelatedInformation[0].Range);
    Assert.Equal(external.Uri.AbsoluteUri, value.GetProperty("location").GetProperty("uri").GetString());
    Assert.Equal(external.Uri.AbsoluteUri,
      value.GetProperty("relatedInformation")[0].GetProperty("location").GetProperty("uri").GetString());
  }

  // JSON paths and URIs use physical locations while basename mode keeps the full physical URI.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public void JsonLocationsUsePhysicalPaths(bool basename) {
    var cached = Diagnostic();
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      UseBaseNameForFileName = basename,
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request())
    };
    options.Set(CommonOptionBag.JsonOutput, true);

    options.OutputWriter.WriteDiagnostic(AnalysisSessionCommand.RemapDiagnostic(cached, Request()));

    using var document = JsonDocument.Parse(output.ToString());
    var value = document.RootElement.GetProperty("value");
    var primary = value.GetProperty("location");
    var related = value.GetProperty("relatedInformation")[0].GetProperty("location");
    Assert.Equal(new Uri(Physical + "/Main.dfy").AbsoluteUri, primary.GetProperty("uri").GetString());
    Assert.Equal(new Uri(Physical + "/Spec.dfy").AbsoluteUri, related.GetProperty("uri").GetString());
    Assert.Equal(basename ? "Main.dfy" : Physical + "/Main.dfy", primary.GetProperty("filePath").GetString());
    Assert.Equal(basename ? "Spec.dfy" : Physical + "/Spec.dfy", related.GetProperty("filePath").GetString());
    Assert.Equal(1, primary.GetProperty("range").GetProperty("start").GetProperty("line").GetInt32());
    Assert.Equal(2, primary.GetProperty("range").GetProperty("start").GetProperty("character").GetInt32());
    Assert.Equal(Logical + "/Main.dfy", cached.Range.Uri.LocalPath);
  }

  // Mapping a file URI changes its path and preserves the query and fragment components.
  [Fact]
  public void JsonLocationMappingPreservesUriComponents() {
    var cached = Diagnostic(Range("file://" + Logical + "/Main.dfy?key=value#anchor"));
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) {
      PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, Request())
    };
    options.Set(CommonOptionBag.JsonOutput, true);

    options.OutputWriter.WriteDiagnostic(AnalysisSessionCommand.RemapDiagnostic(cached, Request()));

    using var document = JsonDocument.Parse(output.ToString());
    Assert.Equal("file://" + Physical + "/Main.dfy?key=value#anchor",
      document.RootElement.GetProperty("value").GetProperty("location").GetProperty("uri").GetString());
    Assert.Equal("file://" + Logical + "/Main.dfy?key=value#anchor", cached.Range.Uri.AbsoluteUri);
  }

  // Missing or identical root mappings preserve the whole diagnostic and normal basename formatting.
  [Theory]
  [InlineData(null, Physical)]
  [InlineData(Logical, null)]
  [InlineData(Logical, Logical)]
  public void AbsentOrEqualRootsPreserveTheDiagnostic(string? logical, string? physical) {
    var cached = Diagnostic();
    var request = Request() with { LogicalRoot = logical, SourceRoot = physical };
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null) { UseBaseNameForFileName = true };
    options.PrintPathMapper = path => AnalysisSessionCommand.RemapOutputPath(path, request);
    options.Set(Snippets.ShowSnippets, false);

    var mapped = AnalysisSessionCommand.RemapDiagnostic(cached, request);
    options.OutputWriter.WriteDiagnostic(mapped);

    Assert.Same(cached, mapped);
    Assert.StartsWith("Main.dfy(1,2): Error:", output.ToString());
    Assert.Contains("Spec.dfy(1,2): Related location:", output.ToString());
  }

  // Presentation mapping preserves exclusive ranges and special CLI/no-location tokens.
  [Fact]
  public void ExclusiveRangesAndSpecialTokensKeepTheirMeaning() {
    var exclusive = Diagnostic(Range(Logical + "/Main.dfy", inclusive: false));
    var mapped = AnalysisSessionCommand.RemapDiagnostic(exclusive, Request());
    Assert.False(mapped.Range.InclusiveEnd);
    Assert.Equal(exclusive.Range.ToDafnyRange(), mapped.Range.ToDafnyRange());
    foreach (var token in new[] { Token.Cli, Token.NoToken }) {
      var special = Diagnostic(new TokenRange(token, token));
      Assert.Same(special.Range, AnalysisSessionCommand.RemapDiagnostic(special, Request()).Range);
    }
  }

  private sealed class MemoryFiles(Dictionary<Uri, string> values) : IFileSystem {
    public List<Uri> Reads { get; } = [];
    public FileSnapshot ReadFile(Uri uri) {
      Reads.Add(uri);
      return new FileSnapshot(new StringReader(values[uri]), null);
    }
    public bool Exists(Uri path) => values.ContainsKey(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }
}
