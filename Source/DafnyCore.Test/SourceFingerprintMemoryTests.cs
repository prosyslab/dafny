using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyCore.Test;

// Every source is an in-memory dictionary entry; the scanner and hash never access these paths.
public sealed class SourceFingerprintMemoryTests {
  private const string SourcePath = "/workspace/source-fingerprint-memory.dfy";

  private static string Fingerprint(string content) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    var result = SourceFingerprint.Compute(options, new SourceFingerprintRequest([
      new("source", SourcePath, null, [])
    ]), new Dictionary<string, string> { [SourcePath] = content }, out var error);
    Assert.Null(error);
    return Assert.Single(result!.Fingerprints).Sha256;
  }

  // Whitespace and comments do not change the analyzer's shared token identity.
  [Fact]
  public void IgnoresFormattingAndComments() {
    Assert.Equal(Fingerprint("method M() { assert true; }"),
      Fingerprint("// comment\n method M ( ) { /* comment */ assert true ; }"));
  }

  // Boolean weakening changes the same token fingerprint used by definition analysis.
  [Fact]
  public void DistinguishesWeakenedProperty() {
    Assert.NotEqual(Fingerprint("method M() { assert P(); }"),
      Fingerprint("method M() { assert P() || true; }"));
  }

  // Reordering statements changes the fingerprint even when every original token remains present.
  [Fact]
  public void PreservesStatementOrder() {
    Assert.NotEqual(Fingerprint("method M() { A(); B(); }"),
      Fingerprint("method M() { B(); A(); }"));
  }

  // Region spans are checked against the supplied UTF-8 bytes and cannot split a multibyte token.
  [Fact]
  public void RejectsSplitUtf8Token() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    var result = SourceFingerprint.Compute(options, new SourceFingerprintRequest([
      new("source", SourcePath, new(0, 1), [])
    ]), new Dictionary<string, string> { [SourcePath] = "α" }, out var error);

    Assert.Null(result);
    Assert.Contains("splits a token", error);
  }

  // Missing dictionary entries fail closed without trying the process filesystem.
  [Fact]
  public void RejectsMissingSnapshot() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    var result = SourceFingerprint.Compute(options, new SourceFingerprintRequest([
      new("source", SourcePath, null, [])
    ]), new Dictionary<string, string>(), out var error);

    Assert.Null(result);
    Assert.Contains("supplied Dafny source", error);
  }
}
