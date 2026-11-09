using System.Text.Json;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;
using BoogieParser = Microsoft.Boogie.Parser;

namespace DafnyDriver.Test;

/// <summary>
/// Sessions pin VerifySnapshots=1 for native result caching. Boogie then gives every lambda its own {:checksum}
/// attribute, and its alpha-equality compares attribute parameter lists by reference, so equal lambdas stop sharing
/// one lifted function. A proof that relies on two equal set comprehensions being the same term then fails in the
/// session while the one-shot CLI (VerifySnapshots 0) proves it.
/// </summary>
[Collection("Proof input translation")]
public class AnalysisSessionLambdaLiftingTests {
  private const string Boogie = """
    function F(m: [int]bool): int;
    procedure P(n: int) returns (r: bool)
    {
      r := F((lambda q: int :: q < n)) == F((lambda q: int :: q < n));
    }
    """;

  private static DafnyOptions SnapshotOptions() {
    var options = DafnyOptions.CreateUsingOldParser(TextWriter.Null);
    options.VerifySnapshots = 1;
    return options;
  }

  private static Microsoft.Boogie.Program Parse(DafnyOptions options) {
    Assert.Equal(0, BoogieParser.Parse(Boogie, "Lambdas.bpl", out var program));
    Assert.Equal(0, program.Resolve(options));
    Assert.Equal(0, program.Typecheck(options));
    return program;
  }

  private static List<Microsoft.Boogie.Function> Lifted(Microsoft.Boogie.Program program) =>
    program.Functions.Where(function => function.Name.StartsWith("lambda#")).ToList();

  [Fact]
  public void BoogieSnapshotLiftingDoesNotShareEqualLambdas() {
    var options = SnapshotOptions();
    var program = Parse(options);
    LambdaHelper.ExpandLambdas(options, program);
    // The cause, pinned so that a fixed Boogie makes this test fail and the session workaround can be revisited.
    Assert.Equal(2, Lifted(program).Count);
  }

  [Fact]
  public void SessionLiftingSharesEqualLambdasAndKeepsTheDependencyChecksum() {
    var options = SnapshotOptions();
    var program = Parse(options);
    AnalysisSessionCommand.LiftLambdasAsOneShot(options, program);
    var lifted = Assert.Single(Lifted(program));
    Assert.Equal("lambda expression", lifted.Checksum);
    Assert.Equal(0, program.Resolve(options));
    Assert.Equal(0, program.Typecheck(options));
    // The engine's own lifting then has nothing left to lift.
    LambdaHelper.ExpandLambdas(options, program);
    Assert.Single(Lifted(program));
  }

  [Fact]
  public void LiftingWithoutSnapshotsIsLeftToTheEngine() {
    var options = SnapshotOptions();
    options.VerifySnapshots = 0;
    var program = Parse(options);
    AnalysisSessionCommand.LiftLambdasAsOneShot(options, program);
    Assert.Empty(Lifted(program));
  }

  private const string Cwd = "/workspace/session-lambda";
  private const string Path = Cwd + "/Count.dfy";
  // Valid: one-shot `dafny verify` proves it; with distinct lifted functions the two comprehensions are only
  // extensionally equal and the postcondition is not proved.
  private const string Source = """
    module Count {
      opaque ghost function Count(s: seq<int>, n: nat): nat
      {
        |set q: nat | q < n && q < |s| && s[q] > 0|
      }

      lemma SameComprehension(s: seq<int>, n: nat)
        ensures Count(s, n) == |set q: nat | q < n && q < |s| && s[q] > 0|
      {
        reveal Count();
      }
    }
    """;

  [Fact]
  public async Task SessionVerifiesAProofThatNeedsEqualComprehensionsToBeOneTerm() {
    using var session = new AnalysisSessionCommand.Session();
    var response = await session.Execute(new AnalysisSessionCommand.Request("count",
      ["verify", "--standard-libraries:false", "--log-format:json", Path], Cwd, "role",
      new Dictionary<string, string> { [Path] = Source }), CancellationToken.None);
    Assert.True(response.Returncode == 0, response.Stdout + response.Stderr);
    var evidence = JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions);
    Assert.True(evidence.GetProperty("solverRunCount").GetInt32() > 0);
  }

  // An ill-formed Boogie program is rejected by the pre-lift pass, as the engine would reject it, never accepted.
  [Theory]
  [InlineData("procedure P(n: int) { var b: [int]bool; b := (lambda q: int :: q < n && Undeclared(q)); }", "resolution errors")]
  [InlineData("function F(m: [int]bool): int;\nprocedure P(n: int) { var x: int; x := F((lambda q: int :: q + true)); }", "type errors")]
  public void IllFormedProgramsAreRejectedBeforeLifting(string text, string expected) {
    Assert.Equal(0, BoogieParser.Parse(text, "Invalid.bpl", out var program));
    var error = Assert.Throws<ArgumentException>(() => AnalysisSessionCommand.LiftLambdasAsOneShot(SnapshotOptions(), program));
    Assert.Contains(expected, error.Message);
  }
}
