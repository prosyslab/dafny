using System.Text.Json;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;

namespace DafnyDriver.Test;

public class JsonVerificationLoggerTests {
  // Successful batches preserve their identity, exact duration and assertion records.
  [Fact]
  public async Task NormalScopePreservesVerificationData() {
    var json = await Log(Result(1, SolverOutcome.Valid), Result(2, SolverOutcome.Valid));

    Assert.Equal(["verificationResults"], json.EnumerateObject().Select(property => property.Name).ToArray());
    var scope = Assert.Single(json.GetProperty("verificationResults").EnumerateArray());
    Assert.Equal("Correct", scope.GetProperty("outcome").GetString());
    Assert.Equal("00:00:03", scope.GetProperty("runTime").GetString());
    var vcResults = scope.GetProperty("vcResults").EnumerateArray().ToArray();
    Assert.Equal([1, 2], vcResults.Select(result => result.GetProperty("vcNum").GetInt32()).ToArray());
    Assert.All(vcResults, result => {
      Assert.Equal("Valid", result.GetProperty("outcome").GetString());
      Assert.Empty(result.GetProperty("assertions").EnumerateArray());
    });
    Assert.Equal(["00:00:01", "00:00:02"],
      vcResults.Select(result => result.GetProperty("runTime").GetString()).ToArray());
  }

  // An empty scope retains a successful outcome with zero elapsed time and no batches.
  [Fact]
  public async Task EmptyScopePreservesVerificationData() {
    var json = await Log();

    var scope = Assert.Single(json.GetProperty("verificationResults").EnumerateArray());
    Assert.Equal("Correct", scope.GetProperty("outcome").GetString());
    Assert.Equal("00:00:00", scope.GetProperty("runTime").GetString());
    Assert.Empty(scope.GetProperty("vcResults").EnumerateArray());
  }

  // Unsuccessful solver outcomes survive aggregation alongside valid batches.
  [Theory]
  [InlineData(SolverOutcome.Invalid, "Errors")]
  [InlineData(SolverOutcome.TimeOut, "TimedOut")]
  [InlineData(SolverOutcome.OutOfResource, "OutOfResource")]
  public async Task MixedScopePreservesUnsuccessfulOutcome(SolverOutcome outcome, string expectedOutcome) {
    var json = await Log(Result(1, SolverOutcome.Valid), Result(2, outcome));

    var scope = Assert.Single(json.GetProperty("verificationResults").EnumerateArray());
    Assert.Equal(expectedOutcome, scope.GetProperty("outcome").GetString());
    var vcResults = scope.GetProperty("vcResults").EnumerateArray().ToArray();
    Assert.Equal("Valid", vcResults[0].GetProperty("outcome").GetString());
    Assert.Equal(outcome.ToString(), vcResults[1].GetProperty("outcome").GetString());
  }

  // Mixed results retain the modern scope schema, outcomes and exact duration strings.
  [Fact]
  public async Task MixedScopeRetainsSchemaOutcomesAndDurations() {
    var json = await Log(
      Result(3, SolverOutcome.Valid),
      Result(4, SolverOutcome.Invalid));

    var scope = Assert.Single(json.GetProperty("verificationResults").EnumerateArray());
    Assert.Equal(["name", "outcome", "runTime", "vcResults"],
      scope.EnumerateObject().Select(property => property.Name).OrderBy(name => name).ToArray());
    Assert.Equal("SyntheticScope", scope.GetProperty("name").GetString());
    Assert.Equal("Errors", scope.GetProperty("outcome").GetString());
    Assert.Equal("00:00:07", scope.GetProperty("runTime").GetString());

    var vcResults = scope.GetProperty("vcResults").EnumerateArray().ToArray();
    Assert.Equal(["Valid", "Invalid"],
      vcResults.Select(vc => vc.GetProperty("outcome").GetString()).ToArray());
    Assert.Equal(["00:00:03", "00:00:04"],
      vcResults.Select(vc => vc.GetProperty("runTime").GetString()).ToArray());
    Assert.All(vcResults, vc => Assert.Equal(
      ["assertions", "outcome", "runTime", "vcNum"],
      vc.EnumerateObject().Select(property => property.Name).OrderBy(name => name).ToArray()));
  }

  private static VerificationTaskResult Result(int vcNumber, SolverOutcome outcome) {
    var partialResult = new VerificationRunResultPartialCopy(
      vcNumber,
      DateTime.UnixEpoch,
      TimeSpan.FromSeconds(vcNumber),
      outcome,
      [],
      Array.Empty<TrackedNodeComponent>(),
      Array.Empty<Axiom>(),
      0);
    return LegacyJsonVerificationLogger.VCResultLogEntryToPartialVerificationRunResult(partialResult);
  }

  private static async Task<JsonElement> Log(params VerificationTaskResult[] results) {
    using var output = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, output, TextWriter.Null);
    var logger = new JsonVerificationLogger(new ProofDependencyManager(), options.OutputWriter);
    logger.Initialize(new Dictionary<string, string>());
    logger.LogScopeResults(new VerificationScopeResult(
      new VerificationScope("SyntheticScope", Microsoft.Boogie.Token.NoToken), results));

    await logger.Flush();

    return JsonDocument.Parse(output.ToString()).RootElement.Clone();
  }
}
