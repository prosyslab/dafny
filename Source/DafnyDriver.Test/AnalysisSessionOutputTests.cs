using DafnyDriver.Commands;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class AnalysisSessionOutputTests {
  // A real diagnostic cannot corrupt a proof-input JSON document or weaken warning policy.
  [Theory]
  [InlineData(ErrorLevel.Warning, true)]
  [InlineData(ErrorLevel.Warning, false)]
  [InlineData(ErrorLevel.Error, true)]
  public void ProofInputDiagnosticsStaySeparateFromJson(ErrorLevel level, bool allowWarnings) {
    using var stdout = new StringWriter();
    using var stderr = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, stdout, stderr) {
      FailOnWarnings = !allowWarnings
    };
    options.Set(CommonOptionBag.AllowWarnings, allowWarnings);
    options.Set(DefinitionAnalysisCommand.IncludeProofInputs, true);
    AnalysisSessionCommand.RouteAnalysisDiagnostics(options, "definition-analysis");
    var reporter = new ConsoleErrorReporter(options);
    reporter.Message(MessageSource.Resolver, level, "retained_diagnostic", Token.Cli, "retained diagnostic");
    stdout.Write("{\"definitions\":[]}");

    Assert.Equal("{\"definitions\":[]}", stdout.ToString());
    Assert.Contains("retained diagnostic", stderr.ToString());
    Assert.Equal(1, reporter.Count(level));
    Assert.Equal(allowWarnings, options.Get(CommonOptionBag.AllowWarnings));
    Assert.Equal(!allowWarnings, options.FailOnWarnings);
  }

  // Routing proof-input diagnostics does not redirect other CLI request output.
  [Theory]
  [InlineData("resolve")]
  [InlineData("verify")]
  [InlineData("definition-analysis")]
  public void OtherRequestDiagnosticsKeepTheirWriter(string command) {
    using var stdout = new StringWriter();
    using var stderr = new StringWriter();
    var options = new DafnyOptions(TextReader.Null, stdout, stderr);
    AnalysisSessionCommand.RouteAnalysisDiagnostics(options, command);
    var reporter = new ConsoleErrorReporter(options);
    reporter.Warning(MessageSource.Resolver, "retained_diagnostic", Token.Cli, "retained diagnostic");

    Assert.Contains("retained diagnostic", stdout.ToString());
    Assert.Empty(stderr.ToString());
    Assert.Equal(1, reporter.Count(ErrorLevel.Warning));
  }
}
