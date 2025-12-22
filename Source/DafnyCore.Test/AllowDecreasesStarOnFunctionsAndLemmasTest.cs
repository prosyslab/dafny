using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class AllowDecreasesStarOnFunctionsAndLemmasTest {
  private const string FullFilePath = "untitled:AllowDecreasesStarOnFunctionsAndLemmasTest";

  private static async Task<(Program Program, BatchErrorReporter Reporter)> Parse(string dafnyProgramText, DafnyOptions options) {
    var rootUri = new Uri(FullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, reporter);
    return (parseResult.Program, reporter);
  }

  private static async Task<(Program Program, BatchErrorReporter Reporter)> ParseAndResolve(string dafnyProgramText, DafnyOptions options) {
    var (program, reporter) = await Parse(dafnyProgramText, options);
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    return (program, reporter);
  }

  [Fact]
  public async Task DefaultDisallowsDecreasesStarOnFunctionsAndLemmas() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var (_, reporter) = await Parse(@"
function F(n: nat): nat
  decreases *
{
  if n == 0 then 0 else F(n - 1)
}

lemma L(n: nat)
  decreases *
{
  if n != 0 {
    L(n - 1);
  }
}
", options);

    Assert.True(reporter.ErrorCount > 0);
    Assert.Contains(reporter.AllMessages, d => d.Level == ErrorLevel.Error && d.Message.Contains("A '*' expression is not allowed here"));
  }

  [Fact]
  public async Task OptionAllowsDecreasesStarOnFunctionsAndLemmas() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);

    var (_, reporter) = await ParseAndResolve(@"
function F(n: nat): nat
  decreases *
{
  if n == 0 then 0 else F(n - 1)
}

lemma L(n: nat)
  decreases *
{
  if n != 0 {
    L(n - 1);
  }
}
", options);

    Assert.Equal(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
  }

  [Fact]
  public async Task CallingPossiblyNonTerminatingFunctionRequiresCallerToBeMarkedDecreasesStar() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);

    var (program, reporter) = await ParseAndResolve(@"
function F(): int
  decreases *
{
  F()
}

method M() returns (x: int) {
  x := F();
}
", options);

    var warnings = reporter.AllMessagesByLevel[ErrorLevel.Warning]
      .Where(d => d.Source == MessageSource.Resolver)
      .Where(d => d.Message.Contains("a call to a possibly non-terminating function"))
      .ToList();
    Assert.Single(warnings);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
  }

  [Fact]
  public async Task CallingPossiblyNonTerminatingFunctionIsAllowedFromDecreasesStarMethod() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);

    var (_, reporter) = await ParseAndResolve(@"
function F(): int
  decreases *
{
  F()
}

method M() returns (x: int)
  decreases *
{
  x := F();
}
", options);

    Assert.Equal(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
  }
}

