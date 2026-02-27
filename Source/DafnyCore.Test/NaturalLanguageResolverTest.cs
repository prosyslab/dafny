using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NaturalLanguageResolverTest {
  private const string FullFilePath = "untitled:NaturalLanguageResolverTest";
  private const string UnsupportedNaturalLanguageBlocksDiagnostic =
    "Natural-language blocks are parsed experimentally, but semantics are not supported yet";

  private static async Task<(Program Program, BatchErrorReporter Reporter)> ParseAndResolve(string dafnyProgramText,
    DafnyOptions options) {
    var rootUri = new Uri(FullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, reporter);
    var resolver = new ProgramResolver(parseResult.Program);
    await resolver.Resolve(CancellationToken.None);
    return (parseResult.Program, reporter);
  }

  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NaturalLanguageBlocks_ReportDeterministicResolverDiagnostics_InLegacyAndPreType(bool typeSystemRefresh) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.NaturalLanguageBlocks, true);
    options.Set(CommonOptionBag.TypeSystemRefresh, typeSystemRefresh);

    var (_, reporter) = await ParseAndResolve(@"
method UsesNaturalLanguageBlocks() {
  assert ``pick a deterministic integer`` == 0;
  ``increment x in a human-readable way``;
}
", options);

    var diagnostics = reporter.AllMessages
      .Where(message => message.Level == ErrorLevel.Warning)
      .Where(message => message.Source == MessageSource.Resolver)
      .Where(message => message.Message.Contains(UnsupportedNaturalLanguageBlocksDiagnostic))
      .ToList();

    Assert.Equal(0, reporter.ErrorCount);
    Assert.Equal(2, diagnostics.Count);
  }
}
