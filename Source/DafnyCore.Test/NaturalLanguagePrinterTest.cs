using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NaturalLanguagePrinterTest {
  private const string Source = @"
module {:options ""--natural-language-blocks""} M {
  method UseNaturalLanguageBlocks() {
    var x := ``pick  one   integer``;
    ``increment x\n  and keep spacing``;
  }
}
";

  private static DafnyOptions CreateOptions() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.NaturalLanguageBlocks, true);
    return options;
  }

  private static async Task<Program> ParseProgram(string text, DafnyOptions options, string fileName) {
    var rootUri = new Uri(fileName);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(text, rootUri, reporter);
    Assert.Equal(0, reporter.ErrorCount);
    return parseResult.Program;
  }

  private static string PrintWithPrinter(Program program, DafnyOptions options) {
    using var writer = new StringWriter();
    var printer = new Printer(writer, options);
    printer.PrintProgram(program, false);
    return writer.ToString();
  }

  private static string PrintWithSimplifyPrinter(Program program, DafnyOptions options) {
    using var writer = new StringWriter();
    var printer = new SimplifyPrinter(writer, options);
    printer.PrintProgram(program, false);
    return writer.ToString();
  }

  [Fact]
  public async Task NaturalLanguagePrinter_PrinterRoundTrip_IsStable() {
    var options = CreateOptions();
    const string uri = "untitled:NaturalLanguagePrinterRoundTrip";
    var firstProgram = await ParseProgram(Source, options, uri);
    var firstPrint = PrintWithPrinter(firstProgram, options);

    Assert.Contains("``pick  one   integer``", firstPrint);
    Assert.Contains("``increment x\\n  and keep spacing``;", firstPrint);

    var secondProgram = await ParseProgram(firstPrint, options, uri);
    var secondPrint = PrintWithPrinter(secondProgram, options);

    Assert.Equal(firstPrint, secondPrint);
  }

  [Fact]
  public async Task NaturalLanguagePrinter_SimplifyPrinterRoundTrip_IsStable() {
    var options = CreateOptions();
    const string uri = "untitled:NaturalLanguageSimplifyPrinterRoundTrip";
    var firstProgram = await ParseProgram(Source, options, uri);
    var firstPrint = PrintWithSimplifyPrinter(firstProgram, options);

    Assert.Contains("``pick  one   integer``", firstPrint);
    Assert.Contains("``increment x\\n  and keep spacing``;", firstPrint);

    var secondProgram = await ParseProgram(firstPrint, options, uri);
    var secondPrint = PrintWithSimplifyPrinter(secondProgram, options);

    Assert.Equal(firstPrint, secondPrint);
  }

  [Fact]
  public void NaturalLanguagePrinter_ExistingFieldLocationBacktickRendering_IsUnchanged() {
    var options = CreateOptions();
    var origin = Token.NoToken;
    var field = new Field(origin, new Name(origin, "f"), false, new IntType(), null);
    var fieldLocation = new FieldLocation(new Name(origin, "f"), field, false);

    Assert.Equal("`f", Printer.ExprToString(options, fieldLocation));
    Assert.Equal("`f", SimplifyPrinter.ExprToString(options, fieldLocation));
  }
}
