using System.CommandLine;
using System.CommandLine.Parsing;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NaturalLanguageBlocksOptionTest {
  private static ParseResult ParseParserOptions(params string[] args) {
    var command = new RootCommand();
    foreach (var option in DafnyCommands.ParserOptions) {
      command.AddOption(option);
    }

    return command.Parse(args);
  }

  [Fact]
  public void NaturalLanguageBlocks_DefaultOff() {
    Assert.Contains(DafnyCommands.ParserOptions, option => option == CommonOptionBag.NaturalLanguageBlocks);

    var parserOptionResult = ParseParserOptions();
    Assert.False(parserOptionResult.GetValueForOption(CommonOptionBag.NaturalLanguageBlocks));
  }

  [Fact]
  public void NaturalLanguageBlocks_OptionOn() {
    var parserOptionResult = ParseParserOptions("--natural-language-blocks");
    Assert.True(parserOptionResult.GetValueForOption(CommonOptionBag.NaturalLanguageBlocks));
  }

  [Fact]
  public void NaturalLanguageIntermediateProductsDirectory_DefaultOff() {
    Assert.Contains(DafnyCommands.ParserOptions,
      option => option == CommonOptionBag.NaturalLanguageIntermediateProductsDirectory);

    var parserOptionResult = ParseParserOptions();
    Assert.Null(parserOptionResult.GetValueForOption(CommonOptionBag.NaturalLanguageIntermediateProductsDirectory));
  }

  [Fact]
  public void NaturalLanguageIntermediateProductsDirectory_OptionOn() {
    var parserOptionResult = ParseParserOptions("--natural-language-intermediate-products-directory", "out/nl-intermediates");
    Assert.Equal("out/nl-intermediates", parserOptionResult.GetValueForOption(CommonOptionBag.NaturalLanguageIntermediateProductsDirectory)?.ToString());
  }
}
