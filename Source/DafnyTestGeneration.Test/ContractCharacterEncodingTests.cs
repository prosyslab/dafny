using System.Collections.Generic;
using System.Globalization;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractCharacterEncodingTests {
  // Captured control characters keep their exact scalar value in both supported character modes.
  [Theory]
  [InlineData(0, true)]
  [InlineData(1, true)]
  [InlineData(31, true)]
  [InlineData(127, true)]
  [InlineData(159, true)]
  [InlineData(0, false)]
  [InlineData(31, false)]
  [InlineData(159, false)]
  public async Task ControlCharacterPreservesValue(int scalar, bool unicode) {
    var character = new ContractValue(ContractValueKind.Character, char.ConvertFromUtf32(scalar));
    var source = "method ContractDiagnosticQuery(c:char) requires c == " + ContractModelCodec.ToDafny(character) +
      " { assert {:error \"contract_query_target\"} c as int == " + scalar.ToString(CultureInfo.InvariantCulture) + "; }";
    var result = await Check(source, unicode);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Encoding an observed control character cannot prove a different captured value.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task ControlCharacterRejectsIncorrectValue(bool unicode) {
    var character = new ContractValue(ContractValueKind.Character, "\u0001");
    var source = "method ContractDiagnosticQuery(c:char) requires c == " + ContractModelCodec.ToDafny(character) +
      " { assert {:error \"contract_query_target\"} c as int == 2; }";
    var result = await Check(source, unicode);
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
  }

  // Existing quoting and supplementary scalar encodings retain their original values.
  [Theory]
  [InlineData(39)]
  [InlineData(92)]
  [InlineData(10)]
  [InlineData(0xAC00)]
  [InlineData(0x1F642)]
  public async Task EscapedAndSupplementaryCharacterPreservesValue(int scalar) {
    var character = new ContractValue(ContractValueKind.Character, char.ConvertFromUtf32(scalar));
    var source = "method ContractDiagnosticQuery(c:char) requires c == " + ContractModelCodec.ToDafny(character) +
      " { assert {:error \"contract_query_target\"} c as int == " + scalar.ToString(CultureInfo.InvariantCulture) + "; }";
    var result = await Check(source, true);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Nested captured controls survive datatype, map and sequence rendering together.
  [Fact]
  public async Task NestedCharacterValuesPreserveContainerContents() {
    var character = new ContractValue(ContractValueKind.Character, "\u0001");
    var nested = new ContractValue(ContractValueKind.Datatype, Constructor: "Box",
      Fields: new Dictionary<string, ContractValue> {
        ["items"] = new(ContractValueKind.Map, Entries: [new ContractMapEntry(character,
          new ContractValue(ContractValueKind.Sequence, Items: [character]))])
      });
    var source = "datatype Box = Box(items: map<char,seq<char>>) " +
      "method ContractDiagnosticQuery(b:Box) requires b == " + ContractModelCodec.ToDafny(nested) +
      " { assert {:error \"contract_query_target\"} b.items[1 as char][0] as int == 1; }";
    var result = await Check(source, true);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Correct character rendering does not hide an invalid collection access.
  [Fact]
  public async Task CharacterEncodingRetainsDefinednessErrors() {
    var sequence = new ContractValue(ContractValueKind.Sequence,
      Items: [new ContractValue(ContractValueKind.Character, "\0")]);
    var source = "method ContractDiagnosticQuery(s:seq<char>) requires s == " + ContractModelCodec.ToDafny(sequence) +
      " { assert {:error \"contract_query_target\"} s[1] as int == 0; }";
    var result = await Check(source, true);
    Assert.True(result.Outcome == ContractQueryOutcome.Error, result.Diagnostics);
  }

  private static Task<ContractQueryResult> Check(string source, bool unicode) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.UnicodeCharacters, unicode);
    options.TimeLimit = 5;
    return ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None);
  }
}
