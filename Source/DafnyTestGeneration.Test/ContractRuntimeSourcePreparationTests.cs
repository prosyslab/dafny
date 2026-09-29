#nullable enable
using System;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeSourcePreparationTests {
  private const string Source = "module M { method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } method Goal(x: int) returns (y: int) ensures y == x + 1 { y := Helper(x); } }";
  private const string Generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 2; }";

  // A draft body and its helpers run under the original helper contract, ignoring draft specifications.
  [Fact]
  public async Task ReplacesBodyAndPreservesContract() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) ensures y == -9 { y := Increment(x); } function Increment(x: int): int { x + 1 }";
    var prepared = await Prepare(Source, draft);
    var content = Assert.Single(prepared.Sources).Content;
    Assert.Contains("ensures y == x + 1", content);
    Assert.DoesNotContain("ensures y == -9", content);
    Assert.DoesNotContain("assert false", content);
    await Resolve(prepared);
  }

  // A draft whose output name differs from the original callable cannot be substituted.
  [Fact]
  public async Task RejectsSignatureMismatch() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (other: int) { other := x; }";
    var exception = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(Source, draft));
    Assert.Contains("signature", exception.Message);
  }

  // A draft helper cannot shadow an existing module-level declaration.
  [Fact]
  public async Task RejectsHelperCollision() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; } function Goal(x: int): int { x }";
    var exception = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(Source, draft));
    Assert.Contains("collides", exception.Message);
  }

  // Once a helper has a real body, an older reusable draft must not replace its implementation.
  [Fact]
  public async Task KeepsImplementedHelper() {
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := -100; }";
    var prepared = await Prepare(Source.Replace("assert false;", "y := x + 1;"), draft);
    Assert.DoesNotContain("-100", prepared.Sources[0].Content);
    await Resolve(prepared);
  }

  // Generator outputs must preserve the goal input names and types.
  [Fact]
  public async Task RejectsGeneratorMismatch() {
    var exception = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(
      Source.Replace("assert false;", "y := x + 1;"), null,
      Generator.Replace("returns (x: int)", "returns (z: int)").Replace("x :=", "z :=")));
    Assert.Contains("outputs", exception.Message);
  }

  // Unicode comments and inserted declarations cannot shift the reported original contract location.
  [Fact]
  public async Task MapsOriginalUtf8Position() {
    var source = "// 한글\n" + Source.Replace("assert false;", "y := x + 1;");
    var prepared = await Prepare(source, null);
    var marker = "ensures y == x + 1";
    var current = prepared.Sources[0];
    var position = Encoding.UTF8.GetByteCount(current.Content[..current.Content.IndexOf(marker, StringComparison.Ordinal)]);
    var location = prepared.SourceMap.ResolveLocation(ContractSourceSnapshot.UriFor(current.Path), position, "M.Helper");
    Assert.Equal(2, location.Line);
    Assert.Equal(source.IndexOf(marker, StringComparison.Ordinal) - source.IndexOf('\n'), location.Column);
    Assert.Equal(ContractHarnessBuilder.Hash(source), location.Sha256);
    Assert.Equal("M.dfy", location.Path);
  }

  // Bodyless external declarations receive the draft body and lose their native binding.
  [Fact]
  public async Task ReplacesBodylessExtern() {
    const string source = "module M { method {:extern} {:axiom} Helper(x: int) returns (y: int) ensures y == x + 1 method Goal(x: int) returns (y: int) { y := Helper(x); } }";
    const string draft = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x + 1; }";
    var prepared = await Prepare(source, draft);
    Assert.DoesNotContain("{:extern}", prepared.Sources[0].Content);
    Assert.DoesNotContain("{:axiom}", prepared.Sources[0].Content);
    await Resolve(prepared);
  }

  // Bodyless functions retain their original ensures while receiving the draft expression.
  [Fact]
  public async Task ReplacesBodylessFunction() {
    const string source = "module M { function {:axiom} Helper(x: int): int ensures Helper(x) == x + 1 method Goal(x: int) returns (y: int) { y := Helper(x); } }";
    const string draft = "function {:pbt_draft \"M.Helper\"} Helper(x: int): int ensures Helper(x) == -9 { x + 1 }";
    var prepared = await Prepare(source, draft);
    Assert.DoesNotContain("ensures Helper(x) == -9", prepared.Sources[0].Content);
    await Resolve(prepared);
  }

  // A class member's draft body stays inside the class while its helper declarations stay in the module.
  [Fact]
  public async Task ReplacesClassMember() {
    const string source = "module M { class Device { method {:extern} {:axiom} Helper(x: int) returns (y: int) ensures y == x + 1 } method Goal(x: int, device: Device) returns (y: int) { y := device.Helper(x); } }";
    const string draft = "method {:pbt_draft \"M.Device.Helper\"} Helper(x: int) returns (y: int) { y := Increment(x); } function Increment(x: int): int { x + 1 }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int, device: Device) { x := 2; device := new Device; }";
    var prepared = await Prepare(source, draft, generator, "M.Device.Helper");
    await Resolve(prepared);
  }

  // Explicit constructor parameters preserve annotation order and retain the original inaccessible constructor.
  [Fact]
  public async Task AddsOrderedDiagnosticConstructorWithoutChangingOriginal() {
    const string source = "module M { class Box { ghost var left: int ghost var right: int constructor Init() requires false {} } method Goal(box: Box) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Box\", \"M.Box.right\", \"M.Box.left\"} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box.ContractDiagnosticCreate(2, 1); }";
    var prepared = await Prepare(source, null, generator);
    await Resolve(prepared);
    Assert.Contains("constructor Init() requires false", prepared.Sources[0].Content);
    Assert.Contains("constructor {:pbt_supplied_fields \"right\", \"left\"} ContractDiagnosticCreate(ghost right: int, ghost left: int)",
      prepared.Sources[0].Content);
    Assert.Contains("M.Box.ContractDiagnosticCreate", prepared.DiagnosticConstructors!);
  }

  // A diagnostic constructor cannot omit a runtime field even if the selected goal does not read it.
  [Fact]
  public async Task RejectsOmittedRuntimeConstructorField() {
    const string source = "module M { class Box { var value: int } method Goal(box: Box) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Box\"} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box.ContractDiagnosticCreate(); }";
    var error = await Assert.ThrowsAsync<ArgumentException>(() => Prepare(source, null, generator));
    Assert.Contains("omits required non-ghost field", error.Message);
  }

  // An omitted ghost field used by the original postcondition remains required supplied state.
  [Fact]
  public async Task RejectsRelevantOmittedConstructorField() {
    const string source = "module M { class Box { ghost var value: int } method Goal(box: Box) ensures box.value == 7 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Box\"} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box.ContractDiagnosticCreate(); }";
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(source, null, generator));
    Assert.Contains("is omitted", error.Message);
  }

  // Malformed or ambiguous field declarations do not create a diagnostic constructor.
  [Theory]
  [InlineData("\"M.Box\", \"M.Box.value\", \"M.Box.value\"")]
  [InlineData("\"M.Box\", \"M.Other.value\"")]
  [InlineData("\"M.Box\", 1")]
  [InlineData("\"M.Box\", \"M.Box.value.inner\"")]
  [InlineData("\"M.Box\", \"M.Box.\"")]
  public async Task RejectsInvalidConstructorAnnotation(string arguments) {
    const string source = "module M { class Box { ghost var value: int } method Goal(box: Box) {} }";
    var generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor " + arguments + "} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box.ContractDiagnosticCreate(7); }";
    await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(source, null, generator));
  }

  // Leaf paths and default allocations give each distinct inner shape its own generated constructor.
  [Fact]
  public async Task NestedPathsGenerateOneConstructorPerInnerShape() {
    const string source = "module M { class Box { ghost var value: int constructor Init() requires false {} } " +
      "class Pair { ghost const left: Box ghost const right: Box constructor Init() requires false {} } method Goal(pair: Pair) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Pair\", \"M.Pair.left.value\"} " +
      "Generate(r: PbtRandom.Source) returns (pair: Pair) { pair := new Pair.ContractDiagnosticCreate(3); }";
    var prepared = await Prepare(source, null, generator);
    await Resolve(prepared);
    Assert.Equal(new[] { "M.Box.ContractDiagnosticCreate_1", "M.Box.ContractDiagnosticCreate_2", "M.Pair.ContractDiagnosticCreate" },
      prepared.DiagnosticConstructors!.Order(StringComparer.Ordinal));
  }

  // One field cannot be both a constructor parameter and a nested allocation.
  [Fact]
  public async Task RejectsParameterAndNestedPathForOneField() {
    const string source = "module M { class Box { ghost var value: int constructor Init() requires false {} } " +
      "class Pair { ghost const left: Box constructor Init() requires false {} } method Goal(pair: Pair) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} {:pbt_heap_constructor \"M.Pair\", \"M.Pair.left\", \"M.Pair.left.value\"} " +
      "Generate(r: PbtRandom.Source) returns (pair: Pair) { pair := new Pair.ContractDiagnosticCreate(null, 3); }";
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(source, null, generator));
    Assert.Contains("both a parameter and a nested allocation", error.Message);
  }

  private static async Task<ContractRuntimePreparedSources> Prepare(string source, string? draft,
    string generator = Generator, string draftSymbol = "M.Helper") {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var snapshots = new[] { new ContractSource("M.dfy", source, ContractHarnessBuilder.Hash(source)) };
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    var drafts = draft == null ? Array.Empty<ContractRuntimeDraft>() :
      new[] { new ContractRuntimeDraft(draftSymbol, "Helper.dfy", draft, ContractHarnessBuilder.Hash(draft)) };
    return await ContractRuntimeSourcePreparation.PrepareAsync(program, snapshots, goal, drafts,
      new("Generator.dfy", generator, ContractHarnessBuilder.Hash(generator)), options, CancellationToken.None);
  }

  private static async Task Resolve(ContractRuntimePreparedSources prepared) {
    const string runtime = "module PbtRandom { class Source {} }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(reporter,
      prepared.Sources.Append(new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))).ToList(),
      CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }
}
