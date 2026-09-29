#nullable enable
using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

public class ContractRuntimeObservationTests {
  // Generic result values retain nested sequence data across a checked callee return.
  [Fact]
  public async Task CapturesGenericCalleeResult() {
    const string source = """
      module M {
        datatype Result<T> = Ok(value: T) | Error
        method Read() returns (result: Result<seq<char>>)
          ensures result == Ok(['f'])
        { result := Ok(['f']); }
        method Goal(x: int) returns (result: Result<seq<char>>)
          ensures result == Error
        { result := Read(); }
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    Assert.Equal(1, result.Population.Valid);
    var violation = Assert.Single(result.Violations);
    var observed = violation.Values["result"];
    Assert.Equal("M.Result.Ok", observed.Constructor);
    Assert.Equal("f", Assert.Single(observed.Fields!["value"].Items!).Value);
  }

  // Nested generic records preserve Dafny bit widths that share the same CLR byte representation.
  [Fact]
  public async Task CapturesNestedGenericBitvectorShapes() {
    const string source = """
      module M {
        datatype Result<T> = Ok(value: T) | Error
        datatype Envelope<T> = Envelope(data: map<int, seq<Result<T>>>)
        method Goal(left: Envelope<bv7>, right: Envelope<bv8>) ensures false {}
      }
      """;
    const string generator = """
      method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
        returns (left: Envelope<bv7>, right: Envelope<bv8>) {
        left := Envelope(map[1 := [Ok(7 as bv7)]]);
        right := Envelope(map[1 := [Ok(7 as bv8)]]);
      }
      """;
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    var inputs = Assert.Single(result.Violations).Inputs;
    foreach (var (name, width) in new[] { ("left", 7), ("right", 8) }) {
      var mapping = inputs[name].Fields!["data"];
      var item = Assert.Single(Assert.Single(mapping.Entries!).Value.Items!);
      var value = item.Fields!["value"];
      Assert.Equal(ContractValueKind.Bitvector, value.Kind);
      Assert.Equal(width, value.Width);
      Assert.Equal("7", value.Value);
    }
  }

  // Entry and postcondition snapshots retain a mutated field without losing reference identity.
  [Fact]
  public async Task CapturesReferenceFieldValues() {
    const string source = """
      module M {
        class Box {
          var value: int
          constructor(value: int) { this.value := value; }
        }
        method Goal(box: Box) modifies box
          ensures box.value == old(box.value) + 2
        { box.value := box.value + 1; }
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box(7); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    var violation = Assert.Single(result.Violations);
    Assert.Equal(ContractValueKind.Reference, violation.Inputs["box"].Kind);
    Assert.Equal("7", violation.Inputs["box.value"].Value);
    Assert.Equal("8", violation.Values["box.value"].Value);
    Assert.Equal(violation.Inputs["box"].Value, violation.Values["box"].Value);
  }

  // Cyclic class fields remain finite snapshots and point back to the same stable reference.
  [Fact]
  public async Task CapturesCyclicReferenceIdentity() {
    const string source = """
      module M {
        class Box {
          var value: int
          var next: Box?
          constructor(value: int) { this.value := value; this.next := null; }
        }
        method Goal(box: Box) ensures box.value == 0 {}
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box(7); box.next := box; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    var violation = Assert.Single(result.Violations);
    Assert.Equal("7", violation.Values["box.value"].Value);
    Assert.Equal(violation.Values["box"].Value, violation.Values["box.next"].Value);
    Assert.False(violation.Values.ContainsKey("box.next.next"));
  }

  // A ghost field compiled for the diagnostic is captured as flat field evidence, while an unused ghost field stays absent.
  [Fact]
  public async Task CapturesCompiledGhostFieldValue() {
    const string source = "module M { class Box { ghost var f: int ghost var unused: int constructor() { f := 7; } } method Goal(x: Box) ensures x.f == 8 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: Box) { x := new Box(); }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    var violation = Assert.Single(result.Violations);
    Assert.Equal("7", violation.Inputs["x.f"].Value);
    Assert.Equal("7", violation.Values["x.f"].Value);
    Assert.Equal(ContractValueKind.Reference, violation.Values["x"].Kind);
    Assert.False(violation.Values.ContainsKey("x.unused"));
  }

  // An array value is captured as a stable reference with flat length and element values.
  [Fact]
  public async Task CapturesArrayReferenceElements() {
    const string source = "module M { method Goal(n: nat) returns (a: array<int>) ensures forall i :: 0 <= i < n ==> a[i] == 1 { a := new int[n]; var j := 0; while j < n invariant 0 <= j <= n { a[j] := 2; j := j + 1; } } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (n: nat) { n := 2; }";
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, result.Reason + "\n" + result.Diagnostics);
    var violation = result.Violations.Single(v => v.Kind == ContractRuntimeObligationKind.Postcondition);
    Assert.Equal(ContractValueKind.Reference, violation.Values["a"].Kind);
    Assert.Equal("2", violation.Values["a.Length"].Value);
    Assert.Equal("2", violation.Values["a[1]"].Value);
  }

  // A faulting executable statement reports its original source line and invalidates the sample.
  [Fact]
  public async Task ReportsOriginalRuntimeErrorLocation() {
    const string source = """
      module M {
        method Goal(x: int) {
          var values := [x];
          var y := values[1];
        }
      }
      """;
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 7; }";
    var result = await Run(source, generator);
    Assert.Equal(0, result.Population.Valid);
    Assert.Equal(1, result.Population.RuntimeErrors);
    var error = Assert.Single(result.RuntimeErrors);
    Assert.StartsWith("M.dfy:4:", error.Location);
    Assert.NotEmpty(error.Message);
  }

  private static async Task<ContractRuntimeCampaignResult> Run(string source, string generator) {
    var directory = Path.Combine("/workspace/tmp", "contract-runtime-observations-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var request = new ContractRuntimeCampaignRequest(1,
      [new("M.dfy", source, ContractHarnessBuilder.Hash(source))], new("M.Goal"), "17",
      Generator: new("G.dfy", generator, ContractHarnessBuilder.Hash(generator)),
      SampleCount: 1, TimeoutMilliseconds: 60000, MaxClosedQueries: 0);
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(60));
    return await ContractRuntimeCampaignRunner.RunAsync(request, options, directory, timeout.Token);
  }
}
