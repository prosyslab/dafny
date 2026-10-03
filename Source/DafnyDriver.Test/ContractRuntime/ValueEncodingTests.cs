#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Captured value encoding; every scenario is one bucket of a single campaign.</summary>
public class ValueEncodingTests : IClassFixture<ValueEncodingTests.Fixture> {
  private static readonly CampaignSpec Main = CampaignSpec.Fixture("ValueEncoding", "Main").Buckets(8);

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [Main];
  }

  public ValueEncodingTests(Fixture fixture) { }

  private static async Task<ContractRuntimeViolation> FirstViolation(int bucket, string clause) {
    var run = await Campaign.RunAsync(Main);
    var violations = run.Violations(bucket, clause);
    Assert.True(violations.Count == CampaignSpec.BucketSize, run.Detail());
    return violations[0];
  }

  // Generic result values retain nested sequence data across a checked callee return.
  [Fact]
  public async Task CapturesGenericCalleeResult() {
    var observed = (await FirstViolation(0, "result == Error")).Values["result"];
    Assert.Equal("M.Result.Ok", observed.Constructor);
    Assert.Equal("f", Assert.Single(observed.Fields!["value"].Items!).Value);
  }

  // Nested generic records preserve Dafny bit widths that share the same CLR byte representation.
  [Fact]
  public async Task CapturesNestedGenericBitvectorShapes() {
    var inputs = (await FirstViolation(1, "tag == 1 ==> false")).Inputs;
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
    var violation = await FirstViolation(2, "box.value == old(box.value) + 2");
    Assert.Equal(ContractValueKind.Reference, violation.Inputs["box"].Kind);
    Assert.Equal("7", violation.Inputs["box.value"].Value);
    Assert.Equal("8", violation.Values["box.value"].Value);
    Assert.Equal(violation.Inputs["box"].Value, violation.Values["box"].Value);
  }

  // Cyclic class fields remain finite snapshots and point back to the same stable reference.
  [Fact]
  public async Task CapturesCyclicReferenceIdentity() {
    var violation = await FirstViolation(3, "cyclic.value == 0");
    Assert.Equal("7", violation.Values["cyclic.value"].Value);
    Assert.Equal(violation.Values["cyclic"].Value, violation.Values["cyclic.next"].Value);
    Assert.False(violation.Values.ContainsKey("cyclic.next.next"));
  }

  // A ghost field compiled for the diagnostic is captured as flat field evidence, while an unused ghost field stays absent.
  [Fact]
  public async Task CapturesCompiledGhostFieldValue() {
    var violation = await FirstViolation(4, "ghosted.f == 8");
    Assert.Equal("7", violation.Inputs["ghosted.f"].Value);
    Assert.Equal("7", violation.Values["ghosted.f"].Value);
    Assert.Equal(ContractValueKind.Reference, violation.Values["ghosted"].Kind);
    Assert.False(violation.Values.ContainsKey("ghosted.unused"));
  }

  // An array value is captured as a stable reference with flat length and element values.
  [Fact]
  public async Task CapturesArrayReferenceElements() {
    var violation = await FirstViolation(5, "a[i] == 1");
    Assert.Equal(ContractRuntimeObligationKind.Postcondition, violation.Kind);
    Assert.Equal(ContractValueKind.Reference, violation.Values["a"].Kind);
    Assert.Equal("2", violation.Values["a.Length"].Value);
    Assert.Equal("2", violation.Values["a[1]"].Value);
  }

  // A faulting executable statement reports its original source line and invalidates the sample.
  [Fact]
  public async Task ReportsOriginalRuntimeErrorLocation() {
    var run = await Campaign.RunAsync(Main);
    var line = PreCompilationTests.LineOf(Main.Sources[0].Content, "var y := values[1];");
    var errors = run.Errors(6);
    Assert.True(errors.Count == CampaignSpec.BucketSize, run.Detail());
    Assert.All(errors, error => {
      Assert.StartsWith("M.dfy:" + line + ":", error.Location);
      Assert.NotEmpty(error.Message);
    });
    Assert.Equal(CampaignSpec.BucketSize, run.Population.RuntimeErrors);
    Assert.Empty(run.Violations(6));
  }

  // Generic functions and methods forward exact nested Dafny shapes even when CLR bitvector types coincide.
  [Fact]
  public async Task CapturesNestedGenericCallSiteBitvectorShapes() {
    var run = await Campaign.RunAsync(Main);
    Assert.True(run.Violations(7, "tag != 7").Count == CampaignSpec.BucketSize, run.Detail());
    var widths = new HashSet<int>();
    foreach (var observation in run.Records(CampaignRun.Ordinals(7)[0])) {
      if (observation.GetProperty("kind").GetString() != "check" ||
          !observation.GetProperty("id").GetString()!.StartsWith("callee_postcondition:", StringComparison.Ordinal)) { continue; }
      foreach (var value in observation.GetProperty("values").EnumerateObject()) {
        var captured = JsonSerializer.Deserialize<ContractValue>(value.Value.GetRawText(), ContractJson.Options)!;
        foreach (var item in captured.Items ?? []) {
          if (item.Kind == ContractValueKind.Bitvector) { widths.Add(item.Width!.Value); }
        }
      }
    }
    Assert.Equal(new[] { 7, 8 }, widths.Order().ToArray());
  }
}
