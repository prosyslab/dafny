using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractScreenSourcePreparationTests {
  // Explicit local types remain traversable until the original body is omitted.
  [Fact]
  public async Task ExplicitlyTypedLocalPreparesContractsOnlyProjection() {
    const string source = "method Child(x: int) returns (y: int) ensures y == x + 1 { var z: int := 0; y := x + 1; }";
    var reporter = Reporter();

    var parsed = await Prepare(source, reporter);

    Assert.Equal(0, reporter.ErrorCount);
    Assert.NotNull(parsed.Projection);
    Assert.Equal("Child", parsed.Projection.Target.Name);
    Assert.Equal(parsed.Projection.Target, Assert.Single(parsed.Projection.Members));
    var omitted = Assert.Single(parsed.OmittedBodies);
    Assert.Equal("Child", omitted.Symbol);
    Assert.Equal(source.IndexOf('{'), omitted.Start);
    Assert.Equal(source.Length, omitted.End);
    var method = ContractCallableSelector.SelectMethod(parsed.Program, new("Child"));
    Assert.Null(method.Body);
    Assert.Single(method.Ens);
  }

  // Declaration options are rejected before projection even when the body has a typed local.
  [Fact]
  public async Task DeclarationOptionsRemainRejected() {
    const string source = "method {:options \"/quantifierSyntax:4\"} Child(x: int) returns (y: int) { var z: int := 0; y := x; }";
    var reporter = Reporter();

    var failure = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(source, reporter));

    Assert.Equal(0, reporter.ErrorCount);
    Assert.Equal("source_options", failure.Message);
  }

  // Module options stay visible to the raw module scan despite typed locals in nested declarations.
  [Fact]
  public async Task ModuleOptionsRemainRejected() {
    const string source = "module {:options \"/quantifierSyntax:4\"} M { method Child(x: int) returns (y: int) { var z: int := 0; y := x; } }";
    var reporter = Reporter();

    var failure = await Assert.ThrowsAsync<NotSupportedException>(() => Prepare(source, reporter, "M.Child"));

    Assert.Equal(0, reporter.ErrorCount);
    Assert.Equal("source_options", failure.Message);
  }

  private static BatchErrorReporter Reporter() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    return new BatchErrorReporter(options);
  }

  private static Task<ContractScreenParsed> Prepare(string source, BatchErrorReporter reporter, string symbol = "Child") =>
    ContractScreenSourcePreparation.ParseAsync(reporter,
      [new("input.dfy", source, ContractHarnessBuilder.Hash(source))], CancellationToken.None, target: new(symbol));
}
