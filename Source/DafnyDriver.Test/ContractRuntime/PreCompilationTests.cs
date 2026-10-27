#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Requests that end before the runtime diagnostic is compiled.</summary>
public class PreCompilationTests : IClassFixture<PreCompilationTests.Fixture> {
  private const string File = "PreCompilation";
  private static readonly CampaignSpec Drafts = CampaignSpec.Fixture(File, "Drafts") with { Generator = null };
  private static readonly CampaignSpec NoGenerator = CampaignSpec.Fixture(File, "NoGenerator");
  private static readonly CampaignSpec GeneratorDraft = CampaignSpec.Fixture(File, "GeneratorDraft");
  private static readonly CampaignSpec GeneratorSyntax = CampaignSpec.Fixture(File, "GeneratorSyntax",
    generatorPath: ".top-down-pbt/generators/Goal.dfy");
  private static readonly CampaignSpec OrdinalInput = CampaignSpec.Fixture(File, "OrdinalInput");
  private static readonly CampaignSpec HigherOrderShape = CampaignSpec.Fixture(File, "HigherOrderShape");
  private static readonly CampaignSpec ShapeCollision = CampaignSpec.Fixture(File, "ShapeCollision");

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() =>
      [Drafts, NoGenerator, GeneratorDraft, GeneratorSyntax, OrdinalInput, HigherOrderShape, ShapeCollision];
  }

  public PreCompilationTests(Fixture fixture) { }

  // Missing drafts take precedence over a missing generator, whose signature is still reported.
  [Fact]
  public async Task DraftsTakePrecedenceOverMissingGenerator() {
    var run = await Campaign.RunAsync(Drafts);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, run.Result.Status);
    Assert.NotNull(run.Result.MissingGenerator);
  }

  // Bodyless and assert-false scaffold callees are requested with their original signature and contract.
  [Theory]
  [InlineData("M.Helper")]
  [InlineData("M.Scaffold")]
  public async Task RequestsMissingCalleeDraft(string symbol) {
    var run = await Campaign.RunAsync(Drafts);
    var missing = Assert.Single(run.Result.MissingDrafts, draft => draft.Symbol == symbol);
    Assert.Equal(ContractRuntimeDraftKind.Method, missing.Kind);
    Assert.Contains("returns", missing.Signature);
    Assert.Contains("ensures", missing.Contract);
  }

  // Unimplemented native externs are requested as drafts of their own kind rather than called natively.
  [Theory]
  [InlineData("M.NativeMethod", ContractRuntimeDraftKind.ExternMethod)]
  [InlineData("M.NativeFunction", ContractRuntimeDraftKind.Function)]
  public async Task RequestsExternDraftKind(string symbol, ContractRuntimeDraftKind kind) {
    var run = await Campaign.RunAsync(Drafts);
    Assert.Equal(kind, Assert.Single(run.Result.MissingDrafts, draft => draft.Symbol == symbol).Kind);
  }

  // A missing generator is surfaced before compilation or sample execution.
  [Fact]
  public async Task RequiresGenerator() {
    var run = await Campaign.RunAsync(NoGenerator);
    Assert.Equal(ContractRuntimeStatus.GeneratorRequired, run.Result.Status);
    Assert.NotNull(run.Result.MissingGenerator);
    Assert.Equal(0, run.Population.Generated);
  }

  // A missing implementation reached only through the generator is reported at its original source line.
  [Fact]
  public async Task ReportsGeneratorMissingDraftAtOriginalLine() {
    var run = await Campaign.RunAsync(GeneratorDraft);
    Assert.Equal(ContractRuntimeStatus.DraftsRequired, run.Result.Status);
    var missing = Assert.Single(run.Result.MissingDrafts);
    Assert.Equal("M.dfy", missing.Path);
    Assert.Equal(LineOf(GeneratorDraft.Sources[0].Content, "method MakeInput"), missing.Line);
  }

  // A generator syntax error is an unsupported result naming its model-relative path with line and column.
  [Fact]
  public async Task LocatesGeneratorSyntaxError() {
    var run = await Campaign.RunAsync(GeneratorSyntax);
    Assert.Equal(ContractRuntimeStatus.Unsupported, run.Result.Status);
    Assert.Contains(".top-down-pbt/generators/Goal.dfy:2:8: invalid Rhs", run.Result.Reason);
    Assert.Equal(0, run.Population.Generated);
  }

  // Non-compilable ghost inputs fail before requesting an impossible concrete generator.
  [Fact]
  public async Task RejectsOrdinalInput() {
    var run = await Campaign.RunAsync(OrdinalInput);
    Assert.Equal(ContractRuntimeStatus.Unsupported, run.Result.Status);
    Assert.Contains("non_compilable_input_type", run.Result.Reason);
  }

  // First-class generic references remain explicit unsupported results until they can carry shape arguments.
  [Fact]
  public async Task RejectsGenericHigherOrderShapeErasure() {
    var run = await Campaign.RunAsync(HigherOrderShape);
    Assert.Equal(ContractRuntimeStatus.Unsupported, run.Result.Status);
    Assert.Contains("unsupported_generic_reference", run.Result.Reason);
    Assert.Contains("Generic higher-order function references", run.Result.Reason);
    Assert.Equal(0, run.Population.Generated);
  }

  // User formals cannot shadow the generated type-shape parameters.
  [Fact]
  public async Task RejectsGenericShapeFormalCollision() {
    var run = await Campaign.RunAsync(ShapeCollision);
    Assert.Equal(ContractRuntimeStatus.Unsupported, run.Result.Status);
    Assert.Contains("reserved_diagnostic_name", run.Result.Reason);
    Assert.Contains("Reserved Pbt diagnostic name collision", run.Result.Reason);
    Assert.Equal(0, run.Population.Generated);
  }

  internal static int LineOf(string source, string text) =>
    source[..source.IndexOf(text, StringComparison.Ordinal)].Count(character => character == '\n') + 1;
}
