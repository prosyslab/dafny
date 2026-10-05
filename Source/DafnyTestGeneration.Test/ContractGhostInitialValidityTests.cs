#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractGhostInitialValidityTests {
  // A supported captured ghost input participates in the original initial certificate.
  [Fact]
  public async Task SupportedGhostInputParticipatesInInitialCertificate() {
    var (program, campaign) = await Parse("module Store { method Entry(ghost n: int) {} }");
    var value = Integer(2);
    var inputs = Values(("n", value));
    var specifications = await Certify(program, campaign);

    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, inputs, [], specifications);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, inputs, [], specifications);

    Assert.True(initial.Prepared.Method.Ins.Single().IsGhost);
    Assert.Equal(value, initial.Request.Inputs["n"]);
    Assert.NotNull(proof);
    Assert.False(proof.RequiresNativeProof);
    Assert.Equal(1, proof.HostMembershipChecks);
  }

  // Initial preparation rejects an absent ghost value before any type or premise proof can use the sample.
  [Fact]
  public async Task MissingGhostInputIsRejected() {
    var (program, campaign) = await Parse("module Store { method Entry(ghost n: int) {} }");

    var error = Assert.Throws<ArgumentException>(() =>
      ContractRuntimeHeapChecking.PrepareInitial(program, campaign, Values(), []));

    Assert.Contains("Missing captured input 'n'", error.Message);
  }

  // A well-formed value with the wrong concrete kind cannot satisfy the original ghost formal type.
  [Fact]
  public async Task InconsistentGhostInputKindIsRejected() {
    var (program, campaign) = await Parse("module Store { method Entry(ghost n: int) {} }");
    var inputs = Values(("n", new ContractValue(ContractValueKind.Boolean, "true")));
    var specifications = await Certify(program, campaign);

    Assert.Null(ContractInitialTypeProof.TryPrepare(program, campaign, inputs, [], specifications));
  }

  // A ghost input whose value cannot enter the diagnostic compiled-value contract stays unsupported.
  [Fact]
  public async Task NonCompilableGhostInputTypeIsRejected() {
    var (program, campaign) = await Parse("module Store { method Entry(ghost callback: int -> int) {} }");

    Assert.Throws<NotSupportedException>(() => ContractRuntimeHeapChecking.PrepareInitial(program, campaign,
      Values(("callback", Integer(0))), []));
  }

  // Native assignment to the original refined type distinguishes a valid ghost carrier from an invalid one.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Error)]
  public async Task GhostInputRetainsOriginalRefinedType(int value, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("module Store { type Positive = n: int | n > 0 witness 1 method Entry(ghost n: Positive) {} }");
    var inputs = Values(("n", Integer(value)));
    var specifications = await Certify(program, campaign);
    var proof = ContractInitialTypeProof.TryPrepare(program, campaign, inputs, [], specifications);

    Assert.NotNull(proof);
    Assert.True(proof.RequiresNativeProof);
    var result = await ContractSolver.CheckAsync(proof.BuildQuery(), ContractQueryKind.ClosedClause,
      program.Options, CancellationToken.None, queryName: ContractQueryBuilder.Name(proof.Initial.Prepared),
      sourceSnapshots: proof.Initial.Prepared.DiagnosticSourceSnapshots,
      sourcePath: proof.Initial.Prepared.Source.Path);

    Assert.Equal(expected, result.Outcome);
  }

  // Binding the captured ghost value preserves both truth polarities of the original entry requirement.
  [Theory]
  [InlineData(2, ContractQueryOutcome.Unsat)]
  [InlineData(-1, ContractQueryOutcome.Sat)]
  public async Task GhostInputRetainsOriginalRequirement(int value, ContractQueryOutcome expected) {
    var (program, campaign) = await Parse("module Store { method Entry(ghost n: int) requires n > 0 {} }");
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, Values(("n", Integer(value))), []);
    var query = ContractQueryBuilder.Build(initial.Prepared, initial.Request, ContractQueryKind.EntryPrecondition);

    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.EntryPrecondition,
      program.Options, CancellationToken.None, queryName: ContractQueryBuilder.Name(initial.Prepared),
      sourceSnapshots: initial.Prepared.DiagnosticSourceSnapshots, sourcePath: initial.Prepared.Source.Path);

    Assert.Equal(expected, result.Outcome);
  }

  private static async Task<ContractSpecificationChecker> Certify(Program program,
    ContractRuntimeCampaignRequest campaign) {
    var specifications = new ContractSpecificationChecker(program, campaign.Sources, program.Options);
    var scope = ContractInitialTypeProof.RequiredScope(program, campaign, [], specifications);
    Assert.Null(scope.Failure);
    foreach (var module in specifications.PendingModules(scope)) {
      var result = await specifications.CheckModuleAsync(scope, module, CancellationToken.None);
      Assert.True(result.Verified, result.Diagnostics);
    }
    Assert.True(specifications.Accept(scope));
    return specifications;
  }

  private static async Task<(Program Program, ContractRuntimeCampaignRequest Campaign)> Parse(string content) {
    var source = new ContractSource("ghost-initial.dfy", content, ContractHarnessBuilder.Hash(content));
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, [source], CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (program, new ContractRuntimeCampaignRequest(2, [source],
      new ContractEntry("Store.Entry"), "ghost-initial"));
  }

  private static ContractValue Integer(int value) =>
    new(ContractValueKind.Integer, value.ToString(System.Globalization.CultureInfo.InvariantCulture));

  private static Dictionary<string, ContractValue> Values(params (string Name, ContractValue Value)[] values) =>
    values.ToDictionary(pair => pair.Name, pair => pair.Value);
}
