using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractQueryTests {
  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> Prepare(string source) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var request = new ContractTestRequest(1, [new ContractSource("contract.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractEntry("Entry"), new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "2") });
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    return (ContractHarnessBuilder.Prepare(program, request), request);
  }

  // An observed value contradicting the original ensures must remain a satisfiable violation.
  [Fact]
  public async Task WrongObservationViolatesOriginalPostcondition() {
    var (prepared, request) = await Prepare("method Entry(x: int) returns (r: int) ensures r == x + 1 { r := x + 1; }");
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "8") };
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
    Assert.True(result.Outcome == ContractQueryOutcome.Sat, result.Diagnostics);
  }

  // Infinite quantification is translated through Dafny/Boogie rather than compiled away.
  [Fact]
  public async Task OriginalQuantifierAcceptsConcreteCorrectObservation() {
    var (prepared, request) = await Prepare("method Entry(x: int) returns (r: int) ensures forall k: int :: k >= x ==> r <= k { r := x; }");
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "2") };
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
  }

  // An infinite quantified postcondition has a definite false value for this observed result.
  [Fact]
  public async Task OriginalQuantifierRejectsConcreteWrongObservation() {
    var (prepared, request) = await Prepare("method Entry(x: int) returns (r: int) ensures forall k: int :: k >= x ==> r <= k { r := x + 1; }");
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "3") };
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
    var opposite = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs, negate: true);
    var oppositeResult = await ContractSolver.CheckAsync(opposite, ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Unsat, oppositeResult.Outcome);
  }

  // An uncalled abstract specification function can leave both truth values possible for an observed result.
  [Fact]
  public async Task UnobservedPureChoiceDoesNotEstablishDefiniteViolation() {
    var (prepared, request) = await Prepare("function Spec(): (r: int) ensures r == 0 || r == 1\nmethod Entry(x: int) returns (r: int) ensures r == Spec() { r := 0; }");
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "0") };
    foreach (var negate in new[] { false, true }) {
      var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs, negate: negate);
      var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition, prepared.Program.Options, CancellationToken.None);
      Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
    }
  }

  // A contradictory property is tested only after independently establishing a satisfiable input premise.
  [Fact]
  public async Task ContradictoryPostconditionDoesNotEraseInput() {
    var (prepared, request) = await Prepare("method Entry(x: int) returns (r: int) ensures false { r := x; }");
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.PremiseConsistency);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.PremiseConsistency, prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
  }

  // An unproved contract on a real function must not make a concrete input premise inconsistent.
  [Fact]
  public async Task IncorrectImplementedFunctionContractDoesNotEraseInput() {
    var (prepared, request) = await Prepare("""
      function Broken(x:int): (r:int) ensures r == x + 1 { x }
      method Entry(x:int) returns(r:int) requires Broken(x) == x + 1 { r := x; }
      """);
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.EntryPrecondition);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.EntryPrecondition,
      prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
  }

  // An external function's unchecked contract cannot prove a predicate about its actual implementation.
  [Fact]
  public async Task ExternalFunctionEnsuresAreNotDiagnosticAxioms() {
    var (prepared, request) = await Prepare("""
      function {:extern} External(x:int):(r:int) ensures r == x + 1
      method Entry(x:int) returns(r:int) ensures External(x) == x + 1 { r := x; }
      """);
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "2") };
    foreach (var negate in new[] { false, true }) {
      var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition,
        outputs, negate: negate);
      var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition,
        prepared.Program.Options, CancellationToken.None);
      Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
    }
  }

  // Concrete input substitution supplies finite instances while the original quantified assertion remains checked.
  [Fact]
  public async Task ConcreteQuantifierReductionRemainsPartOfOriginalQuery() {
    var (prepared, request) = await Prepare("""
      method Entry(x:int) returns(r:int)
        ensures forall i | 0 <= i < x :: r > i
      { r := x; }
      """);
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, "2") };
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, outputs);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition,
      prepared.Program.Options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("quantifierInstances=2/", result.Diagnostics);
  }

  // A target assertion failure cannot hide a separate division-definedness failure in the same query.
  [Fact]
  public async Task MixedDefinednessAndTargetFailuresRemainQueryErrors() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var result = await ContractSolver.CheckAsync("""
      method ContractDiagnosticQuery(x:int) requires x == 0 {
        assert {:error "contract_query_target"} 1 / x == 0 && false;
      }
      """, ContractQueryKind.ObservedPostcondition, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }
}
