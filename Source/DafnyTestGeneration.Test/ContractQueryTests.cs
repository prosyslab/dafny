using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractQueryTests {
  // Reading the original readonly value activates its type/RHS facts without adding any assumption.
  [Fact]
  public async Task UnprunedReadonlyFactsExposeInconsistentDatatype() {
    const string source = "type Empty = value:int | false witness * datatype Item = Item { const bad:Empty := 0 } " +
      "method ContractDiagnosticQuery() { assert Item().bad == 0; assert {:error \"contract_query_target\"} false; }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.PremiseConsistency, options, CancellationToken.None);
    Assert.True(result.Outcome == ContractQueryOutcome.Unsat, result.Diagnostics);
  }

  // Proof-only queries recover quantified proofs without using target counterexamples as concrete models.
  [Theory]
  [InlineData("exists k:int :: result == 2*k", ContractQueryOutcome.Unsat)]
  [InlineData("forall n:int :: n <= result", ContractQueryOutcome.Sat)]
  [InlineData("!(forall n:int :: n <= result)", ContractQueryOutcome.Unsat)]
  [InlineData("exists k:int :: 10 / (result-result) == k", ContractQueryOutcome.Error)]
  public async Task ProofOnlyQuantifiersRetainOriginalAssertionAndDefinedness(string assertion, ContractQueryOutcome expected) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    using var cancellation = new CancellationTokenSource(3000);
    var source = "method ContractDiagnosticQuery(result:int) requires result == 4 " +
      "{ assert {:error \"contract_query_target\"} " + assertion + "; }";
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, cancellation.Token,
      deadlineTimestamp: ContractQueryDeadline.AfterMilliseconds(3000));
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // A false nonlinear existential cannot turn into a valid proof through native proof pruning.
  [Fact]
  public async Task ProofOnlyNonlinearFalseClauseIsNotProved() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    var result = await ContractSolver.CheckAsync("method ContractDiagnosticQuery() " +
      "{ assert {:error \"contract_query_target\"} exists k:int :: k*k == 2; }",
      ContractQueryKind.ClosedClause, options, CancellationToken.None);
    Assert.NotEqual(ContractQueryOutcome.Unsat, result.Outcome);
  }

  // Unused inconsistent global type axioms must remain in every premise or model-producing query despite inherited pruning.
  [Theory]
  [InlineData(ContractQueryKind.ClosedClause, false, ContractQueryOutcome.Sat)]
  [InlineData(ContractQueryKind.ObservedPostcondition, false, ContractQueryOutcome.Sat)]
  [InlineData(ContractQueryKind.PremiseConsistency, false, ContractQueryOutcome.Unsat)]
  [InlineData(ContractQueryKind.ContractRealization, false, ContractQueryOutcome.Unsat)]
  [InlineData(ContractQueryKind.ContractRealization, true, ContractQueryOutcome.Unsat)]
  [InlineData(ContractQueryKind.ClosedClause, true, ContractQueryOutcome.Unsat)]
  public async Task ModelAndPremiseQueriesRetainUnusedInconsistentAxiom(ContractQueryKind kind, bool captureModel, ContractQueryOutcome expected) {
    const string source = "type Empty = value:int | false witness 0 ghost const unused:Empty " +
      "method ContractDiagnosticQuery() { assert {:error \"contract_query_target\"} false; }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 3;
    options.Prune = true;
    var result = await ContractSolver.CheckAsync(source, kind, options, CancellationToken.None, captureModel);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Inherited routine-ignore filters cannot skip native diagnostic correctness or well-definedness obligations.
  [Theory]
  [InlineData("x > 0", ContractQueryOutcome.Unsat)]
  [InlineData("x < 0", ContractQueryOutcome.Error)]
  public async Task IgnoresInheritedRoutineSuppression(string precondition, ContractQueryOutcome expected) {
    var source = "function Partial(x:int):int requires " + precondition + " { x } " +
      "method ContractDiagnosticQuery(x:int) requires x == 2 { assert {:error \"contract_query_target\"} Partial(x) == x; }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    options.ProcsToIgnore = ["*"];
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Native reveals retain imported opaque definitions and their transitive bodies in both goal polarities.
  [Theory]
  [InlineData(3, false, ContractQueryOutcome.Unsat)]
  [InlineData(4, false, ContractQueryOutcome.Sat)]
  [InlineData(3, true, ContractQueryOutcome.Sat)]
  [InlineData(4, true, ContractQueryOutcome.Unsat)]
  public async Task OriginalOpaqueDefinitionsSupportBothPolarities(int expectedValue, bool negate, ContractQueryOutcome expected) {
    var source = "module Model { opaque function Leaf(x:int):int { x + 1 } opaque function Wrapper(x:int):int { Leaf(x) } } " +
      "module Client { import M = Model method Entry(x:int) ensures M.Wrapper(x) == " + expectedValue + " {} }";
    var (prepared, request) = await Prepare(source, "Client.Entry");
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, negate: negate);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition,
      prepared.Program.Options, CancellationToken.None, sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Equal(source, request.Sources[0].Content);
  }

  // Revealing an original opaque body does not excuse an invalid precondition in either truth polarity.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task OriginalOpaqueCallPreservesDefinedness(bool negate) {
    const string source = "module Model { opaque function Partial(x:int):int requires x > 2 { x } } " +
      "module Client { import M = Model method Entry(x:int) ensures M.Partial(x) == x {} }";
    var (prepared, request) = await Prepare(source, "Client.Entry");
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, negate: negate);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition,
      prepared.Program.Options, CancellationToken.None, sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // A provided-only export does not make its hidden body available as a query proof in either polarity.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task OriginalOpaqueExportRemainsHidden(bool negate) {
    const string source = "module Model { export provides Hidden opaque function Hidden(x:int):int { x + 1 } } " +
      "module Client { import M = Model method Entry(x:int) ensures M.Hidden(x) == 3 {} }";
    var (prepared, request) = await Prepare(source, "Client.Entry");
    var query = ContractQueryBuilder.Build(prepared, request, ContractQueryKind.ObservedPostcondition, negate: negate);
    var result = await ContractSolver.CheckAsync(query, ContractQueryKind.ObservedPostcondition,
      prepared.Program.Options, CancellationToken.None, sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
  }

  // A hidden opaque precondition cannot supply a concrete consistency witness through its unconstrained abstraction.
  [Fact]
  public async Task OriginalOpaquePremiseRequiresDefinitionAccess() {
    const string source = "module Model { export provides Hidden opaque function Hidden(x:int):bool { false } } " +
      "module Client { import M = Model method Entry(x:int) requires M.Hidden(x) {} }";
    var (prepared, request) = await Prepare(source, "Client.Entry");
    Assert.Throws<NotSupportedException>(() => ContractQueryBuilder.Build(prepared, request,
      ContractQueryKind.PremiseConsistency, outputs: new Dictionary<string, ContractValue>()));
  }

  // Translating only the diagnostic owner preserves imported definitions in either truth polarity.
  [Theory]
  [InlineData(3, false, ContractQueryOutcome.Unsat)]
  [InlineData(4, false, ContractQueryOutcome.Sat)]
  [InlineData(3, true, ContractQueryOutcome.Sat)]
  [InlineData(4, true, ContractQueryOutcome.Unsat)]
  public async Task ScopedTranslationPreservesImportedDefinition(int observed, bool negate, ContractQueryOutcome expected) {
    var source = $$"""
      module Definitions {
        function Next(x: int): int { x + 1 }
      }
      module Diagnostic {
        import D = Definitions
        method ContractDiagnosticQuery(x: int, result: int)
          requires x == 2
          requires result == {{observed}}
        { assert {:error "contract_query_target"} {{(negate ? "!(result == D.Next(x))" : "result == D.Next(x)")}}; }
      }
      """;
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var phases = new List<(string Phase, string State)>();
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options,
      CancellationToken.None, phaseObserver: (phase, state) => phases.Add((phase, state)));
    Assert.True(result.Outcome == expected, result.Diagnostics);
    var solverStarts = phases.Where(item => item.Phase.StartsWith("boogie:", StringComparison.Ordinal) && item.State == "started").ToList();
    Assert.Single(solverStarts);
    Assert.Equal("boogie:Diagnostic", solverStarts[0].Phase);
  }

  // A false imported call precondition blocks both truth polarities even when reduction folds the equality.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task ScopedTranslationPreservesImportedPrecondition(bool negate) {
    var source = $$"""
      module Definitions {
        function Partial(x: int): int requires x > 0 { x }
      }
      module Diagnostic {
        import D = Definitions
        method ContractDiagnosticQuery(x: int)
          requires x == 0
        { assert {:error "contract_query_target"} {{(negate ? "!(D.Partial(x) == D.Partial(x))" : "D.Partial(x) == D.Partial(x)")}}; }
      }
      """;
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    var result = await ContractSolver.CheckAsync(source, ContractQueryKind.ClosedClause, options, CancellationToken.None);
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  private static async Task<(ContractPreparedProgram Prepared, ContractTestRequest Request)> Prepare(string source, string entry = "Entry") {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var request = new ContractTestRequest(1, [new ContractSource("contract.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractEntry(entry), new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "2") });
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
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

  // Imported constructor identities survive rendering in fixed-state and closed runtime queries.
  [Theory]
  [InlineData(false, false)]
  [InlineData(false, true)]
  [InlineData(true, false)]
  [InlineData(true, true)]
  public async Task ImportedDatatypeConstructorRetainsScope(bool closed, bool wrong) {
    var (prepared, request) = await Prepare("""
      module Schema { datatype Item = Box(value: int) }
      module Client {
        import Data = Schema
        datatype Item = Box(value: bool)
        method Entry(x: int) returns (r: int)
          ensures Data.Box(x).value == r
        { r := x; }
      }
      """, "Client.Entry");
    await CheckImportedClause(prepared, request, closed, wrong);
  }

  // Imported static function calls retain the import alias instead of the synthetic default class.
  [Theory]
  [InlineData(false, false)]
  [InlineData(false, true)]
  [InlineData(true, false)]
  [InlineData(true, true)]
  public async Task ImportedStaticFunctionRetainsScope(bool closed, bool wrong) {
    var (prepared, request) = await Prepare("""
      module Library { function Identity(x: int): int { x } }
      module Client {
        import Ops = Library
        function Identity(x: int): int { x + 100 }
        method Entry(x: int) returns (r: int)
          ensures Ops.Identity(x) == r
        { r := x; }
      }
      """, "Client.Entry");
    await CheckImportedClause(prepared, request, closed, wrong);
  }

  // Function descriptors retain imported static identities after cloning erases receiver surface syntax.
  [Theory]
  [InlineData(false, false)]
  [InlineData(false, true)]
  [InlineData(true, false)]
  [InlineData(true, true)]
  public async Task FunctionDescriptorRetainsImportedScope(bool closed, bool wrong) {
    var (prepared, request) = await Prepare("""
      module Library { function Identity(x: int): int { x } }
      module Client {
        import Ops = Library
        function Identity(x: int): int { x + 100 }
        function Entry(x: int): (r: int)
          ensures r == Ops.Identity(x)
        { x } by method { return x; }
      }
      """, "Client.Entry");
    await CheckImportedClause(prepared, request, closed, wrong);
  }

  // A query inserted outside a class still selects that class's static function rather than a module shadow.
  [Theory]
  [InlineData(false, false)]
  [InlineData(false, true)]
  [InlineData(true, false)]
  [InlineData(true, true)]
  public async Task ClassStaticFunctionRetainsScope(bool closed, bool wrong) {
    var (prepared, request) = await Prepare("""
      module Client {
        function Identity(x: int): int { x + 100 }
        class Worker {
          static function Identity(x: int): int { x }
          static method Entry(x: int) returns (r: int)
            ensures r == Identity(x)
          { r := x; }
        }
      }
      """, "Client.Worker.Entry");
    await CheckImportedClause(prepared, request, closed, wrong);
  }

  private static async Task CheckImportedClause(ContractPreparedProgram prepared,
    ContractTestRequest request, bool closed, bool wrong) {
    var outputs = new Dictionary<string, ContractValue> { ["r"] = new(ContractValueKind.Integer, wrong ? "3" : "2") };
    var clause = new ContractRuntimeClause(new ContractRuntimeObligation("entry-post", ContractRuntimeObligationKind.Postcondition,
      "contract.dfy", 1, 1, "original", null, ContractRuntimeDecisionMethod.ClosedSmt, null, new()),
      prepared.Method.Ens[0].E, prepared.Method.Ins.Concat(prepared.Method.Outs).Cast<IVariable>().ToList(), prepared.Method);
    var values = request.Inputs.Concat(outputs).ToDictionary(pair => pair.Key, pair => pair.Value);
    foreach (var negate in new[] { false, true }) {
      var kind = closed ? ContractQueryKind.ClosedClause : ContractQueryKind.ObservedPostcondition;
      var source = closed ? ContractQueryBuilder.BuildClosedClause(prepared, clause, values, negate) :
        ContractQueryBuilder.Build(prepared, request, kind, outputs, negate);
      var result = await ContractSolver.CheckAsync(source, kind, prepared.Program.Options, CancellationToken.None,
        queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
      var expected = wrong != negate ? ContractQueryOutcome.Sat : ContractQueryOutcome.Unsat;
      Assert.True(result.Outcome == expected, result.Diagnostics + "\n" + source);
    }
  }
}
