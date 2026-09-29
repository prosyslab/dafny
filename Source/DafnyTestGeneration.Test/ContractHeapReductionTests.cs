#nullable enable
using System;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractHeapReductionTests {
  // Native proofs retain both epoch semantics and legitimate target counterexamples.
  [Theory]
  [InlineData("old(a.value) == 1 && a.value == 3", ContractQueryOutcome.Unsat)]
  [InlineData("old(a).value == 3", ContractQueryOutcome.Unsat)]
  [InlineData("a.value == 1", ContractQueryOutcome.Sat)]
  [InlineData("Delta(a) == 2", ContractQueryOutcome.Unsat)]
  [InlineData("Captured(a.value)", ContractQueryOutcome.Unsat)]
  public async Task NativeHeapProjectionPreservesOriginalTarget(string property, ContractQueryOutcome expected) {
    var result = await Check(Source("", "a.value := 3;", property));
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("addedCheckedEquivalences=1", result.Diagnostics);
    Assert.Contains("inlineDepth=2", result.Diagnostics);
  }

  // An unknown alias must invalidate current facts; only explicit equality/distinctness can preserve them.
  [Theory]
  [InlineData("requires a == b", "b.value == 3", ContractQueryOutcome.Unsat)]
  [InlineData("requires a != b", "b.value == 1", ContractQueryOutcome.Unsat)]
  [InlineData("", "b.value == 1", ContractQueryOutcome.Sat)]
  public async Task NativeHeapProjectionInvalidatesMayAliases(string alias, string property, ContractQueryOutcome expected) {
    var result = await Check(Source("requires b.value == 1 " + alias, "a.value := 3;", property));
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("aliasInvalidations=", result.Diagnostics);
  }

  // Only a resolved explicit reveal makes an opaque original definition available to projection.
  [Theory]
  [InlineData("reveal Opaque();", ContractQueryOutcome.Unsat)]
  [InlineData("", ContractQueryOutcome.Sat)]
  public async Task NativeHeapProjectionRespectsReveals(string reveal, ContractQueryOutcome expected) {
    var result = await Check(Source("", reveal + "a.value := 3;", "Opaque(a)"));
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains(reveal.Length == 0 ? "statefulInlines=0" : "statefulInlines=1", result.Diagnostics);
  }

  // Original call preconditions remain WD obligations even if the projected function body is concrete.
  [Fact]
  public async Task NativeHeapProjectionRejectsUndefinedCall() {
    var result = await Check(Source("", "a.value := 3;", "Bad(a) == 3"));
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
  }

  // A failed auxiliary equivalence is never mistaken for a target counterexample or proof.
  [Fact]
  public async Task NativeHeapProjectionRejectsFailedEquivalence() {
    var result = await Check("method ContractDiagnosticQuery() { assert {:error \"contract_reduction_equivalence\"} false; " +
      "assert {:error \"contract_query_target\"} true; }");
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
    Assert.Contains(ContractQueryHeapReduction.EquivalenceMarker, result.Diagnostics);
  }

  // Unsupported executable effects retain the complete original query without a projection step.
  [Theory]
  [InlineData("if a.value == 1 { a.value := 3; }")]
  [InlineData("Set(a);")]
  public async Task NativeHeapProjectionLeavesUnsupportedEffects(string body) {
    var result = await Check(Source("", body, "a.value == 3"));
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.DoesNotContain("addedCheckedEquivalences=1", result.Diagnostics);
  }

  // Projection leaves the original statements, target expression, source and attributes intact.
  [Fact]
  public async Task HeapProjectionPreservesResolvedOriginalIdentities() {
    var (program, method) = await Parse(Source("", "a.value := 3;", "old(a.value) == 1 && a.value == 3"));
    var originals = method.Body!.Body.ToArray();
    var target = (AssertStmt)originals[^1];
    var expression = target.Expr;
    var token = target.Origin;
    var attributes = target.Attributes;
    using var log = new StringWriter();
    Assert.True(ContractQueryHeapReduction.TryApply(program, method, log));
    var added = Assert.Single(method.Body.Body.Except(originals));
    Assert.Equal(originals, method.Body.Body.Where(statement => statement != added));
    Assert.Same(expression, target.Expr);
    Assert.Same(token, target.Origin);
    Assert.Same(attributes, target.Attributes);
    Assert.Equal(BinaryExpr.Opcode.Iff, Assert.IsType<BinaryExpr>(Assert.IsType<AssertStmt>(added).Expr).Op);
  }

  // An unavailable label remains a native old expression rather than using the entry epoch.
  [Fact]
  public async Task NativeHeapProjectionLeavesLabeledOld() {
    var result = await Check(Source("", "a.value := 2; label L: a.value := 3;", "old@L(a.value) == 2"));
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("unsupported_statement", result.Diagnostics);
    Assert.DoesNotContain("addedCheckedEquivalences=1", result.Diagnostics);
  }

  // The native language rejects twostate calls in old's single-state context before reduction.
  [Fact]
  public async Task NativeHeapProjectionDoesNotAdmitInvalidOldCall() {
    var result = await Check(Source("", "a.value := 3;", "old(Delta(a)) == 0"));
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
    Assert.Contains("two-state context", result.Diagnostics);
    Assert.DoesNotContain("addedCheckedEquivalences=1", result.Diagnostics);
  }

  // A literal readonly cell remains fixed while unrelated mutable state changes.
  [Fact]
  public async Task NativeHeapProjectionPreservesReadonlyCell() {
    var result = await Check(Source("requires a.tag == 7", "a.value := 3;", "a.tag == 7 && old(a.tag) == 7"));
    Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
    Assert.Contains("entryReads=2", result.Diagnostics);
  }

  // A missing heap-dependent actual cannot be substituted beneath the callee's old.
  [Fact]
  public async Task NativeHeapProjectionLeavesUncapturedArgument() {
    var result = await Check(Source("", "a.value := 3;", "Captured(a.omitted)"));
    Assert.Equal(ContractQueryOutcome.Sat, result.Outcome);
    Assert.Contains("uncaptured_call_argument_or_label", result.Diagnostics);
  }

  // Imported definitions unfold only in the resolved signature's scope, including diagnostic resolution.
  [Theory]
  [InlineData("provides", false, ContractQueryOutcome.Sat, 0)]
  [InlineData("reveals", false, ContractQueryOutcome.Unsat, 1)]
  [InlineData("provides", true, ContractQueryOutcome.Unsat, 1)]
  [InlineData("reveals", true, ContractQueryOutcome.Unsat, 1)]
  public async Task NativeHeapProjectionKeepsImportedVisibility(string visibility, bool disableScopes,
    ContractQueryOutcome expected, int statefulInlines) {
    var source = "module Store { export reveals Cell provides Cell.value " + visibility + " Good " +
      "class Cell { var value:int } predicate Good(c:Cell) reads c { c.value == 3 } } " +
      "module Client { import Store method ContractDiagnosticQuery(c:Store.Cell) requires c.value == 1 modifies c " +
      "{ c.value := 3; assert {:error \"contract_query_target\"} Store.Good(c); } }";
    var result = await Check(source, disableScopes);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("statefulInlines=" + statefulInlines, result.Diagnostics);
    Assert.Contains("currentReads=" + statefulInlines, result.Diagnostics);
  }

  // An unbounded body remains intact so a native nonproof cannot become an auxiliary equivalence error.
  [Theory]
  [InlineData("true", "original", ContractQueryOutcome.Sat)]
  [InlineData("false", "original", ContractQueryOutcome.Sat)]
  [InlineData("true", "no-quantifier", ContractQueryOutcome.Unsat)]
  public async Task NativeHeapProjectionPreservesQuantifiedMatch(string positive, string shape, ContractQueryOutcome expected) {
    var source = """
module Store {
  class Cell { var value: int function Value(): int reads this { value } }
  datatype Command = Command(mode: bool)
  function Build(raw: bool): Command { Command(raw) }
}
module Client {
  import Store
  datatype Witness = Empty | Value(n: int)
  twostate predicate Relation(c: Store.Cell, raw: bool, trace: Witness) reads c {
    var cmd := Store.Build(raw);
    if cmd.mode then c.Value() == old(c.Value()) + 2 else
      match trace case Empty => false case Value(n) => c.Value() == n && old(c.Value()) == n - 2
  }
  twostate predicate Summary(c: Store.Cell, raw: bool) reads c {
    exists trace: Witness :: Relation(c, raw, trace)
  }
  method ContractDiagnosticQuery(c: Store.Cell) requires c.value == 1 modifies c {
    c.value := 3;
    assert {:error "contract_query_target"} POSITIVE == Summary(c, false);
  }
}
""".Replace("POSITIVE", positive);
    if (shape == "no-quantifier") {
      source = source.Replace("var cmd := Store.Build(raw);", "").Replace("cmd.mode", "raw")
        .Replace("match trace case Empty => false case Value(n) => c.Value() == n && old(c.Value()) == n - 2", "c.Value() == old(c.Value()) + 2")
        .Replace("exists trace: Witness :: Relation(c, raw, trace)", "Relation(c, raw, Empty)");
    }
    var result = await Check(source, disableScopes: true);
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("addedCheckedEquivalences=1", result.Diagnostics);
    if (shape == "original") { Assert.Contains("unbounded_quantifier", result.Diagnostics); }
  }

  // Finite domains project concrete instances, but an unproved negative iff still fails the auxiliary gate.
  [Theory]
  [InlineData(3, ContractQueryOutcome.Unsat)]
  [InlineData(4, ContractQueryOutcome.Error)]
  public async Task NativeHeapProjectionUnrollsFiniteDomain(int expectedValue, ContractQueryOutcome expected) {
    var result = await Check(Source("", "a.value := 3;",
      "forall i:int | 0 <= i < 2 :: a.value == " + expectedValue));
    Assert.True(result.Outcome == expected, result.Diagnostics);
    Assert.Contains("addedCheckedEquivalences=1", result.Diagnostics);
    Assert.Contains("quantifierInstances=", result.Diagnostics);
    Assert.DoesNotContain("quantifierInstances=0", result.Diagnostics);
    if (expected == ContractQueryOutcome.Error) {
      Assert.Contains("Error: " + ContractQueryHeapReduction.EquivalenceMarker, result.Diagnostics);
    }
  }

  private static string Source(string requirements, string body, string property) => """
class Cell { var value:int ghost var omitted:int const tag:int := 7 }
twostate function Delta(c:Cell):int reads c { c.value - old(c.value) }
twostate predicate Captured(x:int) { old(x) == x && x == 3 }
opaque predicate Opaque(c:Cell) reads c { c.value == 3 }
function Bad(c:Cell):int requires false reads c { c.value }
method Set(c:Cell) modifies c ensures c.value == 3 { c.value := 3; }
method ContractDiagnosticQuery(a:Cell,b:Cell) requires a.value == 1 REQUIREMENTS modifies a,b
{ BODY assert {:error "contract_query_target"} PROPERTY; }
""".Replace("REQUIREMENTS", requirements).Replace("BODY", body).Replace("PROPERTY", property);

  private static async Task<(Program, Method)> Parse(string source) {
    var options = Options();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter,
      [new ContractSource("model.dfy", source, ContractHarnessBuilder.Hash(source))], CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var method = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
      .SelectMany(type => type.Members).OfType<Method>().Single(method => method.Name == ContractQueryBuilder.QueryName);
    return (program, method);
  }

  private static DafnyOptions Options(bool disableScopes = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    options.DisableScopes = disableScopes;
    return options;
  }

  private static async Task<ContractQueryResult> Check(string source, bool disableScopes = false) {
    using var timeout = new CancellationTokenSource(10000);
    return await ContractSolver.CheckAsync(source, ContractQueryKind.ObservedPostcondition, Options(disableScopes), timeout.Token,
      deadlineTimestamp: ContractQueryDeadline.AfterMilliseconds(10000));
  }
}
