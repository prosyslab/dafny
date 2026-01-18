using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class PartialEvaluatorTest {
  private static async Task<Program> ParseAndResolve(string dafnyProgramText, DafnyOptions options) {
    const string fullFilePath = "untitled:partial-eval";
    var rootUri = new Uri(fullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    Assert.Equal(0, errorReporter.ErrorCount);

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    return program;
  }

  private static async Task<(Program Program, BatchErrorReporter Reporter)> ParseAndResolveWithReporter(
    string dafnyProgramText, DafnyOptions options) {
    const string fullFilePath = "untitled:partial-eval-reporter";
    var rootUri = new Uri(fullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    return (program, errorReporter);
  }

  private static IEnumerable<Statement> DescendantStatements(Statement root) {
    var stack = new Stack<Statement>();
    stack.Push(root);
    while (stack.Count > 0) {
      var current = stack.Pop();
      yield return current;
      foreach (var child in current.SubStatements) {
        stack.Push(child);
      }
    }
  }

  [Fact]
  public async Task PartialEvaluation_InlinesEntryAndPropagatesConstants() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 3U);

    var program = await ParseAndResolve(@"
predicate Spec(x: int) { forall i :: 0 < i < x ==> i == 0 }
predicate Wrap(x: int) { Spec(x + 0) }

method Entry() {
  assert Wrap(5);
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    Assert.NotNull(entry.Body);

    var assertStmt = DescendantStatements(entry.Body!)
      .OfType<AssertStmt>()
      .Single();
    var assertExpr = assertStmt.Expr.Resolved ?? assertStmt.Expr;

    var forallExpr = Assert.IsType<ForallExpr>(assertExpr);
    Assert.NotNull(forallExpr.Bounds);
    Assert.Single(forallExpr.Bounds);
    var bound = Assert.IsType<IntBoundedPool>(forallExpr.Bounds![0]);

    Assert.NotNull(bound.UpperBound);
    Assert.True(Expression.IsIntLiteral(bound.UpperBound, out var upper));
    Assert.Equal(5, (int)upper);

    Assert.NotNull(bound.LowerBound);
    Assert.True(Expression.IsIntLiteral(bound.LowerBound, out var lower));
    Assert.Equal(1, (int)lower);

    var calls = assertExpr.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .Select(call => call.Function.Name)
      .ToList();
    Assert.DoesNotContain("Spec", calls);
    Assert.DoesNotContain("Wrap", calls);
  }

  [Fact]
  public async Task PartialEvaluation_NoEntryConfiguredRunsWithoutWarnings() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var (_, reporter) = await ParseAndResolveWithReporter(@"
method Entry() {
  assert true;
}
", options);

    Assert.Empty(reporter.AllMessagesByLevel[ErrorLevel.Warning]
      .Where(d => d.Source == MessageSource.Rewriter));
  }

  [Fact]
  public async Task PartialEvaluation_WarnsWhenEntryIsMissing() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "MissingEntry");

    var (_, reporter) = await ParseAndResolveWithReporter(@"
method ActualEntry() {
  assert true;
}
", options);

    var warnings = reporter.AllMessagesByLevel[ErrorLevel.Warning]
      .Where(d => d.Source == MessageSource.Rewriter)
      .Select(d => d.Message)
      .ToList();
    Assert.Contains(warnings, m => m.Contains("Partial evaluation entry 'MissingEntry' was not found"));
  }

  [Fact]
  public async Task PartialEvaluation_WarnsOnMultipleEntries() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");

    var (_, reporter) = await ParseAndResolveWithReporter(@"
class A {
  method Entry() { }
}

class B {
  method Entry() { }
}
", options);

    var warnings = reporter.AllMessagesByLevel[ErrorLevel.Warning]
      .Where(d => d.Source == MessageSource.Rewriter)
      .Select(d => d.Message)
      .ToList();
    Assert.Contains(warnings, m => m.Contains("Multiple callables named 'Entry'"));
  }

  [Fact]
  public async Task PartialEvaluation_SimplifiesStatementsAndOperators() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 2U);

    var program = await ParseAndResolve(@"
opaque function G(): int { 1 }

method Foo(x: int) { }

method Entry(x: int, b: bool) returns (r: int) {
  var y := x;
  y := 0 + y;
  y := y + 0;
  y := y - 0;
  y := 1 + 2;
  y := 0 * y;
  y := 1 * y;
  y := y * 0;
  y := y * 1;
  y := 4 / 2;
  y := 1 / 0;
  y := 5 % 2;
  y := 1 % 0;
  y := (1 + 1);
  y := if true then 1 else 2;
  y := if b then 1 else 2;
  y := (var t := 1 + 1; t);

  if true && b { } else { }

  while 0 < 1
    invariant 1 + 1 == 2
    decreases 3 - 0
  { }

  assert true && b;
  assert b && true;
  assert false || b;
  assert b || true;
  assert true ==> b;
  assert b ==> false;
  assert true <==> b;
  assert b <==> false;
  assert 1 < 2;
  assert 2 <= 2;
  assert 3 > 2;
  assert 3 >= 3;
  assert true == false;
  assert 1 != 1;
  assert (0 + y) == y;
  assert !false;
  assert 1 in {1};
  assume 1 + 1 == 2;
  expect 1 + 1 == 2, ""ok"";
  Foo(1 + 1);
  reveal G();
  hide G;
  forall i | 0 <= i < 1 + 1 {
    assert 1 + 1 == 2;
  }
  return 1 + 1;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    var body = Assert.IsType<BlockStmt>(entry.Body);

    var ifStmt = Assert.IsType<IfStmt>(body.Body.First(stmt => stmt is IfStmt));
    Assert.IsType<IdentifierExpr>(ifStmt.Guard);

    var whileStmt = Assert.IsType<WhileStmt>(body.Body.First(stmt => stmt is WhileStmt));
    Assert.True(Expression.IsBoolLiteral(whileStmt.Guard, out var whileCond) && whileCond);
    Assert.All(whileStmt.Invariants, inv => Assert.True(Expression.IsBoolLiteral(inv.E, out var invLit) && invLit));
    Assert.NotNull(whileStmt.Decreases);
    var decreases = whileStmt.Decreases!;
    Assert.NotNull(decreases.Expressions);
    var decreasesExpressions = decreases.Expressions!;
    Assert.NotEmpty(decreasesExpressions);
    Assert.True(Expression.IsIntLiteral(decreasesExpressions[0], out var decLit));
    Assert.Equal(3, (int)decLit);

    var asserts = body.Body.OfType<AssertStmt>().ToList();
    Assert.True(asserts.Count >= 16);
    Assert.IsType<IdentifierExpr>(asserts[0].Expr);
    Assert.IsType<IdentifierExpr>(asserts[1].Expr);
    Assert.IsType<IdentifierExpr>(asserts[2].Expr);
    Assert.True(Expression.IsBoolLiteral(asserts[3].Expr, out var orLit) && orLit);
    Assert.IsType<IdentifierExpr>(asserts[4].Expr);
    Assert.IsType<UnaryOpExpr>(asserts[5].Expr);
    Assert.IsType<IdentifierExpr>(asserts[6].Expr);
    Assert.IsType<UnaryOpExpr>(asserts[7].Expr);
    Assert.True(Expression.IsBoolLiteral(asserts[8].Expr, out _));
    Assert.True(Expression.IsBoolLiteral(asserts[9].Expr, out _));
    Assert.True(Expression.IsBoolLiteral(asserts[10].Expr, out _));
    Assert.True(Expression.IsBoolLiteral(asserts[11].Expr, out _));
    Assert.True(Expression.IsBoolLiteral(asserts[12].Expr, out var eqBool) && !eqBool);
    Assert.True(Expression.IsBoolLiteral(asserts[13].Expr, out var neqBool) && !neqBool);

    var equality = Assert.IsType<BinaryExpr>(asserts[14].Expr);
    Assert.IsType<IdentifierExpr>(equality.E0);
    Assert.IsType<IdentifierExpr>(equality.E1);

    Assert.True(Expression.IsBoolLiteral(asserts[15].Expr, out var notFalseLit) && notFalseLit);

    var forallStmt = Assert.IsType<ForallStmt>(body.Body.First(stmt => stmt is ForallStmt));
    var forallBody = Assert.IsType<BlockStmt>(forallStmt.Body);
    var innerAssert = Assert.IsType<AssertStmt>(Assert.Single(forallBody.Body));
    Assert.True(Expression.IsBoolLiteral(innerAssert.Expr, out var innerLit) && innerLit);
  }

  [Fact]
  public async Task PartialEvaluation_SimplifiesQuantifierBounds() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 2U);

    var program = await ParseAndResolve(@"
function Limit(): int { 2 }
function SetVal(): set<int> { {1} }
function SubsetVal(): set<int> { {1, 2} }
function SeqVal(): seq<int> { [1, 2] }
function MapVal(): map<int, int> { map[1 := 2] }
function MultiVal(): multiset<int> { multiset{1, 1} }

method Entry() {
  assert forall i | 0 < i < Limit() :: i != 0;
  assert forall x | x in SetVal() :: true;
  assert forall s: set<int> | s <= SubsetVal() :: true;
  assert forall s: set<int> | SubsetVal() <= s :: true;
  assert forall x | x in SeqVal() :: true;
  assert forall k | k in MapVal() :: true;
  assert forall x | x in MultiVal() :: true;
  assert forall b: bool | b == true :: true;
  assert forall u: int :: true;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    var body = Assert.IsType<BlockStmt>(entry.Body);
    var asserts = body.Body.OfType<AssertStmt>().ToList();
    Assert.Equal(9, asserts.Count);

    var intQuantifier = Assert.IsType<ForallExpr>(asserts[0].Expr);
    var intBound = Assert.Single(intQuantifier.Bounds);
    if (intBound is IntBoundedPool intPool) {
      Assert.True(Expression.IsIntLiteral(intPool.UpperBound, out var upper));
      Assert.Equal(2, (int)upper);
    } else {
      var exactPool = Assert.IsType<ExactBoundedPool>(intBound);
      Assert.IsNotType<FunctionCallExpr>(exactPool.E);
    }

    var setQuantifier = Assert.IsType<ForallExpr>(asserts[1].Expr);
    var setBound = Assert.IsType<SetBoundedPool>(Assert.Single(setQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(setBound.Set);

    var subsetQuantifier = Assert.IsType<ForallExpr>(asserts[2].Expr);
    var subsetBound = Assert.IsType<SubSetBoundedPool>(Assert.Single(subsetQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(subsetBound.UpperBound);

    var supersetQuantifier = Assert.IsType<ForallExpr>(asserts[3].Expr);
    var supersetBound = Assert.IsType<SuperSetBoundedPool>(Assert.Single(supersetQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(supersetBound.LowerBound);

    var seqQuantifier = Assert.IsType<ForallExpr>(asserts[4].Expr);
    var seqBound = Assert.IsType<SeqBoundedPool>(Assert.Single(seqQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(seqBound.Seq);

    var mapQuantifier = Assert.IsType<ForallExpr>(asserts[5].Expr);
    var mapBound = Assert.IsType<MapBoundedPool>(Assert.Single(mapQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(mapBound.Map);

    var multiQuantifier = Assert.IsType<ForallExpr>(asserts[6].Expr);
    var multiBound = Assert.IsType<MultiSetBoundedPool>(Assert.Single(multiQuantifier.Bounds));
    Assert.IsNotType<FunctionCallExpr>(multiBound.MultiSet);

    var boolQuantifier = Assert.IsType<ForallExpr>(asserts[7].Expr);
    Assert.IsType<ExactBoundedPool>(Assert.Single(boolQuantifier.Bounds));

    var unboundedQuantifier = Assert.IsType<ForallExpr>(asserts[8].Expr);
    Assert.NotNull(unboundedQuantifier.Bounds);
    Assert.IsType<AssignSuchThatStmt.WiggleWaggleBound>(Assert.Single(unboundedQuantifier.Bounds));
  }

  [Fact]
  public async Task PartialEvaluation_InliningGuardsAndDepthAreRespected() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 1U);

    var program = await ParseAndResolve(@"
class C {
  var x: int
  function Read(): int reads this { x }
}

function Square(x: int): int { x * x }
function Inner(x: int): int { x + 1 }
function Outer(x: int): int { Inner(x) }
function Rec(n: nat): int { if n == 0 then 0 else Rec(n - 1) }
opaque function Hidden(): int { 1 }

function Entry(n: int, c: C): int {
  Square(2) + Square(n) + Hidden() + c.Read() + Outer(1) + Rec(1)
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "Entry"));
    Assert.NotNull(entry.Body);
    var entryBody = entry.Body!;

    var calls = entryBody.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .Select(call => call.Function.Name)
      .ToList();

    Assert.Contains("Square", calls);
    Assert.Contains("Hidden", calls);
    Assert.Contains("Read", calls);
    Assert.Contains("Inner", calls);
    Assert.Contains("Rec", calls);
    Assert.DoesNotContain("Outer", calls);
  }

  [Fact]
  public async Task PartialEvaluation_InlinesAfterArgumentSimplification() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 1U);

    var program = await ParseAndResolve(@"
function Id(x: int): int { x }

function Entry(): int {
  Id(1 + 1)
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "Entry"));
    Assert.NotNull(entry.Body);

    Assert.True(Expression.IsIntLiteral(entry.Body!, out var value));
    Assert.Equal(2, (int)value);
  }

  [Fact]
  public async Task PartialEvaluation_CacheDoesNotCrossInliningDepthBoundaries() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 2U);

    var program = await ParseAndResolve(@"
function G(): int { 1 }
function F(): int { G() }
function H(): int { F() }

function Entry(): int {
  F() + H()
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "Entry"));
    Assert.NotNull(entry.Body);

    // At depth=2: F() at the top level simplifies to 1, but H() calls F() at depth=1, which cannot
    // inline G() at depth=0. So we should still see a call to G().
    var add = Assert.IsType<BinaryExpr>(entry.Body!);
    Assert.Equal(BinaryExpr.ResolvedOpcode.Add, add.ResolvedOp);
    Assert.True(Expression.IsIntLiteral(add.E0, out var left) && (int)left == 1);
    var gCall = Assert.IsType<FunctionCallExpr>(add.E1);
    Assert.Equal("G", gCall.Function.Name);
  }

  [Fact]
  public async Task PartialEvaluation_SubstitutesLiteralInitializedLocals() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 1U);

    var program = await ParseAndResolve(@"
predicate Spec(x: int, y: int) { x + y == 108 }

method Entry() {
  var arg_0 := 100;
  var arg_1 := 8;
  assert !Spec(arg_0, arg_1);
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    Assert.NotNull(entry.Body);

    var assertStmt = DescendantStatements(entry.Body!)
      .OfType<AssertStmt>()
      .Single();

    Assert.True(Expression.IsBoolLiteral(assertStmt.Expr, out var value));
    Assert.False(value);
  }

  [Fact]
  public async Task PartialEvaluation_ReassignmentCancelsLocalSubstitution() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 1U);

    var program = await ParseAndResolve(@"
function Id(x: int): int { x }

method Entry() {
  var a := 1;
  assert Id(a) == 1;
  a := 2;
  assert Id(a) == 2;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    var body = Assert.IsType<BlockStmt>(entry.Body);
    var asserts = body.Body.OfType<AssertStmt>().ToList();
    Assert.Equal(2, asserts.Count);

    Assert.True(Expression.IsBoolLiteral(asserts[0].Expr, out var first) && first);
    Assert.False(Expression.IsBoolLiteral(asserts[1].Expr, out _));
    Assert.Contains(asserts[1].Expr.DescendantsAndSelf.OfType<IdentifierExpr>(), ide => ide.Name == "a");
  }

  [Fact]
  public async Task PartialEvaluation_NestedBlocksRespectConstScopes() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 1U);

    var program = await ParseAndResolve(@"
function Id(x: int): int { x }

method Entry() {
  var a := 1;
  {
    var b := 2;
    assert Id(a) == 1;
    assert Id(b) == 2;
  }
  assert Id(a) == 1;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    Assert.NotNull(entry.Body);

    var asserts = DescendantStatements(entry.Body!)
      .OfType<AssertStmt>()
      .ToList();
    Assert.Equal(3, asserts.Count);

    Assert.All(asserts, a => Assert.True(Expression.IsBoolLiteral(a.Expr, out var b) && b));
  }
}
