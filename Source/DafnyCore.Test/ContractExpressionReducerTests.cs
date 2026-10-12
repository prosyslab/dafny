using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class ContractExpressionReducerTests {
  // A projected scalar enters pure proof composition while the captured heap epochs remain distinct.
  [Fact]
  public async Task ProjectedHeapComposesPurePredicateChain() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
class Cell { var value:int }
predicate Leaf(value:int) { exists items:seq<int> :: items == [value] && |items| == 1 }
predicate Middle(value:int) { Leaf(value) }
predicate Outer(value:int) { Middle(value) }
method M(c:Cell) ensures Outer(c.value) && old(c.value) == 1 {}
""", options);
    var method = FindCallable<Method>(program, "M");
    var field = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(c => c.Name == "Cell").Members.OfType<Field>().Single();
    var context = new ContractHeapReductionContext(
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 1))],
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 3))]);
    var original = method.Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var reducer = CreateReducer(program, options);
    Assert.Empty(reducer.ReduceWithHeap(original, context).ProofObligations);
    var result = reducer.ReduceWithHeapForNativeProofComposition(original, context);
    Assert.NotEmpty(result.ProofObligations);
    Assert.Contains(result.ProofObligations, obligation => obligation.Kind == ContractReductionProofKind.Witness);
    Assert.True(result.HeapReduction!.EntryReads > 0);
    Assert.True(result.HeapReduction.CurrentReads > 0);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Unbounded quantifiers retaining any heap epoch never enter pure structural witness processing.
  [Theory]
  [InlineData("c.value")]
  [InlineData("old(c.value)")]
  [InlineData("old@L(c.value)")]
  public async Task ComposedHeapKeepsStatefulQuantifierResidual(string read) {
    var options = CreateOptions();
    var program = await ParseAndResolve("class Cell { var value:int } " +
      "method M(c:Cell) modifies c { c.value := 2; label L: c.value := 3; " +
      "assert exists item:int :: " + read + " == item && item > 3; }", options);
    var method = FindCallable<Method>(program, "M");
    var field = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(c => c.Name == "Cell").Members.OfType<Field>().Single();
    var context = new ContractHeapReductionContext(
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 1))],
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 3))]);
    var original = ((AssertStmt)method.Body!.Body[^1]).Expr;
    var result = CreateReducer(program, options).ReduceWithHeapForNativeProofComposition(original, context);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Empty(result.ProofObligations);
    Assert.Empty(result.ProofWitnesses);
    Assert.Contains("unbounded_quantifier", result.HeapReduction!.ResidualReasons);
    Assert.Equal(0, result.HeapReduction.EntryReads + result.HeapReduction.CurrentReads);
  }

  // Old changes only heap reads; scalar values and readonly cells keep their original meanings.
  [Theory]
  [InlineData("old(c.value) == 1 && c.value == 3", ContractReductionDecision.True)]
  [InlineData("old(c).value == 3 && old(c.value) == 1", ContractReductionDecision.True)]
  [InlineData("old(x) == 9 && c.tag == 7", ContractReductionDecision.True)]
  [InlineData("c.value == old(c.value)", ContractReductionDecision.False)]
  [InlineData("c.omitted == 0", ContractReductionDecision.Residual)]
  [InlineData("Delta(c) == 2", ContractReductionDecision.True)]
  [InlineData("Captured(c.value)", ContractReductionDecision.True)]
  [InlineData("Captured(c.omitted)", ContractReductionDecision.Residual)]
  [InlineData("c.value == 3 && Fixed() == [3]", ContractReductionDecision.True)]
  public async Task ReduceWithHeapKeepsEpochsAndEvaluatedArguments(string property, ContractReductionDecision expected) {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
class Cell { var value:int const tag:int := 7 ghost var omitted:int }
twostate function Delta(c:Cell):int reads c { c.value - old(c.value) }
twostate predicate Captured(x:int) { old(x) == x && x == 3 }
function Fixed():seq<int> { [1 + 2] }
method M(c:Cell, x:int) ensures PROPERTY {}
""".Replace("PROPERTY", property), options);
    var method = FindCallable<Method>(program, "M");
    var cell = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(declaration => declaration.Name == "Cell");
    var value = cell.Members.OfType<Field>().Single(field => field.Name == "value");
    var tag = cell.Members.OfType<Field>().Single(field => field.Name == "tag");
    Expression Number(int n) => Expression.CreateIntLiteral(method.Origin, n);
    var context = new ContractHeapReductionContext(
      [new(method.Ins[0], value, Number(1)), new(method.Ins[0], tag, Number(7))],
      [new(method.Ins[0], value, Number(3)), new(method.Ins[0], tag, Number(7))]);
    var original = method.Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var definitions = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Function>().Where(function => function.Body != null).ToDictionary(function => function,
        function => Printer.ExprToString(options, function.Body!));
    var result = CreateReducer(program, options).ReduceWithHeap(original, context,
      new Dictionary<IVariable, Expression> { [method.Ins[1]] = Number(9) });
    Assert.Equal(expected, result.Decision);
    Assert.Equal(before, Printer.ExprToString(options, original));
    Assert.All(definitions, pair => Assert.Equal(pair.Value, Printer.ExprToString(options, pair.Key.Body!)));
    Assert.NotNull(result.HeapReduction);
    Assert.Equal((uint)2, result.InlineDepthLimit);
    Assert.False(result.BudgetExhausted);
    if (property.Contains("omitted")) { Assert.Contains("unknown_heap_cell", result.HeapReduction!.ResidualReasons); }
  }

  // Proof statements and higher-order calls retain their original context and effects.
  [Theory]
  [InlineData("(Proof(); c.value == 3)", "proof_statement")]
  [InlineData("f(c.value) == 3", "higher_order_apply")]
  [InlineData("old@L(c.value) == 1", "labeled_old")]
  [InlineData("exists i:int :: c.value == i && i > 3", "unbounded_quantifier")]
  public async Task ReduceWithHeapLeavesUnsupportedContexts(string property, string reason) {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
class Cell { var value:int }
lemma Proof() ensures true {}
method M(c:Cell, f:int -> int) modifies c { c.value := 2; label L: c.value := 3; assert PROPERTY; }
""".Replace("PROPERTY", property), options);
    var method = FindCallable<Method>(program, "M");
    var field = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(c => c.Name == "Cell").Members.OfType<Field>().Single();
    var context = new ContractHeapReductionContext(
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 1))],
      [new(method.Ins[0], field, Expression.CreateIntLiteral(method.Origin, 3))]);
    var original = ((AssertStmt)method.Body!.Body[^1]).Expr;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).ReduceWithHeap(original, context);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(reason, result.HeapReduction!.ResidualReasons);
    Assert.Equal(before, Printer.ExprToString(options, original));
    Assert.Equal(0, result.HeapReduction.EntryReads + result.HeapReduction.CurrentReads);
  }

  // New heap projection shares the node bound instead of creating a fresh budget per field.
  [Fact]
  public async Task ReduceWithHeapKeepsSharedNodeBudget() {
    var options = CreateOptions();
    var program = await ParseAndResolve("class Cell { var value:seq<int> } method M(c:Cell) ensures |c.value| == 4 {}", options);
    var method = FindCallable<Method>(program, "M");
    var field = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(c => c.Name == "Cell").Members.OfType<Field>().Single();
    var literal = new SeqDisplayExpr(method.Origin, Enumerable.Range(0, 4).Select(n => (Expression)Expression.CreateIntLiteral(method.Origin, n)).ToList()) {
      Type = new SeqType(Microsoft.Dafny.Type.Int)
    };
    var context = new ContractHeapReductionContext([new(method.Ins[0], field, literal)], [new(method.Ins[0], field, literal)]);
    var result = CreateReducer(program, options).ReduceWithHeap(method.Ens.Single().E, context,
      budget: new ContractReductionBudget(expressionNodeLimit: 6));
    Assert.True(result.BudgetExhausted);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, result.ExhaustionReasons);
  }

  // Sibling heap quantifiers consume one shared cap and retain an untouched residual when it is exhausted.
  [Fact]
  public async Task ReduceWithHeapKeepsSharedQuantifierBudget() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
class Cell { var value:int }
method M(c:Cell)
  ensures (forall i:int | 0 <= i < 2 :: c.value + i >= 3) &&
    (forall j:int | 0 <= j < 2 :: c.value + j >= 3)
{}
""", options);
    var method = FindCallable<Method>(program, "M");
    var field = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(c => c.Name == "Cell").Members.OfType<Field>().Single();
    var value = Expression.CreateIntLiteral(method.Origin, 3);
    var context = new ContractHeapReductionContext([new(method.Ins[0], field, value)], [new(method.Ins[0], field, value)]);
    var original = method.Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).ReduceWithHeap(original, context,
      budget: new ContractReductionBudget(quantifierInstanceLimit: 3));
    Assert.Equal(3U, result.QuantifierInstancesUsed);
    Assert.DoesNotContain("unbounded_quantifier", result.HeapReduction!.ResidualReasons);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(before, Printer.ExprToString(options, original));
    Assert.Contains(DescendantsAndSelf(result.ReducedExpression), expression => expression is QuantifierExpr);
  }

  private static DafnyOptions CreateOptions() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    return options;
  }

  private static async Task<Program> ParseAndResolve(string source, DafnyOptions options) {
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(source, new Uri("untitled:contract-reducer"), reporter);
    Assert.Equal(0, reporter.ErrorCount);
    var program = parseResult.Program;
    await new ProgramResolver(program).Resolve(CancellationToken.None);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    return program;
  }

  private static T FindCallable<T>(Program program, string name) where T : MemberDecl, ICallable {
    return ModuleDefinition.AllCallablesIncludingPrefixDeclarations(
      program.DefaultModuleDef.TopLevelDecls).OfType<T>().Single(callable => callable.Name == name);
  }

  private static ContractExpressionReducer CreateReducer(Program program, DafnyOptions options) {
    return new ContractExpressionReducer(options, program.DefaultModuleDef, program.SystemModuleManager);
  }

  private static bool ContainsVariable(Expression expression, IVariable variable) {
    if (expression.Resolved is IdentifierExpr identifier && identifier.Var == variable) {
      return true;
    }
    return expression.SubExpressions.Any(child => ContainsVariable(child, variable));
  }

  private static IEnumerable<Expression> DescendantsAndSelf(Expression expression) {
    yield return expression;
    foreach (var child in expression.SubExpressions) {
      foreach (var descendant in DescendantsAndSelf(child)) {
        yield return descendant;
      }
    }
  }

  // Reduces a contract-only declaration from concrete input while preserving the original resolved AST.
  [Fact]
  public async Task Reduce_SubstitutesConcreteInputWithoutDeclarationBodyOrOriginalMutation() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
trait ContractOnly {
  method M(x: int)
    requires x + 1 == 3
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    Assert.Null(method.Body);
    var original = Assert.Single(method.Req).E;
    var originalResolved = original.Resolved;
    Assert.True(ContainsVariable(original, method.Ins[0]));
    var two = Expression.CreateIntLiteral(original.Origin, 2);
    two.Type = Microsoft.Dafny.Type.Int;

    var result = CreateReducer(program, options).Reduce(original,
      new Dictionary<IVariable, Expression> { [method.Ins[0]] = two });

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(ContractReductionResidualKind.None, result.ResidualKind);
    Assert.Same(original, result.OriginalExpression);
    Assert.NotSame(original, result.ReducedExpression);
    Assert.Same(originalResolved, original.Resolved);
    Assert.True(ContainsVariable(original, method.Ins[0]));
    Assert.False(ContainsVariable(result.SubstitutedExpression, method.Ins[0]));
    Assert.False(result.BudgetExhausted);
  }

  // Reduces concrete recursive datatype predicates over finite map keys and values within the explicit budget.
  [Theory]
  [InlineData("Leaf(7)", ContractReductionDecision.True)]
  [InlineData("Leaf(12)", ContractReductionDecision.False)]
  [InlineData("Branch([Leaf(7)])", ContractReductionDecision.True)]
  public async Task Reduce_EvaluatesRecursiveDatatypeAndFiniteMapMembership(
    string tree, ContractReductionDecision expected) {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Tree = Leaf(value: int) | Branch(children: seq<Tree>)

predicate ValidTree(tree: Tree)
  decreases tree
{
  (tree.Leaf? && 0 <= tree.value < 10) ||
  (tree.Branch? && forall i | 0 <= i < |tree.children| :: ValidTree(tree.children[i]))
}

predicate ValidForest(forest: map<int, Tree>) {
  forall key <- forest.Keys :: ValidTree(forest[key])
}

method M()
  ensures ValidForest(map[1 := TREE_VALUE])
{}
""".Replace("TREE_VALUE", tree), options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var validForest = FindCallable<Function>(program, "ValidForest");
    Assert.False(validForest.IsRecursive,
      $"recursive={validForest.IsRecursive}, reads={validForest.Reads.Expressions?.Count}");

    var result = CreateReducer(program, options).Reduce(original,
      budget: new ContractReductionBudget(inlineDepthLimit: 8));

    Assert.True(expected == result.Decision,
      Printer.ExprToString(options, result.ReducedExpression));
    Assert.False(result.BudgetExhausted);
  }

  // A destructor that does not belong to the concrete constructor remains residual.
  [Fact]
  public async Task Reduce_PreservesWrongConstructorDestructor() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Choice = A(value: int) | B(other: int)

method M()
  ensures B(1).value == 1
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is MemberSelectExpr { Member: DatatypeDestructor });
  }

  // Preserves the original quantifier as a residual when the cumulative instance budget runs out.
  [Fact]
  public async Task Reduce_PreservesOriginalQuantifierOnIncompleteUnroll() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures (forall i | 0 <= i < 1 :: i == 0) &&
          (forall j | 0 <= j < 2 :: j == 0)
{
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;

    var result = CreateReducer(program, options).Reduce(original, budget:
      new ContractReductionBudget(quantifierInstanceLimit: 1));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(ContractReductionResidualKind.BudgetExhausted, result.ResidualKind);
    Assert.Equal(1U, result.QuantifierInstancesUsed);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit,
      result.ExhaustionReasons);
    Assert.Contains(DescendantsAndSelf(result.ReducedExpression),
      expression => expression is QuantifierExpr quantifier &&
                    Attributes.Contains(quantifier.Attributes, "_partial_unroll"));
    Assert.DoesNotContain(DescendantsAndSelf(original),
      expression => expression is QuantifierExpr quantifier &&
                    Attributes.Contains(quantifier.Attributes, "_partial_unroll"));
  }

  // Leaves opaque and heap-reading function calls visible for the solver instead of opening their bodies.
  [Fact]
  public async Task Reduce_PreservesOpaqueAndReadsVisibilityBoundaries() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
opaque function Hidden(x: int): int {
  x + 1
}

class C {
  var value: int

  function Read(): int
    reads this
  {
    value
  }
}

method M(c: C)
  requires Hidden(1) == 2 && c.Read() == 0
{
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Req).E;

    var result = CreateReducer(program, options).Reduce(original);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Equal(ContractReductionResidualKind.RequiresSolver, result.ResidualKind);
    Assert.False(result.BudgetExhausted);
    Assert.Equal(2, DescendantsAndSelf(result.ReducedExpression).OfType<FunctionCallExpr>().Count());
  }

  // Reports a depth-limited otherwise-visible call as a budget residual.
  [Fact]
  public async Task Reduce_ReportsInlineDepthExhaustionSeparately() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
function AddOne(x: int): int {
  x + 1
}

method M()
  ensures AddOne(1) == 2
{
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;

    var result = CreateReducer(program, options).Reduce(original, budget:
      new ContractReductionBudget(inlineDepthLimit: 0));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.InlineDepthLimit, result.ExhaustionReasons);
    Assert.IsType<FunctionCallExpr>(DescendantsAndSelf(result.ReducedExpression)
      .Single(expression => expression is FunctionCallExpr));
  }

  // Applies the shared quantifier budget to the specialized finite-sequence enumerator as well.
  [Fact]
  public async Task Reduce_BoundsFiniteSequenceQuantifierEnumeration() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures exists s: seq<int> ::
    |s| == 2 &&
    (forall i | 0 <= i < 2 :: 0 <= s[i] < 2) &&
    s[0] == 1 && s[1] == 1
{
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;

    var result = CreateReducer(program, options).Reduce(original, budget:
      new ContractReductionBudget(quantifierInstanceLimit: 3));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit,
      result.ExhaustionReasons);
    Assert.Contains(DescendantsAndSelf(result.ReducedExpression), expression => expression is ExistsExpr);
  }

  // Nested quantifier work must consume the next sequence candidate's shared allowance.
  [Fact]
  public async Task Reduce_StopsSequenceEnumerationAfterNestedBudgetConsumption() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures exists s: seq<int> ::
    |s| == 1 &&
    (forall i | 0 <= i < 1 :: 0 <= s[i] < 2) &&
    (s[0] == 1 || (forall k | 0 <= k < 2 :: s[0] + k != 0))
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var result = CreateReducer(program, options).Reduce(original, budget:
      new ContractReductionBudget(quantifierInstanceLimit: 2));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, result.ExhaustionReasons);
    Assert.Equal(2u, result.QuantifierInstancesUsed);
  }

  // Uses resolved constructor and destructor identities when reducing concrete datatype operations.
  [Fact]
  public async Task Reduce_EvaluatesConcreteDatatypeIdentityAndSharedDestructor() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Choice = A(value: int) | B(value: int, extra: int)

method M()
  ensures A(1) != B(1, 0) && B(2, 3).value == 2
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
  }

  // Reduces range-valid bitvector conversions nested in datatype values used for equality and map lookup.
  [Fact]
  public async Task Reduce_EvaluatesConcreteBitvectorConversionInNestedDatatype() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Block = Block(index: bv32)

predicate Accept(block: Block, known: map<Block, bool>) {
  block == Block(493 as bv32) && known[block]
}

method M()
  ensures Accept(Block(493 as bv32), map[Block(493 as bv32) := true])
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.DoesNotContain(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is ConversionExpr);
  }

  // Preserves an out-of-range bitvector conversion as a solver residual.
  [Fact]
  public async Task Reduce_PreservesOutOfRangeConcreteBitvectorConversion() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Tiny = Tiny(value: bv8)

predicate Accept(value: Tiny) {
  true
}

method M()
  ensures Accept(Tiny(256 as bv8))
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is ConversionExpr);
  }

  // Preserves an exact real-to-integer conversion outside the contract concrete value domain.
  [Fact]
  public async Task Reduce_PreservesExactRealToIntegerConversion() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Index = Index(value: int)

predicate Accept(value: Index) {
  true
}

method M()
  ensures Accept(Index(1.0 as int))
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is ConversionExpr);
  }

  // Preserves an invalid conversion to nat instead of treating the constrained target as a plain integer.
  [Fact]
  public async Task Reduce_PreservesInvalidNaturalNumberConversion() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Count = Count(value: nat)

predicate Accept(value: Count) {
  true
}

method M()
  ensures Accept(Count((-1) as nat))
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is ConversionExpr);
  }

  // Preserves an invalid conversion to a user-defined subset type as a solver residual.
  [Fact]
  public async Task Reduce_PreservesInvalidSubsetTypeConversion() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
type Positive = value: int | 0 < value

datatype Index = Index(value: Positive)

predicate Accept(value: Index) {
  true
}

method M()
  ensures Accept(Index(0 as Positive))
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is ConversionExpr);
  }

  // Applies Dafny's last-write-wins map semantics with concrete datatype keys.
  [Fact]
  public async Task Reduce_EvaluatesDuplicateConcreteDatatypeMapKey() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Key = K(value: int)

method M()
  ensures map[K(1) := 0, K(1) := 7][K(1)] == 7
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
  }

  // Leaves a missing key lookup residual because Dafny maps do not provide a value for absent keys.
  [Fact]
  public async Task Reduce_PreservesMissingConcreteMapKeyLookup() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures map[1 := 7][2] == 7
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is SeqSelectExpr { Seq: MapDisplayExpr });
  }

  // Unrolls a recursive quantified predicate when its sequence argument remains closed and concrete.
  [Fact]
  public async Task Reduce_EvaluatesQuantifiedRecursionOverConcreteSequence() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
predicate AllSmall(values: seq<int>)
  decreases |values|
{
  |values| == 0 ||
    ((forall i | 0 <= i < 1 :: values[i] < 10) && AllSmall(values[1..]))
}

method M()
  ensures AllSmall([1, 2])
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E,
      budget: new ContractReductionBudget(inlineDepthLimit: 8));

    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.False(result.BudgetExhausted);
  }

  // Stops a recursive call with the same concrete argument at the call-cycle boundary.
  [Fact]
  public async Task Reduce_PreservesDirectRecursiveCallCycle() {
    var options = CreateOptions();
    options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);
    var program = await ParseAndResolve("""
ghost predicate Loop(value: int)
  decreases *
{
  Loop(value)
}

ghost function Entry(): bool
  decreases *
{
  Loop(0)
}
""", options);
    var entry = FindCallable<Function>(program, "Entry");

    var result = CreateReducer(program, options).Reduce(entry.Body!,
      budget: new ContractReductionBudget(inlineDepthLimit: 8));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.False(result.BudgetExhausted);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is FunctionCallExpr { Function.Name: "Loop" });
  }

  // Leaves a bodyless function visible as a solver residual.
  [Fact]
  public async Task Reduce_PreservesBodylessFunctionCall() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
trait ContractOnly {
  ghost function Missing(value: int): bool

  method M()
    requires Missing(0)
}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Req).E);

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is FunctionCallExpr { Function.Name: "Missing" });
  }

  // Keeps quantified recursive concrete evaluation disabled in the default partial-evaluation profile.
  [Fact]
  public async Task DefaultPartialEvaluation_PreservesQuantifiedRecursiveConcreteCall() {
    var options = CreateOptions();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 8U);
    var program = await ParseAndResolve("""
predicate AllSmall(values: seq<int>)
  decreases |values|
{
  |values| == 0 ||
    ((forall i | 0 <= i < 1 :: values[i] < 10) && AllSmall(values[1..]))
}

function Entry(): bool {
  AllSmall([1, 2])
}
""", options);
    var entry = FindCallable<Function>(program, "Entry");
    Assert.NotNull(entry.Body);
    var reduced = entry.Body!;

    Assert.False(Expression.IsBoolLiteral(reduced, out _));
    Assert.Contains(reduced.DescendantsAndSelf,
      candidate => candidate is FunctionCallExpr { Function.Name: "AllSmall" });
  }

  // Slices a closed sequence of datatype values while recursively consuming the sequence.
  [Fact]
  public async Task Reduce_EvaluatesRecursiveDatatypeSequenceSlice() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Tree = Leaf(value: int) | Branch(children: seq<Tree>)

predicate AllLeaves(values: seq<Tree>)
  decreases |values|
{
  |values| == 0 ||
    (values[0].Leaf? && values[0].value < 10 && AllLeaves(values[1..]))
}

method M()
  ensures AllLeaves([Leaf(1), Leaf(2)])
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E,
      budget: new ContractReductionBudget(inlineDepthLimit: 8));

    Assert.Equal(ContractReductionDecision.True, result.Decision);
  }

  // Compares closed sequences and maps containing nested datatypes by resolved constructor identity.
  [Fact]
  public async Task Reduce_EvaluatesNestedDatatypeCollectionEquality() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Tree = Leaf(value: int) | Branch(children: seq<Tree>)

method M()
  ensures [Branch([Leaf(1)])] == [Branch([Leaf(1)])] &&
          map[0 := Branch([Leaf(1)])] == map[0 := Branch([Leaf(1)])] &&
          map[0 := Leaf(1)] != map[0 := Branch([])]
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");

    var result = CreateReducer(program, options).Reduce(Assert.Single(method.Ens).E);

    Assert.Equal(ContractReductionDecision.True, result.Decision);
  }

  // Returns distinct detached residuals when the substituted expression already exceeds the node limit.
  [Fact]
  public async Task Reduce_DetachesInitialExpressionNodeLimitResidual() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures (1 + 2 == 3) && (4 + 5 == 9)
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var originalText = Printer.ExprToString(options, original);

    var result = CreateReducer(program, options).Reduce(original,
      budget: new ContractReductionBudget(expressionNodeLimit: 1));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, result.ExhaustionReasons);
    Assert.NotSame(result.SubstitutedExpression, result.ReducedExpression);
    Assert.Equal(originalText, Printer.ExprToString(options, original));
    Assert.Equal(0U, result.ExpressionExpansionNodeCount);
  }

  // Stops finite quantifier instantiation before constructing an instance that exceeds the node limit.
  [Fact]
  public async Task Reduce_StopsQuantifierExpansionAtExpressionNodeLimit() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
method M()
  ensures forall i | 0 <= i < 20 :: i < 10
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var baseline = CreateReducer(program, options).Reduce(original);

    var result = CreateReducer(program, options).Reduce(original,
      budget: new ContractReductionBudget(expressionNodeLimit: baseline.SubstitutedExpressionNodeCount));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, result.ExhaustionReasons);
    Assert.Equal(0U, result.ExpressionExpansionNodeCount);
    Assert.Equal(0U, result.QuantifierInstancesUsed);
    Assert.NotSame(result.SubstitutedExpression, result.ReducedExpression);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is QuantifierExpr);
  }

  // Stops function-body substitution before constructing an inline body that exceeds the node limit.
  [Fact]
  public async Task Reduce_StopsInliningAtExpressionNodeLimit() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
function Wide(value: int): bool {
  value == 1 && value + 1 == 2 && value + 2 == 3
}

method M()
  ensures Wide(1)
{}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var baseline = CreateReducer(program, options).Reduce(original);

    var result = CreateReducer(program, options).Reduce(original,
      budget: new ContractReductionBudget(expressionNodeLimit: baseline.SubstitutedExpressionNodeCount));

    Assert.Equal(ContractReductionDecision.Residual, result.Decision);
    Assert.Contains(ContractReductionExhaustionReason.ExpressionNodeLimit, result.ExhaustionReasons);
    Assert.Equal(0U, result.ExpressionExpansionNodeCount);
    Assert.NotSame(result.SubstitutedExpression, result.ReducedExpression);
    Assert.Contains(result.ReducedExpression.DescendantsAndSelf,
      expression => expression is FunctionCallExpr { Function.Name: "Wide" });
  }

  // Checked cloning interrupts deterministically without changing any resolved source node.
  [Fact]
  public async Task CheckedCloneCancellationPreservesOriginalResolvedExpression() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(x:int) requires (x + 1 == 2) && (x + 2 == 3) {}", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Req).E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var checks = 0;

    Assert.Throws<OperationCanceledException>(() =>
      new ContractReductionCloner(() => {
        if (++checks == 4) { throw new OperationCanceledException(); }
      }).CloneExpr(original));

    Assert.Equal(4, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Checked substitution interrupts deterministically without changing the source binding or expression.
  [Fact]
  public async Task CheckedSubstitutionCancellationPreservesOriginalResolvedExpression() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(x:int) requires (x + 1 == 2) && (x + 2 == 3) {}", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Req).E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var checks = 0;
    var replacement = Expression.CreateIntLiteral(original.Origin, 1);
    var substituter = new ContractReductionSubstituter(null,
      new Dictionary<IVariable, Expression> { [method.Ins[0]] = replacement },
      new Dictionary<TypeParameter, Microsoft.Dafny.Type>(), null, program.SystemModuleManager, () => {
        if (++checks == 4) { throw new OperationCanceledException(); }
      });

    Assert.Throws<OperationCanceledException>(() => substituter.Substitute(original));

    Assert.Equal(4, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.True(ContainsVariable(original, method.Ins[0]));
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Recursive constructor proof composition observes cancellation and preserves the original resolved target.
  [Fact]
  public async Task RecursiveConstructorProofCancellationPreservesOriginalTarget() {
    var options = CreateOptions();
    var program = await ParseAndResolve("""
datatype Parsed = Bad | Good(value:nat, rest:Parsed)
function Size(items:seq<int>):nat { if |items| == 0 then 0 else 1 + Size(items[1..]) }
ghost predicate Parse(items:seq<int>, parsed:Parsed) {
  if |items| == 0 then parsed == Bad else parsed == Good(Size(items), Bad)
}
ghost predicate Walk(groups:seq<seq<int>>, state:nat, result:nat)
  decreases |groups|
{
  if |groups| == 0 then result == state else
    exists parsed:Parsed :: Parse(groups[0], parsed) &&
      (match parsed
       case Bad => result == state
       case Good(value, rest) => Walk(groups[1..], value, result))
}
method M() ensures Walk([[3,4],[9]], 7, 1) {}
""", options);
    var method = FindCallable<MethodOrConstructor>(program, "M");
    var original = Assert.Single(method.Ens).E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var totalChecks = 0;
    var reducer = CreateReducer(program, options);
    var baseline = reducer.ReduceForNativeProofComposition(original,
      cancellationCheck: () => totalChecks++);
    Assert.Equal(ContractReductionDecision.True, baseline.Decision);
    Assert.NotEmpty(baseline.ProofObligations);
    Assert.Contains(baseline.ProofObligations, obligation =>
      obligation.Kind == ContractReductionProofKind.Witness &&
      obligation.Expression.DescendantsAndSelf.OfType<FunctionCallExpr>()
        .Any(call => call.Function.Name == "Walk"));
    var cancellationCheckNumber = totalChecks / 2;
    Assert.InRange(cancellationCheckNumber, 2, totalChecks - 1);
    var checks = 0;

    Assert.Throws<OperationCanceledException>(() => reducer.ReduceForNativeProofComposition(original,
      cancellationCheck: () => {
        if (++checks == cancellationCheckNumber) { throw new OperationCanceledException(); }
      }));

    Assert.Equal(cancellationCheckNumber, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Nested value preflight observes cancellation inside each container and retains unary delegate compatibility.
  [Theory]
  [InlineData("seq<Box>", "[Box([1,2]), Box([3,4])]")]
  [InlineData("set<Box>", "{Box([1,2]), Box([3,4])}")]
  [InlineData("multiset<Box>", "multiset{Box([1,2]), Box([3,4])}")]
  [InlineData("map<Box,seq<int>>", "map[Box([1,2]) := [3,4], Box([5,6]) := [7,8]]")]
  public async Task ConcreteValuePreflightCancelsWithinNestedValues(string type, string value) {
    var options = CreateOptions();
    var program = await ParseAndResolve("datatype Box = Box(values:seq<int>) function Value():" + type +
      " { " + value + " }", options);
    var original = FindCallable<Function>(program, "Value").Body!;
    var resolved = original.Resolved;
    var originalType = original.Type;
    var before = Printer.ExprToString(options, original);
    Func<Expression, bool> defaultCheck = ContractExpressionReducer.IsConcreteValue;
    Assert.True(defaultCheck(original));
    var completeChecks = 0;
    Assert.True(ContractExpressionReducer.IsConcreteValue(original, () => completeChecks++));
    Assert.True(completeChecks > 4);
    bool? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result = ContractExpressionReducer.IsConcreteValue(original, () => {
      if (++checks == 4) { throw new OperationCanceledException(); }
    }));
    Assert.Null(result);
    Assert.Equal(4, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Same(originalType, original.Type);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // The original range spelling retains its valid structural witness even when enumeration reaches its cap.
  [Theory]
  [InlineData(101)]
  [InlineData(1024)]
  public async Task OriginalIntegerSequenceRangeRetainsSemanticWitness(int bound) {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(bound:int) ensures exists items:seq<int> :: |items| == 1 && " +
      "(forall i:int | 0 <= i < 1 :: 0 <= items[i] < bound) {}", options);
    var method = FindCallable<Method>(program, "M");
    var original = method.Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).Reduce(original, new Dictionary<IVariable, Expression> {
      [method.Ins[0]] = Expression.CreateIntLiteral(method.Origin, bound)
    });
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Equivalent full-index ranges generate the whole integer domain and retain the valid fallback witness.
  [Theory]
  [InlineData("i >= 0 && i < 1")]
  [InlineData("0 <= i && i < 1")]
  [InlineData("i >= 0 && 1 > i")]
  [InlineData("0 <= i && 1 > i")]
  [InlineData("i >= 0 && i <= 0")]
  [InlineData("0 <= i && 0 >= i")]
  [InlineData("i > -1 && i < 1")]
  [InlineData("-1 < i && 1 > i")]
  public async Task IntegerSequenceDomainGenerationObservesCancellation(string indexRange) {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(bound:int) ensures exists items:seq<int> :: |items| == 1 && " +
      "(forall i:int {:split false} | " + indexRange + " :: 0 <= items[i] < bound) {}", options);
    var method = FindCallable<Method>(program, "M");
    var original = method.Ens.Single().E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var reducer = CreateReducer(program, options);
    Dictionary<IVariable, Expression> Bind(int bound) => new() {
      [method.Ins[0]] = Expression.CreateIntLiteral(method.Origin, bound)
    };
    var smallChecks = 0;
    var small = reducer.Reduce(original, Bind(101), cancellationCheck: () => smallChecks++);
    var largeChecks = 0;
    var large = reducer.Reduce(original, Bind(1024), cancellationCheck: () => largeChecks++);
    Assert.Equal(ContractReductionDecision.True, small.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, small.ExhaustionReasons);
    Assert.Equal(ContractReductionDecision.True, large.Decision);
    Assert.Contains(ContractReductionExhaustionReason.QuantifierInstanceLimit, large.ExhaustionReasons);
    Assert.True(largeChecks >= smallChecks + 923);
    ContractReductionResult? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result = reducer.Reduce(original, Bind(1024),
      cancellationCheck: () => {
        if (++checks == smallChecks + 1) { throw new OperationCanceledException(); }
      }));
    Assert.Null(result);
    Assert.Equal(smallChecks + 1, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Cropped or refined index ranges cannot constrain elements outside the quantified indices.
  [Theory]
  [InlineData("int", "i > 0 && i < 2", ContractReductionDecision.True)]
  [InlineData("int", "0 < i && i < 2", ContractReductionDecision.True)]
  [InlineData("int", "i >= 0 && i < 2 && i != 0", ContractReductionDecision.True)]
  [InlineData("int", "i >= 0 && i < 2 && i == 1", ContractReductionDecision.True)]
  [InlineData("PositiveIndex", "i >= 0 && i < 2", ContractReductionDecision.True)]
  [InlineData("int", "i >= 0 && i < 2", ContractReductionDecision.False)]
  [InlineData("nat", "i < 2", ContractReductionDecision.False)]
  public async Task SequenceElementDomainRequiresEveryIndex(string indexType, string indexRange,
    ContractReductionDecision expected) {
    var options = CreateOptions();
    var program = await ParseAndResolve("type PositiveIndex = i:int | i > 0 witness 1 " +
      "method M() ensures exists items:seq<int> :: |items| == 2 && " +
      "(forall i:" + indexType + " {:split false} | " + indexRange + " :: items[i] in {0}) && " +
      "items[0] == 1 && items[1] == 0 {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).Reduce(original);
    Assert.Equal(expected, result.Decision);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // A shortened upper range leaves the final sequence element outside the inferred element domain.
  [Theory]
  [InlineData("i >= 0 && i < 1")]
  [InlineData("i >= 0 && i < 2 && i != 1")]
  public async Task CroppedUpperIndexRangeRetainsUnconstrainedElement(string indexRange) {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() ensures exists items:seq<int> :: |items| == 2 && " +
      "(forall i:int {:split false} | " + indexRange + " :: items[i] in {0}) && " +
      "items[0] == 0 && items[1] == 1 {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).Reduce(original);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Empty sequences retain vacuous full-index constraints under either ordinary index type.
  [Theory]
  [InlineData("int", "0 <= i && i < 0")]
  [InlineData("int", "i >= 0 && 0 > i")]
  [InlineData("nat", "i < 0")]
  public async Task EmptySequenceIndexRangeRetainsVacuity(string indexType, string indexRange) {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() ensures exists items:seq<int> :: |items| == 0 && " +
      "(forall i:" + indexType + " {:split false} | " + indexRange + " :: items[i] in {0}) {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var before = Printer.ExprToString(options, original);
    var result = CreateReducer(program, options).Reduce(original);
    Assert.Equal(ContractReductionDecision.True, result.Decision);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Proof-only datatype let admission does not change the default partial evaluator's binding policy.
  [Fact]
  public async Task DefaultPartialEvaluationPreservesConcreteDatatypeLet() {
    var options = CreateOptions();
    options.Set(CommonOptionBag.PartialEvalEntry, "Entry");
    var program = await ParseAndResolve("datatype Chain = End | Link(value:nat, rest:Chain) " +
      "function Entry():bool { var rest:Chain := End; rest == End }", options);
    var original = FindCallable<Function>(program, "Entry").Body!;
    Assert.False(Expression.IsBoolLiteral(original, out _));
    Assert.Contains(original.DescendantsAndSelf, expression => expression is LetExpr);
  }

  // Cancellation at every observed boundary of a nested concrete let publishes no result or AST mutation.
  [Fact]
  public async Task ConcreteExactLetCancellationPreservesOriginalTarget() {
    var options = CreateOptions();
    var program = await ParseAndResolve("datatype Box<T> = Box(value:T) " +
      "method M() ensures (var value:Box<seq<nat>> := Box([1,2]); value.value == [1,2]) {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var resolved = original.Resolved;
    var originalType = original.Type;
    var originalOrigin = original.Origin;
    var before = Printer.ExprToString(options, original);
    var reducer = CreateReducer(program, options);
    var totalChecks = 0;
    var complete = reducer.ReduceForNativeProofComposition(original, cancellationCheck: () => totalChecks++);
    Assert.Equal(ContractReductionDecision.True, complete.Decision);
    Assert.True(totalChecks > 0);
    for (var stop = 1; stop <= totalChecks; stop++) {
      var checks = 0;
      ContractReductionResult? result = null;
      Assert.Throws<OperationCanceledException>(() => result = reducer.ReduceForNativeProofComposition(original,
        cancellationCheck: () => {
          if (++checks == stop) { throw new OperationCanceledException(); }
        }));
      Assert.Null(result);
      Assert.Equal(stop, checks);
      Assert.Same(resolved, original.Resolved);
      Assert.Same(originalType, original.Type);
      Assert.Same(originalOrigin, original.Origin);
      Assert.Equal(before, Printer.ExprToString(options, original));
    }
  }

  // Character-domain work observes the query boundary while a finite range exceeds its shared allowance.
  [Fact]
  public async Task CharacterDomainGenerationObservesCancellation() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() ensures |set c:char | '\\u0000' <= c < '\\u0100' :: c| == 256 {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var reducer = CreateReducer(program, options);
    var smallChecks = 0;
    var small = reducer.Reduce(original, budget: new ContractReductionBudget(quantifierInstanceLimit: 4),
      cancellationCheck: () => smallChecks++);
    var largeChecks = 0;
    var large = reducer.Reduce(original, budget: new ContractReductionBudget(quantifierInstanceLimit: 64),
      cancellationCheck: () => largeChecks++);
    Assert.Equal(ContractReductionDecision.Residual, small.Decision);
    Assert.Equal(ContractReductionDecision.Residual, large.Decision);
    Assert.True(largeChecks >= smallChecks + 60);
    ContractReductionResult? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result = reducer.Reduce(original,
      budget: new ContractReductionBudget(quantifierInstanceLimit: 64), cancellationCheck: () => {
        if (++checks == smallChecks + 1) { throw new OperationCanceledException(); }
      }));
    Assert.Null(result);
    Assert.Equal(smallChecks + 1, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Relational bound propagation checks each fixed-point pass before rejecting unanchored domains.
  [Fact]
  public async Task RelationalDomainFixedPointObservesCancellation() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(offset:int) ensures forall i:int, j:int | " +
      "0 <= i && i <= j && j + offset <= i :: i + j >= 0 {}", options);
    var method = FindCallable<Method>(program, "M");
    var original = method.Ens.Single().E;
    var resolved = original.Resolved;
    var before = Printer.ExprToString(options, original);
    var reducer = CreateReducer(program, options);
    Dictionary<IVariable, Expression> Bind(int offset) => new() {
      [method.Ins[0]] = new LiteralExpr(method.Origin, new System.Numerics.BigInteger(offset)) { Type = Microsoft.Dafny.Type.Int }
    };
    var stableChecks = 0;
    var stable = reducer.Reduce(original, Bind(-1), cancellationCheck: () => stableChecks++);
    var cyclicChecks = 0;
    var cyclic = reducer.Reduce(original, Bind(1), cancellationCheck: () => cyclicChecks++);
    Assert.Equal(ContractReductionDecision.Residual, stable.Decision);
    Assert.Equal(ContractReductionDecision.Residual, cyclic.Decision);
    Assert.True(cyclicChecks > stableChecks);
    ContractReductionResult? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result = reducer.Reduce(original, Bind(1),
      cancellationCheck: () => {
        if (++checks == stableChecks + 1) { throw new OperationCanceledException(); }
      }));
    Assert.Null(result);
    Assert.Equal(stableChecks + 1, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Cancellation during constructor field instantiation leaves later fields untouched and publishes no reduction.
  [Fact]
  public async Task ConstructorFieldInstantiationObservesCancellation() {
    var options = CreateOptions();
    var program = await ParseAndResolve("datatype Row = Row(a:int, b:int, c:int) " +
      "method M() ensures exists row:Row :: row.a + row.b + row.c == 6 {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var resolved = original.Resolved;
    var originalType = original.Type;
    var before = Printer.ExprToString(options, original);
    var constructor = program.DefaultModuleDef.TopLevelDecls.OfType<IndDatatypeDecl>().Single().Ctors.Single();
    var visits = new int[constructor.Formals.Count];
    for (var index = 0; index < constructor.Formals.Count; index++) {
      var fieldIndex = index;
      var formal = constructor.Formals[index];
      constructor.Formals[index] = new Formal(formal.Origin, formal.Name,
        new ObservedIntegerType(() => visits[fieldIndex]++), formal.InParam, formal.IsGhost, formal.DefaultValue);
    }
    var formals = constructor.Formals.ToArray();
    var reducer = CreateReducer(program, options);
    var control = reducer.Reduce(original);
    Assert.NotNull(control);
    Assert.All(visits, count => Assert.True(count > 0));
    Array.Clear(visits);
    ContractReductionResult? result = null;
    Assert.Throws<OperationCanceledException>(() => result = reducer.Reduce(original, cancellationCheck: () => {
      if (visits[0] > 0) { throw new OperationCanceledException(); }
    }));
    Assert.Null(result);
    Assert.Equal(1, visits[0]);
    Assert.All(visits.Skip(1), count => Assert.Equal(0, count));
    Assert.Equal(formals, constructor.Formals);
    Assert.Same(resolved, original.Resolved);
    Assert.Same(originalType, original.Type);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Free-variable scanning preserves binder and heap epochs while cancellation leaves the source expression intact.
  [Fact]
  public async Task FreeVariableCancellationPreservesBindersAndHeapEpochs() {
    var options = CreateOptions();
    var program = await ParseAndResolve("class Cell { var value:int } method M(c:Cell, x:int) " +
      "ensures old(c.value) == c.value && (forall y:int :: y + x >= x) {}", options);
    var method = FindCallable<Method>(program, "M");
    var original = method.Ens.Single().E;
    var resolved = original.Resolved;
    var originalType = original.Type;
    var before = Printer.ExprToString(options, original);
    Func<DafnyOptions, Expression, ISet<IVariable>> defaultScan = FreeVariablesUtil.ComputeFreeVariables;
    Assert.True(defaultScan(options, original).SetEquals(method.Ins));
    var variables = new HashSet<IVariable>();
    var usesHeap = false;
    var usesOldHeap = false;
    Microsoft.Dafny.Type? usesThis = null;
    var labels = new HashSet<Label>();
    var totalChecks = 0;
    FreeVariablesUtil.ComputeFreeVariables(options, original, variables, ref usesHeap, ref usesOldHeap,
      labels, ref usesThis, true, () => totalChecks++);
    Assert.True(variables.SetEquals(method.Ins));
    Assert.True(usesHeap);
    Assert.True(usesOldHeap);
    Assert.Null(usesThis);
    Assert.Empty(labels);
    Assert.True(totalChecks > 4);
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => FreeVariablesUtil.ComputeFreeVariables(options, original,
      new HashSet<IVariable>(), () => {
        if (++checks == 4) { throw new OperationCanceledException(); }
      }));
    Assert.Equal(4, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Same(originalType, original.Type);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Including statement expressions discovers assertion-only variables and checks the same recursive traversal.
  [Fact]
  public async Task FreeVariableStatementTraversalObservesCancellation() {
    var options = CreateOptions();
    var program = await ParseAndResolve("function F(x:int, y:int):int { assert y >= 0; x + 1 }", options);
    var function = FindCallable<Function>(program, "F");
    var original = function.Body!;
    var before = Printer.ExprToString(options, original);
    var withoutStatements = FreeVariablesUtil.ComputeFreeVariables(options, original);
    Assert.True(withoutStatements.SetEquals(new[] { function.Ins[0] }));
    var withStatements = new HashSet<IVariable>();
    var usesHeap = false;
    var totalChecks = 0;
    FreeVariablesUtil.ComputeFreeVariables(options, original, withStatements, ref usesHeap, true,
      () => totalChecks++);
    Assert.True(withStatements.SetEquals(function.Ins));
    Assert.False(usesHeap);
    Assert.True(totalChecks > 3);
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => FreeVariablesUtil.ComputeFreeVariables(options, original,
      new HashSet<IVariable>(), ref usesHeap, true, () => {
        if (++checks == 3) { throw new OperationCanceledException(); }
      }));
    Assert.Equal(3, checks);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Production proof-key printing matches the native printer and cancels between output writes without modifying the AST.
  [Fact]
  public async Task ProofKeyPrintingObservesCancellationAndPreservesNativeText() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(x:int) ensures (x + 1 == 2) && " +
      "(exists items:seq<int> :: items == [x,2,3] && |items| == 3) {}", options);
    var original = FindCallable<Method>(program, "M").Ens.Single().E;
    var resolved = original.Resolved;
    var originalType = original.Type;
    var before = Printer.ExprToString(options, original);
    Assert.Equal(before, ContractReductionTraversal.PrintExpression(options, original));
    var totalChecks = 0;
    Assert.Equal(before, ContractReductionTraversal.PrintExpression(options, original, () => totalChecks++));
    Assert.True(totalChecks > 4);
    string? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result =
      ContractReductionTraversal.PrintExpression(options, original, () => {
        if (++checks == 4) { throw new OperationCanceledException(); }
      }));
    Assert.Null(result);
    Assert.Equal(4, checks);
    Assert.Same(resolved, original.Resolved);
    Assert.Same(originalType, original.Type);
    Assert.Equal(before, Printer.ExprToString(options, original));
  }

  // Deep resolved printer spines observe the callback before the first output attempt and preserve source metadata.
  [Theory]
  [InlineData("and")]
  [InlineData("add")]
  [InlineData("dotted")]
  public async Task PrinterTraversalCancellationStopsDeepLeftSpineBeforeWriting(string shape) {
    var options = CreateOptions();
    var original = await CreateDeepPrinterExpression(shape, options);
    var current = original;
    for (var depth = 0; depth < 512; depth++) {
      current = LeftSpineChild(shape, current, depth);
    }
    var metadata = original.DescendantsAndSelf.Select(node => (
      Node: node,
      Origin: node.Origin,
      PreType: node.PreType,
      Type: node.UnnormalizedType,
      Resolved: node.Resolved)).ToArray();
    var expected = new OperationCanceledException("printer traversal cancellation");
    var checks = 0;
    var writer = new CountingTextWriter();
    var printer = new Printer(writer, options, PrintModes.Everything, new PrintFlags(), () => {
      if (++checks == 64) {
        throw expected;
      }
    });

    var actual = Assert.Throws<OperationCanceledException>(() => printer.PrintExpression(original, false));

    Assert.Same(expected, actual);
    Assert.Equal(64, checks);
    Assert.Equal(0, writer.WriteAttempts);
    Assert.All(metadata, entry => {
      Assert.Same(entry.Origin, entry.Node.Origin);
      Assert.Same(entry.PreType, entry.Node.PreType);
      Assert.Same(entry.Type, entry.Node.UnnormalizedType);
      Assert.Same(entry.Resolved, entry.Node.Resolved);
    });
  }

  // The legacy constructor and explicit null/no-op callbacks produce identical bytes for every mode and flag setting.
  [Fact]
  public async Task PrinterTraversalCancellationPreservesConstructorBytes() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M(value:int) requires value + 1 == 2 {}", options);
    var original = FindCallable<Method>(program, "M").Req.Single().E.Resolved;
    var previousCulture = CultureInfo.CurrentCulture;
    var previousUiCulture = CultureInfo.CurrentUICulture;
    try {
      var culture = CultureInfo.GetCultureInfo("fr-FR");
      CultureInfo.CurrentCulture = culture;
      CultureInfo.CurrentUICulture = culture;
      var defaultBytes = PrintBytes(original, culture, writer => new Printer(writer, options));
      var explicitDefaultBytes = PrintBytes(original, culture,
        writer => new Printer(writer, options, PrintModes.Everything, null));
      Assert.Equal(defaultBytes, explicitDefaultBytes);

      PrintFlags?[] flags = [null, new PrintFlags(), new PrintFlags(true)];
      foreach (var mode in Enum.GetValues<PrintModes>()) {
        foreach (var flag in flags) {
          var legacyBytes = PrintBytes(original, culture, writer => new Printer(writer, options, mode, flag));
          var nullBytes = PrintBytes(original, culture, writer => new Printer(writer, options, mode, flag, null));
          var noOpBytes = PrintBytes(original, culture, writer => new Printer(writer, options, mode, flag, () => { }));
          Assert.Equal(legacyBytes, nullBytes);
          Assert.Equal(legacyBytes, noOpBytes);
        }
      }
    }
    finally {
      CultureInfo.CurrentCulture = previousCulture;
      CultureInfo.CurrentUICulture = previousUiCulture;
    }
  }

  private static async Task<Expression> CreateDeepPrinterExpression(string shape, DafnyOptions options) {
    const int depth = 512;
    string source;
    if (shape == "and") {
      source = "method M(value:bool) requires " +
        string.Join(" && ", Enumerable.Repeat("value", depth + 1)) + " {}";
    } else if (shape == "add") {
      source = "method M(value:int) requires " +
        string.Join(" + ", Enumerable.Repeat("value", depth + 1)) + " == 0 {}";
    } else {
      Assert.Equal("dotted", shape);
      source = "codatatype Node = More(next: Node) function F(node:Node):Node { " +
        "node" + string.Concat(Enumerable.Repeat(".next", depth)) + " }";
    }

    var program = await ParseAndResolve(source, options);
    if (shape == "dotted") {
      return FindCallable<Function>(program, "F").Body!.Resolved;
    }
    var resolved = FindCallable<Method>(program, "M").Req.Single().E.Resolved;
    if (shape == "and") {
      return resolved;
    }
    return Assert.IsType<BinaryExpr>(resolved).E0;
  }

  private static Expression LeftSpineChild(string shape, Expression expression, int depth) {
    if (shape == "dotted") {
      if (depth == 0) {
        return Assert.IsType<MemberSelectExpr>(expression).Obj;
      }
      var dot = Assert.IsType<ExprDotName>(expression);
      Assert.IsType<MemberSelectExpr>(dot.Resolved);
      return dot.Lhs;
    }
    var binary = Assert.IsType<BinaryExpr>(expression);
    Assert.Equal(shape == "and" ? BinaryExpr.ResolvedOpcode.And : BinaryExpr.ResolvedOpcode.Add,
      binary.ResolvedOp);
    return binary.E0;
  }

  private static byte[] PrintBytes(Expression expression, CultureInfo culture,
    Func<TextWriter, Printer> createPrinter) {
    using var writer = new StringWriter(culture);
    createPrinter(writer).PrintExpression(expression, false);
    return Encoding.UTF8.GetBytes(writer.ToString());
  }

  private sealed class CountingTextWriter : TextWriter {
    public int WriteAttempts { get; private set; }

    public override Encoding Encoding => Encoding.UTF8;

    public override void Write(char value) {
      WriteAttempts++;
    }

    public override void Write(string? value) {
      WriteAttempts++;
    }

    public override void Write(char[] buffer, int index, int count) {
      WriteAttempts++;
    }

    public override void Write(ReadOnlySpan<char> buffer) {
      WriteAttempts++;
    }

    public override void Write(StringBuilder? value) {
      WriteAttempts++;
    }

    public override void WriteLine(string? value) {
      WriteAttempts++;
    }

    public override void WriteLine(ReadOnlySpan<char> buffer) {
      WriteAttempts++;
    }

    public override void WriteLine(StringBuilder? value) {
      WriteAttempts++;
    }

    public override void WriteLine() {
      WriteAttempts++;
    }
  }

  private sealed class ObservedIntegerType(Action onSubstitution) : IntType {
    public override Microsoft.Dafny.Type Subst(IDictionary<TypeParameter, Microsoft.Dafny.Type> substitutions) {
      onSubstitution();
      return this;
    }
  }

}
