using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class ContractExpressionReducerTests {
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
}
