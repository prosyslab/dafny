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
    Assert.False(result.BudgetExhausted);
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
}
