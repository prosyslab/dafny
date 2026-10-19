using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class TriggerBoundVariableScopeTests {
  // Recombining rewritten splits must not leave another split's generated variable free.
  [Theory]
  [InlineData("forall index: nat :: index + 1 < |values| ==> " +
              "values[index] <= values[index + 1] && values[index + 1] <= ceiling && values[index + 1] < ceiling")]
  [InlineData("exists index: nat :: index + 1 < |values| && " +
              "(values[index] <= values[index + 1] || values[index + 1] <= ceiling || values[index + 1] < ceiling)")]
  public async Task RewrittenSplitsKeepGeneratedVariablesBound(string condition) {
    var (options, quantifier, method) = await ResolvePrecondition(condition);
    Assert.NotNull(quantifier.SplitQuantifier);
    var splits = quantifier.SplitQuantifier!.Cast<QuantifierExpr>().ToList();
    Assert.Contains(splits, split => split.BoundVars.Count > quantifier.BoundVars.Count);
    foreach (var split in splits) {
      var freeVariables = FreeVariablesUtil.ComputeFreeVariables(options, split);
      Assert.All(freeVariables, variable => Assert.Contains(variable, method.Ins));
    }
  }

  // Splits with the same binder and trigger still combine into a closed quantifier.
  [Fact]
  public async Task CompatibleSplitsStillCombine() {
    var (options, quantifier, method) = await ResolvePrecondition(
      "forall index: nat | index < |values| :: values[index] <= ceiling && values[index] < ceiling");
    var combined = Assert.IsType<ForallExpr>(Assert.Single(quantifier.SplitQuantifier!));
    Assert.Single(combined.BoundVars);
    Assert.All(FreeVariablesUtil.ComputeFreeVariables(options, combined),
      variable => Assert.Contains(variable, method.Ins));
  }

  private static async Task<(DafnyOptions, QuantifierExpr, Method)> ResolvePrecondition(string condition) {
    Microsoft.Dafny.Type.ResetScopes();
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var source = "method CheckAdjacent(values: seq<int>, ceiling: int) requires " + condition + " {}";
    var parsed = await ProgramParser.Parse(source, new Uri("untitled:trigger-bound-variable-scope"), reporter);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.Equal(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(parsed.Program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single();
    return (options, Assert.IsAssignableFrom<QuantifierExpr>(method.Req.Single().E.Resolved), method);
  }
}
