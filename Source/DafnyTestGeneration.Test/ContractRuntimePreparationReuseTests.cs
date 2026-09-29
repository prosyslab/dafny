using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimePreparationReuseTests {
  // Repeated call sites retain distinct obligations and avoid every source result-name collision.
  [Theory]
  [InlineData("contractResult", "contractResult0")]
  [InlineData("contractResult0", "contractResult00")]
  public async Task RepeatedDescriptorsPreserveCollisionSafeResult(string collision, string expected) {
    var transformation = await Transform(collision);
    var clauses = transformation.Clauses.Where(clause => clause.Owner.FullDafnyName == "M.Increment").ToList();
    Assert.Equal(2, clauses.Count);
    Assert.Equal(2, clauses.Select(clause => clause.Obligation.Id).Distinct().Count());
    Assert.All(clauses, clause => Assert.Equal(expected, Assert.Single(clause.Owner.Outs).Name));
    Assert.NotSame(clauses[0].Owner, clauses[1].Owner);
    Assert.NotSame(clauses[0].Owner.Outs[0], clauses[1].Owner.Outs[0]);
    await Resolve(transformation.Sources.ToArray());
  }

  // A later parsed program reserves its own family independently of a preceding transformation.
  [Fact]
  public async Task SeparateProgramsRetainTheirOwnResultFamilies() {
    var first = await Transform("contractResult00");
    var second = await Transform("unrelated");
    Assert.All(first.Clauses, clause => Assert.Equal("contractResult000", clause.Owner.Outs.Single().Name));
    Assert.All(second.Clauses, clause => Assert.Equal("contractResult", clause.Owner.Outs.Single().Name));
  }

  private static async Task<ContractRuntimeTransformation> Transform(string collision) {
    var source = "module M { import PbtRandom function Increment(x:int):int ensures Increment(x) == x+1 { x+1 } " +
      "method Goal(x:int) { var " + collision + " := Increment(x); var y := Increment(" + collision + "); } " +
      "method Generate(r:PbtRandom.Source) returns(x:int) { x := 0; } }";
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] sources = [new("Reuse.dfy", source, ContractHarnessBuilder.Hash(source)),
      new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))];
    var program = await Resolve(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Goal"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
  }

  private static async Task<Program> Resolve(ContractSource[] sources) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return program;
  }
}
