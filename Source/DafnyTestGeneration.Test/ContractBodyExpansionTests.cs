using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractBodyExpansionTests {
  private static async Task<ContractGenerationResult> FixedGuard(string source, string guard,
    string input, int loopBound = 3) {
    var options = ContractInputTests.Options();
    var program = await Utils.Parse(new BatchErrorReporter(options), source);
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var expansion = new ContractBodyExpander(program, new(MaxLoopIterations: loopBound)).Expand(method);
    var goal = expansion.Goals.Single(item => item.Location.Position == source.IndexOf(guard, System.StringComparison.Ordinal) && item.BranchValue == true);
    var request = ContractInputTests.Request(source, bounds: new(MaxInputs: 1, MaxLoopIterations: loopBound)) with {
      RequiredGoalId = goal.Id,
      CandidateInputs = new System.Collections.Generic.Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, input) }
    };
    return await ContractInputGenerator.GenerateAsync(request, options, CancellationToken.None);
  }
  // A bounded loop frontier does not become a normal post-loop path or mutate the source AST.
  [Fact]
  public async Task LoopFrontierPreservesOriginalBody() {
    var options = ContractInputTests.Options();
    var reporter = new BatchErrorReporter(options);
    var program = await Utils.Parse(reporter, "method Entry(x:int) returns(r:int) { r := 0; while r < x { r := r + 1; } }");
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var original = Printer.StatementToString(options, method.Body!);
    var result = new ContractBodyExpander(program, new(MaxLoopIterations: 1)).Expand(method);
    Assert.Contains(result.Frontier, item => item.Reason == "loop_bound");
    Assert.Equal(original, Printer.StatementToString(options, method.Body!));
    Assert.NotSame(method.Body, result.DetachedBody);
  }

  // Simultaneous assignments retain their original pre-state value relation during path solving.
  [Fact]
  public async Task ParallelAssignmentPreservesSwap() {
    var request = ContractInputTests.Request("""
      method Entry(x:int) returns(r:int) {
        var a,b := x,1;
        a,b := b,a;
        r := if a == 1 && b == 8 then -1 else 0;
      }
      """, count: 4);
    var result = await ContractInputGenerator.GenerateAsync(request, ContractInputTests.Options(), CancellationToken.None);
    Assert.Contains(result.Inputs, input => input.Request.Inputs["x"].Value == "8");
  }

  // A true guard at the loop bound cannot reach a normal post-loop branch goal.
  [Fact]
  public async Task LoopCapDoesNotPretendToTerminate() {
    var result = await FixedGuard("""
      method Entry(x:int) returns(r:int) {
        r := 0;
        while r < x { r := r + 1; }
        r := if r == 2 then -1 else 0;
      }
      """, "r == 2", "3", 2);
    Assert.Empty(result.Inputs);
    Assert.True(result.Counts.BoundedUnsat > 0);
    Assert.Equal(0, result.Counts.Unknown);
    Assert.Contains(result.Frontier, frontier => frontier.Reason == "loop_bound");
  }

  // Completing exactly the permitted iteration count may reach the original continuation.
  [Fact]
  public async Task LoopAtExactBoundCanTerminate() {
    var result = await FixedGuard("""
      method Entry(x:int) returns(r:int) {
        r := 0;
        while r < x { r := r + 1; }
        r := if r == 2 then -1 else 0;
      }
      """, "r == 2", "2", 2);
    Assert.Single(result.Inputs);
  }

  // Original continue and break destinations survive bounded loop expansion.
  [Fact]
  public async Task LoopBreakAndContinuePreserveContinuation() {
    var result = await FixedGuard("""
      method Entry(x:int) returns(r:int) {
        r := 0; var i := 0;
        while i < x {
          i := i + 1;
          if i == 2 { continue; }
          if i == 3 { break; }
          r := r + 1;
        }
        r := if r == 1 then -1 else 0;
      }
      """, "r == 1", "5");
    Assert.Single(result.Inputs);
  }

  // Nested by-method calls use the executed body even when it disagrees with the function definition.
  [Fact]
  public async Task ByMethodBodyConstrainsGeneratedPath() {
    var result = await FixedGuard("""
      function Transform(x:int):int { x } by method { return x + 1; }
      method Entry(x:int) returns(r:int) { var t := Transform(x); r := if t == 8 then -1 else 0; }
      """, "t == 8", "7");
    Assert.Single(result.Inputs);
  }

  // A bodyless external method is captured at the call site as an abstract contract call.
  [Fact]
  public async Task ExternalMethodExpandsAsAbstractCall() {
    var options = ContractInputTests.Options();
    var program = await Utils.Parse(new BatchErrorReporter(options),
      "method {:extern} External(x:int) returns(r:int) ensures r == x+1 method Entry(x:int) { var r := External(x); }");
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var result = new ContractBodyExpander(program).Expand(method);
    Assert.Empty(result.Frontier);
    Assert.Equal("External", Assert.Single(result.AbstractCalls));
    Assert.Equal("External", Assert.Single(result.CapturedCalls).Callable.FullDafnyName);
  }

  // An external function with a Dafny body remains abstract rather than inlining that body.
  [Fact]
  public async Task ExternalFunctionBodyExpandsAsAbstractCall() {
    var options = ContractInputTests.Options();
    var program = await Utils.Parse(new BatchErrorReporter(options),
      "function {:extern} External(x:int):int ensures External(x) == x+1 { x-1 } method Entry(x:int) { var r := External(x); }");
    var method = ContractCallableSelector.SelectMethod(program, new("Entry"));
    var result = new ContractBodyExpander(program).Expand(method);
    Assert.Empty(result.Frontier);
    Assert.Equal("External", Assert.Single(result.AbstractCalls));
    Assert.Equal("External", Assert.Single(result.CapturedCalls).Callable.FullDafnyName);
  }
}
