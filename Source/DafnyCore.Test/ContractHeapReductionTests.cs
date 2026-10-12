using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class ContractHeapReductionTests {
  // Heap-independent nested values stop during recursive inspection without modifying the caller's resolved value.
  [Fact]
  public async Task HeapIndependenceCancellationPreservesNestedValue() {
    var (program, method, fields) = await Parse();
    var value = ((BinaryExpr)method.Req.Single().E.Resolved).E1;
    var resolved = value.Resolved;
    var originalType = value.Type;
    var before = Printer.ExprToString(program.Options, value);
    Func<Expression, bool> defaultCheck = ContractHeapReductionContext.IsHeapIndependent;
    Assert.True(defaultCheck(value));
    var totalChecks = 0;
    Assert.True(ContractHeapReductionContext.IsHeapIndependent(value, () => totalChecks++));
    Assert.True(totalChecks > 4);
    bool? result = null;
    var checks = 0;
    Assert.Throws<OperationCanceledException>(() => result = ContractHeapReductionContext.IsHeapIndependent(value, () => {
      if (++checks == 4) { throw new OperationCanceledException(); }
    }));
    Assert.Null(result);
    Assert.Equal(4, checks);
    Assert.Same(resolved, value.Resolved);
    Assert.Same(originalType, value.Type);
    Assert.Equal(before, Printer.ExprToString(program.Options, value));
  }

  // Copying an input fact stream stops before later facts are requested and cannot publish a partial context.
  [Fact]
  public async Task HeapContextCancellationStopsFactCopy() {
    var (program, method, fields) = await Parse();
    var value = ((BinaryExpr)method.Req.Single().E.Resolved).E1;
    var before = Printer.ExprToString(program.Options, value);
    var facts = fields.Select(field => new ContractHeapReductionFact(method.Ins[0], field, value)).ToArray();
    var complete = new ContractHeapReductionContext(facts, facts);
    var reducer = new ContractExpressionReducer(program.Options, program.DefaultModuleDef, program.SystemModuleManager);
    var control = reducer.ReduceWithHeap(method.Ens.Single().E, complete);
    Assert.Equal(ContractReductionDecision.True, control.Decision);
    var requested = 0;
    IEnumerable<ContractHeapReductionFact> Input() {
      foreach (var fact in facts) {
        requested++;
        yield return fact;
      }
    }
    ContractHeapReductionContext? context = null;
    Assert.Throws<OperationCanceledException>(() => context = new ContractHeapReductionContext(Input(), [],
      cancellationCheck: () => {
        if (requested == 2) { throw new OperationCanceledException(); }
      }));
    Assert.Null(context);
    Assert.Equal(2, requested);
    Assert.True(facts.Length > requested);
    Assert.All(facts, fact => Assert.Same(value, fact.Value));
    Assert.Equal(before, Printer.ExprToString(program.Options, value));
  }

  // Reveal identity copying observes the boundary before consuming the entire caller-controlled stream.
  [Fact]
  public async Task HeapContextCancellationStopsRevealCopy() {
    var (program, method, fields) = await Parse();
    var function = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Function>().Single(candidate => candidate.Name == "Known");
    var requested = 0;
    IEnumerable<Function> Reveals() {
      for (var index = 0; index < 8; index++) {
        requested++;
        yield return function;
      }
    }
    ContractHeapReductionContext? context = null;
    Assert.Throws<OperationCanceledException>(() => context = new ContractHeapReductionContext([], [], Reveals(), () => {
      if (requested == 2) { throw new OperationCanceledException(); }
    }));
    Assert.Null(context);
    Assert.Equal(2, requested);
    Assert.NotNull(function.Body);
  }

  private static async Task<(Program Program, Method Method, List<Field> Fields)> Parse() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse("class Cell { var a:seq<seq<int>> var b:seq<seq<int>> var c:seq<seq<int>> } " +
      "predicate Known() { true } method M(cell:Cell) requires cell.a == [[1,2],[3,4]] " +
      "ensures cell.a == [[1,2],[3,4]] {}", new Uri("untitled:contract-heap-context"), reporter);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var program = parsed.Program;
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single(candidate => candidate.Name == "M");
    var fields = program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Single(declaration => declaration.Name == "Cell")
      .Members.OfType<Field>().ToList();
    return (program, method, fields);
  }
}
