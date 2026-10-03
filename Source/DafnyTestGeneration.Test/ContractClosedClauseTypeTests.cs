using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractClosedClauseTypeTests {
  // Inferred imported aliases retain their refined element type despite a conflicting local name.
  [Theory]
  [InlineData(2, false, ContractQueryOutcome.Unsat)]
  [InlineData(3, false, ContractQueryOutcome.Sat)]
  [InlineData(2, true, ContractQueryOutcome.Sat)]
  [InlineData(3, true, ContractQueryOutcome.Unsat)]
  public async Task InferredImportedSequencePreservesBothPolarities(int captured, bool negate, ContractQueryOutcome expected) {
    const string source = """
      module Library {
        type Byte = b: int | 0 <= b < 256 witness 0
        type Bytes = seq<Byte>
        function Make(): Bytes { [2] }
      }
      module Client {
        import L = Library
        type Byte = b: int | b == 99 witness 99
        method Entry() {
          var captured := L.Make();
          assert captured[0] == 2;
        }
      }
      """;
    var value = new ContractValue(ContractValueKind.Sequence,
      Items: [new ContractValue(ContractValueKind.Integer, captured.ToString())]);
    var result = await Check(source, value, negate);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Qualifying a captured type does not hide an out-of-bounds assertion in either polarity.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task InferredImportedSequenceRetainsDefinedness(bool negate) {
    const string source = """
      module Library { type Bytes = seq<int> function Make(): Bytes { [2] } }
      module Client {
        import L = Library
        method Entry() { var captured := L.Make(); assert captured[0] == 2; }
      }
      """;
    var result = await Check(source, new ContractValue(ContractValueKind.Sequence, Items: []), negate);
    Assert.True(result.Outcome == ContractQueryOutcome.Error, result.Diagnostics);
  }

  // Inferred generic datatype arguments remain bound to the imported declaration through a collection.
  [Theory]
  [InlineData(false, ContractQueryOutcome.Unsat)]
  [InlineData(true, ContractQueryOutcome.Sat)]
  public async Task InferredGenericDatatypePreservesImportIdentity(bool negate, ContractQueryOutcome expected) {
    const string source = """
      module Library {
        datatype Box<T> = Box(value: T)
        type Boxes = seq<Box<int>>
        function Make(): Boxes { [Box(2)] }
      }
      module Client {
        import L = Library
        datatype Box<T> = Other(other: T)
        method Entry() { var captured := L.Make(); assert captured[0].value == 2; }
      }
      """;
    var value = new ContractValue(ContractValueKind.Sequence, Items: [new ContractValue(
      ContractValueKind.Datatype, Constructor: "Library.Box.Box", Fields: new Dictionary<string, ContractValue> {
        ["value"] = new(ContractValueKind.Integer, "2")
      })]);
    var result = await Check(source, value, negate);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Captured built-in naturals from another resolved context retain nat identity and both truth polarities.
  [Theory]
  [InlineData(2, false, ContractQueryOutcome.Unsat)]
  [InlineData(3, false, ContractQueryOutcome.Sat)]
  [InlineData(2, true, ContractQueryOutcome.Sat)]
  [InlineData(3, true, ContractQueryOutcome.Unsat)]
  public async Task DetachedNaturalCapturePreservesBuiltinIdentity(int value, bool negate, ContractQueryOutcome expected) {
    const string source = "module Client { method Entry() { var captured: nat := 2; assert captured == 2; } }";
    var result = await Check(source, new ContractValue(ContractValueKind.Integer, value.ToString()), negate, detachedCapture: true);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  private static async Task<ContractQueryResult> Check(string source, ContractValue value, bool negate, bool detachedCapture = false) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    var reporter = new BatchErrorReporter(options);
    var request = new ContractTestRequest(1, [new ContractSource("contract.dfy", source, ContractHarnessBuilder.Hash(source))],
      new ContractEntry("Client.Entry"), new Dictionary<string, ContractValue>());
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var prepared = ContractHarnessBuilder.PrepareObservedHeap(program, request);
    var captureMethod = prepared.Method;
    if (detachedCapture) {
      var capturedProgram = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, CancellationToken.None);
      Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
      captureMethod = ContractHarnessBuilder.PrepareObservedHeap(capturedProgram, request).Method;
    }
    var local = captureMethod.Body!.Body.OfType<VarDeclStmt>().Single().Locals.Single();
    var assertion = prepared.Method.Body.Body.OfType<AssertStmt>().Single();
    var clause = new ContractRuntimeClause(new ContractRuntimeObligation("captured-assert", ContractRuntimeObligationKind.Postcondition,
      "contract.dfy", 1, 1, "original", null, ContractRuntimeDecisionMethod.ClosedSmt, null, new()),
      assertion.Expr, [local], prepared.Method);
    var query = ContractQueryBuilder.BuildClosedClause(prepared, clause,
      new Dictionary<string, ContractValue> { [local.Name] = value }, negate);
    return await ContractSolver.CheckAsync(query, ContractQueryKind.ClosedClause, options, CancellationToken.None,
      queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
  }
}
