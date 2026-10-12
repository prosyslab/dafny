using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractClosedClauseTypeTests {
  // A captured nullable reference bound to null cannot acquire an inconsistent non-null parameter premise.
  [Theory]
  [InlineData("captured == null", false, ContractQueryOutcome.Unsat)]
  [InlineData("captured == null", true, ContractQueryOutcome.Sat)]
  [InlineData("captured != null", false, ContractQueryOutcome.Sat)]
  [InlineData("captured != null", true, ContractQueryOutcome.Unsat)]
  public async Task NullableCapturedNullPreservesBothPolarities(string property, bool negate, ContractQueryOutcome expected) {
    var source = "module Library { class Cell {} type MaybeCell = Cell? } " +
      "module Client { import L = Library class Cell {} " +
      "method Entry() { var captured:L.MaybeCell := null; assert " + property + "; } }";
    var result = await Check(source, new ContractValue(ContractValueKind.Null), negate);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

  // Closed pure queries reject reference identities instead of inventing a non-null object encoding.
  [Fact]
  public async Task NullableCapturedReferenceRetainsUnsupportedEncoding() {
    const string source = "module Library { class Cell {} } " +
      "module Client { import L = Library method Entry() { var captured:L.Cell? := null; assert captured != null; } }";
    await Assert.ThrowsAsync<System.NotSupportedException>(() =>
      Check(source, new ContractValue(ContractValueKind.Reference, "object-1"), negate: false));
  }

  // Constructor instantiations preserve imported aliases through nested collections despite local type shadows.
  [Theory]
  [InlineData(false, 2, false, ContractQueryOutcome.Unsat)]
  [InlineData(false, 3, false, ContractQueryOutcome.Sat)]
  [InlineData(false, 2, true, ContractQueryOutcome.Sat)]
  [InlineData(false, 3, true, ContractQueryOutcome.Unsat)]
  [InlineData(true, 2, false, ContractQueryOutcome.Unsat)]
  [InlineData(true, 3, false, ContractQueryOutcome.Sat)]
  [InlineData(true, 2, true, ContractQueryOutcome.Sat)]
  [InlineData(true, 3, true, ContractQueryOutcome.Unsat)]
  public async Task ImportedConstructorTypeArgumentsRetainNestedIdentity(bool nested, int captured, bool negate,
    ContractQueryOutcome expected) {
    var property = nested ? "L.Ok(map[0 := L.Box(captured)]).value[0].value[0] == 2" :
      "L.Ok(captured).value[0] == 2";
    var source = """
      module Library {
        type Byte = b: int | 0 <= b < 256 witness 0
        type Bytes = seq<Byte>
        datatype Result<T> = Ok(value: T)
        datatype Box<T> = Box(value: T)
        function Make(): Bytes { [2] }
      }
      module Client {
        import L = Library
        type Byte = b: int | b == 99 witness 99
        datatype Box<T> = Other(other: T)
        method Entry() { var captured := L.Make(); assert PROPERTY; }
      }
      """.Replace("PROPERTY", property);
    var result = await Check(source, new ContractValue(ContractValueKind.Sequence,
      Items: [new ContractValue(ContractValueKind.Integer, captured.ToString())]), negate);
    Assert.True(result.Outcome == expected, result.Diagnostics);
  }

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
    var constructors = assertion.Expr.DescendantsAndSelf.OfType<DatatypeValue>().ToDictionary(
      constructor => constructor, constructor => (constructor.Ctor, constructor.InferredTypeArgs,
        Items: constructor.InferredTypeArgs.ToArray()));
    var query = ContractQueryBuilder.BuildClosedClause(prepared, clause,
      new Dictionary<string, ContractValue> { [local.Name] = value }, negate);
    foreach (var (constructor, original) in constructors) {
      Assert.Same(original.Ctor, constructor.Ctor);
      Assert.Same(original.InferredTypeArgs, constructor.InferredTypeArgs);
      Assert.Equal(original.Items.Length, constructor.InferredTypeArgs.Count);
      for (var index = 0; index < original.Items.Length; index++) {
        Assert.Same(original.Items[index], constructor.InferredTypeArgs[index]);
      }
    }
    return await ContractSolver.CheckAsync(query, ContractQueryKind.ClosedClause, options, CancellationToken.None,
      queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: prepared.SourceSnapshots, sourcePath: prepared.Source.Path);
  }
}
