#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeUnreachableBodyTests {
  // Unrelated concrete declarations receive diagnostic trap bodies without disturbing the selected complete helper.
  [Fact]
  public async Task AddsBodiesToUnreachableConcreteCallables() {
    const string declarations =
      "  method Goal(x: int) returns (y: int)\n" +
      "    requires \"시작\" != \"\"\n" +
      "    ensures y == x && \"끝\" == \"끝\" // 메서드 끝\n" +
      "  function UnusedFunction(x: int): int\n" +
      "    ensures UnusedFunction(x) == x && \"끝\" == \"끝\" // 함수 끝\n";
    var source = Source(declarations);
    var snapshots = Snapshots(source);

    var transformed = await Transform(snapshots);
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var members = ContractRuntimeObligationTransformer.Members(reparsed).ToList();

    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
    Assert.Contains("requires \"시작\" != \"\"", transformedSource);
    Assert.Contains("ensures y == x && \"끝\" == \"끝\"", transformedSource);
    Assert.Contains("ensures UnusedFunction(x) == x && \"끝\" == \"끝\"", transformedSource);
    var complete = members.OfType<Method>().Single(method => method.FullDafnyName == "M.Complete");
    var method = members.OfType<Method>().Single(candidate => candidate.Name == "Goal");
    var function = members.OfType<Function>().Single(candidate => candidate.Name == "UnusedFunction");
    Assert.DoesNotContain(complete.Body!.Descendants().OfType<CallStmt>(),
      call => call.Method.Name is "UnreachableBody" or "Unreachable");
    Assert.Contains(complete.Body.Descendants().OfType<SingleAssignStmt>(), assignment =>
      assignment.Lhs.Resolved is IdentifierExpr { Var.Name: "y" } &&
      assignment.Rhs is ExprRhs { Expr.Resolved: IdentifierExpr { Var.Name: "x" } });
    Assert.Single(method.Req);
    Assert.Single(method.Ens);
    Assert.Single(function.Ens);
    Assert.False(Attributes.Contains(method.Attributes, "axiom"));
    Assert.False(Attributes.Contains(function.Attributes, "axiom"));
    Assert.Contains(method.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.Equal("UnreachableValue", Assert.IsType<FunctionCallExpr>(function.Body!.Resolved).Function.Name);
  }

  // Concrete overrides receive diagnostic bodies while the virtual trait declarations remain abstract.
  [Fact]
  public async Task AddsBodiesToUnreachableConcreteOverrides() {
    var source = Source(
      "  trait Contract {\n" +
      "    method Call(x: int) returns (y: int)\n" +
      "    function Read(x: int): int\n" +
      "  }\n" +
      "  class Implementation extends Contract {\n" +
      "    method Call(x: int) returns (y: int)\n" +
      "    function Read(x: int): int\n" +
      "  }\n");

    var transformed = await Transform(Snapshots(source));
    var reparsed = await Parse(transformed.Sources);
    var members = ContractRuntimeObligationTransformer.Members(reparsed).ToList();
    var trait = members.Where(member => member.EnclosingClass is TraitDecl).ToList();
    var implementation = members.Where(member => member.EnclosingClass.Name == "Implementation").ToList();

    Assert.Null(trait.OfType<Method>().Single(method => method.Name == "Call").Body);
    Assert.Null(trait.OfType<Function>().Single(function => function.Name == "Read").Body);
    var method = implementation.OfType<Method>().Single(candidate => candidate.Name == "Call");
    var function = implementation.OfType<Function>().Single(candidate => candidate.Name == "Read");
    Assert.Contains(method.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.Equal("UnreachableValue", Assert.IsType<FunctionCallExpr>(function.Body!.Resolved).Function.Name);
  }

  // A bodyless concrete constructor initializes every source field before entering its diagnostic trap.
  [Fact]
  public async Task AddsBodyToUnreachableConcreteConstructor() {
    var source = Source(
      "  class Box {\n" +
      "    var value: int\n" +
      "    ghost var proof: int\n" +
      "    constructor Create() // 생성자 끝\n" +
      "  }\n");

    var transformed = await Transform(Snapshots(source));
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var constructor = ContractRuntimeObligationTransformer.Members(reparsed).OfType<Constructor>()
      .Single(candidate => candidate.Name == "Create");

    Assert.NotNull(constructor.Body);
    Assert.Contains("this.value :=", transformedSource);
    Assert.Contains("this.proof :=", transformedSource);
    Assert.Contains("new;", transformedSource);
    Assert.Contains("UnreachableBody();", transformedSource);
    Assert.Contains(constructor.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
  }

  // Constructor traps preserve authored constant initializers while assigning mutable and uninitialized fields.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task PreservesInitializedConstantsInUnreachableConstructor(bool bodyless) {
    var constructorBody = bodyless ? "" : " { pending := 0; mutable := 0; }";
    var source =
      "module M {\n" +
      "  import PbtRandom\n" +
      "  class Box {\n" +
      "    const initialized: int := 7\n" +
      "    const pending: int\n" +
      "    var mutable: int\n" +
      "    constructor Create()" + constructorBody + "\n" +
      "    constructor Make() { pending := 0; mutable := 0; }\n" +
      "  }\n" +
      "  method Complete(box: Box) { var observed := box.mutable; }\n" +
      "  method Generate(r: PbtRandom.Source) returns (box: Box) { box := new Box.Make(); }\n" +
      "}";

    var transformed = await Transform(Snapshots(source));
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var constructor = ContractRuntimeObligationTransformer.Members(reparsed).OfType<Constructor>()
      .Single(candidate => candidate.Name == "Create");
    var box = (ClassDecl)constructor.EnclosingClass;
    var fields = box.Members.OfType<Field>().ToList();

    Assert.Contains("const initialized: int := 7", transformedSource);
    Assert.DoesNotContain("this.initialized :=", transformedSource);
    Assert.Contains("this.pending :=", transformedSource);
    Assert.Contains("this.mutable :=", transformedSource);
    Assert.NotNull(constructor.Body);
    Assert.Contains(constructor.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.NotNull(fields.OfType<ConstantField>().Single(field => field.Name == "initialized").Rhs);
    Assert.Null(fields.OfType<ConstantField>().Single(field => field.Name == "pending").Rhs);
  }

  // Native, ghost and virtual declarations retain their original bodyless compilation semantics.
  [Fact]
  public async Task PreservesBodylessExcludedDeclarations() {
    var source = Source(
      "  trait Contract {\n" +
      "    method Call()\n" +
      "    function Read(): int\n" +
      "  }\n" +
      "  ghost method GhostMethod()\n" +
      "  ghost function GhostFunction(): int\n" +
      "  method {:extern} NativeMethod()\n" +
      "  function {:extern} NativeFunction(): int\n" +
      "  static method {:synthesize} Synthesized() returns (value: int)\n" +
      "  class NativeBox { constructor {:extern} Create() }\n") +
      "\nabstract module AbstractApi {\n" +
      "  method AbstractMethod()\n" +
      "  function AbstractFunction(): int\n" +
      "}";

    var transformed = await Transform(Snapshots(source));
    var reparsed = await Parse(transformed.Sources);
    var members = ContractRuntimeObligationTransformer.Members(reparsed).ToList();

    Assert.Null(members.OfType<Method>().Single(method => method.Name == "GhostMethod").Body);
    Assert.Null(members.OfType<Function>().Single(function => function.Name == "GhostFunction").Body);
    var nativeMethod = members.OfType<Method>().Single(method => method.Name == "NativeMethod");
    var nativeFunction = members.OfType<Function>().Single(function => function.Name == "NativeFunction");
    var nativeConstructor = members.OfType<Constructor>().Single(constructor => constructor.Name == "Create");
    var synthesized = members.OfType<Method>().Single(method => method.Name == "Synthesized");
    var abstractMethod = members.OfType<Method>().Single(method => method.Name == "AbstractMethod");
    var abstractFunction = members.OfType<Function>().Single(function => function.Name == "AbstractFunction");
    Assert.Null(nativeMethod.Body);
    Assert.Null(nativeFunction.Body);
    Assert.Null(nativeConstructor.Body);
    Assert.Null(synthesized.Body);
    Assert.Null(abstractMethod.Body);
    Assert.Null(abstractFunction.Body);
    Assert.True(Attributes.Contains(nativeMethod.Attributes, "extern"));
    Assert.True(Attributes.Contains(nativeFunction.Attributes, "extern"));
    Assert.True(Attributes.Contains(nativeConstructor.Attributes, "extern"));
    Assert.True(Attributes.Contains(synthesized.Attributes, "synthesize"));
    Assert.All(members.Where(member => member.EnclosingClass is TraitDecl).OfType<MethodOrFunction>(),
      callable => Assert.True(callable switch {
        Method method => method.Body == null,
        Function function => function.Body == null,
        _ => false
      }));
  }

  // A bodyless executable callee in the selected closure remains visible to the earlier draft-request phase.
  [Fact]
  public async Task PreservesReachableBodylessCallee() {
    var source = Source(
      "  method Needed(x: int) returns (y: int) ensures y == x\n",
      completeBody: "{ y := Needed(x); }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);

    Assert.Contains(ContractRuntimeObligationTransformer.DiagnosticReachable(original, goal),
      callable => callable.Name == "Needed");
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var reparsed = await Parse(transformed.Sources);

    Assert.Null(ContractRuntimeObligationTransformer.Members(reparsed).OfType<Method>()
      .Single(method => method.Name == "Needed").Body);
  }

  // Bodyless method and function callees from the selected generator remain available for draft requests.
  [Fact]
  public async Task PreservesGeneratorReachableBodylessCallees() {
    var source = Source(
      "  method GenerateMethod() returns (x: int)\n" +
      "  function GenerateFunction(x: int): int\n",
      generatorBody: "{ var value := GenerateMethod(); x := GenerateFunction(value); }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");
    var reachable = ContractRuntimeObligationTransformer.DiagnosticReachable(original, goal, generator);

    Assert.Contains(reachable, callable => callable.Name == "GenerateMethod");
    Assert.Contains(reachable, callable => callable.Name == "GenerateFunction");
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var reparsed = await Parse(transformed.Sources);
    var members = ContractRuntimeObligationTransformer.Members(reparsed).ToList();

    Assert.Null(members.OfType<Method>().Single(method => method.Name == "GenerateMethod").Body);
    Assert.Null(members.OfType<Function>().Single(function => function.Name == "GenerateFunction").Body);
  }

  private static string Source(string declarations, string completeBody = "{ y := x; }",
    string generatorBody = "{ x := 0; }") =>
    "module M {\n" +
    "  import PbtRandom\n" +
    "  method Complete(x: int) returns (y: int) " + completeBody + "\n" +
    "  method Generate(r: PbtRandom.Source) returns (x: int) " + generatorBody + "\n" +
    declarations +
    "}";

  private static ContractSource[] Snapshots(string source) {
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    return [
      new("M.dfy", source, ContractHarnessBuilder.Hash(source)),
      new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))
    ];
  }

  private static async Task<ContractRuntimeTransformation> Transform(IReadOnlyList<ContractSource> sources) {
    var program = await Parse(sources);
    var goal = ContractCallableSelector.SelectMethod(program, new("M.Complete"), requireConcreteReceiver: false);
    return new ContractRuntimeObligationTransformer(program, sources, goal).Transform();
  }

  private static async Task<Program> Parse(IReadOnlyList<ContractSource> sources) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return program;
  }
}
