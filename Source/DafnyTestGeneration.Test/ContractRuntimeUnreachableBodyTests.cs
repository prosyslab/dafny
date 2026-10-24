#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeUnreachableBodyTests {
  // A detached diagnostic gives an unrelated bodyless iterator a compilable trap without changing its authored contract.
  [Fact]
  public async Task AddsBodyToUnreachableConcreteIterator() {
    const string declarations =
      "  iterator Unused() yields (value: int)\n" +
      "    yield ensures value >= 0 // 반복 끝\n";
    var source = Source(declarations);
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var iterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Unused");

    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
    Assert.Contains("yield ensures value >= 0 // 반복 끝", transformedSource);
    Assert.NotNull(iterator.Body);
    Assert.Contains(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    AssertCodeGenerates(reparsed);
  }

  // An unrelated implemented iterator keeps its clauses while its executable body becomes the diagnostic trap.
  [Fact]
  public async Task ReplacesBodyOfUnreachableConcreteIterator() {
    const string declarations =
      "  iterator Unused() yields (value: int)\n" +
      "    yield requires \"시작\" != \"\"\n" +
      "    yield ensures value >= 0\n" +
      "  { value := 1; yield; }\n";
    var source = Source(declarations);
    var snapshots = Snapshots(source);

    var transformed = await Transform(snapshots);
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var iterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Unused");

    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
    Assert.Contains("yield requires \"시작\" != \"\"", transformedSource);
    Assert.Contains("yield ensures value >= 0", transformedSource);
    Assert.DoesNotContain("value := 1", transformedSource);
    Assert.Contains(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    AssertCodeGenerates(reparsed);
  }

  // An iterator type mentioned by selected generator code remains intact even when no generated iterator member is called.
  [Fact]
  public async Task PreservesTypeReachableIteratorBody() {
    const string body = "{ value := 1; yield; }";
    var source = Source(
      "  iterator Needed() yields (value: int) " + body + "\n",
      generatorBody: "{ var unused: Needed? := null; x := 0; }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var iterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Needed");

    Assert.Contains(body, transformedSource);
    Assert.Contains(iterator.Body.Descendants().OfType<YieldStmt>(), _ => true);
    Assert.DoesNotContain(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    AssertCodeGenerates(reparsed);
  }

  // Calls reachable only through an unused iterator body do not imply runtime execution of either iterator.
  [Fact]
  public async Task IgnoresIteratorBodyOnlyConstructorForRuntimeCapability() {
    var source = Source(
      "  iterator Nested() yields (value: int)\n" +
      "    yield ensures value >= 0\n" +
      "  method Helper() { var nested := new Nested(); }\n" +
      "  iterator Unused() yields (value: int)\n" +
      "    yield ensures value == 1\n" +
      "  { Helper(); value := 1; yield; }\n",
      generatorBody: "{ var unused: Unused? := null; x := 0; }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var reparsed = await Parse(transformed.Sources);
    var iterators = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .ToDictionary(iterator => iterator.Name);
    var helper = ContractRuntimeObligationTransformer.Members(reparsed).OfType<Method>()
      .Single(method => method.Name == "Helper");
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;

    Assert.Contains(iterators["Nested"].Body.Descendants().OfType<CallStmt>(),
      call => call.Method.Name == "UnreachableBody");
    Assert.Contains(helper.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.Contains(iterators["Unused"].Body.Descendants().OfType<YieldStmt>(), _ => true);
    Assert.Contains(iterators["Unused"].Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "Helper");
    Assert.Contains("yield ensures value >= 0", transformedSource);
    Assert.Contains("yield ensures value == 1", transformedSource);
    Assert.Contains("{ Helper(); value := 1; yield; }", transformedSource);
    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
    AssertCodeGenerates(reparsed);
  }

  // An iterator type mentioned by the selected goal remains supported without implying constructor or advancement execution.
  [Fact]
  public async Task PreservesIteratorTypeMentionedOnlyBySelectedGoal() {
    const string body = "{ value := 1; yield; }";
    var source = Source(
      "  iterator Needed() yields (value: int) " + body + "\n",
      completeBody: "{ var unused: Needed? := null; y := x; }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal));
    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var transformed = new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform();
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "M.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var iterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Needed");

    Assert.Contains(body, transformedSource);
    Assert.Contains(iterator.Body.Descendants().OfType<YieldStmt>(), _ => true);
    Assert.DoesNotContain(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
    AssertCodeGenerates(reparsed);
  }

  // Executed iterators are rejected structurally after retaining their original body and transitive dispatch closure.
  [Fact]
  public async Task RejectsExecutedIteratorAfterPreservingDynamicDependencies() {
    const string declarations =
      "  trait Worker { method Step(x: int) returns (y: int) }\n" +
      "  class Implementation extends Worker {\n" +
      "    method Step(x: int) returns (y: int) { y := Helper(x); }\n" +
      "  }\n" +
      "  method Helper(x: int) returns (y: int) { y := x; }\n" +
      "  iterator Needed(worker: Worker, input: int) yields (value: int)\n" +
      "  { value := worker.Step(input); yield; }\n";
    const string completeBody =
      "{ var worker: Worker := new Implementation; var iter := new Needed(worker, x); " +
      "var more := iter.MoveNext(); if more { y := iter.value; } else { y := 0; } }";
    var source = Source(declarations, completeBody);
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");
    var iterator = original.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Needed");
    var reachable = ContractRuntimeObligationTransformer.DiagnosticReachable(original, goal, generator).ToHashSet();

    Assert.Contains(iterator.Member_Init, reachable);
    Assert.Contains(iterator.Member_MoveNext, reachable);
    Assert.Contains(reachable, callable => callable.FullDafnyName == "M.Worker.Step");
    Assert.Contains(reachable, callable => callable.FullDafnyName == "M.Implementation.Step");
    Assert.Contains(reachable, callable => callable.FullDafnyName == "M.Helper");
    var members = ContractRuntimeObligationTransformer.Members(original).ToList();
    var implementation = members.OfType<Method>()
      .Single(method => method.FullDafnyName == "M.Implementation.Step");
    var helper = members.OfType<Method>().Single(method => method.FullDafnyName == "M.Helper");

    Assert.Contains(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "Step");
    Assert.Contains(iterator.Body.Descendants().OfType<YieldStmt>(), _ => true);
    Assert.Contains(implementation.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "Helper");
    Assert.DoesNotContain(helper.Body!.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    var reason = Assert.IsType<string>(
      ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var exception = Assert.Throws<NotSupportedException>(() =>
      new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform());
    Assert.Equal(reason, exception.Message);
    Assert.Contains("M.Needed", reason, System.StringComparison.Ordinal);
    Assert.Equal(source, snapshots[0].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(source), snapshots[0].Sha256);
  }

  // A generator-only iterator execution is rejected by the same structural closure guard while the ordinary goal remains supported.
  [Fact]
  public async Task RejectsIteratorReachedOnlyByGenerator() {
    var source = Source(
      "  iterator Generated() yields (value: int) { value := 1; yield; }\n",
      generatorBody: "{ var iter := new Generated(); var more := iter.MoveNext(); x := 0; }");
    var snapshots = Snapshots(source);
    var original = await Parse(snapshots);
    var goal = ContractCallableSelector.SelectMethod(original, new("M.Complete"), requireConcreteReceiver: false);
    var generator = ContractRuntimeObligationTransformer.Members(original).OfType<Method>()
      .Single(method => method.Name == "Generate");

    Assert.Null(ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal));
    var reason = Assert.IsType<string>(
      ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(original, goal, generator));
    var exception = Assert.Throws<NotSupportedException>(() =>
      new ContractRuntimeObligationTransformer(original, snapshots, goal).Transform());

    Assert.Equal(reason, exception.Message);
    Assert.Contains("M.Generated", reason, System.StringComparison.Ordinal);
    Assert.Equal(source, snapshots[0].Content);
  }

  // A default-module iterator ending in a Unicode comment receives its body strictly after the true source EOF.
  [Fact]
  public async Task AddsBodyAfterDefaultModuleIteratorAtSourceEnd() {
    const string iteratorSource =
      "iterator Unused() yields (value: int)\n" +
      "  yield ensures value >= 0 // 실제 파일 끝";
    var goalSource = Source("");
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    ContractSource[] snapshots = [
      new("M.dfy", goalSource, ContractHarnessBuilder.Hash(goalSource)),
      new("Unused.dfy", iteratorSource, ContractHarnessBuilder.Hash(iteratorSource)),
      new("PbtRuntime.dfy", runtime, ContractHarnessBuilder.Hash(runtime))
    ];

    var transformed = await Transform(snapshots);
    var transformedSource = transformed.Sources.Single(snapshot => snapshot.Path == "Unused.dfy").Content;
    var reparsed = await Parse(transformed.Sources);
    var iterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(candidate => candidate.Name == "Unused");

    Assert.Equal(iteratorSource, snapshots[1].Content);
    Assert.Equal(ContractHarnessBuilder.Hash(iteratorSource), snapshots[1].Sha256);
    Assert.StartsWith(iteratorSource + "\n{ ", transformedSource, System.StringComparison.Ordinal);
    Assert.EndsWith("UnreachableBody(); }\n", transformedSource, System.StringComparison.Ordinal);
    Assert.Contains(iterator.Body.Descendants().OfType<CallStmt>(), call => call.Method.Name == "UnreachableBody");
    AssertCodeGenerates(reparsed);
  }

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
      "  iterator {:compile false} DisabledIterator() yields (value: int)\n" +
      "  class NativeBox { constructor {:extern} Create() }\n") +
      "\nabstract module AbstractApi {\n" +
      "  method AbstractMethod()\n" +
      "  function AbstractFunction(): int\n" +
      "  iterator AbstractIterator() yields (value: int)\n" +
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
    var abstractIterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(iterator => iterator.Name == "AbstractIterator");
    Assert.Null(abstractIterator.Body);
    Assert.True(Attributes.Contains(nativeMethod.Attributes, "extern"));
    Assert.True(Attributes.Contains(nativeFunction.Attributes, "extern"));
    Assert.True(Attributes.Contains(nativeConstructor.Attributes, "extern"));
    Assert.True(Attributes.Contains(synthesized.Attributes, "synthesize"));
    var disabledIterator = reparsed.RawModules().SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
      .Single(iterator => iterator.Name == "DisabledIterator");
    Assert.Null(disabledIterator.Body);
    Assert.True(Attributes.Contains(disabledIterator.Attributes, "compile"));
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

  private static void AssertCodeGenerates(Program program) {
    var backend = new CsharpBackend(program.Options);
    program.Options.Backend = backend;
    backend.OnPreCompile(program.Reporter, new ReadOnlyCollection<string>([]));
    backend.Compile(program, "M.dfy", new ConcreteSyntaxTree());
    var reporter = Assert.IsType<BatchErrorReporter>(program.Reporter);
    Assert.True(reporter.ErrorCount == 0,
      string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }
}
