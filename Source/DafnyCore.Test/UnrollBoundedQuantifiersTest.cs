using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace DafnyCore.Test;

public class UnrollBoundedQuantifiersTest {
  private static async Task<Program> ParseAndResolve(string dafnyProgramText, DafnyOptions options) {
    const string fullFilePath = "untitled:UnrollBoundedQuantifiersTest";
    var rootUri = new Uri(fullFilePath);

    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    if (errorReporter.ErrorCount != 0) {
      var messages = string.Join(Environment.NewLine, errorReporter.AllMessages);
      throw new InvalidOperationException($"Parse errors:{Environment.NewLine}{messages}");
    }

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    if (program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error) != 0) {
      var messages = string.Join(Environment.NewLine, errorReporter.AllMessages);
      throw new InvalidOperationException($"Resolution errors:{Environment.NewLine}{messages}");
    }
    return program;
  }

  private static DafnyOptions CreateOptions(uint maxInstances = 10U) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, maxInstances);
    return options;
  }

  private static IEnumerable<Statement> DescendantStatements(Statement root) {
    var stack = new Stack<Statement>();
    stack.Push(root);
    while (stack.Count > 0) {
      var current = stack.Pop();
      yield return current;
      foreach (var child in current.SubStatements) {
        stack.Push(child);
      }
    }
  }

  private static async Task<Bpl.Implementation> TranslateSingleImplementation(string dafnyProgramText, DafnyOptions options, string methodName) {
    const string fullFilePath = "untitled:UnrollBoundedQuantifiersTest";
    var rootUri = new Uri(fullFilePath);

    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    Assert.Equal(0, errorReporter.ErrorCount);

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));

    var bplPrograms = BoogieGenerator.Translate(program, errorReporter).Select(t => t.Item2).ToList();

    // Use Contains (not equality) because Dafny may mangle names (module prefix, overload suffixes, etc.).
    // In particular, Dafny-to-Boogie name mangling may double underscores, e.g. Foo_Bar -> Foo__Bar.
    bool MatchesName(string boogieName) =>
      boogieName.Contains(methodName) || boogieName.Contains(methodName.Replace("_", "__"));

    var candidates = bplPrograms
      .SelectMany(p => p.Implementations)
      .Where(i => MatchesName(i.Name))
      .ToList();

    if (candidates.Count != 1) {
      var allNames = bplPrograms.SelectMany(p => p.Implementations).Select(i => i.Name).OrderBy(n => n).ToList();
      throw new InvalidOperationException(
        $"Expected exactly one Boogie implementation containing '{methodName}', but found {candidates.Count}.{Environment.NewLine}" +
        $"Implementations:{Environment.NewLine}{string.Join(Environment.NewLine, allNames)}");
    }

    return candidates.Single();
  }

  private static IEnumerable<Bpl.Cmd> Commands(Bpl.Implementation impl) {
    return impl.Blocks.SelectMany(b => b.Cmds);
  }

  private static ProofObligationDescription? TryGetProofObligationDescription(Bpl.AssertCmd cmd) {
    const BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
    var type = cmd.GetType();

    // Prefer the canonical property name if present.
    var descriptionProperty = type.GetProperty("Description", flags);
    if (descriptionProperty?.GetIndexParameters().Length == 0) {
      if (descriptionProperty.GetValue(cmd) is ProofObligationDescription pod) {
        return pod;
      }
    }

    foreach (var prop in type.GetProperties(flags)) {
      if (prop.GetIndexParameters().Length != 0) {
        continue;
      }
      object? value;
      try {
        value = prop.GetValue(cmd);
      } catch {
        continue;
      }
      if (value is ProofObligationDescription pod) {
        return pod;
      }
    }

    foreach (var field in type.GetFields(flags)) {
      var value = field.GetValue(cmd);
      if (value is ProofObligationDescription pod) {
        return pod;
      }
    }

    return null;
  }

  private static IEnumerable<Bpl.AssertCmd> AssertStatementAsserts(Bpl.Implementation impl) {
    return Commands(impl)
      .OfType<Bpl.AssertCmd>()
      .Where(a => TryGetProofObligationDescription(a) is AssertStatementDescription);
  }

  private static bool ContainsForall(Bpl.Expr expr) {
    switch (expr) {
      case Bpl.ForallExpr:
        return true;
      case Bpl.ExistsExpr existsExpr:
        return ContainsForall(existsExpr.Body);
      case Bpl.LetExpr letExpr:
        return ContainsForall(letExpr.Body) || GetLetExprRhss(letExpr).Any(ContainsForall);
      case Bpl.OldExpr oldExpr:
        return ContainsForall(oldExpr.Expr);
      case Bpl.NAryExpr nAryExpr:
        return nAryExpr.Args.Any(ContainsForall);
      case Bpl.QuantifierExpr quantifierExpr:
        return ContainsForall(quantifierExpr.Body);
      default:
        return false;
    }
  }

  private static bool ContainsAnyQuantifier(Bpl.Expr expr) {
    switch (expr) {
      case Bpl.ForallExpr:
      case Bpl.ExistsExpr:
        return true;
      case Bpl.LetExpr letExpr:
        return ContainsAnyQuantifier(letExpr.Body) || GetLetExprRhss(letExpr).Any(ContainsAnyQuantifier);
      case Bpl.OldExpr oldExpr:
        return ContainsAnyQuantifier(oldExpr.Expr);
      case Bpl.NAryExpr nAryExpr:
        return nAryExpr.Args.Any(ContainsAnyQuantifier);
      case Bpl.QuantifierExpr quantifierExpr:
        return ContainsAnyQuantifier(quantifierExpr.Body);
      default:
        return false;
    }
  }

  private static IEnumerable<Bpl.Expr> GetLetExprRhss(Bpl.LetExpr letExpr) {
    const BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
    var type = letExpr.GetType();

    IEnumerable<Bpl.Expr> FromValue(object? value) {
      if (value is IEnumerable<Bpl.Expr> typed) {
        return typed;
      }
      if (value is System.Collections.IEnumerable enumerable) {
        return enumerable.OfType<Bpl.Expr>();
      }
      return Array.Empty<Bpl.Expr>();
    }

    // Prefer common / historical member names.
    foreach (var name in new[] { "RHSs", "Rhss", "Rhs", "RHS", "RhsList" }) {
      var prop = type.GetProperty(name, flags);
      if (prop?.GetIndexParameters().Length == 0) {
        try {
          var value = prop.GetValue(letExpr);
          var rhss = FromValue(value);
          if (rhss.Any()) {
            return rhss;
          }
        } catch {
          // Ignore and keep searching.
        }
      }

      var field = type.GetField(name, flags);
      if (field != null) {
        var value = field.GetValue(letExpr);
        var rhss = FromValue(value);
        if (rhss.Any()) {
          return rhss;
        }
      }
    }

    // Fallback: find any property that looks like an RHS collection.
    foreach (var prop in type.GetProperties(flags)) {
      if (prop.GetIndexParameters().Length != 0) {
        continue;
      }
      if (!prop.Name.Contains("rhs", StringComparison.OrdinalIgnoreCase)) {
        continue;
      }
      object? value;
      try {
        value = prop.GetValue(letExpr);
      } catch {
        continue;
      }
      var rhss = FromValue(value);
      if (rhss.Any()) {
        return rhss;
      }
    }

    return Array.Empty<Bpl.Expr>();
  }

  private static bool ContainsBinaryOps(Expression expr, params BinaryExpr.ResolvedOpcode[] opcodes) {
    var opcodeSet = new HashSet<BinaryExpr.ResolvedOpcode>(opcodes);
    return expr.DescendantsAndSelf
      .OfType<BinaryExpr>()
      .Any(binary => opcodeSet.Contains(binary.ResolvedOp));
  }

  private static object CreateUnrollEngine(Program program, uint maxInstances) {
    var rewriterType = typeof(UnrollBoundedQuantifiersRewriter);
    var engineType = rewriterType
      .GetNestedType("UnrollEngine", BindingFlags.Public | BindingFlags.NonPublic)
      ?? rewriterType.Assembly.GetTypes()
        .FirstOrDefault(t =>
          t.FullName == "Microsoft.Dafny.UnrollBoundedQuantifiersRewriter+UnrollEngine" ||
          (t.Name == "UnrollEngine" && t.DeclaringType == rewriterType));
    var resolvedEngineType = engineType
      ?? throw new InvalidOperationException("UnrollEngine type not found via reflection.");
    var ctor = resolvedEngineType.GetConstructor(
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(SystemModuleManager), typeof(uint) },
      modifiers: null);
    if (ctor == null) {
      throw new InvalidOperationException("UnrollEngine constructor not found via reflection.");
    }
    return ctor.Invoke(new object[] { program.SystemModuleManager, maxInstances });
  }

  private static Expression InvokeRewriteExpr(object engine, Expression expr) {
    var method = engine.GetType().GetMethod("RewriteExpr", BindingFlags.Instance | BindingFlags.NonPublic);
    Assert.NotNull(method);
    return (Expression)method!.Invoke(engine, new object[] { expr })!;
  }

  private static void InvokeRewriteStmt(object engine, Statement stmt) {
    var method = engine.GetType().GetMethod("RewriteStmt", BindingFlags.Instance | BindingFlags.NonPublic);
    Assert.NotNull(method);
    method!.Invoke(engine, new object[] { stmt });
  }

  private static void InvokeRewriteCallable(object engine, ICallable decl) {
    var method = engine.GetType().GetMethod("Rewrite", BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic);
    Assert.NotNull(method);
    method!.Invoke(engine, new object[] { decl });
  }

  private static Expression CreateBoogieWrapper(Bpl.Expr expr, Microsoft.Dafny.Type type) {
    var wrapperType = typeof(BoogieGenerator).GetNestedType("BoogieWrapper", BindingFlags.NonPublic);
    Assert.NotNull(wrapperType);
    var wrapper = Activator.CreateInstance(
      wrapperType!,
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      args: new object[] { expr, type },
      culture: null);
    Assert.NotNull(wrapper);
    return (Expression)wrapper!;
  }

  private sealed class TestConcreteSyntaxExpr : ConcreteSyntaxExpression {
    public TestConcreteSyntaxExpr(IOrigin origin, Expression resolvedExpression) : base(origin) {
      ResolvedExpression = resolvedExpression;
    }
  }

  // Objective: unroll a simple bounded forall within the instance cap.
  [Fact]
  public async Task SingleVariableBoundedForall_IsUnrolled_WhenWithinMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    var impl = await TranslateSingleImplementation(@"
method SingleVar() {
  assert forall x :: 0 <= x < 3 ==> x == 0;
}
", options, "SingleVar");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.All(asserts, a => Assert.False(ContainsForall(a.Expr)));
  }

  // Objective: confirm the AST no longer contains forall after unrolling.
  [Fact]
  public async Task BoundedForall_IsUnrolledInAst_WhenWithinMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    var program = await ParseAndResolve(@"
method SingleVar() {
  assert forall x :: 0 <= x < 3 ==> x == 0;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var method = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "SingleVar"));
    Assert.NotNull(method.Body);

    var assertStmt = DescendantStatements(method.Body!)
      .OfType<AssertStmt>()
      .Single();
    var assertExpr = assertStmt.Expr.Resolved ?? assertStmt.Expr;

    Assert.DoesNotContain(assertExpr.DescendantsAndSelf, e => e is ForallExpr);
  }

  // Objective: avoid repeating guaranteed bounds in unrolled implications.
  [Fact]
  public async Task UnrolledForall_DropsGuaranteedBoundsFromImplication() {
    var options = CreateOptions(10);
    var program = await ParseAndResolve(@"
predicate q(i: int) { i % 2 == 0 }

method Test() {
  assert forall i :: 0 <= i < 3 ==> q(i);
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var method = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Test"));
    Assert.NotNull(method.Body);

    var assertStmt = DescendantStatements(method.Body!)
      .OfType<AssertStmt>()
      .Single();
    var assertExpr = assertStmt.Expr.Resolved ?? assertStmt.Expr;

    Assert.False(ContainsBinaryOps(assertExpr,
      BinaryExpr.ResolvedOpcode.Imp,
      BinaryExpr.ResolvedOpcode.Le,
      BinaryExpr.ResolvedOpcode.Lt,
      BinaryExpr.ResolvedOpcode.Ge,
      BinaryExpr.ResolvedOpcode.Gt));

    var calls = assertExpr.DescendantsAndSelf
      .OfType<FunctionCallExpr>()
      .Where(call => call.Function?.Name == "q")
      .ToList();
    Assert.Equal(3, calls.Count);
    Assert.All(calls, call =>
      Assert.True(call.Args.Count == 1 && Expression.IsIntLiteral(call.Args[0], out _)));
  }

  // Objective: unroll bounded foralls with nat upper bounds when in range.
  [Fact]
  public async Task NatUpperBoundOnlyForall_IsUnrolled_WhenWithinMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    var impl = await TranslateSingleImplementation(@"
function IsZero(x: nat): bool { x == 0 }

method NatUpperOnly() {
  assert forall x: nat :: x < 3 ==> IsZero(x);
}
", options, "NatUpperOnly");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.All(asserts, a => Assert.False(ContainsForall(a.Expr)));
  }

  // Objective: unroll multi-variable bounded foralls within the cap.
  [Fact]
  public async Task MultiVariableBoundedForall_IsUnrolled_WhenWithinMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    var impl = await TranslateSingleImplementation(@"
method MultiVar() {
  assert forall x, y :: 0 <= x < 3 && 0 <= y < 2 ==> x + y == 0;
}
", options, "MultiVar");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.All(asserts, a => Assert.False(ContainsForall(a.Expr)));
  }

  // Objective: unroll a simple bounded exists within the instance cap.
  [Fact]
  public async Task SingleVariableBoundedExists_IsUnrolled_WhenWithinMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    var impl = await TranslateSingleImplementation(@"
predicate IsOne(x: int) { x == 1 }

method SingleExists() {
  assert exists x :: 0 <= x < 3 && IsOne(x);
}
", options, "SingleExists");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.All(asserts, a => Assert.False(ContainsAnyQuantifier(a.Expr)));
  }

  // Objective: keep exists when the domain size exceeds the cap.
  [Fact]
  public async Task BoundedExists_IsNotUnrolled_WhenExceedingMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    // Domain size is 4 * 4 = 16, which exceeds the max-instances cap (10).
    var impl = await TranslateSingleImplementation(@"
method ExistsExceedsCap() {
  assert exists x, y :: 0 <= x < 4 && 0 <= y < 4 && x + y == 0;
}
", options, "ExistsExceedsCap");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.Contains(asserts, a => ContainsAnyQuantifier(a.Expr));
  }

  // Objective: keep forall when the domain size exceeds the cap.
  [Fact]
  public async Task BoundedForall_IsNotUnrolled_WhenExceedingMaxInstances() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Induction = 0;
    options.Set(CommonOptionBag.UnrollBoundedQuantifiers, 10U);

    // Domain size is 4 * 4 = 16, which exceeds the max-instances cap (10).
    var impl = await TranslateSingleImplementation(@"
method ExceedsCap() {
  assert forall x, y :: 0 <= x < 4 && 0 <= y < 4 ==> x + y == 0;
}
", options, "ExceedsCap");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.Contains(asserts, a => ContainsForall(a.Expr));
  }

  // Objective: traverse diverse statement kinds without skipping any.
  [Fact]
  public async Task Rewriter_Traverses_DiverseStatements() {
    var options = CreateOptions(0);
    var program = await ParseAndResolve(@"
datatype Result<T> = Failure(msg: string) | Success(value: T)

class C {
  var c: int
  method TryGet(x: int) returns (r: Result<int>, y: int) {
    r := Success(x);
    y := x;
  }

  method VoidCall() {
  }

  method StatementCoverage(a: array<int>)
    modifies a
  {
    var x: int;

    if true {
      assert true;
    } else {
      assert true;
    }

    while true
      invariant true
      decreases 1
    {
      assert true;
      break;
    }

    for i := 0 to 2 {
      assert true;
    }

    forall i | 0 <= i < a.Length {
      assert true;
    }

    assume true;
    assert true;
    expect true;

    modify a {
      assert true;
    }

    print 1;
    VoidCall();
    return;
  }

  method AlternativeLoop() {
    var k := 0;
    var d := 0;
    while
      decreases 10 - k;
    {
      case k < 3 =>
        k := k + 1;
      case k < 6 =>
        if (*) { d := d + 1; }
        k := k + 2;
    }
  }
}
", options);

    var typeDecl = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Where(m => m.Name == "C"));
    var method = Assert.Single(typeDecl.Members.OfType<Method>().Where(m => m.Name == "StatementCoverage"));
    Assert.NotNull(method.Body);
    var statements = DescendantStatements(method.Body!).ToList();
    Assert.Contains(statements, s => s is IfStmt);
    Assert.Contains(statements, s => s is WhileStmt);
    Assert.Contains(statements, s => s is ForLoopStmt);
    Assert.Contains(statements, s => s is ForallStmt);
    Assert.Contains(statements, s => s is AssumeStmt);
    Assert.Contains(statements, s => s is AssertStmt);
    Assert.Contains(statements, s => s is ExpectStmt);
    Assert.Contains(statements, s => s is ModifyStmt);
    Assert.Contains(statements, s => s is PrintStmt);
    Assert.Contains(statements, s => s is VarDeclStmt);

    var altMethod = Assert.Single(typeDecl.Members.OfType<Method>().Where(m => m.Name == "AlternativeLoop"));
    Assert.NotNull(altMethod.Body);
    Assert.Contains(DescendantStatements(altMethod.Body!), s => s is AlternativeLoopStmt);

  }

  // Objective: traverse diverse expression kinds without errors.
  [Fact]
  public async Task Rewriter_Traverses_DiverseExpressions() {
    var options = CreateOptions();
    var program = await ParseAndResolve(@"
datatype D = D(v: int)

class C {
  var f: int

  function F(x: int): int { x + 1 }

  method ExprCoverage(x: int) returns (y: int)
    ensures old(x) == x
    ensures unchanged(this)
  {
    var localSeq := [1, 2, 3];
    var slice := localSeq[0..2];
    var updated := localSeq[0 := 5];
    var set1 := {1, 2};
    var map1 := map[1 := 2];
    var ms1 := multiset{1, 2};
    var dt := D(1);
    var dt2 := D(v := 2);
    var paren := (1 + 2);
    var unary := -1;
    var binary := 1 + 2;
    var ite := if 0 < 1 then 1 else 2;
    var member := this.f;
    var call := F(1);
    var seqSelect := localSeq[0];
    var mapSelect := map1[1];
    var arr := new int[2,2];
    var multiSelect := arr[0,1];

    assert old(x) == x;

    y := call + member + paren + unary + binary + ite + seqSelect + mapSelect + multiSelect;
  }
}
", options);

    var typeDecl = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<ClassDecl>().Where(m => m.Name == "C"));
    var method = Assert.Single(typeDecl.Members.OfType<Method>().Where(m => m.Name == "ExprCoverage"));
    var function = Assert.Single(typeDecl.Members.OfType<Function>().Where(m => m.Name == "F"));

    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    InvokeRewriteCallable(engine, function);
    InvokeRewriteCallable(engine, method);
  }

  // Objective: rewrite internal statements used by expression rewrites.
  [Fact]
  public async Task RewriteExpr_Handles_InternalNodes() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() {}", options);
    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    var origin = Token.NoToken;

    var intLiteral = Expression.CreateIntLiteral(origin, 1);
    var boolLiteral = Expression.CreateBoolLiteral(origin, true);

    var assertStmt = new AssertStmt(origin, boolLiteral, null, null);
    InvokeRewriteStmt(engine, assertStmt);

    var initStatements = new List<Statement> { new AssertStmt(origin, boolLiteral, null, null) };
    var properStatements = new List<Statement> { new AssumeStmt(origin, boolLiteral, null) };
    var dividedBlock = new DividedBlockStmt(origin, initStatements, origin, properStatements, new List<Label>());
    InvokeRewriteStmt(engine, dividedBlock);
  }

  // Objective: exercise unrolling for all bounded pool kinds.
  [Fact]
  public async Task RewriteBounds_CoversAllPoolKinds() {
    var options = CreateOptions();
    var program = await ParseAndResolve(@"
method PoolCoverage(s: set<int>, t: seq<int>, m: map<int, int>, ms: multiset<int>) {
  assert forall x :: x in s ==> x >= 0;
  assert forall x :: x in t ==> x >= 0;
  assert forall x :: x in m ==> x >= 0;
  assert forall x :: x in ms ==> x >= 0;
  assert forall s0: set<int> :: s0 <= s ==> s0 <= s;
  assert forall s0: set<int> :: s <= s0 ==> s <= s0;
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var method = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "PoolCoverage"));
    Assert.NotNull(method.Body);
    Assert.Contains(DescendantStatements(method.Body!), s => s is AssertStmt);

    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    InvokeRewriteCallable(engine, method);
  }

  // Objective: stop unrolling on unsupported or open bounds.
  [Fact]
  public async Task TryUnrollForall_StopsOnUnsupportedBounds() {
    var options = CreateOptions();

    var impl = await TranslateSingleImplementation(@"
method UnsupportedBounds(n: int) {
  assert forall b: bool :: b ==> b;
  assert forall x :: 0 <= x ==> x == 0;
  assert forall x :: 0 <= x < n ==> x == 0;
  assert forall x :: 1 <= x < 0 ==> x == 0;
}
", options, "UnsupportedBounds");

    var asserts = AssertStatementAsserts(impl).ToList();
    Assert.NotEmpty(asserts);
    Assert.Contains(asserts, a => ContainsForall(a.Expr));
  }

  // Objective: rewrite iterator specs and body without breaking structure.
  [Fact]
  public async Task RewriteIterator_RewritesSpecsAndBody() {
    var options = CreateOptions();
    var program = await ParseAndResolve(@"
iterator Iter(n: int) yields (y: int)
  requires n >= 0
  ensures y >= 0
  yield requires y >= 0
  yield ensures y <= n
  decreases n
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    yield i;
    i := i + 1;
  }
}
", options);
    var iterator = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<IteratorDecl>().Where(m => m.Name == "Iter"));

    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    InvokeRewriteCallable(engine, iterator);

    Assert.NotNull(iterator.Body);
  }

  // Objective: cover assignment and return statement variants.
  [Fact]
  public async Task RewriteStmt_Covers_AssignmentVariants() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() {}", options);
    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    var origin = Token.NoToken;

    var intLiteral = Expression.CreateIntLiteral(origin, 1);
    var boolLiteral = Expression.CreateBoolLiteral(origin, true);
    intLiteral.Type = new IntType();
    boolLiteral.Type = new BoolType();
    var lhs = new IdentifierExpr(origin, "x") { Type = new IntType() };

    var singleAssign = new SingleAssignStmt(origin, lhs, new ExprRhs(intLiteral));
    var assignStmt = new AssignStatement(origin, new List<Expression> { lhs }, new List<AssignmentRhs> { new ExprRhs(intLiteral) });
    var assignSuchThat = new AssignSuchThatStmt(origin, new List<Expression> { lhs }, boolLiteral, null, null);
    var assignOrReturn = new AssignOrReturnStmt(origin, new List<Expression> { lhs }, new ExprRhs(intLiteral), null, new List<AssignmentRhs>());
    var returnStmt = new ReturnStmt(origin, new List<AssignmentRhs> { new ExprRhs(intLiteral) });
    var printStmt = new PrintStmt(origin, new List<Expression> { intLiteral });

    foreach (var stmt in new Statement[] { singleAssign, assignStmt, assignSuchThat, assignOrReturn, returnStmt, printStmt }) {
      InvokeRewriteStmt(engine, stmt);
    }
  }

  // Objective: rewrite internal and translation expression nodes safely.
  [Fact]
  public async Task RewriteExpr_Handles_InternalAndTranslationNodes() {
    var options = CreateOptions();
    var program = await ParseAndResolve("method M() {}", options);
    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    var origin = Token.NoToken;

    var intLiteral = Expression.CreateIntLiteral(origin, 1);
    intLiteral.Type = new IntType();
    var boolLiteral = Expression.CreateBoolLiteral(origin, true);
    boolLiteral.Type = new BoolType();

    var boxing = new BoxingCastExpr(intLiteral, new IntType(), new IntType());
    boxing.Type = new IntType();
    var unboxing = new UnboxingCastExpr(intLiteral, new IntType(), new IntType());
    unboxing.Type = new IntType();

    var localsObject = new LocalsObjectExpression(origin);
    localsObject.Type = new IntType();

    var field = new Field(origin, new Name(origin, "f"), false, new IntType(), null);
    var fieldLocation = new FieldLocation(new Name(origin, "f"), field, false);
    fieldLocation.Type = new IntType();

    var parens = new ParensExpression(origin, intLiteral) { ResolvedExpression = intLiteral };
    parens.Type = new IntType();
    var concreteSyntax = new TestConcreteSyntaxExpr(origin, parens);
    concreteSyntax.Type = new IntType();

    var letVar = new BoundVar(origin, "v", new IntType());
    var letExpr = new LetExpr(origin, new List<CasePattern<BoundVar>> { new(origin, letVar) }, new List<Expression> { intLiteral },
      new IdentifierExpr(origin, letVar), true);
    letExpr.Type = new IntType();

    var decreases = new DecreasesToExpr(origin, new[] { intLiteral }, new[] { intLiteral }, allowNoChange: true);
    decreases.Type = new BoolType();

    var stmtExpr = new StmtExpr(origin, new AssertStmt(origin, boolLiteral, null, null), boolLiteral);
    stmtExpr.Type = new BoolType();

    var boogieWrapper = CreateBoogieWrapper(Bpl.Expr.True, new BoolType());
    boogieWrapper.Type = new BoolType();

    var apply = new ApplyExpr(origin, new IdentifierExpr(origin, "f") { Type = new IntType() }, new List<Expression> { intLiteral }, Token.NoToken);
    apply.Type = new IntType();
    var typeTest = new TypeTestExpr(origin, intLiteral, new IntType()) { Type = new BoolType() };
    var conversion = new ConversionExpr(origin, intLiteral, new IntType()) { Type = new IntType() };
    var multiSelect = new MultiSelectExpr(origin, new IdentifierExpr(origin, "arr") { Type = new IntType() },
      new List<Expression> { intLiteral, intLiteral }) { Type = new IntType() };

    foreach (var expr in new Expression[] { boxing, unboxing, localsObject, fieldLocation, concreteSyntax, letExpr, decreases, stmtExpr, boogieWrapper, apply, typeTest, conversion, multiSelect }) {
      var rewritten = InvokeRewriteExpr(engine, expr);
      Assert.NotNull(rewritten);
    }
  }

  // Objective: verify TryUnrollForall early-exit and edge cases.
  [Fact]
  public async Task RewriteExpr_TryUnrollForall_NegativeAndEdgeCases() {
    var options = CreateOptions(2);
    var program = await ParseAndResolve("method M() {}", options);
    var engine = CreateUnrollEngine(program, options.Get(CommonOptionBag.UnrollBoundedQuantifiers));
    var origin = Token.NoToken;

    ForallExpr MakeForall(Microsoft.Dafny.Type varType, BoundedPool bound, Expression term) {
      var bv = new BoundVar(origin, "x", varType);
      var forall = new ForallExpr(origin, new List<BoundVar> { bv }, null, term);
      forall.Bounds = new List<BoundedPool?> { bound };
      forall.Type = new BoolType();
      return forall;
    }

    Expression IntLiteral(int value) {
      var literal = Expression.CreateIntLiteral(origin, value);
      literal.Type = new IntType();
      return literal;
    }

    var intLiteral = IntLiteral(1);
    var boolLiteral = Expression.CreateBoolLiteral(origin, false);
    boolLiteral.Type = new BoolType();

    var splitQuantifier = MakeForall(new IntType(), new IntBoundedPool(intLiteral, intLiteral), boolLiteral);
    splitQuantifier.SplitQuantifier = new List<Expression> { boolLiteral };
    Assert.Same(splitQuantifier, InvokeRewriteExpr(engine, splitQuantifier));

    var boundsMismatch = new ForallExpr(origin, new List<BoundVar> { new(origin, "x", new IntType()) }, null, boolLiteral) {
      Type = new BoolType(),
      Bounds = new List<BoundedPool?>()
    };
    Assert.Same(boundsMismatch, InvokeRewriteExpr(engine, boundsMismatch));

    var nonIntType = MakeForall(new BoolType(), new IntBoundedPool(intLiteral, intLiteral), boolLiteral);
    Assert.Same(nonIntType, InvokeRewriteExpr(engine, nonIntType));

    var noUpper = MakeForall(new IntType(), new IntBoundedPool(intLiteral, null), boolLiteral);
    Assert.Same(noUpper, InvokeRewriteExpr(engine, noUpper));

    var nonLiteralLower = MakeForall(new IntType(), new IntBoundedPool(new IdentifierExpr(origin, "k"), intLiteral), boolLiteral);
    var nonLiteralLowerPool = nonLiteralLower.Bounds![0] as IntBoundedPool;
    Assert.NotNull(nonLiteralLowerPool);
    var nonLiteralLowerId = nonLiteralLowerPool!.LowerBound as IdentifierExpr;
    Assert.NotNull(nonLiteralLowerId);
    nonLiteralLowerId!.Type = new IntType();
    Assert.Same(nonLiteralLower, InvokeRewriteExpr(engine, nonLiteralLower));

    var nonLiteralUpper = MakeForall(new IntType(), new IntBoundedPool(intLiteral, new IdentifierExpr(origin, "k")), boolLiteral);
    var nonLiteralUpperPool = nonLiteralUpper.Bounds![0] as IntBoundedPool;
    Assert.NotNull(nonLiteralUpperPool);
    var nonLiteralUpperId = nonLiteralUpperPool!.UpperBound as IdentifierExpr;
    Assert.NotNull(nonLiteralUpperId);
    nonLiteralUpperId!.Type = new IntType();
    Assert.Same(nonLiteralUpper, InvokeRewriteExpr(engine, nonLiteralUpper));

    var exceeds = MakeForall(new IntType(), new IntBoundedPool(IntLiteral(0), IntLiteral(4)), boolLiteral);
    Assert.Same(exceeds, InvokeRewriteExpr(engine, exceeds));

    var emptyDomain = MakeForall(new IntType(), new IntBoundedPool(IntLiteral(2), IntLiteral(1)), boolLiteral);
    var emptyRewrite = InvokeRewriteExpr(engine, emptyDomain);
    Assert.True(Expression.IsBoolLiteral(emptyRewrite, out var emptyValue) && emptyValue);

    var shortCircuit = MakeForall(new IntType(), new IntBoundedPool(IntLiteral(0), IntLiteral(2)), boolLiteral);
    var shortCircuitRewrite = InvokeRewriteExpr(engine, shortCircuit);
    Assert.True(Expression.IsBoolLiteral(shortCircuitRewrite, out var shortCircuitValue) && !shortCircuitValue);

    var natVar = new BoundVar(origin, "n", program.SystemModuleManager.Nat());
    var natForall = new ForallExpr(origin, new List<BoundVar> { natVar }, null, boolLiteral) {
      Bounds = new List<BoundedPool?> { new IntBoundedPool(null, IntLiteral(1)) },
      Type = new BoolType()
    };
    var natRewrite = InvokeRewriteExpr(engine, natForall);
    Assert.True(Expression.IsBoolLiteral(natRewrite, out var natValue) && !natValue);
  }
}

