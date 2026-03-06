using System.Reflection;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class HelperFunctionInterpreterTest {
  private const string HelperFunctionDefinitions = @"
function {:fuel 100} Abs(x: int): int
  decreases *
{
  if x >= 0 then x else -x
}

function {:fuel 100} Min(a: int, b: int): int
  decreases *
{
  if a <= b then a else b
}

function {:fuel 100} Max(a: int, b: int): int
  decreases *
{
  if a >= b then a else b
}

function {:fuel 100} Sum(s: seq<int>): int
  decreases *
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

function {:fuel 100} Product(s: seq<int>): int
  decreases *
{
  if |s| == 0 then 1 else s[0] * Product(s[1..])
}

function {:fuel 100} Power(base: int, exp: int): int
  decreases *
{
  if exp <= 0 then 1 else base * Power(base, exp - 1)
}

function {:fuel 100} Factorial(n: int): int
  decreases *
{
  if n <= 0 then 1 else n * Factorial(n - 1)
}

function {:fuel 100} GCD(a: int, b: int): int
  decreases *
{
  if b == 0 then Abs(a) else GCD(b, a % b)
}

function {:fuel 100} LCM(a: int, b: int): int
  decreases *
{
  if a == 0 || b == 0 then 0 else Abs(a * b) / GCD(a, b)
}

predicate {:fuel 100} IsPrime(n: int)
  decreases *
{
  n >= 2 && forall d :: 2 <= d < n ==> n % d != 0
}

function {:fuel 100} DivisorCount(n: int): int
  decreases *
{
  if n <= 0 then 0 else |set d: int | 1 <= d <= n && n % d == 0 :: d|
}

predicate {:fuel 100} IsSorted(s: seq<int>)
  decreases *
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate {:fuel 100} IsSortedDesc(s: seq<int>)
  decreases *
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

predicate {:fuel 100} IsPermutation<T(==)>(a: seq<T>, b: seq<T>)
  decreases *
{
  multiset(a) == multiset(b)
}

function {:fuel 100} Count<T(==)>(s: seq<T>, x: T): int
  decreases *
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

function {:fuel 100} Range(lo: int, hi: int): seq<int>
  decreases *
{
  if lo >= hi then [] else [lo] + Range(lo + 1, hi)
}

predicate {:fuel 100} IsSubsequence<T(==)>(sub: seq<T>, main: seq<T>)
  decreases *
{
  if |sub| == 0 then true
  else if |main| == 0 then false
  else if sub[0] == main[0] then IsSubsequence(sub[1..], main[1..])
  else IsSubsequence(sub, main[1..])
}

function {:fuel 100} PrefixSum(s: seq<int>): seq<int>
  decreases *
{
  if |s| == 0 then [0]
  else PrefixSum(s[..|s|-1]) + [Sum(s)]
}

function {:fuel 100} Map<T, U>(s: seq<T>, f: T -> U): seq<U>
  decreases *
{
  if |s| == 0 then []
  else [f(s[0])] + Map(s[1..], f)
}

function {:fuel 100} MapIFrom<T, U>(from: int, s: seq<T>, f: (int, T) -> U): seq<U>
  decreases *
{
  if |s| == 0 then []
  else [f(from, s[0])] + MapIFrom(from + 1, s[1..], f)
}

function {:fuel 100} MapI<T, U>(s: seq<T>, f: (int, T) -> U): seq<U>
  decreases *
{
  MapIFrom(0, s, f)
}

function {:fuel 100} Fold<T, U>(s: seq<T>, unit: U, f: (U, T) -> U): U
  decreases *
{
  if |s| == 0 then unit
  else Fold(s[1..], f(unit, s[0]), f)
}

function {:fuel 100} FoldIFrom<T, U>(from: int, s: seq<T>, unit: U, f: (int, U, T) -> U): U
  decreases *
{
  if |s| == 0 then unit
  else FoldIFrom(from + 1, s[1..], f(from, unit, s[0]), f)
}

function {:fuel 100} FoldI<T, U>(s: seq<T>, unit: U, f: (int, U, T) -> U): U
  decreases *
{
  FoldIFrom(0, s, unit, f)
}

function {:fuel 100} Fold_i<T, U>(from: int, s: seq<T>, unit: U, f: (int, U, T) -> U): U
  decreases *
{
  FoldIFrom(from, s, unit, f)
}

function {:fuel 100} Filter<T>(s: seq<T>, p: T -> bool): seq<T>
  decreases *
{
  if |s| == 0 then []
  else (if p(s[0]) then [s[0]] else []) + Filter(s[1..], p)
}

function {:fuel 100} FilterIFrom<T>(from: int, s: seq<T>, p: (int, T) -> bool): seq<T>
  decreases *
{
  if |s| == 0 then []
  else (if p(from, s[0]) then [s[0]] else []) + FilterIFrom(from + 1, s[1..], p)
}

function {:fuel 100} FilterI<T>(s: seq<T>, p: (int, T) -> bool): seq<T>
  decreases *
{
  FilterIFrom(0, s, p)
}

function {:fuel 100} Filter_i<T>(from: int, s: seq<T>, p: (int, T) -> bool): seq<T>
  decreases *
{
  FilterIFrom(from, s, p)
}

predicate {:fuel 100} IsDigit(c: char)
  decreases *
{
  '0' <= c <= '9'
}

predicate {:fuel 100} IsLower(c: char)
  decreases *
{
  'a' <= c <= 'z'
}

predicate {:fuel 100} IsUpper(c: char)
  decreases *
{
  'A' <= c <= 'Z'
}

function {:fuel 100} ToLower(c: char): char
  decreases *
{
  if IsUpper(c) then ((c as int) - ('A' as int) + ('a' as int)) as char else c
}

function {:fuel 100} ToUpper(c: char): char
  decreases *
{
  if IsLower(c) then ((c as int) - ('a' as int) + ('A' as int)) as char else c
}

function {:fuel 100} CharToNat(c: char): int
  decreases *
{
  (c as int) - ('0' as int)
}

function {:fuel 100} NatToChar(n: int): char
  decreases *
{
  if 0 <= n <= 9 then (n + ('0' as int)) as char else '0'
}

function {:fuel 100} IntToString(n: int): string
  decreases *
{
  if n < 0 then ""-"" + NatToString(-n)
  else NatToString(n)
}

function {:fuel 100} NatToString(n: int): string
  decreases *
{
  if n < 10 then [NatToChar(n)]
  else NatToString(n / 10) + [NatToChar(n % 10)]
}

function {:fuel 100} StringToNat(s: string): int
  decreases *
{
  if |s| == 0 then 0
  else StringToNat(s[..|s|-1]) * 10 + CharToNat(s[|s|-1])
}

function {:fuel 100} StringToInt(s: string): int
  decreases *
{
  if |s| > 0 && s[0] == '-' then -StringToNat(s[1..])
  else StringToNat(s)
}
";

  private static async Task<Program> ParseAndResolve(string dafnyProgramText, DafnyOptions options) {
    const string fullFilePath = "untitled:helper-function-interpreter-test";
    var rootUri = new Uri(fullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    Assert.Equal(0, errorReporter.ErrorCount);

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    return program;
  }

  private static DafnyOptions CreateOptions() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AllowDecreasesStarOnFunctionsAndLemmas, true);
    options.Set(CommonOptionBag.PartialEvalInlineDepth, 20U);
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

  private static async Task<(bool Interpreted, Expression? InterpretedExpression)> TryInterpret(
    string methodSignature,
    string methodBody,
    string functionName,
    string extraDeclarations = "") {
    var options = CreateOptions();
    var programText = $@"
{HelperFunctionDefinitions}
{extraDeclarations}
{methodSignature} {{
  {methodBody}
}}
";

    var program = await ParseAndResolve(programText, options);
    var engineType = typeof(Program).Assembly.GetType("Microsoft.Dafny.PartialEvaluatorEngine");
    Assert.NotNull(engineType);

    var engineCtor = engineType!.GetConstructor(
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(DafnyOptions), typeof(ModuleDefinition), typeof(SystemModuleManager), typeof(uint) },
      modifiers: null);
    Assert.NotNull(engineCtor);
    var engine = engineCtor!.Invoke(new object[] { options, program.DefaultModuleDef, program.SystemModuleManager, 20U });

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    Assert.NotNull(entry.Body);

    var callExpr = DescendantStatements(entry.Body!)
      .OfType<AssertStmt>()
      .Select(stmt => stmt.Expr.Resolved ?? stmt.Expr)
      .SelectMany(expr => expr.DescendantsAndSelf.OfType<FunctionCallExpr>())
      .First(call => call.Function?.Name == functionName);

    var stateType = engineType.GetNestedType("PartialEvalState", BindingFlags.NonPublic);
    Assert.NotNull(stateType);

    var stateCtor = stateType!.GetConstructor(
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(int), typeof(HashSet<Function>), typeof(HashSet<string>) },
      modifiers: null);
    Assert.NotNull(stateCtor);

    var state = stateCtor!.Invoke(new object[] {
      20,
      new HashSet<Function>(),
      new HashSet<string>(StringComparer.Ordinal)
    });

    var interpreterField = engineType.GetField("helperInterpreter", BindingFlags.Instance | BindingFlags.NonPublic);
    var interpreter = interpreterField?.GetValue(engine);
    if (interpreter == null) {
      var interpreterProperty = engineType.GetProperty("HelperInterpreter", BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public);
      interpreter = interpreterProperty?.GetValue(engine);
    }
    Assert.NotNull(interpreter);

    var tryInterpretMethod = interpreter!.GetType()
      .GetMethods(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
      .SingleOrDefault(method => {
        if (method.Name != "TryInterpret") {
          return false;
        }

        var parameters = method.GetParameters();
        return parameters.Length == 4
               && parameters[0].ParameterType == typeof(FunctionCallExpr)
               && parameters[2].ParameterType == stateType
               && parameters[3].IsOut
               && parameters[3].ParameterType == typeof(Expression).MakeByRefType();
      });
    Assert.NotNull(tryInterpretMethod);

    var simplifyDelegateType = tryInterpretMethod!.GetParameters()[1].ParameterType;
    var simplifyInvoke = simplifyDelegateType.GetMethod("Invoke");
    Assert.NotNull(simplifyInvoke);
    var simplifyParameters = simplifyInvoke!.GetParameters();
    Assert.Equal(2, simplifyParameters.Length);

    var simplifyExprParameter = System.Linq.Expressions.Expression.Parameter(simplifyParameters[0].ParameterType, "expr");
    var simplifyStateParameter = System.Linq.Expressions.Expression.Parameter(simplifyParameters[1].ParameterType, "state");
    var simplifyExpressionMethod = engineType.GetMethod(
      "SimplifyExpression",
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(Expression) },
      modifiers: null);
    Assert.NotNull(simplifyExpressionMethod);
    var simplifyCall = System.Linq.Expressions.Expression.Call(
      System.Linq.Expressions.Expression.Constant(engine),
      simplifyExpressionMethod!,
      simplifyExprParameter);
    var simplifyDelegate = System.Linq.Expressions.Expression
      .Lambda(simplifyDelegateType, simplifyCall, simplifyExprParameter, simplifyStateParameter)
      .Compile();

    object[] args = { callExpr, simplifyDelegate, state, null! };
    var interpreted = (bool)tryInterpretMethod!.Invoke(interpreter, args)!;
    return (interpreted, args[3] as Expression);
  }

  private static async Task AssertInterpretsToInt(string methodSignature, string methodBody, string functionName, int expected) {
    var (interpreted, interpretedExpression) = await TryInterpret(methodSignature, methodBody, functionName);
    Assert.True(interpreted);
    Assert.NotNull(interpretedExpression);
    Assert.True(Expression.IsIntLiteral(interpretedExpression!, out var value));
    Assert.Equal(expected, (int)value);
  }

  private static async Task AssertInterpretsToBool(string methodSignature, string methodBody, string functionName, bool expected) {
    var (interpreted, interpretedExpression) = await TryInterpret(methodSignature, methodBody, functionName);
    Assert.True(interpreted);
    Assert.NotNull(interpretedExpression);
    Assert.True(Expression.IsBoolLiteral(interpretedExpression!, out var value));
    Assert.Equal(expected, value);
  }

  private static async Task AssertInterpretsToChar(string methodSignature, string methodBody, string functionName, char expected) {
    var (interpreted, interpretedExpression) = await TryInterpret(methodSignature, methodBody, functionName);
    Assert.True(interpreted);
    var charLiteral = Assert.IsType<CharLiteralExpr>(interpretedExpression);
    Assert.Equal(expected.ToString(), charLiteral.Value as string);
  }

  private static async Task AssertInterpretsToString(string methodSignature, string methodBody, string functionName, string expected) {
    var (interpreted, interpretedExpression) = await TryInterpret(methodSignature, methodBody, functionName);
    Assert.True(interpreted);
    var stringLiteral = Assert.IsType<StringLiteralExpr>(interpretedExpression);
    Assert.Equal(expected, stringLiteral.Value as string);
  }

  private static async Task AssertInterpretsToIntSeq(string methodSignature, string methodBody, string functionName, params int[] expected) {
    var (interpreted, interpretedExpression) = await TryInterpret(methodSignature, methodBody, functionName);
    Assert.True(interpreted);
    var sequence = Assert.IsType<SeqDisplayExpr>(interpretedExpression);
    Assert.Equal(expected.Length, sequence.Elements.Count);
    for (var i = 0; i < expected.Length; i++) {
      Assert.True(Expression.IsIntLiteral(sequence.Elements[i], out var value));
      Assert.Equal(expected[i], (int)value);
    }
  }

  private static async Task AssertExpressionSimplifiesToTrue(string methodSignature, string methodBody, string extraDeclarations = "") {
    var options = CreateOptions();
    var programText = $@"
{HelperFunctionDefinitions}
{extraDeclarations}
{methodSignature} {{
  {methodBody}
}}
";

    var program = await ParseAndResolve(programText, options);
    var engineType = typeof(Program).Assembly.GetType("Microsoft.Dafny.PartialEvaluatorEngine");
    Assert.NotNull(engineType);

    var engineCtor = engineType!.GetConstructor(
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(DafnyOptions), typeof(ModuleDefinition), typeof(SystemModuleManager), typeof(uint) },
      modifiers: null);
    Assert.NotNull(engineCtor);
    var engine = engineCtor!.Invoke(new object[] { options, program.DefaultModuleDef, program.SystemModuleManager, 20U });

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var entry = Assert.Single(defaultClass.Members.OfType<Method>().Where(m => m.Name == "Entry"));
    var assertStmt = Assert.Single(DescendantStatements(entry.Body!).OfType<AssertStmt>());
    var assertExpr = assertStmt.Expr.Resolved ?? assertStmt.Expr;

    var simplifyExpressionMethod = engineType.GetMethod(
      "SimplifyExpression",
      BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
      binder: null,
      new[] { typeof(Expression) },
      modifiers: null);
    Assert.NotNull(simplifyExpressionMethod);

    var simplifiedExpr = (Expression)simplifyExpressionMethod!.Invoke(engine, new object[] { assertExpr })!;
    Assert.True(Expression.IsBoolLiteral(simplifiedExpr, out var value));
    Assert.True(value);
  }

  [Fact]
  public async Task TestAbsPositive() {
    await AssertInterpretsToInt("method Entry()", "assert Abs(5) == 5;", "Abs", 5);
  }

  [Fact]
  public async Task TestAbsNegative() {
    await AssertInterpretsToInt("method Entry()", "assert Abs(-3) == 3;", "Abs", 3);
  }

  [Fact]
  public async Task TestAbsZero() {
    await AssertInterpretsToInt("method Entry()", "assert Abs(0) == 0;", "Abs", 0);
  }

  [Fact]
  public async Task TestMinBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Min(3, 7) == 3;", "Min", 3);
  }

  [Fact]
  public async Task TestMinNegativeNumbers() {
    await AssertInterpretsToInt("method Entry()", "assert Min(-100, -200) == -200;", "Min", -200);
  }

  [Fact]
  public async Task TestMaxBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Max(3, 7) == 7;", "Max", 7);
  }

  [Fact]
  public async Task TestSumEmpty() {
    await AssertInterpretsToInt("method Entry()", "assert Sum([]) == 0;", "Sum", 0);
  }

  [Fact]
  public async Task TestSumBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Sum([1, 2, 3, 4, 5]) == 15;", "Sum", 15);
  }

  [Fact]
  public async Task TestSumSingleElement() {
    await AssertInterpretsToInt("method Entry()", "assert Sum([42]) == 42;", "Sum", 42);
  }

  [Fact]
  public async Task TestSumNegativeNumbers() {
    await AssertInterpretsToInt("method Entry()", "assert Sum([-1, -2, -3]) == -6;", "Sum", -6);
  }

  [Fact]
  public async Task TestSumLargeInputThousandElements() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert Sum(Range(1, 1001)) == 500500;");
  }

  [Fact]
  public async Task TestIntegrationSumRange() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert Sum(Range(1, 6)) == 15;");
  }

  [Fact]
  public async Task TestProductEmpty() {
    await AssertInterpretsToInt("method Entry()", "assert Product([]) == 1;", "Product", 1);
  }

  [Fact]
  public async Task TestProductBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Product([2, 3, 4]) == 24;", "Product", 24);
  }

  [Fact]
  public async Task TestPowerBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Power(2, 10) == 1024;", "Power", 1024);
  }

  [Fact]
  public async Task TestPowerZeroExp() {
    await AssertInterpretsToInt("method Entry()", "assert Power(5, 0) == 1;", "Power", 1);
  }

  [Fact]
  public async Task TestPowerNegativeExp() {
    await AssertInterpretsToInt("method Entry()", "assert Power(5, -1) == 1;", "Power", 1);
  }

  [Fact]
  public async Task TestFactorialBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Factorial(10) == 3628800;", "Factorial", 3628800);
  }

  [Fact]
  public async Task TestFactorialZero() {
    await AssertInterpretsToInt("method Entry()", "assert Factorial(0) == 1;", "Factorial", 1);
  }

  [Fact]
  public async Task TestFactorialNegative() {
    await AssertInterpretsToInt("method Entry()", "assert Factorial(-5) == 1;", "Factorial", 1);
  }

  [Fact]
  public async Task TestGCDBasic() {
    await AssertInterpretsToInt("method Entry()", "assert GCD(48, 18) == 6;", "GCD", 6);
  }

  [Fact]
  public async Task TestGCDWithZero() {
    await AssertInterpretsToInt("method Entry()", "assert GCD(0, 5) == 5;", "GCD", 5);
  }

  [Fact]
  public async Task TestGCDBothZero() {
    await AssertInterpretsToInt("method Entry()", "assert GCD(0, 0) == 0;", "GCD", 0);
  }

  [Fact]
  public async Task TestGCDNegative() {
    await AssertInterpretsToInt("method Entry()", "assert GCD(-12, 8) == 4;", "GCD", 4);
  }

  [Fact]
  public async Task TestLCMBasic() {
    await AssertInterpretsToInt("method Entry()", "assert LCM(4, 6) == 12;", "LCM", 12);
  }

  [Fact]
  public async Task TestLCMWithZero() {
    await AssertInterpretsToInt("method Entry()", "assert LCM(0, 5) == 0;", "LCM", 0);
  }

  [Fact]
  public async Task TestIsPrimeTwoTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsPrime(2);", "IsPrime", true);
  }

  [Fact]
  public async Task TestIsPrimeOneFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPrime(1);", "IsPrime", false);
  }

  [Fact]
  public async Task TestIsPrimeZeroFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPrime(0);", "IsPrime", false);
  }

  [Fact]
  public async Task TestIsPrimeNegativeFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPrime(-5);", "IsPrime", false);
  }

  [Fact]
  public async Task TestIsPrimeNinetySevenTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsPrime(97);", "IsPrime", true);
  }

  [Fact]
  public async Task TestIsPrimeHundredFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPrime(100);", "IsPrime", false);
  }

  [Fact]
  public async Task TestIsPrimeBoundary10001False() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPrime(10001);", "IsPrime", false);
  }

  [Fact]
  public async Task TestIsPrimeInterpreterPathSucceeds() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry()",
      "assert IsPrime(97);",
      "IsPrime");

    Assert.True(interpreted);
    Assert.NotNull(interpretedExpression);
    Assert.True(Expression.IsBoolLiteral(interpretedExpression!, out var value));
    Assert.True(value);
  }

  [Fact]
  public async Task TestDivisorCountTwelve() {
    await AssertInterpretsToInt("method Entry()", "assert DivisorCount(12) == 6;", "DivisorCount", 6);
  }

  [Fact]
  public async Task TestDivisorCountOne() {
    await AssertInterpretsToInt("method Entry()", "assert DivisorCount(1) == 1;", "DivisorCount", 1);
  }

  [Fact]
  public async Task TestDivisorCountZero() {
    await AssertInterpretsToInt("method Entry()", "assert DivisorCount(0) == 0;", "DivisorCount", 0);
  }

  [Fact]
  public async Task TestDivisorCountNegative() {
    await AssertInterpretsToInt("method Entry()", "assert DivisorCount(-5) == 0;", "DivisorCount", 0);
  }

  [Fact]
  public async Task TestDivisorCountBoundary10000() {
    await AssertInterpretsToInt("method Entry()", "assert DivisorCount(10000) == 25;", "DivisorCount", 25);
  }

  [Fact]
  public async Task TestRangeBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Range(2, 5) == [2, 3, 4];", "Range", 2, 3, 4);
  }

  [Fact]
  public async Task TestRangeEmptyWhenLoGeHi() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Range(3, 3) == [];", "Range");
  }

  [Fact]
  public async Task TestRangeLargeInputFiveThousand() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert |Range(0, 5000)| == 5000;");
  }

  [Fact]
  public async Task TestPrefixSumEmpty() {
    await AssertInterpretsToIntSeq("method Entry()", "assert PrefixSum([]) == [0];", "PrefixSum", 0);
  }

  [Fact]
  public async Task TestPrefixSumBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert PrefixSum([3, 1, 4]) == [0, 3, 4, 8];", "PrefixSum", 0, 3, 4, 8);
  }

  [Fact]
  public async Task TestMapBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Map([1, 2, 3], x => x + 10) == [11, 12, 13];", "Map", 11, 12, 13);
  }

  [Fact]
  public async Task TestMapEmpty() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Map([], x => x + 1) == [];", "Map");
  }

  [Fact]
  public async Task TestMapSingleElement() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Map([1], x => x + 1) == [2];", "Map", 2);
  }

  [Fact]
  public async Task TestIntegrationMapRangePower() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert Map(Range(1, 4), x => Power(x, 2)) == [1, 4, 9];");
  }

  [Fact]
  public async Task TestMapIFromBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert MapIFrom(5, [2, 4, 6], (i, x) => i + x) == [7, 10, 13];", "MapIFrom", 7, 10, 13);
  }

  [Fact]
  public async Task TestMapIBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert MapI([2, 4, 6], (i, x) => i * x) == [0, 4, 12];", "MapI", 0, 4, 12);
  }

  [Fact]
  public async Task TestFoldBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Fold([1, 2, 3], 10, (acc, x) => acc + x) == 16;", "Fold", 16);
  }

  [Fact]
  public async Task TestFoldEmpty() {
    await AssertInterpretsToInt("method Entry()", "assert Fold([], 7, (acc, x) => acc + x) == 7;", "Fold", 7);
  }

  [Fact]
  public async Task TestFoldSingleElement() {
    await AssertInterpretsToInt("method Entry()", "assert Fold([1], 0, (acc, x) => acc + x) == 1;", "Fold", 1);
  }

  [Fact]
  public async Task TestIntegrationFoldMapRange() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert Fold(Map(Range(1, 4), x => x * x), 0, (a, b) => a + b) == 14;");
  }

  [Fact]
  public async Task TestFoldIFromBasic() {
    await AssertInterpretsToInt("method Entry()", "assert FoldIFrom(2, [5, 6], 1, (i, acc, x) => acc + i + x) == 17;", "FoldIFrom", 17);
  }

  [Fact]
  public async Task TestFoldIBasic() {
    await AssertInterpretsToInt("method Entry()", "assert FoldI([2, 3], 1, (i, acc, x) => acc + i * x) == 4;", "FoldI", 4);
  }

  [Fact]
  public async Task TestFold_iBasic() {
    await AssertInterpretsToInt("method Entry()", "assert Fold_i(3, [2, 3], 1, (i, acc, x) => acc + i + x) == 13;", "Fold_i", 13);
  }

  [Fact]
  public async Task TestFilterBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Filter([1, 2, 3, 4], x => x % 2 == 0) == [2, 4];", "Filter", 2, 4);
  }

  [Fact]
  public async Task TestFilterEmpty() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Filter([], x => x > 0) == [];", "Filter");
  }

  [Fact]
  public async Task TestFilterSingleElement() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Filter([1], x => true) == [1];", "Filter", 1);
  }

  [Fact]
  public async Task TestFilterIFromBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert FilterIFrom(2, [10, 11, 12, 13], (i, x) => i % 2 == 0 && x % 2 == 0) == [10, 12];", "FilterIFrom", 10, 12);
  }

  [Fact]
  public async Task TestFilterIBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert FilterI([10, 11, 12, 13], (i, x) => i % 2 == 1) == [11, 13];", "FilterI", 11, 13);
  }

  [Fact]
  public async Task TestFilter_iBasic() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Filter_i(1, [10, 11, 12, 13], (i, x) => i % 2 == 0) == [11, 13];", "Filter_i", 11, 13);
  }

  [Fact]
  public async Task TestFilterReentrantIsPrime() {
    await AssertInterpretsToIntSeq("method Entry()", "assert Filter([1, 2, 3, 4, 5, 6], x => IsPrime(x)) == [2, 3, 5];", "Filter", 2, 3, 5);
  }

  [Fact]
  public async Task TestMapDeclinesNonLiteralLambdaResult() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry(y: int)",
      "assert Map([1, 2], x => x + y) == [1, 2];",
      "Map");

    Assert.False(interpreted);
    Assert.Null(interpretedExpression);
  }

  [Fact]
  public async Task TestFoldDeclinesNonLiteralAccumulatorResult() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry(s: seq<int>)",
      "assert Fold([1, 2], s, (acc, x) => acc + [x]) == s;",
      "Fold");

    Assert.False(interpreted);
    Assert.Null(interpretedExpression);
  }

  [Fact]
  public async Task TestIsSortedTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsSorted([1, 2, 2, 9]);", "IsSorted", true);
  }

  [Fact]
  public async Task TestIsSortedFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsSorted([1, 3, 2]);", "IsSorted", false);
  }

  [Fact]
  public async Task TestIsSortedDescTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsSortedDesc([9, 2, 2, 1]);", "IsSortedDesc", true);
  }

  [Fact]
  public async Task TestIsSortedDescFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsSortedDesc([2, 1, 3]);", "IsSortedDesc", false);
  }

  [Fact]
  public async Task TestIsSortedAllEqualTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsSorted([4, 4, 4, 4]);", "IsSorted", true);
  }

  [Fact]
  public async Task TestIntegrationIsSortedRange() {
    await AssertExpressionSimplifiesToTrue("method Entry()", "assert IsSorted(Range(1, 10));");
  }

  [Fact]
  public async Task TestIsSortedDescAllEqualTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsSortedDesc([4, 4, 4, 4]);", "IsSortedDesc", true);
  }

  [Fact]
  public async Task TestCountInt() {
    await AssertInterpretsToInt("method Entry()", "assert Count([1, 2, 1, 3, 1], 1) == 3;", "Count", 3);
  }

  [Fact]
  public async Task TestCountChar() {
    await AssertInterpretsToInt("method Entry()", "assert Count(['a', 'b', 'a'], 'a') == 2;", "Count", 2);
  }

  [Fact]
  public async Task TestCountEmpty() {
    await AssertInterpretsToInt("method Entry()", "assert Count([], 7) == 0;", "Count", 0);
  }

  [Fact]
  public async Task TestIsSubsequenceTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsSubsequence([2, 4], [1, 2, 3, 4]);", "IsSubsequence", true);
  }

  [Fact]
  public async Task TestIsSubsequenceFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsSubsequence([2, 5], [1, 2, 3, 4]);", "IsSubsequence", false);
  }

  [Fact]
  public async Task TestIsPermutationTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsPermutation([1, 2, 2, 3], [2, 1, 3, 2]);", "IsPermutation", true);
  }

  [Fact]
  public async Task TestIsPermutationFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsPermutation([1, 2, 2], [1, 1, 2]);", "IsPermutation", false);
  }

  [Fact]
  public async Task TestIsPermutationEmptySequences() {
    await AssertInterpretsToBool("method Entry()", "assert IsPermutation<int>([], []);", "IsPermutation", true);
  }

  [Fact]
  public async Task TestRangeSizeLimitDeclines() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry()",
      "assert |Range(0, 10001)| == 10001;",
      "Range");

    Assert.False(interpreted);
    Assert.Null(interpretedExpression);
  }

  [Fact]
  public async Task TestIsDigitTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsDigit('5');", "IsDigit", true);
  }

  [Fact]
  public async Task TestIsDigitFalse() {
    await AssertInterpretsToBool("method Entry()", "assert !IsDigit('a');", "IsDigit", false);
  }

  [Fact]
  public async Task TestIsLowerTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsLower('a');", "IsLower", true);
  }

  [Fact]
  public async Task TestIsUpperTrue() {
    await AssertInterpretsToBool("method Entry()", "assert IsUpper('A');", "IsUpper", true);
  }

  [Fact]
  public async Task TestToLowerUpper() {
    await AssertInterpretsToChar("method Entry()", "assert ToLower('A') == 'a';", "ToLower", 'a');
  }

  [Fact]
  public async Task TestToUpperLower() {
    await AssertInterpretsToChar("method Entry()", "assert ToUpper('a') == 'A';", "ToUpper", 'A');
  }

  [Fact]
  public async Task TestCharToNat() {
    await AssertInterpretsToInt("method Entry()", "assert CharToNat('5') == 5;", "CharToNat", 5);
  }

  [Fact]
  public async Task TestNatToChar() {
    await AssertInterpretsToChar("method Entry()", "assert NatToChar(5) == '5';", "NatToChar", '5');
  }

  [Fact]
  public async Task TestNatToCharOutOfRange() {
    await AssertInterpretsToChar("method Entry()", "assert NatToChar(15) == '0';", "NatToChar", '0');
  }

  [Fact]
  public async Task TestIntToString() {
    await AssertInterpretsToString("method Entry()", "assert IntToString(42) == \"42\";", "IntToString", "42");
  }

  [Fact]
  public async Task TestIntToStringNegative() {
    await AssertInterpretsToString("method Entry()", "assert IntToString(-5) == \"-5\";", "IntToString", "-5");
  }

  [Fact]
  public async Task TestStringToNat() {
    await AssertInterpretsToInt("method Entry()", "assert StringToNat(\"123\") == 123;", "StringToNat", 123);
  }

  [Fact]
  public async Task TestStringToNatEmpty() {
    await AssertInterpretsToInt("method Entry()", "assert StringToNat(\"\") == 0;", "StringToNat", 0);
  }

  [Fact]
  public async Task TestStringToInt() {
    await AssertInterpretsToInt("method Entry()", "assert StringToInt(\"-42\") == -42;", "StringToInt", -42);
  }

  [Fact]
  public async Task TestDeclinesNonLiteralArgs() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry(s: seq<int>)",
      "assert Sum(s) == 0;",
      "Sum");

    Assert.False(interpreted);
    Assert.Null(interpretedExpression);
  }

  [Fact]
  public async Task TestDeclinesUnknownFunction() {
    var (interpreted, interpretedExpression) = await TryInterpret(
      "method Entry()",
      "assert UnknownFunction([1, 2]) == 0;",
      "UnknownFunction",
      "function UnknownFunction(s: seq<int>): int { 0 }");

    Assert.False(interpreted);
    Assert.Null(interpretedExpression);
  }
}
