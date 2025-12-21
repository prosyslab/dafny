using System.Numerics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class AutoFuelRewriterTest {
  private static async Task<(Program Program, BatchErrorReporter Reporter)> ParseAndResolveWithReporter(string dafnyProgramText, DafnyOptions options) {
    const string fullFilePath = "untitled:autofuel";
    var rootUri = new Uri(fullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var errorReporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, errorReporter);
    Assert.Equal(0, errorReporter.ErrorCount);

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    Assert.Equal(0, program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    return (program, errorReporter);
  }

  private static async Task<Program> ParseAndResolve(string dafnyProgramText, DafnyOptions options) {
    var (program, _) = await ParseAndResolveWithReporter(dafnyProgramText, options);
    return program;
  }

  private static async Task<(bool Verified, Microsoft.Boogie.PipelineStatistics Stats)> ParseResolveAndVerify(string dafnyProgramText, DafnyOptions options) {
    var (program, reporter) = await ParseAndResolveWithReporter(dafnyProgramText, options);

    // We only care about verification outcomes; avoid code generation.
    options.Compile = false;

    // Make sure solver options (notably Z3 path) are set before verification.
    options.RunningBoogieFromCommandLine = true;
    var oldErrorCount = reporter.ErrorCount;
    options.ProcessSolverOptions(reporter, Token.NoToken);
    Assert.Equal(oldErrorCount, reporter.ErrorCount);

    using var engine = Microsoft.Boogie.ExecutionEngine.CreateWithoutSharedCache(options);
    var boogiePrograms = BoogieGenerator.Translate(program, reporter).ToList();

    var verified = true;
    var totalStats = new Microsoft.Boogie.PipelineStatistics();
    foreach (var (moduleName, boogieProgram) in boogiePrograms) {
      var (outcome, stats) = await DafnyMain.BoogieOnce(reporter, options, TextWriter.Null, engine, "autofuel",
        moduleName, boogieProgram, programId: null);
      verified &= DafnyMain.IsBoogieVerified(outcome, stats);

      totalStats.VerifiedCount += stats.VerifiedCount;
      totalStats.ErrorCount += stats.ErrorCount;
      totalStats.TimeoutCount += stats.TimeoutCount;
      totalStats.OutOfResourceCount += stats.OutOfResourceCount;
      totalStats.OutOfMemoryCount += stats.OutOfMemoryCount;
      totalStats.SolverExceptionCount += stats.SolverExceptionCount;
      totalStats.InconclusiveCount += stats.InconclusiveCount;
    }

    return (verified, totalStats);
  }

  [Fact]
  public async Task SelfRecursiveFunctionGetsFuelAndOutOfFuelSiblings() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    // Default-class function (implicitly static) with a direct self call.
    var program = await ParseAndResolve(@"
function {:autofuel 5} F(n: int): int {
  if n == 0 then 0 else F(n - 1)
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());

    var original = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F"));
    var fuelized = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F__fuel"));
    var outOfFuel = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F__out_of_fuel"));

    // Out-of-fuel sibling is bodyless and extern.
    Assert.Null(outOfFuel.Body);
    Assert.True(Attributes.Contains(outOfFuel.Attributes, Attributes.ExternAttributeName));

    // Fuelized has an extra fuel parameter and decreases fuel.
    Assert.True(fuelized.Ins.Count == original.Ins.Count + 1);
    var fuelFormalName = fuelized.Ins[^1].Name;
    Assert.StartsWith("__fuel", fuelFormalName);
    Assert.True(fuelized.Decreases.Expressions is { Count: 1 });
    var dec0 = fuelized.Decreases.Expressions![0];
    Assert.Equal(fuelFormalName, (dec0.Resolved as IdentifierExpr)?.Name ?? (dec0 as IdentifierExpr)?.Name);

    // Wrapper body calls the fuelized sibling with the default fuel value (5).
    var wrapperCall = Assert.IsType<FunctionCallExpr>(original.Body!.Resolved);
    Assert.Equal("F__fuel", wrapperCall.Function.Name);
    Assert.Equal(2, wrapperCall.Args.Count);
    Assert.Equal(5, (int)(BigInteger)Assert.IsType<LiteralExpr>(wrapperCall.Args[1]).Value!);

    // Fuel guard: if fuel < 0 then F__out_of_fuel(n) else ...
    var ite = Assert.IsType<ITEExpr>(fuelized.Body!);
    var thnCall = Assert.IsType<FunctionCallExpr>(ite.Thn.Resolved);
    Assert.Equal("F__out_of_fuel", thnCall.Function.Name);
    Assert.Single(thnCall.Args);

    // Recursive calls inside else branch target F__fuel(..., fuelFormalName - 1).
    var recursiveCall = ite.Els.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .FirstOrDefault(fc => fc.Function.Name == "F__fuel" && fc.Args.Count == 2);
    Assert.NotNull(recursiveCall);
  }

  [Fact]
  public async Task NonRecursiveFunctionIsLeftUntouched() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var program = await ParseAndResolve(@"
function {:autofuel 5} G(n: int): int {
  n + 1
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());

    var g = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "G"));
    Assert.DoesNotContain(defaultClass.Members, m => m.Name is "G__fuel" or "G__out_of_fuel");

    // No wrapper call was introduced.
    Assert.IsNotType<FunctionCallExpr>(g.Body!.Resolved);
  }

  [Fact]
  public async Task SelfRecursiveCallWithNamedArgumentsIsRewritten() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var program = await ParseAndResolve(@"
function {:autofuel 5} F(n: int): int {
  if n == 0 then 0 else F(n := n - 1)
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    var original = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F"));
    var fuelized = Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F__fuel"));
    Assert.Single(defaultClass.Members.OfType<Function>().Where(f => f.Name == "F__out_of_fuel"));

    // Wrapper body calls the fuelized sibling with the default fuel value (5).
    var wrapperCall = Assert.IsType<FunctionCallExpr>(original.Body!.Resolved);
    Assert.Equal("F__fuel", wrapperCall.Function.Name);
    Assert.Equal(2, wrapperCall.Args.Count);
    Assert.Equal(5, (int)(BigInteger)Assert.IsType<LiteralExpr>(wrapperCall.Args[1]).Value!);

    // Recursive calls inside else branch target F__fuel(..., __fuel - 1).
    var ite = Assert.IsType<ITEExpr>(fuelized.Body!);
    var recursiveCall = ite.Els.DescendantsAndSelf.OfType<FunctionCallExpr>()
      .FirstOrDefault(fc => fc.Function.Name == "F__fuel" && fc.Args.Count == 2);
    Assert.NotNull(recursiveCall);
  }

  [Fact]
  public async Task GcdTerminationFailsWithoutAutoFuelButSucceedsWithAutoFuel() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var (verifiedWithoutAutoFuel, statsWithoutAutoFuel) = await ParseResolveAndVerify(@"
datatype Pair = Pair(a: nat, b: nat)

function Gcd(p: Pair): nat {
  match p
  case Pair(a, b) => if b == 0 then a else Gcd(Pair(b, a % b))
}
", new DafnyOptions(options));

    Assert.False(verifiedWithoutAutoFuel);
    Assert.True(statsWithoutAutoFuel.ErrorCount > 0);

    var (verifiedWithAutoFuel, statsWithAutoFuel) = await ParseResolveAndVerify(@"
datatype Pair = Pair(a: nat, b: nat)

function {:autofuel 10} Gcd(p: Pair): nat {
  match p
  case Pair(a, b) => if b == 0 then a else Gcd(Pair(b, a % b))
}
", new DafnyOptions(options));

    Assert.True(verifiedWithAutoFuel);
    Assert.Equal(0, statsWithAutoFuel.ErrorCount);
  }

  [Fact]
  public async Task MutualRecursiveFunctionsAreSkippedWithWarningsUntilImplemented() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var (program, reporter) = await ParseAndResolveWithReporter(@"
function {:autofuel 5} Even(n: int): bool {
  if n == 0 then true else Odd(n - 1)
}

function {:autofuel 5} Odd(n: int): bool {
  if n == 0 then false else Even(n - 1)
}
", options);

    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    Assert.DoesNotContain(defaultClass.Members, m => m.Name is "Even__fuel" or "Even__out_of_fuel" or "Odd__fuel" or "Odd__out_of_fuel");

    var warnings = reporter.AllMessagesByLevel[ErrorLevel.Warning]
      .Where(d => d.Source == MessageSource.Rewriter && d.ErrorId == "rw_autofuel")
      .Select(d => d.Message)
      .Where(m => m.Contains("mutual recursion is not supported"))
      .ToList();

    Assert.Contains(warnings, w => w.Contains("Skipping function 'Even'"));
    Assert.Contains(warnings, w => w.Contains("Skipping function 'Odd'"));
  }
}

