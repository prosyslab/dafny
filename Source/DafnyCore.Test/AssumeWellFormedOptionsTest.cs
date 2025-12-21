using System.Threading;
using System.Threading.Tasks;
using Microsoft.BaseTypes;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace DafnyCore.Test;

public class AssumeWellFormedOptionsTest {
  private static async Task<Bpl.Implementation> TranslateSingleImplementation(string dafnyProgramText, DafnyOptions options, string methodName) {
    const string fullFilePath = "untitled:AssumeWellFormedOptionsTest";
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

  private static bool TryGetBinary(Bpl.Expr expr, Bpl.BinaryOperator.Opcode opcode, out Bpl.Expr left, out Bpl.Expr right) {
    if (expr is Bpl.NAryExpr { Fun: Bpl.BinaryOperator op, Args: { Count: 2 } args } && op.Op == opcode) {
      left = args[0];
      right = args[1];
      return true;
    }

    left = null!;
    right = null!;
    return false;
  }

  private static bool IsNumericZeroLiteral(Bpl.Expr expr) {
    if (expr is not Bpl.LiteralExpr lit) {
      return false;
    }

    return lit.Val switch {
      BigNum n => n.IsZero,
      BigDec d => d.IsZero,
      _ => false
    };
  }

  private static bool IsDivisorNonZeroCondition(Bpl.Expr expr) {
    if (!TryGetBinary(expr, Bpl.BinaryOperator.Opcode.Neq, out var left, out var right)) {
      return false;
    }

    // Matches E != 0 (for int/real/bv, etc.).
    return IsNumericZeroLiteral(left) || IsNumericZeroLiteral(right);
  }

  private static bool IsIndexRangeCondition(Bpl.Expr expr) {
    // Matches (0 <= i) && (i < length).
    if (!TryGetBinary(expr, Bpl.BinaryOperator.Opcode.And, out var a, out var b)) {
      return false;
    }

    bool Match(Bpl.Expr lower, Bpl.Expr upper) {
      if (!TryGetBinary(lower, Bpl.BinaryOperator.Opcode.Le, out var loLeft, out var loRight)) {
        return false;
      }
      if (!TryGetBinary(upper, Bpl.BinaryOperator.Opcode.Lt, out var upLeft, out var upRight)) {
        return false;
      }

      return IsNumericZeroLiteral(loLeft) && ReferenceEquals(loRight, upLeft) && !IsNumericZeroLiteral(upRight);
    }

    return Match(a, b) || Match(b, a);
  }

  [Fact]
  public async Task AssumeWellFormedDiv_Off_EmitsAssertForDivisorNonZero() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var impl = await TranslateSingleImplementation(@"
method AssumeWellFormedDiv_Int(y: int) returns (r: int) {
  r := 1 / y;
}
", options, "AssumeWellFormedDiv_Int");

    var cmds = Commands(impl).ToList();
    Assert.Equal(1, cmds.OfType<Bpl.AssertCmd>().Count(c => IsDivisorNonZeroCondition(c.Expr)));
    Assert.Equal(0, cmds.OfType<Bpl.AssumeCmd>().Count(c => IsDivisorNonZeroCondition(c.Expr)));
  }

  [Fact]
  public async Task AssumeWellFormedDiv_On_EmitsAssumeForDivisorNonZero() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AssumeWellFormedDiv, true);

    var impl = await TranslateSingleImplementation(@"
method AssumeWellFormedDiv_Int_Assume(y: int) returns (r: int) {
  r := 1 / y;
}
", options, "AssumeWellFormedDiv_Int_Assume");

    var cmds = Commands(impl).ToList();
    Assert.Equal(0, cmds.OfType<Bpl.AssertCmd>().Count(c => IsDivisorNonZeroCondition(c.Expr)));
    Assert.Equal(1, cmds.OfType<Bpl.AssumeCmd>().Count(c => IsDivisorNonZeroCondition(c.Expr)));
  }

  [Fact]
  public async Task AssumeWellFormedIndex_Off_EmitsAssertForArrayIndexRange() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    var impl = await TranslateSingleImplementation(@"
method AssumeWellFormedIndex_Array1(a: array<int>, i: int) returns (r: int) {
  r := a[i];
}
", options, "AssumeWellFormedIndex_Array1");

    var cmds = Commands(impl).ToList();
    Assert.Equal(1, cmds.OfType<Bpl.AssertCmd>().Count(c => IsIndexRangeCondition(c.Expr)));
    Assert.Equal(0, cmds.OfType<Bpl.AssumeCmd>().Count(c => IsIndexRangeCondition(c.Expr)));
  }

  [Fact]
  public async Task AssumeWellFormedIndex_On_EmitsAssumeForMultiDimArrayIndexRanges() {
    var options = DafnyOptions.Default;
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.AssumeWellFormedIndex, true);

    var impl = await TranslateSingleImplementation(@"
method AssumeWellFormedIndex_Array2(a: array2<int>, i: int, j: int) returns (r: int) {
  r := a[i, j];
}
", options, "AssumeWellFormedIndex_Array2");

    var cmds = Commands(impl).ToList();
    Assert.Equal(0, cmds.OfType<Bpl.AssertCmd>().Count(c => IsIndexRangeCondition(c.Expr)));
    Assert.Equal(2, cmds.OfType<Bpl.AssumeCmd>().Count(c => IsIndexRangeCondition(c.Expr)));
  }
}
