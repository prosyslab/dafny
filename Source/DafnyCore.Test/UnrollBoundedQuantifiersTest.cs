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
}

