using Microsoft.Dafny;

namespace DafnyCore.Test;

[Collection("Proof input translation")]
public class DefinitionReferenceTests {
  private const string Source = """
    module M {
      class C { var f: int  function G(): int { 0 } }
      datatype D = Ctor(x: int) { function Get(): int { x } }
      function Top(): int { 0 }
      function Use(c: C): int reads c { c.f + c.G() + Ctor(1).x + Ctor(2).Get() + Top() + N.Inner() }
      module N { function Inner(): int { 0 } }
    }
    function Outside(): int { M.Top() }
    """;

  // A reference names the module that declares its target, also for members of classes and datatypes.
  [Theory]
  [InlineData("M.Use", "M.C", "M")]
  [InlineData("M.Use", "M.C.f", "M")]
  [InlineData("M.Use", "M.C.G", "M")]
  [InlineData("M.Use", "M.D.Ctor", "M")]
  [InlineData("M.Use", "M.D.Get", "M")]
  [InlineData("M.Use", "M.Top", "M")]
  [InlineData("M.Use", "M.N.Inner", "M.N")]
  [InlineData("Outside", "M.Top", "M")]
  public async Task ReferencesReportTheDeclaringModule(string owner, string target, string module) {
    var program = await ProofInputRepeatabilityTests.Parse(Source);
    var definitions = DefinitionAnalysis.Analyze(program, program.Compilation.RootSourceUris.ToHashSet());
    var references = Assert.Single(definitions, definition => definition.FullName == owner).References
      .Where(reference => reference.TargetFullName == target)
      .ToList();

    Assert.NotEmpty(references);
    Assert.All(references, reference => Assert.Equal(module, reference.TargetModule));
  }
}
