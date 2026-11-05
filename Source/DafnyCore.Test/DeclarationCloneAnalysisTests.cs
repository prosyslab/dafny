using System.Text.Json;
using Microsoft.Dafny;

namespace DafnyCore.Test;

[Collection("Proof input translation")]
public class DeclarationCloneAnalysisTests {
  private const string Source = """
    module {:sourceMarker 1} Outer {
      module Nested {
        class C {
          constructor() {}
          method M() {}
          function F(): int { 1 }
        }
        trait T { function Bodyless(): int }
        datatype D = K { function Zero(): int { 0 } }
        codatatype CD = Cell(value: int) { function Value(): int { value } }
        iterator Items() yields (value: int) { yield 0; }
        predicate P() { true }
        least predicate L() { true }
        greatest predicate G() { true }
        twostate function Old(): int { 0 }
        twostate predicate Same() { true }
        function ByMethod(x: int): int { x + 1 } by method { return x + 1; }
      }
    }
    module Prefix.Child { function Value(): int { 2 } }
    """;

  // Every factory declaration/function subtype retains its authored body delimiter, including NoToken.
  [Fact]
  public async Task CanonicalClonePreservesAllAuthoredBodyMarkers() {
    var original = await Parse(Source);
    var cloned = new Cloner(true, false).CloneModuleDefinition(original, null);
    var declarations = Declarations(original);
    var clonedDeclarations = Declarations(cloned);
    Assert.Equal(SerializeMarkers(declarations), SerializeMarkers(clonedDeclarations));
    foreach (var kind in new[] { "ClassDecl", "TraitDecl", "IndDatatypeDecl", "CoDatatypeDecl", "IteratorDecl",
               "Function", "Predicate", "LeastPredicate", "GreatestPredicate", "TwoStateFunction",
               "TwoStatePredicate", "Method", "Constructor" }) {
      Assert.Contains(declarations, declaration => declaration.GetType().Name == kind);
    }
    Assert.All(declarations.Where(declaration => declaration.Name is "C" or "T" or "D" or "CD" or "Items" or
      "P" or "L" or "G" or "Old" or "Same" or "ByMethod"), declaration => Assert.NotSame(Token.NoToken, declaration.BodyStartTok));
    Assert.Same(Token.NoToken, Assert.Single(declarations.Where(declaration => declaration.Name == "Bodyless")).BodyStartTok);
    var byMethod = Assert.Single(clonedDeclarations.OfType<Function>().Where(function => function.Name == "ByMethod"));
    Assert.NotNull(byMethod.ByMethodTok);
    Assert.NotNull(byMethod.ByMethodBody);
  }

  // Nested and prefix modules retain delimiters while owning independent mutable attribute/name nodes.
  [Fact]
  public async Task ModuleClonePreservesSourceShapeWithoutAliasingMetadata() {
    var original = await Parse(Source);
    var cloned = new Cloner(true, false).CloneModuleDefinition(original, null);
    var before = Modules(original);
    var after = Modules(cloned);
    Assert.Equal(before.Select(module => module.Name).ToArray(), after.Select(module => module.Name).ToArray());
    for (var index = 0; index < before.Count; index++) {
      Assert.Equal(Position(before[index].BodyStartTok), Position(after[index].BodyStartTok));
      if (before[index].BodyStartTok != Token.NoToken) {
        Assert.NotSame(before[index].NameNode, after[index].NameNode);
      }
      if (before[index].Attributes != null) {
        Assert.NotSame(before[index].Attributes, after[index].Attributes);
      }
    }
    Assert.Contains(before, module => module.Name == "Outer" && module.BodyStartTok != Token.NoToken);
    Assert.Contains(before, module => module.Name == "Nested" && module.BodyStartTok != Token.NoToken);
    Assert.Contains(before, module => module.Name == "Child" && module.BodyStartTok != Token.NoToken);
  }

  private static List<Declaration> Declarations(ModuleDefinition module) => module.Descendants().OfType<Declaration>()
    .Distinct().OrderBy(declaration => declaration.StartToken.pos).ThenBy(declaration => declaration.GetType().Name).ToList();
  private static List<ModuleDefinition> Modules(ModuleDefinition module) => module.Descendants().Prepend(module)
    .OfType<ModuleDefinition>().Distinct().OrderBy(item => item.StartToken.pos).ThenBy(item => item.Name).ToList();
  private static string SerializeMarkers(IEnumerable<Declaration> declarations) => JsonSerializer.Serialize(declarations.Select(declaration => new {
    Kind = declaration.GetType().Name,
    declaration.Name,
    Body = Position(declaration.BodyStartTok)
  }));
  private static object Position(IOrigin origin) => new { origin.Filepath, origin.line, origin.col, origin.pos, origin.val };
  private static async Task<ModuleDefinition> Parse(string source) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse(source, new Uri("file:///workspace/clone-shape.dfy"), reporter);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return parsed.Program.DefaultModuleDef;
  }
}
