using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyCore.Test;

public class DefinitionVerificationFactsTest {
  private static readonly Uri SourceUri = new("file:///workspace/verification-facts.dfy");

  private static async Task<(Program Program, List<ICanVerify> Targets)> Resolve(string source) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse(source, SourceUri, reporter);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.Equal(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    var targets = SymbolExtensions.GetSymbolDescendants(parsed.Program.DefaultModule)
      .OfType<ICanVerify>()
      .Where(target => target.Origin.Uri == SourceUri && !target.Origin.IsCopy && target.ShouldVerify)
      .ToList();
    return (parsed.Program, targets);
  }

  // Compiler targets retain constructor names and function ownership across source declaration kinds.
  [Fact]
  public async Task ResolvedTargetsPreserveNativeNamesAndOwnership() {
    var (program, targets) = await Resolve("""
      module Example {
        type Small = n: int | 0 <= n witness 0
        newtype Natural = n: int | 0 <= n witness 0
        datatype Box = Box(value: nat := 0)
        const Number: nat := 0
        function Value(): int { 0 } by method { return 0; }
        method Run() {}
        iterator Items() yields (n: int) { yield 0; }
      }
      """);
    var document = DefinitionAnalysis.AnalyzeDocument(program, new HashSet<Uri> { SourceUri },
      verificationTargets: targets);
    var facts = Assert.IsAssignableFrom<IReadOnlyList<DefinitionVerificationTarget>>(
      document.SourceFacts.VerificationTargets);
    Assert.Equal(targets.Select(target => target.FullDafnyName).Order(),
      facts.Select(target => target.FullName).Order());
    Assert.Contains(facts, target => target.FullName == "#Example.Box.Box");
    Assert.Contains(targets, target => target is SubsetTypeDecl);
    Assert.Contains(targets, target => target is NewtypeDecl);
    Assert.Contains(targets, target => target is ConstantField);
    Assert.Contains(targets, target => target is IteratorDecl);
    var function = Assert.Single(targets.OfType<Function>().Where(function => function.Name == "Value"));
    Assert.Single(facts.Where(target => target.FullName == function.FullDafnyName));
    Assert.All(facts, target => Assert.Equal(SourceUri.LocalPath, target.SourcePath));
  }

  // Authored modern and legacy timeout attributes remain visible without synthesized multipliers.
  [Theory]
  [InlineData("@TimeLimit(90) method Run() {}", "timeLimit")]
  [InlineData("@TimeLimitMultiplier(3) method Run() {}", "timeLimitMultiplier")]
  [InlineData("method {:timeLimit 90} Run() {}", "timeLimit")]
  [InlineData("datatype Box = {:timeLimit 90} Box(value: nat := 0)", "timeLimit")]
  public async Task AuthoredTimeoutAttributesAreReported(string source, string expectedName) {
    var (program, targets) = await Resolve(source);
    var document = DefinitionAnalysis.AnalyzeDocument(program, new HashSet<Uri> { SourceUri },
      verificationTargets: targets);
    var fact = Assert.Single(document.SourceFacts.VerificationTargets!);
    var attribute = Assert.Single(fact.Attributes);
    Assert.Equal(expectedName, attribute.Name);
    Assert.Single(attribute.Arguments);
    Assert.True(attribute.Start < attribute.End);
  }

  // Verification inventory and resolved body visibility compose in the same source-facts document.
  [Fact]
  public async Task VerificationTargetsRetainResolvedBodyVisibility() {
    var (program, targets) = await Resolve("""
      opaque function Hidden(): int { 1 }
      lemma {:timeLimit 90} Root() { reveal Hidden; }
      """);
    var document = DefinitionAnalysis.AnalyzeDocument(program, new HashSet<Uri> { SourceUri },
      verificationTargets: targets);

    var root = Assert.Single(document.Definitions.Where(definition => definition.Name == "Root"));
    var hidden = Assert.Single(targets.OfType<Function>().Where(function => function.Name == "Hidden"));
    var visibility = Assert.IsType<DefinitionBodyVisibility>(root.BodyVisibility);
    Assert.Contains(hidden.FullDafnyName, visibility.RevealedFunctions);
    Assert.False(visibility.RevealsAllFunctions);
    Assert.True(Assert.Single(document.Definitions.Where(definition => definition.Name == "Hidden"))
      .BodyVisibility!.IsOpaque);
    var target = Assert.Single(document.SourceFacts.VerificationTargets!
      .Where(candidate => candidate.FullName == root.FullName));
    Assert.Equal("timeLimit", Assert.Single(target.Attributes).Name);
  }

  // Existing consumers receive the original source-facts schema unless inventory metadata is requested.
  [Fact]
  public async Task LegacyDocumentOmitsVerificationTargets() {
    var (program, _) = await Resolve("method Run() {}");
    var document = DefinitionAnalysis.AnalyzeDocument(program, new HashSet<Uri> { SourceUri });
    using var json = JsonDocument.Parse(JsonSerializer.Serialize(document, new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase
    }));
    Assert.False(json.RootElement.GetProperty("sourceFacts").TryGetProperty("verificationTargets", out _));
  }

  // Target inventory is restricted to the explicitly analyzed source set.
  [Fact]
  public async Task OtherSourceTargetsAreExcluded() {
    var (program, targets) = await Resolve("method Run() {}");
    var document = DefinitionAnalysis.AnalyzeDocument(program, new HashSet<Uri>(), verificationTargets: targets);
    Assert.Empty(document.SourceFacts.VerificationTargets!);
  }
}
