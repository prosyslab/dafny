using System.Collections.Immutable;
using System.Threading;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;

namespace DafnyCore.Test;

public class DefinitionBodyVisibilityTests {
  private static readonly Uri RootUri = new("file:///workspace/body-visibility/root.dfy");
  private static readonly Uri IncludeUri = new("file:///workspace/body-visibility/library.dfy");

  // Effective opacity follows each native language spelling.
  [Theory]
  [InlineData("function F(): int { 1 }", false)]
  [InlineData("opaque function F(): int { 1 }", true)]
  [InlineData("function {:opaque} F(): int { 1 }", true)]
  public async Task ReportsEffectiveOpacity(string source, bool expected) {
    var program = await Parse(source);
    Assert.Equal(expected, Visibility(program, "F").IsOpaque);
  }

  // Default opacity options apply even when no source modifier is present.
  [Fact]
  public async Task ReportsImplicitOpacity() {
    var program = await Parse("function F(): int { 1 }", CommonOptionBag.DefaultFunctionOpacityOptions.Opaque);
    Assert.True(Visibility(program, "F").IsOpaque);
  }

  // Span-only parsing never claims resolved body visibility.
  [Fact]
  public async Task SpanAnalysisOmitsVisibility() {
    var options = Options(CommonOptionBag.DefaultFunctionOpacityOptions.Transparent);
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse("opaque function F(): int { 1 }", RootUri, reporter);
    Assert.Equal(0, reporter.ErrorCount);
    Assert.All(DefinitionAnalysis.AnalyzeSpans(parsed.Program, new HashSet<Uri> { RootUri }),
      definition => Assert.Null(definition.BodyVisibility));
  }

  // Explicit reveals report unique canonical identities in ordinal order.
  [Fact]
  public async Task ExplicitRevealsAreCanonicalSortedAndUnique() {
    var program = await Parse("opaque function Z(): int { 1 } opaque function A(): int { 2 } " +
      "lemma M() { reveal Z; reveal A; reveal Z; }");
    var visibility = Visibility(program, "M");
    Assert.Equal(new[] { Function(program, "A").FullDafnyName, Function(program, "Z").FullDafnyName },
      visibility.RevealedFunctions);
    Assert.False(visibility.RevealsAllFunctions);
  }

  // Reveals in a transitively called lemma's body affect the root.
  [Fact]
  public async Task FollowsTransitiveMethodBodies() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma Helper() { reveal Hidden; } " +
      "lemma Middle() { Helper(); } lemma Root() { Middle(); }");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // A function reference in a contract carries reveals from the referenced function body.
  [Fact]
  public async Task FollowsContractDependencies() {
    var program = await Parse("opaque function Hidden(): int { 1 } " +
      "ghost predicate Wrapper() { reveal Hidden; true } lemma Root() requires Wrapper() {}");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // Included declarations retain their bodies and contracts in the dependency closure.
  [Fact]
  public async Task FollowsIncludedBodiesAndContracts() {
    var program = await Parse("include \"library.dfy\" lemma Root() { Helper(); }", includedSource:
      "opaque function Hidden(): int { 1 } ghost predicate Wrapper() { reveal Hidden; true } " +
      "lemma Helper() requires Wrapper() {}");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // Frozen wrappers retain ordinary transparent-function dependencies for consumer invalidation.
  [Fact]
  public async Task IncludedWrapperReportsReferencedDeclarations() {
    var program = await Parse("include \"library.dfy\" lemma Root() requires Wrapper() == 1 {}", includedSource:
      "function Leaf(): int { 1 } function Wrapper(): int { Leaf() }");
    var visibility = Visibility(program, "Root");
    Assert.Contains(Function(program, "Leaf").FullDafnyName, visibility.ReferencedDeclarations);
    Assert.Contains(Function(program, "Wrapper").FullDafnyName, visibility.ReferencedDeclarations);
    Assert.Equal(visibility.ReferencedDeclarations.Distinct().OrderBy(name => name, StringComparer.Ordinal),
      visibility.ReferencedDeclarations);
    Assert.Empty(visibility.RevealedFunctions);
    Assert.False(visibility.RevealsAllFunctions);
  }

  // Resolved generic component types retain subset constraints and their function dependencies.
  [Fact]
  public async Task GenericSubsetTypeRetainsConstraintDependencies() {
    var program = await Parse("function Leaf(): int { 1 } type S = x:int | Leaf() == 1 witness 0 " +
      "function Id<T>(x:T): T { x } lemma Root() ensures Id<S>(0) == 0 {}");
    var visibility = Visibility(program, "Root");
    Assert.Contains(Function(program, "Leaf").FullDafnyName, visibility.ReferencedDeclarations);
    Assert.Contains(program.DefaultModuleDef.TopLevelDecls.OfType<SubsetTypeDecl>()
      .Single(declaration => declaration.Name == "S").FullDafnyName, visibility.ReferencedDeclarations);
    Assert.False(visibility.RevealsAllFunctions);
  }

  // Reveals inside instantiated subset constraints remain visible to generic call consumers.
  [Fact]
  public async Task GenericSubsetTypeRetainsConstraintReveals() {
    var program = await Parse("opaque function Leaf(): int { 1 } " +
      "type S = x:int | (reveal Leaf; Leaf() == 1) witness 0 " +
      "function Id<T>(x:T): T { x } lemma Root() ensures Id<S>(0) == 0 {}");
    Assert.Contains(Function(program, "Leaf").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // An unrelated sibling member's wildcard reveal does not poison the root.
  [Fact]
  public async Task ContainerReferencesDoNotTraverseSiblingMembers() {
    var program = await Parse("class C { static function F(): int { 1 } lemma Unrelated() { reveal *; } } " +
      "lemma Root() requires C.F() == 1 {}");
    Assert.False(Visibility(program, "Root").RevealsAllFunctions);
  }

  // Wildcard reveals in dependencies force conservative all-function exposure.
  [Fact]
  public async Task TransitiveWildcardRevealsAllFunctions() {
    var program = await Parse("lemma Helper() { reveal *; } lemma Root() { Helper(); }");
    Assert.True(Visibility(program, "Root").RevealsAllFunctions);
  }

  // Hiding a function alone does not count as exposing its body.
  [Fact]
  public async Task HideDoesNotReveal() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma Root() { hide Hidden; }");
    var visibility = Visibility(program, "Root");
    Assert.Empty(visibility.RevealedFunctions);
    Assert.False(visibility.RevealsAllFunctions);
  }

  // Auto-generated reveal calls expose resolved function identities without OffsetMembers.
  [Fact]
  public async Task AutoRevealUsesResolvedTargetAttributes() {
    var program = await Parse("function Hidden(): int { 1 } lemma Root() ensures Hidden() == 1 {}",
      CommonOptionBag.DefaultFunctionOpacityOptions.AutoRevealDependencies);
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single(candidate => candidate.Name == "Root");
    Assert.Contains(method.Body!.DescendantsAndSelf.OfType<HideRevealStmt>(),
      reveal => reveal.OffsetMembers.Count == 0 && reveal.ResolvedStatements.OfType<CallStmt>().Any());
    var visibility = Visibility(program, "Root");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, visibility.RevealedFunctions);
    Assert.False(visibility.RevealsAllFunctions);
  }

  // Function-targeted fuel exposes a body through native typed attribute arguments.
  [Fact]
  public async Task FuelCountsAsFunctionExposure() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma {:fuel Hidden, 1, 2} Root() {}");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // Fuel on statements participates in the same resolved closure.
  [Fact]
  public async Task StatementFuelCountsAsFunctionExposure() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma Root() { assert {:fuel Hidden, 1, 2} true; }");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // Function postcondition attributes remain visible even where native Children flattens their wrappers.
  [Fact]
  public async Task FunctionContractFuelCountsAsFunctionExposure() {
    var program = await Parse("opaque function Hidden(): int { 1 } " +
      "function Wrapper(): int ensures {:fuel Hidden, 1, 2} true { 1 } " +
      "lemma Root() requires Wrapper() == 1 {}");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "Root").RevealedFunctions);
  }

  // Malformed resolved auto-reveal target attributes preserve conservative exposure.
  [Fact]
  public async Task MalformedGeneratedRevealTargetRevealsAllFunctions() {
    var program = await Parse("function Hidden(): int { 1 } lemma Root() ensures Hidden() == 1 {}",
      CommonOptionBag.DefaultFunctionOpacityOptions.AutoRevealDependencies);
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single(candidate => candidate.Name == "Root");
    var call = method.Body!.DescendantsAndSelf.OfType<CallStmt>()
      .First(candidate => Attributes.Contains(candidate.Method.Attributes, "revealedFunction"));
    var attribute = Attributes.Find(call.Method.Attributes, "revealedFunction")!;
    attribute.Args.Clear();
    Assert.True(Visibility(program, "Root").RevealsAllFunctions);
  }

  // Malformed resolved reveal metadata fails closed instead of dropping exposure.
  [Fact]
  public async Task UnknownRevealTargetRevealsAllFunctions() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma Root() { reveal Hidden; }");
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single(candidate => candidate.Name == "Root");
    var reveal = Assert.Single(method.Body!.DescendantsAndSelf.OfType<HideRevealStmt>());
    reveal.OffsetMembers.Clear();
    reveal.ResolvedStatements.Clear();
    Assert.True(Visibility(program, "Root").RevealsAllFunctions);
  }

  // Cyclic call dependencies terminate while retaining nested reveal exposure.
  [Fact]
  public async Task CyclicDependenciesTerminate() {
    var program = await Parse("opaque function Hidden(): int { 1 } lemma A() { B(); } " +
      "lemma B() { reveal Hidden; A(); }");
    Assert.Contains(Function(program, "Hidden").FullDafnyName, Visibility(program, "A").RevealedFunctions);
  }

  private static DefinitionBodyVisibility Visibility(Program program, string name) {
    return Assert.IsType<DefinitionBodyVisibility>(DefinitionAnalysis.Analyze(program, new HashSet<Uri> { RootUri })
      .Single(definition => definition.Name == name).BodyVisibility);
  }

  private static Function Function(Program program, string name) {
    return program.Modules().SelectMany(module => ModuleDefinition.AllCallablesIncludingPrefixDeclarations(module.TopLevelDecls))
      .OfType<Function>().Single(function => function.Name == name);
  }

  private static DafnyOptions Options(CommonOptionBag.DefaultFunctionOpacityOptions opacity) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.DefaultFunctionOpacity, opacity);
    return options;
  }

  private static async Task<Program> Parse(string source,
    CommonOptionBag.DefaultFunctionOpacityOptions opacity = CommonOptionBag.DefaultFunctionOpacityOptions.Transparent,
    string? includedSource = null) {
    var options = Options(opacity);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var sources = ImmutableDictionary<Uri, string>.Empty.Add(RootUri, source);
    if (includedSource != null) {
      sources = sources.Add(IncludeUri, includedSource);
    }
    var fileSystem = new InMemoryFileSystem(sources);
    var parser = new ProgramParser(NullLogger<ProgramParser>.Instance, fileSystem);
    var root = DafnyFile.HandleDafnyFile(fileSystem, reporter, options, RootUri, Token.NoToken, false);
    var parsed = await parser.ParseFiles(RootUri.ToString(), new[] { root }, reporter, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return parsed.Program;
  }
}
