using System.Text.Json;
using Microsoft.Dafny;

namespace DafnyCore.Test;

[Collection("Proof input translation")]
public class DefinitionAnalysisSessionTests {
  private const string Source = """
    module A { lemma P() { assert true; } }
    module B { lemma Q() { assert true; } }
    """;

  // Repeated analysis reuses module extraction while preserving every emitted fact.
  [Fact]
  public async Task RepeatedResolvedProgramReusesExtraction() {
    var program = await ProofInputRepeatabilityTests.Parse(Source);
    var uris = program.Compilation.RootSourceUris.ToHashSet();
    var cache = new DefinitionAnalysis.SessionCache();
    var first = DefinitionAnalysis.AnalyzeDocument(program, uris, includeStatements: true, sessionCache: cache);
    var second = DefinitionAnalysis.AnalyzeDocument(program, uris, includeStatements: true, sessionCache: cache);

    Assert.Equal(JsonSerializer.Serialize(first), JsonSerializer.Serialize(second));
    Assert.True(cache.ModuleHits >= 2);
    Assert.Equal(0, cache.ModuleMisses);
  }

  // Alternating reported scopes keep both profiles; neither leaks nodes into the other.
  [Fact]
  public async Task AlternatingReportedScopesReuseEachProfile() {
    var program = await ProofInputRepeatabilityTests.Parse(Source);
    var roots = program.Compilation.RootSourceUris.ToHashSet();
    var empty = new HashSet<Uri>();
    var cache = new DefinitionAnalysis.SessionCache();
    var expectedRoots = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, roots, includeStatements: true));
    var expectedEmpty = JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, empty, includeStatements: true));

    Assert.Equal(expectedRoots, JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, roots, includeStatements: true, sessionCache: cache)));
    Assert.Equal(expectedEmpty, JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, empty, includeStatements: true, sessionCache: cache)));
    Assert.Equal(0, cache.ModuleHits);
    Assert.Equal(expectedRoots, JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, roots, includeStatements: true, sessionCache: cache)));
    Assert.Equal(0, cache.ModuleMisses);
    Assert.True(cache.ModuleHits >= 2);
    Assert.Equal(expectedEmpty, JsonSerializer.Serialize(DefinitionAnalysis.AnalyzeDocument(program, empty, includeStatements: true, sessionCache: cache)));
    Assert.Equal(0, cache.ModuleMisses);
    Assert.Equal(2, cache.ProfileCount);
  }

  // A module replaced while one profile is active is not reused by another profile.
  [Fact]
  public async Task ReplacedModuleIsPrunedFromInactiveProfiles() {
    var before = await ProofInputRepeatabilityTests.Parse(Source);
    var after = await ProofInputRepeatabilityTests.Parse(Source.Replace("lemma Q() { assert true; }", "lemma Q() { assert 1 == 1; }"));
    var oldA = before.DefaultModuleDef.TopLevelDecls.OfType<LiteralModuleDecl>().Single(module => module.Name == "A");
    var newA = after.DefaultModuleDef.TopLevelDecls.OfType<LiteralModuleDecl>().Single(module => module.Name == "A");
    var replaced = newA.ModuleDef;
    newA.ModuleDef = oldA.ModuleDef;
    after.ModuleSigs.Remove(replaced);
    after.ModuleSigs.Add(oldA.ModuleDef, before.ModuleSigs[oldA.ModuleDef]);
    var beforeRoots = before.Compilation.RootSourceUris.ToHashSet();
    var afterRoots = after.Compilation.RootSourceUris.ToHashSet();
    var empty = new HashSet<Uri>();
    var cache = new DefinitionAnalysis.SessionCache();
    DefinitionAnalysis.AnalyzeDocument(before, beforeRoots, sessionCache: cache);
    DefinitionAnalysis.AnalyzeDocument(before, empty, sessionCache: cache);

    // The edit is observed under the root profile; the empty profile then only reuses A.
    DefinitionAnalysis.AnalyzeDocument(after, afterRoots, sessionCache: cache);
    var modules = cache.ModuleHits + cache.ModuleMisses;
    Assert.Equal(modules + 1, cache.CachedModuleCount);
    var actual = DefinitionAnalysis.AnalyzeDocument(after, empty, sessionCache: cache);
    var expected = DefinitionAnalysis.AnalyzeDocument(after, empty);

    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(actual));
    Assert.Equal(1, cache.ModuleHits);
    Assert.True(cache.ModuleMisses >= 1);
  }

  // The resolver's reused independent module identity retains facts after another module changes.
  [Fact]
  public async Task ReusedIndependentModuleKeepsItsExtraction() {
    var before = await ProofInputRepeatabilityTests.Parse(Source);
    var after = await ProofInputRepeatabilityTests.Parse(Source.Replace("lemma Q() { assert true; }", "lemma Q() { assert false; }"));
    var oldA = before.DefaultModuleDef.TopLevelDecls.OfType<LiteralModuleDecl>().Single(module => module.Name == "A");
    var newA = after.DefaultModuleDef.TopLevelDecls.OfType<LiteralModuleDecl>().Single(module => module.Name == "A");
    var replaced = newA.ModuleDef;
    newA.ModuleDef = oldA.ModuleDef;
    after.ModuleSigs.Remove(replaced);
    after.ModuleSigs.Add(oldA.ModuleDef, before.ModuleSigs[oldA.ModuleDef]);
    var cache = new DefinitionAnalysis.SessionCache();
    DefinitionAnalysis.AnalyzeDocument(before, before.Compilation.RootSourceUris.ToHashSet(), sessionCache: cache);

    var actual = DefinitionAnalysis.AnalyzeDocument(after, after.Compilation.RootSourceUris.ToHashSet(), sessionCache: cache);
    var expected = DefinitionAnalysis.AnalyzeDocument(after, after.Compilation.RootSourceUris.ToHashSet());

    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(actual));
    Assert.True(cache.ModuleHits >= 1);
    Assert.True(cache.ModuleMisses >= 1);
  }

  // New source positions are extracted from the replacement native module.
  [Fact]
  public async Task PositionChangesReplaceCachedFacts() {
    var before = await ProofInputRepeatabilityTests.Parse(Source);
    var after = await ProofInputRepeatabilityTests.Parse("\n" + Source);
    var cache = new DefinitionAnalysis.SessionCache();
    var original = DefinitionAnalysis.AnalyzeDocument(before, before.Compilation.RootSourceUris.ToHashSet(), sessionCache: cache);
    var changed = DefinitionAnalysis.AnalyzeDocument(after, after.Compilation.RootSourceUris.ToHashSet(), sessionCache: cache);

    Assert.Equal(original.Definitions[0].Line + 1, changed.Definitions[0].Line);
    Assert.Equal(0, cache.ModuleHits);
    Assert.True(cache.ModuleMisses >= 2);
  }

  // Report destinations do not change native proof inputs or verification cache context.
  [Fact]
  public void ReportPathsDoNotChangeSemanticOptions() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.VerificationLogFormat, new List<string> { "trx;LogFileName=/first/report.trx" });
    var first = DefinitionAnalysis.ContextOptionsIdentity(options);
    options.Set(CommonOptionBag.VerificationLogFormat, new List<string> { "trx;LogFileName=/second/report.trx" });

    Assert.Equal(first, DefinitionAnalysis.ContextOptionsIdentity(options));
  }

  // Effective legacy resource settings partition resolution even without modern option entries.
  [Fact]
  public void EffectiveTimeLimitChangesResolutionContext() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var first = DefinitionAnalysis.ResolutionOptionsIdentity(options);
    options.TimeLimit += 1;

    Assert.NotEqual(first, DefinitionAnalysis.ResolutionOptionsIdentity(options));
  }

  // Only the bound fixed seed is admitted through the legacy Boogie argument escape hatch.
  [Fact]
  public void FixedSeedDoesNotEnableArbitraryBoogieArguments() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.RandomSeed = 42;
    options.Set(BoogieOptionBag.BoogieArguments, new[] { "/randomSeed:42" });
    Assert.True(DefinitionAnalysis.SupportsDiagnosticContext(options));
    options.Set(BoogieOptionBag.BoogieArguments, new[] { "/noVerify" });
    Assert.False(DefinitionAnalysis.SupportsDiagnosticContext(options));
  }

  // Fingerprinting a shared translation preserves all native implementation and assertion origins.
  [Fact]
  public async Task ProofInputHashingPreservesSharedTranslationOrigins() {
    var program = await ProofInputRepeatabilityTests.Parse("lemma P(x: int) { assert x + 1 > x; }");
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    var implementations = translations.SelectMany(module => module.Item2.Implementations).ToList();
    Assert.NotEmpty(implementations);
    var declarations = translations.SelectMany(module => module.Item2.TopLevelDeclarations).ToList();
    var declarationTokens = declarations.Select(declaration => declaration.tok).ToList();
    var assertions = implementations.SelectMany(implementation => implementation.Blocks)
      .SelectMany(block => block.Cmds).OfType<Microsoft.Boogie.AssertCmd>().ToList();
    var assertionTokens = assertions.Select(assertion => assertion.tok).ToList();

    var inputs = DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      _ => translations, () => new string('a', 64));

    Assert.NotNull(inputs);
    for (var index = 0; index < declarations.Count; index++) {
      Assert.Same(declarationTokens[index], declarations[index].tok);
    }
    for (var index = 0; index < assertions.Count; index++) {
      Assert.Same(assertionTokens[index], assertions[index].tok);
    }
  }

  // Unsupported certificate owners cannot replay a result from another native state.
  [Fact]
  public void NativeChecksumBindsCompleteProofInputs() {
    static Microsoft.Boogie.Program Translation() {
      var program = new Microsoft.Boogie.Program();
      program.AddTopLevelDeclaration(new Microsoft.Boogie.Implementation(Microsoft.Boogie.Token.NoToken,
        "synthetic", [], [], [], [], new List<Microsoft.Boogie.Block>(),
        new Microsoft.Boogie.QKeyValue(Microsoft.Boogie.Token.NoToken, "checksum", ["original"], null)));
      return program;
    }
    var first = Translation();
    var second = Translation();
    DefinitionAnalysis.BindNativeVerificationChecksums(new[] { Tuple.Create("A", first) }, null);
    DefinitionAnalysis.BindNativeVerificationChecksums(new[] { Tuple.Create("A", second) }, null);

    Assert.NotEqual("original", first.Implementations.Single().Checksum);
    Assert.NotEqual(first.Implementations.Single().Checksum, second.Implementations.Single().Checksum);
  }

  // Complete native inputs invalidate axiom changes while preserving independent modular body edits.
  [Fact]
  public async Task NativeChecksumTracksAxiomsAndPreservesUnrelatedBodies() {
    const string source = "const Value: int := 1\nlemma Good(x:int) { assert x + Value > x; }\n" +
      "lemma Other(x:int) { assert x + 1 > x; }\n";
    static async Task<string> Checksum(string text) {
      var program = await ProofInputRepeatabilityTests.Parse(text);
      var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
      var inputs = DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
        _ => translations, () => new string('a', 64));
      Assert.Contains(inputs!.Definitions, definition => definition.FullName.EndsWith("Good"));
      DefinitionAnalysis.BindNativeVerificationChecksums(translations, inputs);
      return translations.SelectMany(module => module.Item2.Implementations)
        .Single(implementation => implementation.Name.Contains("Impl$") && implementation.Name.EndsWith("Good")).Checksum;
    }
    var original = await Checksum(source);
    Assert.NotEqual(original, await Checksum(source.Replace("Value: int := 1", "Value: int := 0")));
    Assert.Equal(original, await Checksum(source.Replace("x + 1 > x", "x + 2 > x")));
  }

  private static async Task<(string Proof, string Native)> GoodChecksum(string text) {
    var program = await ProofInputRepeatabilityTests.Parse(text);
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    var inputs = DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      _ => translations, () => new string('a', 64));
    var proof = Assert.Single(inputs!.Definitions.Where(definition => definition.FullName == "Good")).Sha256;
    DefinitionAnalysis.BindNativeVerificationChecksums(translations, inputs);
    var native = translations.SelectMany(module => module.Item2.Implementations)
      .Single(implementation => implementation.Name.Contains("Impl$") && implementation.Name.EndsWith("Good")).Checksum;
    return (proof, native);
  }

  private const string Good = "lemma Good(x:int)\n  ensures x + 1 > x\n{\n  assert x + 1 > x;\n  assert x + 2 > x;\n}\n";

  // Result keys carry no positions: moving a declaration or reformatting inside it keeps the key.
  [Theory]
  [InlineData("shift-above")]
  [InlineData("comment-above")]
  [InlineData("whitespace-in-contract")]
  [InlineData("whitespace-in-body")]
  [InlineData("indentation")]
  public async Task NativeChecksumIgnoresPositions(string change) {
    var edited = change switch {
      "shift-above" => "\n\n" + Good,
      "comment-above" => "// moved down\n" + Good,
      "whitespace-in-contract" => Good.Replace("  ensures", "\n  ensures"),
      "whitespace-in-body" => Good.Replace("  assert x + 1", "\n    assert  x + 1"),
      _ => Good.Replace("\n  assert", "\n        assert")
    };
    var before = await GoodChecksum(Good);
    var after = await GoodChecksum(edited);
    Assert.Equal(before.Proof, after.Proof);
    Assert.Equal(before.Native, after.Native);
  }

  // A changed assertion, a reordered assertion or a changed contract still changes the key.
  [Theory]
  [InlineData("assertion-text")]
  [InlineData("assertion-order")]
  [InlineData("contract")]
  [InlineData("dropped-assertion")]
  public async Task NativeChecksumTracksSemanticChanges(string change) {
    var edited = change switch {
      "assertion-text" => Good.Replace("assert x + 2 > x", "assert x + 3 > x"),
      "assertion-order" => Good.Replace("  assert x + 1 > x;\n  assert x + 2 > x;", "  assert x + 2 > x;\n  assert x + 1 > x;"),
      "contract" => Good.Replace("ensures x + 1 > x", "ensures x + 2 > x"),
      _ => Good.Replace("  assert x + 2 > x;\n", "")
    };
    Assert.NotEqual(edited, Good);
    Assert.NotEqual((await GoodChecksum(Good)).Native, (await GoodChecksum(edited)).Native);
  }

  private static async Task<string> Shape(string text, string name) {
    var program = await ProofInputRepeatabilityTests.Parse(text);
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    var translation = translations.Select(module => module.Item2).Single(program => program.Implementations
      .Any(implementation => implementation.Name.Contains("Impl$") && implementation.Name.EndsWith(name)));
    return DefinitionAnalysis.AssertionShape(translation.Implementations
      .Single(implementation => implementation.Name.Contains("Impl$") && implementation.Name.EndsWith(name)),
      translation.Procedures.ToDictionary(procedure => procedure.Name));
  }

  // The assertion-shape guard is position-free and distinguishes kinds, texts and order by itself.
  [Fact]
  public async Task AssertionShapeIsPositionFreeAndOrderSensitive() {
    const string callee = "method Callee(x: int) requires x > 0 {}\n";
    const string first = callee + "method Run(x: int) requires x > 0 { assert x > 1; Callee(x); }\n";
    const string second = callee + "method Run(x: int) requires x > 0 { Callee(x); assert x > 1; }\n";
    var original = await Shape(first, "Run");
    Assert.Equal(original, await Shape("\n\n// shifted\n" + first.Replace("{ assert", "{\n  assert"), "Run"));
    Assert.NotEqual(original, await Shape(second, "Run"));
    Assert.NotEqual(original, await Shape(first.Replace("assert x > 1; ", ""), "Run"));
  }
}
