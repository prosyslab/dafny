using System.Threading;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class DefinitionProofInputsTests {
  private const string ModularMethods = """
    method B(x: int) returns (y: int)
      ensures y > x
    { y := x + 1; }
    method A(x: int) returns (y: int)
      ensures y > x
    { y := B(x); }
    """;
  private const string ModularLemmas = """
    lemma B(x: int)
      ensures x + 1 > x
    { }
    lemma A(x: int)
      ensures x + 1 > x
    { B(x); }
    """;

  // Editing an ordinary callee body preserves the caller's modular proof input.
  [Fact]
  public async Task OrdinaryCalleeBodyDoesNotInvalidateCaller() {
    var before = await Analyze(ModularMethods);
    var after = await Analyze(ModularMethods.Replace("{ y := x + 1; }", "{\n y := x + 2;\n assert y > x;\n }"));

    Assert.Equal(Input(before, "A"), Input(after, "A"));
    Assert.NotEqual(Input(before, "B"), Input(after, "B"));
  }

  // Editing a standard helper lemma proof preserves the unchanged caller proof input.
  [Fact]
  public async Task OrdinaryLemmaBodyDoesNotInvalidateCaller() {
    var before = await Analyze(ModularLemmas);
    var after = await Analyze(ModularLemmas.Replace("{ }", "{ assert x + 1 > x; }"));

    Assert.Equal(Input(before, "A"), Input(after, "A"));
    Assert.NotEqual(Input(before, "B"), Input(after, "B"));
  }

  // A standard helper lemma contract remains a proof input of its caller.
  [Fact]
  public async Task LemmaContractInvalidatesCaller() {
    var before = await Analyze(ModularLemmas);
    var after = await Analyze(ModularLemmas.Replace("ensures x + 1 > x\n{ }", "ensures x + 1 >= x\n{ }"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Moving an identical snapshot changes entry paths without changing proof inputs.
  [Fact]
  public async Task SourceRelocationDoesNotInvalidateProofs() {
    var before = await Analyze(ModularMethods, "/workspace/tmp/public-proof-inputs/one.dfy");
    var after = await Analyze(ModularMethods, "/workspace/tmp/public-proof-inputs/relocated/two.dfy");

    Assert.Equal(Input(before, "A"), Input(after, "A"));
    Assert.Equal(Input(before, "B"), Input(after, "B"));
    Assert.NotEqual(before.ProofInputs!.Definitions[0].SourcePath, after.ProofInputs!.Definitions[0].SourcePath);
  }

  // Changing the implementation being certified invalidates its certificate.
  [Fact]
  public async Task TargetBodyInvalidatesProof() {
    var before = await Analyze(ModularMethods);
    var after = await Analyze(ModularMethods.Replace("{ y := B(x); }", "{ y := B(x); assert y > x; }"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // A consumed callee contract remains part of the caller's proof input.
  [Fact]
  public async Task CalleeContractInvalidatesCaller() {
    var before = await Analyze(ModularMethods);
    var after = await Analyze(ModularMethods.Replace("ensures y > x\n{ y := x + 1; }", "ensures y >= x\n{ y := x + 1; }"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Transparent function definitions remain available to the verifier as axioms.
  [Fact]
  public async Task TransparentFunctionBodyInvalidatesCaller() {
    const string source = "function F(x: int): int { x + 1 } method A(x: int) { assert F(x) > x; }";
    var before = await Analyze(source);
    var after = await Analyze(source.Replace("x + 1", "x + 2"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Export visibility controls which transparent function axioms the caller can use.
  [Fact]
  public async Task FunctionVisibilityInvalidatesCaller() {
    const string source = """
      module Lib {
        export E reveals F
        function F(x: int): int { x + 1 }
      }
      module Use {
        import L = Lib`E
        method A(x: int) { assert L.F(x) > x; }
      }
      """;
    var before = await Analyze(source);
    var after = await Analyze(source.Replace("reveals F", "provides F"));

    Assert.NotEqual(Input(before, "Use.A"), Input(after, "Use.A"));
  }

  // Making a function opaque changes the definitions available without an explicit reveal.
  [Fact]
  public async Task FunctionOpacityInvalidatesCaller() {
    const string source = "function F(x: int): int { x + 1 } method A(x: int) { assert F(x) > x; }";
    var before = await Analyze(source);
    var after = await Analyze(source.Replace("function F", "opaque function F"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Creating mutual recursion changes termination context even with unchanged contracts.
  [Fact]
  public async Task RecursiveComponentInvalidatesCaller() {
    const string source = """
      method A(n: nat) decreases n { if n > 0 { B(n - 1); } }
      method B(n: nat) decreases n { }
      """;
    var before = await Analyze(source);
    var after = await Analyze(source.Replace("method B(n: nat) decreases n { }",
      "method B(n: nat) decreases n { if n > 0 { A(n - 1); } }"));

    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Assertion isolation is an actual verifier input even if Boogie text is unchanged.
  [Fact]
  public async Task VerificationOptionsInvalidateProofs() {
    var before = await Analyze(ModularMethods);
    var after = await Analyze(ModularMethods, configure: options => {
      options.Set(BoogieOptionBag.IsolateAssertions, true);
      options.ApplyBinding(BoogieOptionBag.IsolateAssertions);
    });

    Assert.NotEqual(before.ProofInputs!.OptionsSha256, after.ProofInputs!.OptionsSha256);
    Assert.NotEqual(Input(before, "A"), Input(after, "A"));
  }

  // Unsupported logical/by-method identity receives no incomplete certificate.
  [Fact]
  public async Task ByMethodDefinitionIsOmitted() {
    var result = await Analyze("function F(): int { 1 } by method { return 1; }");

    Assert.NotNull(result.ProofInputs);
    Assert.Empty(result.ProofInputs!.Definitions);
  }

  // Arbitrary Boogie transformations cannot receive a partial dependency certificate.
  [Fact]
  public async Task CustomBoogieArgumentsOmitProofInputs() {
    var result = await Analyze(ModularMethods, configure: options =>
      options.Set(BoogieOptionBag.BoogieArguments, new[] { "/inline:assume" }));

    Assert.Null(result.ProofInputs);
  }

  // A body-consuming inlining configuration must not exclude other implementations.
  [Fact]
  public async Task CustomInliningOmitsProofInputs() {
    var result = await Analyze(ModularMethods, configure: options =>
      options.InlineDepth = DafnyOptions.Default.InlineDepth + 1);

    Assert.Null(result.ProofInputs);
  }

  // Inferred modifies clauses consume other implementation bodies before verification.
  [Fact]
  public async Task InferredModifiesOmitsProofInputs() {
    var result = await Analyze(ModularMethods, configure: options => options.InferModifies = true);

    Assert.Null(result.ProofInputs);
  }

  // Nondefault Boogie loop preprocessing is outside the supported projection mode.
  [Fact]
  public async Task CustomLoopUnrollingOmitsProofInputs() {
    var result = await Analyze(ModularMethods, configure: options =>
      options.LoopUnrollCount = DafnyOptions.Default.LoopUnrollCount + 1);

    Assert.Null(result.ProofInputs);
  }

  // Loop-unrolling soundness settings must not bypass the proof configuration boundary.
  [Fact]
  public async Task CustomLoopSoundnessOmitsProofInputs() {
    var result = await Analyze(ModularMethods, configure: options =>
      options.SoundLoopUnrolling = !DafnyOptions.Default.SoundLoopUnrolling);

    Assert.Null(result.ProofInputs);
  }

  // Programmatic plugins have the same unsupported transformation boundary as CLI plugins.
  [Fact]
  public async Task AdditionalPluginOmitsProofInputs() {
    var result = await Analyze(ModularMethods, configure: options =>
      options.AdditionalPlugins = [new ConfiguredPlugin(new EmptyPluginConfiguration())]);

    Assert.Null(result.ProofInputs);
  }

  // Runtime plugin arguments are rejected before translation can load an external assembly.
  [Fact]
  public async Task AdditionalPluginArgumentsOmitProofInputs() {
    var result = await Analyze(ModularMethods, afterResolve: options =>
      options.AdditionalPluginArguments = ["unsupported-proof-input-plugin.dll"]);

    Assert.Null(result.ProofInputs);
  }

  // Mutating the actual cached plugin set must not bypass configuration checks.
  [Fact]
  public async Task CachedPluginOmitsProofInputs() {
    var plugin = new ConfiguredPlugin(new EmptyPluginConfiguration());
    IList<Plugin>? plugins = null;
    try {
      var result = await Analyze(ModularMethods, afterResolve: options => {
        plugins = options.Plugins;
        plugins.Add(plugin);
      });

      Assert.Null(result.ProofInputs);
    }
    finally {
      plugins?.Remove(plugin);
    }
  }

  // Existing document calls preserve the default JSON contract without certificates.
  [Fact]
  public async Task ProofInputsAreOptIn() {
    var result = await Analyze(ModularMethods, includeProofInputs: false);

    Assert.Null(result.ProofInputs);
  }

  private static string Input(DefinitionSourceFacts facts, string name) {
    Assert.NotNull(facts.ProofInputs);
    return Assert.Single(facts.ProofInputs!.Definitions.Where(input => input.FullName == name)).Sha256;
  }

  private static async Task<DefinitionSourceFacts> Analyze(string source,
    string path = "/workspace/tmp/public-proof-inputs/source.dfy", Action<DafnyOptions>? configure = null,
    bool includeProofInputs = true, Action<DafnyOptions>? afterResolve = null) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    configure?.Invoke(options);
    var uri = new Uri(path);
    options.CliRootSourceUris.Add(uri);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parsed = await ProgramParser.Parse(source, uri, reporter);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    afterResolve?.Invoke(options);

    var result = DefinitionAnalysis.AnalyzeDocument(parsed.Program, new HashSet<Uri> { uri },
      includeProofInputs: includeProofInputs);
    Assert.Equal(0, reporter.ErrorCount);
    return result.SourceFacts;
  }

  private sealed class EmptyPluginConfiguration : Microsoft.Dafny.Plugins.PluginConfiguration { }
}
