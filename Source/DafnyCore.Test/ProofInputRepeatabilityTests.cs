using System.Text.Json;
using Microsoft.Dafny;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging.Abstractions;
using Bpl = Microsoft.Boogie;
using Program = Microsoft.Dafny.Program;
using TriggerComparison = Microsoft.Dafny.Triggers.ExprExtensions;

namespace DafnyCore.Test;

// Parse strict dictionary snapshots, resolve, translate with an embedded prelude, and hash in memory.
// No engine/tasks/prover, disk fallback, file staging, directories, toolchain hashing or teardown IO.
[Collection("Proof input translation")]
public class ProofInputRepeatabilityTests {
  private const string QuantifiedHelper = """
    module QuantifiedControl {
      lemma GeneratorRange(prefix: seq<int>, z: int)
        requires forall i: int :: 0 <= i < |prefix| ==> 0 <= prefix[i] <= 4
        requires 0 <= z <= 4
        ensures |prefix + [z]| > 0
        ensures forall i: int :: 0 <= i < |prefix + [z]| ==> 0 <= (prefix + [z])[i] <= 4
      {
        forall i: int | 0 <= i < |prefix + [z]|
          ensures 0 <= (prefix + [z])[i] <= 4
        {
          if i < |prefix| {
            assert (prefix + [z])[i] == prefix[i];
          } else {
            assert i == |prefix|;
            assert (prefix + [z])[i] == z;
          }
        }
      }
    }
    """;

  // Reanalyzing one resolved quantified helper must preserve every emitted input fingerprint.
  [Fact]
  public async Task ConsecutiveAnalysesPreserveQuantifiedHelperInputs() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    var after = Inputs(program);

    Assert.Contains(before.Definitions, item => item.FullName == "QuantifiedControl.GeneratorRange");
    Assert.Equal(JsonSerializer.Serialize(before), JsonSerializer.Serialize(after));
  }

  // An ordinary translation between captures must not change the analyzer's proof input.
  [Fact]
  public async Task OrdinaryTranslationPreservesQuantifiedHelperInputs() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    Assert.NotEmpty(Translate(program).ToArray());
    var after = Inputs(program);

    Assert.Equal(JsonSerializer.Serialize(before), JsonSerializer.Serialize(after));
  }

  // Shadowed nested binders and generated wellformedness locals must remain distinct and repeatable.
  [Fact]
  public async Task NestedBindersRemainRepeatable() {
    var program = await Parse("""
      lemma Nested(xs: seq<int>)
        requires forall i: int :: 0 <= i < |xs| ==> xs[i] >= 0
        ensures forall i: int :: 0 <= i < |xs| ==> (forall i: int :: 0 <= i < |xs| ==> xs[i] >= 0)
      {
        forall i: int | 0 <= i < |xs|
          ensures forall i: int :: 0 <= i < |xs| ==> xs[i] >= 0
        { assert xs[i] >= 0; }
      }
      """);
    var before = Inputs(program);
    var translations = Translate(program).ToArray();
    Assert.All(translations.SelectMany(pair => pair.Item2.Implementations), implementation => {
      var variables = implementation.InParams.Concat(implementation.OutParams).Concat(implementation.LocVars).ToArray();
      Assert.Equal(variables.Length, variables.Select(variable => variable.Name).Distinct().Count());
    });
    Assert.Equal(JsonSerializer.Serialize(before), JsonSerializer.Serialize(Inputs(program)));
  }

  // A resolved assertion edit must change the helper fingerprint even when source tokens are untouched.
  [Fact]
  public async Task ResolvedBodyMutationChangesInput() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    var assertion = program.Descendants().OfType<AssertStmt>().First();
    assertion.Expr = Expression.CreateBoolLiteral(assertion.Origin, false);
    var after = Inputs(program);

    Assert.NotEqual(before.Definitions.Single().Sha256, after.Definitions.Single().Sha256);
    Assert.Equal(JsonSerializer.Serialize(after), JsonSerializer.Serialize(Inputs(program)));
  }

  // A resolved postcondition edit remains an authoritative proof-input change.
  [Fact]
  public async Task ResolvedPostconditionMutationChangesInput() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    var helper = program.Descendants().OfType<Method>().Single(method => method.Name == "GeneratorRange");
    helper.Ens[0].E = Expression.CreateBoolLiteral(helper.Ens[0].Origin, false);

    Assert.NotEqual(before.Definitions.Single().Sha256, Inputs(program).Definitions.Single().Sha256);
  }

  // Effective verifier option drift changes both option and definition fingerprints.
  [Fact]
  public async Task OptionMutationChangesInput() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    program.Options.RandomSeed = 42;
    var after = Inputs(program);

    Assert.NotEqual(before.OptionsSha256, after.OptionsSha256);
    Assert.NotEqual(before.Definitions.Single().Sha256, after.Definitions.Single().Sha256);
  }

  // The injected toolchain boundary still participates in the real definition hash.
  [Fact]
  public async Task ToolchainMutationChangesInput() {
    var program = await Parse(QuantifiedHelper);
    var before = Inputs(program);
    var after = Inputs(program, new string('b', 64));

    Assert.NotEqual(before.ToolchainSha256, after.ToolchainSha256);
    Assert.NotEqual(before.Definitions.Single().Sha256, after.Definitions.Single().Sha256);
  }

  // Production arithmetic and Unicode defines reach the embedded prelude without a filesystem parser.
  [Theory]
  [InlineData(0, true)]
  [InlineData(10, false)]
  public async Task PreludeConfigurationsRemainRepeatable(int arithmetic, bool unicode) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.ArithMode = arithmetic;
    options.Set(CommonOptionBag.UnicodeCharacters, unicode);
    var program = await Parse(QuantifiedHelper, options);

    Assert.Equal(JsonSerializer.Serialize(Inputs(program)), JsonSerializer.Serialize(Inputs(program)));
  }

  // Nested failing translations restore outer names and leave legacy naming unique and observable.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NestedScopeExceptionPreservesNames(bool local) {
    var program = await Parse("method M() { }");
    var method = program.Descendants().OfType<Method>().Single(declaration => declaration.Name == "M");
    IVariable Variable() => local
      ? new LocalVariable(Token.NoToken, "x", Microsoft.Dafny.Type.Int, false)
      : new BoundVar(Token.NoToken, "x", Microsoft.Dafny.Type.Int);
    var original = Variable();
    var legacyName = original.AssignUniqueName(method.IdGenerator);
    var introduced = Variable();
    var compilerGenerator = new CodeGenIdGenerator();
    var compileName = original.GetOrCreateCompileName(compilerGenerator);
    using (new VerificationNamingScope()) {
      Assert.False(original.HasBeenAssignedUniqueName);
      introduced.AssignUniqueName(method.IdGenerator);
      var outerName = original.AssignUniqueName(method.IdGenerator);
      Assert.NotEqual(introduced.UniqueName, outerName);
      Assert.Throws<InvalidOperationException>((Action)(() => {
        using var inner = new VerificationNamingScope();
        Assert.False(original.HasBeenAssignedUniqueName);
        Assert.NotEqual(outerName, original.AssignUniqueName(method.IdGenerator));
        throw new InvalidOperationException("Interrupted translation");
      }));
      Assert.Equal(outerName, original.UniqueName);
      Assert.True(original.HasBeenAssignedUniqueName);
      Assert.Equal(compileName, original.GetOrCreateCompileName(compilerGenerator));
    }
    Assert.Null(VerificationNamingScope.Current);
    Assert.Equal(legacyName, original.UniqueName);
    Assert.True(introduced.HasBeenAssignedUniqueName);
    var nextName = Variable().AssignUniqueName(method.IdGenerator);
    Assert.NotEqual(legacyName, nextName);
    Assert.NotEqual(introduced.UniqueName, nextName);
  }

  // Trigger comparison must see the current translation's binder names rather than stale legacy caches.
  [Fact]
  public async Task TriggerComparisonUsesScopedNames() {
    var program = await Parse("lemma M() ensures forall x: int :: x == x ensures forall x: int :: x == x { }");
    var method = program.Descendants().OfType<Method>().Single(declaration => declaration.Name == "M");
    var first = Assert.IsType<ForallExpr>(method.Ens[0].E.Resolved);
    var second = Assert.IsType<ForallExpr>(method.Ens[1].E.Resolved);
    first.BoundVars.Single().AssignUniqueName(method.IdGenerator);
    second.BoundVars.Single().AssignUniqueName(method.IdGenerator);
    Assert.False(TriggerComparison.ShallowEq_Top(first, second));

    using (new VerificationNamingScope()) {
      Assert.True(TriggerComparison.ShallowEq_Top(first, second));
      first.BoundVars.Single().AssignUniqueName(method.IdGenerator);
      Assert.False(TriggerComparison.ShallowEq_Top(first, second));
      second.BoundVars.Single().AssignUniqueName(method.IdGenerator);
      Assert.False(TriggerComparison.ShallowEq_Top(first, second));
    }
    Assert.False(TriggerComparison.ShallowEq_Top(first, second));
  }

  internal static DafnyProofInputs Inputs(Program program, string toolchain = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") {
    var result = DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      Translate, () => toolchain);
    Assert.Equal(0, program.Reporter.ErrorCount);
    Assert.NotNull(result);
    return result!;
  }

  internal static IEnumerable<Tuple<string, Bpl.Program>> Translate(Program program) {
    Microsoft.Dafny.Type.ResetScopes();
    foreach (var module in BoogieGenerator.VerifiableModules(program)) {
      var translator = new BoogieGenerator(program.Reporter, program.ProofDependencyManager, null, ReadPrelude);
      yield return Tuple.Create(module.SanitizedName, translator.DoTranslation(program, module));
    }
  }

  private static Bpl.Program ReadPrelude(IReadOnlyList<string> defines) {
    using var stream = typeof(ProofInputRepeatabilityTests).Assembly.GetManifestResourceStream("ProofInputPrelude.bpl");
    Assert.NotNull(stream);
    using var reader = new StreamReader(stream!);
    var text = SourcePreprocessor.ProcessDirectives(reader, defines.ToList());
    Assert.Equal(0, Bpl.Parser.Parse(text, "embedded-prelude.bpl", out var prelude));
    Assert.NotNull(prelude);
    return prelude;
  }

  internal static async Task<Program> Parse(string source, DafnyOptions? options = null,
    string path = "/workspace/proof-input-memory.dfy") {
    if (options == null) {
      options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
      options.ApplyDefaultOptionsWithoutSettingsDefault();
    }
    var uri = new Uri(path);
    options.CliRootSourceUris.Add(uri);
    var fileSystem = new StrictFileSystem(new Dictionary<Uri, string> { [uri] = source });
    var reporter = new BatchErrorReporter(options);
    var parser = new ProgramParser(NullLogger<ProgramParser>.Instance, fileSystem);
    var file = DafnyFile.HandleDafnyFile(fileSystem, reporter, options, uri, Token.NoToken)!;
    Microsoft.Dafny.Type.ResetScopes();
    var parsed = await parser.ParseFiles(uri.ToString(), [file], reporter, CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return parsed.Program;
  }

  private sealed class StrictFileSystem(IReadOnlyDictionary<Uri, string> files) : IFileSystem {
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(files[uri]), null);
    public bool Exists(Uri uri) => files.ContainsKey(uri)
      ? true : throw new InvalidOperationException("Unexpected filesystem lookup: " + uri);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }
}

// Resolver type scopes are shared static state; keep these real translation tests serial.
[CollectionDefinition("Proof input translation", DisableParallelization = true)]
public sealed class ProofInputTranslationCollection { }
