#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

// All snapshots, parser filesystems, edits, closures and assertions stay in memory. The only library input
// is the fixed embedded runtime resource. No campaign, analyzer, verifier, solver, process or cleanup runs.
public sealed class ContractRuntimeSelectedDraftPreparationTests {
  private const string Generator = """
    method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int)
      ensures x >= 0
    { x := 2; }
    """;

  private const string Source = """
    module M {
      method Helper(x: int) returns (y: int) ensures y == x { assert false; }
      method Unrelated(x: int) returns (y: int) { assert false; }
      method Goal(x: int) returns (y: int) requires x >= 0 ensures y == x { y := Helper(x); }
    }
    """;

  private static DafnyOptions Options() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null) { DisableScopes = true };
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    return options;
  }

  private static ContractSource Snapshot(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static ContractRuntimeDraft Draft(string symbol, string declaration) =>
    new(symbol, symbol + ".draft.dfy", declaration, ContractHarnessBuilder.Hash(declaration));

  private static Method Method(Program program, string symbol) =>
    Assert.Single(ContractRuntimeObligationTransformer.Members(program).OfType<Method>()
      .Where(method => method.FullDafnyName == symbol));

  private static async Task<Program> Parse(IReadOnlyList<ContractSource> sources, bool resolve = true) {
    var reporter = new BatchErrorReporter(Options());
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None, resolve);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return program;
  }

  private static IReadOnlyList<ContractSource> WithRuntime(IReadOnlyList<ContractSource> sources) =>
    sources.Append(Snapshot("PbtRuntime.dfy", ContractRuntimeInstrumentation.DafnySource)).ToArray();

  private static async Task<ContractRuntimeSelectedDraftSources> Prepare(string source,
    IReadOnlyList<ContractRuntimeDraft> drafts, string generator = Generator, bool proof = false,
    ContractEntry? entry = null, DafnyOptions? options = null, Action<string, string>? phaseObserver = null,
    CancellationToken cancellationToken = default) {
    ContractSource[] sources = [Snapshot("Target.dfy", source)];
    var original = await Parse(sources);
    var goal = entry == null ? Method(original, "M.Goal") :
      ContractCallableSelector.SelectMethod(original, entry, requireConcreteReceiver: false, allowLemmaContract: true);
    return await ContractRuntimeSelectedDraftPreparation.PrepareAsync(original, sources, goal,
      drafts, Snapshot("Generator.dfy", generator), proof, options ?? Options(), cancellationToken,
      phaseObserver, selectedEntry: entry);
  }

  private static async Task<(Program Program, IReadOnlyList<ContractSource> Sources)> Runtime(
    ContractRuntimePreparedSources preparation) {
    var raw = await Parse(preparation.Sources, resolve: false);
    var sources = WithRuntime(ContractRuntimeObligationTransformer.MakeGeneratorVisible(raw, preparation.Sources,
      new HashSet<string>()));
    return (await Parse(sources), sources);
  }

  private static async Task<(Program Program, Method Generator, IReadOnlyList<ContractSource> Sources)> DirectProof(
    ContractRuntimePreparedSources preparation) {
    var sources = WithRuntime(preparation.Sources);
    var authored = await Parse(sources);
    var goal = Method(authored, "M.Goal");
    var generator = ContractRuntimeGeneratorSignature.Select(authored, goal, preparation.GeneratorMethodName);
    var build = ContractGeneratorProof.PrepareProofSources(authored, sources, goal, generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource(), out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proof = await Parse(build!.Sources);
    return (proof, Method(proof, "M.Generate"), build.Sources);
  }

  // Preparation retains the exact resolved runtime source set, Program, options and deferred diagnostics as one bundle.
  [Fact]
  public async Task RetainsResolvedRuntimeBundle() {
    var options = Options();
    var prepared = await Prepare(Source, [
      Draft("M.Helper", "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; }")
    ], options: options);
    var independentlyResolved = await Runtime(prepared.Preparation);

    Assert.Same(prepared.Preparation, prepared.Runtime.Preparation);
    Assert.Same(options, prepared.Runtime.RuntimeProgram.Options);
    Assert.Equal(ContractRuntimeTypeEvidence.SourceSetHash(independentlyResolved.Sources),
      ContractRuntimeTypeEvidence.SourceSetHash(prepared.Runtime.RuntimeSources));
    Assert.Equal(prepared.Runtime.RuntimeSources.Select(source => source.Path),
      independentlyResolved.Sources.Select(source => source.Path));
    Assert.Empty(prepared.Runtime.DeferredGhostDiagnostics);
    Assert.Same(Method(prepared.Runtime.RuntimeProgram, "M.Goal"),
      ContractCallableSelector.SelectMethod(prepared.Runtime.RuntimeProgram, new("M.Goal"),
        requireConcreteReceiver: false));
  }

  // A syntactically broken unrelated registered packet never reaches the selected source parser.
  [Fact]
  public async Task IgnoresMalformedUnrelatedMethodPacket() {
    var prepared = await Prepare(Source, [
      Draft("M.Unrelated", "method broken ("),
      Draft("M.Helper", "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := x; }")
    ]);

    Assert.Equal(new[] { "M.Helper" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    Assert.Null(prepared.ProofPreparationFailure);
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));
    Assert.DoesNotContain(Method(program, "M.Helper").Body!.Descendants().OfType<AssertStmt>(),
      assertion => assertion.Expr.Resolved is LiteralExpr { Value: false });
    Assert.IsType<AssertStmt>(Assert.Single(Method(program, "M.Unrelated").Body!.Body));
  }

  // A selected executable packet's invalid syntax remains a preparation failure with its exact identity.
  [Fact]
  public async Task RejectsMalformedRuntimePacket() {
    var error = await Assert.ThrowsAsync<ContractRuntimeDraftPreparationException>(() =>
      Prepare(Source, [Draft("M.Helper", "method broken (")], proof: true));

    Assert.Contains("M.Helper", error.Message, StringComparison.Ordinal);
    Assert.Contains("M.Helper.draft.dfy", error.Message, StringComparison.Ordinal);
  }

  // A draft's new executable call makes the next malformed packet required even when the original body had no callees.
  [Fact]
  public async Task RejectsNewlyReachedMalformedRuntimePacket() {
    const string source = "module M { method First(x: int) returns (y: int) method Second(x: int) returns (y: int) " +
      "method Goal(x: int) returns (y: int) { y := First(x); } }";
    var error = await Assert.ThrowsAsync<ContractRuntimeDraftPreparationException>(() => Prepare(source, [
      Draft("M.First", "method {:pbt_draft \"M.First\"} First(x: int) returns (y: int) { y := Second(x); }"),
      Draft("M.Second", "method malformed (")
    ], proof: true));

    Assert.Contains("M.Second.draft.dfy", error.Message, StringComparison.Ordinal);
  }

  // Newly installed bodies reveal two further original declarations that the initial goal graph cannot reach.
  [Fact]
  public async Task DiscoversNewTransitiveMethodAndFunctionCalls() {
    const string source = """
      module M {
        method First(x: int) returns (y: int) { assert false; }
        method Second(x: int) returns (y: int) { assert false; }
        function Third(x: int): int
        method Unrelated() { assert false; }
        method Goal(x: int) returns (y: int) { y := First(x); }
      }
      """;
    var prepared = await Prepare(source, [
      Draft("M.First", "method {:pbt_draft \"M.First\"} First(x: int) returns (y: int) { y := Second(x); }"),
      Draft("M.Second", "method {:pbt_draft \"M.Second\"} Second(x: int) returns (y: int) { y := Third(x); }"),
      Draft("M.Third", "function {:pbt_draft \"M.Third\"} Third(x: int): int { x + 1 }"),
      Draft("M.Unrelated", "invalid unrelated payload")
    ]);

    Assert.Equal(new[] { "M.First", "M.Second", "M.Third" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));
    Assert.Contains(Method(program, "M.First").Body!.Descendants().OfType<CallStmt>(),
      call => ReferenceEquals(call.Method, Method(program, "M.Second")));
    var third = Assert.Single(ContractRuntimeObligationTransformer.Members(program).OfType<Function>()
      .Where(function => function.FullDafnyName == "M.Third"));
    Assert.Contains(Method(program, "M.Second").Body!.Descendants().OfType<FunctionCallExpr>(),
      call => ReferenceEquals(call.Function, third));
    Assert.NotNull(third.Body);
  }

  // Explicit entry type arguments survive each reparse while newly installed generic bodies reveal the complete dependency chain.
  [Fact]
  public async Task PreservesExplicitEntryTypeArgumentsAcrossDraftClosure() {
    const string source = "module M { method Goal<T>(x: T) returns (y: T) " +
      "method First<T>(x: T) returns (y: T) method Second<T>(x: T) returns (y: T) }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 2; }";
    var entry = new ContractEntry("M.Goal", new[] { "int" });
    var prepared = await Prepare(source, [
      Draft("M.Goal", "method {:pbt_draft \"M.Goal\"} Goal<T>(x: T) returns (y: T) { y := First<T>(x); }"),
      Draft("M.First", "method {:pbt_draft \"M.First\"} First<T>(x: T) returns (y: T) { y := Second<T>(x); }"),
      Draft("M.Second", "method {:pbt_draft \"M.Second\"} Second<T>(x: T) returns (y: T) { y := x; }")
    ], generator, entry: entry);

    Assert.Equal(new[] { "M.First", "M.Goal", "M.Second" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    var runtime = await Runtime(prepared.Preparation);
    var concrete = Assert.IsType<ContractConcreteMethod>(ContractCallableSelector.SelectMethod(runtime.Program, entry,
      requireConcreteReceiver: false, allowLemmaContract: true));
    Assert.Empty(concrete.TypeArgs);
    Assert.True(Assert.Single(concrete.Ins).Type.IsIntegerType);
    Assert.Null(Assert.Single(concrete.Ins).Type.AsTypeParameter);
    Assert.Equal("int", Assert.Single(concrete.Ins).Type.NormalizeExpand().ToString());
  }

  // A concrete view is accepted only by its owning program even when another parsed program has the same callable names.
  [Fact]
  public async Task RejectsConcreteViewFromSameNamedForeignProgram() {
    const string source = "module M { import PbtRandom method Goal<T>(x: T) returns (y: T) { y := x; } " +
      "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := 2; } }";
    var sources = WithRuntime(new[] { Snapshot("Target.dfy", source) });
    var original = await Parse(sources);
    var other = await Parse(sources);
    var concrete = Assert.IsType<ContractConcreteMethod>(ContractCallableSelector.SelectMethod(original,
      new ContractEntry("M.Goal", new[] { "int" }), requireConcreteReceiver: false));

    Assert.Equal(Method(other, "M.Goal").FullDafnyName, concrete.OriginalCallable.FullDafnyName);
    Assert.Same(Method(original, "M.Generate"), ContractRuntimeGeneratorSignature.Select(original, concrete, "Generate"));
    var error = Assert.Throws<ArgumentException>(() => ContractRuntimeGeneratorSignature.Select(other, concrete, "Generate"));
    Assert.Equal("goal", error.ParamName);
  }

  // A prepared function-by-method descriptor authenticates its native function and selects the exact generator.
  [Fact]
  public async Task SelectsPreparedGeneratorForFunctionByMethodDescriptor() {
    const string source = "module M { function Goal(x: int): int { x } by method { return x; } }";
    var entry = new ContractEntry("M.Goal");
    var prepared = await Prepare(source, [], entry: entry);
    var runtime = await Runtime(prepared.Preparation);
    var goal = ContractCallableSelector.SelectMethod(runtime.Program, entry, requireConcreteReceiver: false);
    var function = Assert.Single(ContractRuntimeObligationTransformer.Members(runtime.Program).OfType<Function>()
      .Where(candidate => candidate.FullDafnyName == "M.Goal"));

    Assert.Same(function, goal.FunctionFromWhichThisIsByMethodDecl);
    Assert.Same(function, ContractCallableSelector.NativeCallable(runtime.Program, goal));
    var generator = ContractRuntimeGeneratorSignature.Select(runtime.Program, goal, prepared.Preparation.GeneratorMethodName);
    Assert.Same(Method(runtime.Program, "M." + prepared.Preparation.GeneratorMethodName), generator);
    Assert.NotNull(function.ByMethodDecl);
    Assert.Contains(function.ByMethodDecl!, ContractRuntimeObligationTransformer.DiagnosticReachable(runtime.Program, goal, generator));
  }

  // Generator-only runtime calls and their newly introduced dependencies are selected independently of the goal body.
  [Fact]
  public async Task DiscoversGeneratorOnlyDependencyChain() {
    const string source = "module M { method Make() returns (value: int) method Deep() returns (value: int) " +
      "method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) { x := Make(); }";
    var prepared = await Prepare(source, [
      Draft("M.Make", "method {:pbt_draft \"M.Make\"} Make() returns (value: int) { value := Deep(); }"),
      Draft("M.Deep", "method {:pbt_draft \"M.Deep\"} Deep() returns (value: int) { value := 2; }")
    ], generator);

    Assert.Equal(new[] { "M.Deep", "M.Make" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
  }

  // Mutually recursive replacement bodies terminate discovery after both canonical declarations are selected.
  [Fact]
  public async Task StabilizesCyclicDraftDependencies() {
    const string source = "module M { method First(x: int) returns (y: int) method Second(x: int) returns (y: int) " +
      "method Goal(x: int) returns (y: int) { y := First(x); } }";
    var prepared = await Prepare(source, [
      Draft("M.First", "method {:pbt_draft \"M.First\"} First(x: int) returns (y: int) { y := Second(x); }"),
      Draft("M.Second", "method {:pbt_draft \"M.Second\"} Second(x: int) returns (y: int) { y := First(x); }")
    ]);

    Assert.Equal(new[] { "M.First", "M.Second" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));
    Assert.Contains(Method(program, "M.Second").Body!.Descendants().OfType<CallStmt>(),
      call => ReferenceEquals(call.Method, Method(program, "M.First")));
  }

  // A newly reached implementation without a supplied packet stays bodyless and visible to the existing missing-draft check.
  [Fact]
  public async Task PreservesUnsuppliedTransitiveMissingBody() {
    const string source = "module M { method First(x: int) returns (y: int) method Missing(x: int) returns (y: int) " +
      "method Goal(x: int) returns (y: int) { y := First(x); } }";
    var prepared = await Prepare(source, [
      Draft("M.First", "method {:pbt_draft \"M.First\"} First(x: int) returns (y: int) { y := Missing(x); }")
    ]);
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));
    var missing = Method(program, "M.Missing");

    Assert.Null(missing.Body);
    Assert.Contains(missing, ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, [Method(program, "M.Goal")]));
  }

  // A reached target's existing implementation takes precedence over an otherwise valid reusable packet.
  [Fact]
  public async Task PreservesImplementedSourceBody() {
    const string source = "module M { function Original(x: int): int { x + 1 } " +
      "method Helper(x: int) returns (y: int) { y := Original(x); } " +
      "method Goal(x: int) returns (y: int) { y := Helper(x); } }";
    var prepared = await Prepare(source, [
      Draft("M.Helper", "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) { y := -100; }")
    ]);
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));

    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    Assert.Equal("M.Original", Assert.Single(Method(program, "M.Helper").Body!.Descendants()
      .OfType<FunctionCallExpr>()).Function.FullDafnyName);
  }

  // A reached concrete implementation still validates the selected reusable packet's exact signature.
  [Fact]
  public async Task RejectsSelectedUnusedSignatureMismatch() {
    var source = Source.Replace("{ assert false; }", "{ y := x; }", StringComparison.Ordinal);
    var error = await Assert.ThrowsAsync<ContractRuntimeDraftPreparationException>(() => Prepare(source, [
      Draft("M.Helper", "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (other: int) { other := x; }")
    ]));

    Assert.Contains("signature", error.Message, StringComparison.Ordinal);
  }

  // The alternate exact native symbol resolves to the canonical target without rewriting the supplied packet fingerprint.
  [Fact]
  public async Task PreservesExactAliasAndDraftLocation() {
    const string source = "// 한글\n" + Source;
    ContractSource[] sources = [Snapshot("Target.dfy", source)];
    var original = await Parse(sources);
    var helper = Method(original, "M.Helper");
    var draft = Draft(helper.FullName, "method {:pbt_draft \"" + helper.FullName +
      "\"} Helper(x: int) returns (y: int) { y := x; }");
    var prepared = await ContractRuntimeSelectedDraftPreparation.PrepareAsync(original, sources, Method(original, "M.Goal"),
      [draft], Snapshot("Generator.dfy", Generator), false, Options(), CancellationToken.None);
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));
    var body = Method(program, "M.Helper").Body!;
    var location = prepared.Preparation.SourceMap.ResolveLocation(body.Origin.Uri, body.StartToken.pos, "M.Helper");

    Assert.Equal(new[] { "M.Helper" }, prepared.Preparation.InstalledDraftSymbols);
    Assert.Equal(draft.Path, location.Path);
    Assert.Equal(draft.Sha256, location.Sha256);
    var originalContract = Method(program, "M.Helper").Ens.Single().E.Origin;
    var contractLocation = prepared.Preparation.SourceMap.ResolveLocation(originalContract.Uri, originalContract.pos);
    Assert.Equal(sources[0].Sha256, contractLocation.Sha256);
    Assert.Equal("Target.dfy", contractLocation.Path);
  }

  // Two native aliases for the same target are rejected from metadata before either malformed payload is parsed.
  [Fact]
  public async Task RejectsDuplicateCanonicalRegistration() {
    var original = await Parse([Snapshot("Target.dfy", Source)]);
    var helper = Method(original, "M.Helper");

    Assert.Throws<ArgumentException>(() => ContractRuntimeSourcePreparation.IndexDrafts(original,
      [Draft(helper.FullName, "invalid"), Draft(helper.FullDafnyName, "also invalid")]));
  }

  // Type constraints retain their executable function dependencies even without an explicit body call.
  [Fact]
  public async Task DiscoversRefinementConstraintDependency() {
    const string source = "module M { function Constraint(x: int): bool " +
      "type Bounded = x: int | Constraint(x) witness 0 method Goal(x: Bounded) {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: Bounded) { x := 0; }";
    var prepared = await Prepare(source, [
      Draft("M.Constraint", "function {:pbt_draft \"M.Constraint\"} Constraint(x: int): bool { true }")
    ], generator);

    Assert.Equal(new[] { "M.Constraint" }, prepared.Preparation.InstalledDraftSymbols);
  }

  // Dynamic trait dispatch selects the concrete unfinished override while retaining the trait declaration.
  [Fact]
  public async Task DiscoversDynamicOverrideDependency() {
    const string source = "module M { trait T { method Help(x: int) returns (y: int) } " +
      "class C extends T { method Help(x: int) returns (y: int) { assert false; } } " +
      "method Goal(c: T, x: int) returns (y: int) { y := c.Help(x); } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (c: T, x: int) { c := new C; x := 2; }";
    var prepared = await Prepare(source, [
      Draft("M.C.Help", "method {:pbt_draft \"M.C.Help\"} Help(x: int) returns (y: int) { y := x; }")
    ], generator);
    var program = await Parse(WithRuntime(prepared.Preparation.Sources));

    Assert.Equal(new[] { "M.C.Help" }, prepared.Preparation.InstalledDraftSymbols);
    Assert.Null(Method(program, "M.T.Help").Body);
  }

  // Instance constant initialization keeps its transitive function body in the selected runtime closure.
  [Fact]
  public async Task DiscoversConstantInitializerDependency() {
    const string source = "module M { function Initial(): int class Box { const Value: int := Initial() } " +
      "method Goal(box: Box, x: int) returns (y: int) { y := box.Value + x; } }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (box: Box, x: int) { box := new Box; x := 2; }";
    var prepared = await Prepare(source, [Draft("M.Initial", "function {:pbt_draft \"M.Initial\"} Initial(): int { 3 }")], generator);

    Assert.Equal(new[] { "M.Initial" }, prepared.Preparation.InstalledDraftSymbols);
  }

  // Calls introduced inside one authored proof draft discover another lemma even though runtime visibility erases both bodies.
  [Fact]
  public async Task DiscoversNewTransitiveProofLemmaCalls() {
    const string source = "module M { lemma FirstProof(x: int) lemma SecondProof(x: int) " +
      "function Value(x: int): int method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) ensures x >= 0 " +
      "{ x := 2; Sibling(x); } lemma Sibling(x: int) { FirstProof(x); }";
    var prepared = await Prepare(source, [
      Draft("M.FirstProof", "lemma {:pbt_draft \"M.FirstProof\"} FirstProof(x: int) { SecondProof(x); }"),
      Draft("M.SecondProof", "lemma {:pbt_draft \"M.SecondProof\"} SecondProof(x: int) { assert Value(x) == x; }"),
      Draft("M.Value", "function {:pbt_draft \"M.Value\"} Value(x: int): int { x }")
    ], generator, proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.FirstProof", "M.SecondProof", "M.Value" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    Assert.Same(prepared.Preparation, prepared.Runtime.Preparation);
    var independentlyResolved = await Runtime(prepared.Preparation);
    Assert.Equal(ContractRuntimeTypeEvidence.SourceSetHash(independentlyResolved.Sources),
      ContractRuntimeTypeEvidence.SourceSetHash(prepared.Runtime.RuntimeSources));
    Assert.Same(Method(prepared.Runtime.RuntimeProgram, "M.Goal"),
      ContractCallableSelector.SelectMethod(prepared.Runtime.RuntimeProgram, new("M.Goal"),
        requireConcreteReceiver: false));
    var authored = await Parse(WithRuntime(prepared.Preparation.Sources));
    Assert.Contains(Method(authored, "M.FirstProof").Body!.Descendants().OfType<CallStmt>(),
      call => ReferenceEquals(call.Method, Method(authored, "M.SecondProof")));
    var authenticated = await ContractGeneratorProof.AuthoredProofSourcesAsync(prepared.Preparation.Sources,
      prepared.Runtime.RuntimeSources, Options(), CancellationToken.None);
    Assert.NotNull(authenticated);
    Assert.Equal(ContractRuntimeTypeEvidence.SourceSetHash(WithRuntime(prepared.Preparation.Sources)),
      ContractRuntimeTypeEvidence.SourceSetHash(authenticated!));
  }

  // A proof statement directly in the goal contract is retained in the generator's installed postcondition.
  [Fact]
  public async Task DiscoversTargetContractProofDependency() {
    const string source = "module M { lemma ContractProof(x: int) " +
      "method Goal(x: int) requires (ContractProof(x); x >= 0) {} }";
    var prepared = await Prepare(source, [
      Draft("M.ContractProof", "lemma {:pbt_draft \"M.ContractProof\"} ContractProof(x: int) {}")
    ], proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.ContractProof" }, prepared.Preparation.InstalledDraftSymbols);
    var proof = await DirectProof(prepared.Preparation);
    var call = Assert.Single(proof.Generator.Ens.SelectMany(clause => clause.E.Descendants().OfType<CallStmt>()));
    Assert.Same(Method(proof.Program, "M.ContractProof"), call.Method);
    var argument = Assert.IsType<IdentifierExpr>(Assert.Single(call.Args).Resolved);
    Assert.Same(Assert.Single(proof.Generator.Outs), argument.Var);
  }

  // A valid authored postcondition proof call retains its generator-output binding inside the ordinary audited scope.
  [Fact]
  public async Task DiscoversGeneratorEnsuresContractProofDependency() {
    const string source = "module M { lemma ContractProof(x: int) method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) " +
      "ensures (ContractProof(x); x >= 0) { x := 2; }";
    var prepared = await Prepare(source, [
      Draft("M.ContractProof", "lemma {:pbt_draft \"M.ContractProof\"} ContractProof(x: int) {}")
    ], generator, proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.ContractProof" }, prepared.Preparation.InstalledDraftSymbols);
    var proof = await DirectProof(prepared.Preparation);
    var call = Assert.Single(proof.Generator.Ens.SelectMany(clause => clause.E.Descendants().OfType<CallStmt>()));
    Assert.Same(Method(proof.Program, "M.ContractProof"), call.Method);
    var formal = Assert.Single(proof.Generator.Outs);
    Assert.Same(formal, Assert.IsType<IdentifierExpr>(Assert.Single(call.Args).Resolved).Var);
    var proofGenerator = Method(proof.Program, "M.Generate");
    var raw = await Parse(proof.Sources, resolve: false);
    var random = ContractGeneratorProof.ExtractPinnedPbtRandomSource();
    Assert.Null(ContractGeneratorProofAudit.AuditRawProgram(raw, proof.Sources, proofGenerator.Origin.Uri,
      proofGenerator.Name, Method(proof.Program, "M.Goal").FullDafnyName, random));
    var scopes = ContractGeneratorProof.ProofScopes(proof.Program, proof.Sources, Method(proof.Program, "M.Goal"),
      proofGenerator, random);
    Assert.All(scopes, scope => Assert.Null(scope.Failure));
    Assert.Contains(scopes, scope => scope.ContainsDeclaration(call.Method));
  }

  // Generic proof-call bindings survive synthesis and remain inside the successful audited proof scope.
  [Fact]
  public async Task PreservesGenericGeneratorEnsuresProofCallTypeArgument() {
    const string source = "module M { lemma ContractProof<T>(x: int) method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) " +
      "ensures (ContractProof<bool>(x); x >= 0) { x := 2; }";
    var prepared = await Prepare(source, [
      Draft("M.ContractProof", "lemma {:pbt_draft \"M.ContractProof\"} ContractProof<T>(x: int) {}")
    ], generator, proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.ContractProof" }, prepared.Preparation.InstalledDraftSymbols);
    var proof = await DirectProof(prepared.Preparation);
    var call = Assert.Single(proof.Generator.Ens.SelectMany(clause => clause.E.Descendants().OfType<CallStmt>()));
    Assert.Same(Method(proof.Program, "M.ContractProof"), call.Method);
    Assert.True(Assert.Single(call.MethodSelect.TypeApplicationJustMember).IsBoolType);
    Assert.Same(Assert.Single(proof.Generator.Outs), Assert.IsType<IdentifierExpr>(Assert.Single(call.Args).Resolved).Var);
    var proofGenerator = Method(proof.Program, "M.Generate");
    var raw = await Parse(proof.Sources, resolve: false);
    var random = ContractGeneratorProof.ExtractPinnedPbtRandomSource();
    var failure = ContractGeneratorProofAudit.AuditRawProgram(raw, proof.Sources, proofGenerator.Origin.Uri,
      proofGenerator.Name, Method(proof.Program, "M.Goal").FullDafnyName, random);
    Assert.Null(failure);
    var originalSources = prepared.Preparation.Sources.Append(Snapshot("PbtRandom.dfy", random)).ToArray();
    var original = await Parse(originalSources, resolve: false);
    Assert.Null(ContractGeneratorProofAudit.AuditRawProgram(original, originalSources, proofGenerator.Origin.Uri,
      proofGenerator.Name, Method(proof.Program, "M.Goal").FullDafnyName, random));
    var scopes = ContractGeneratorProof.ProofScopes(proof.Program, proof.Sources, Method(proof.Program, "M.Goal"),
      proofGenerator, random);
    Assert.All(scopes, scope => Assert.Null(scope.Failure));
    Assert.Contains(scopes, scope => scope.ContainsDeclaration(call.Method));
  }

  // Unrelated generic runtime methods remain source-audited without entering the generator proof dependency scopes.
  [Fact]
  public async Task AllowsUnrelatedGenericRuntimeMethodsInRetainedProofSource() {
    const string source = "module M { method Relay<T>(x: T) returns (y: T) { y := x; } " +
      "method Unused() { var y := Relay<int>(0); } " +
      "method Goal(x: int) returns (y: int) requires x >= 0 ensures y == x }";
    var prepared = await Prepare(source, [
      Draft("M.Goal", "method {:pbt_draft \"M.Goal\"} Goal(x: int) returns (y: int) { y := Relay<int>(x); }")
    ], proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.Goal" }, prepared.Preparation.InstalledDraftSymbols);
    var proof = await DirectProof(prepared.Preparation);
    var goal = Method(proof.Program, "M.Goal");
    var relay = Method(proof.Program, "M.Relay");
    var unused = Method(proof.Program, "M.Unused");
    Assert.Single(goal.Req);
    Assert.Single(goal.Ens);
    Assert.Contains(goal.Body!.Descendants().OfType<CallStmt>(), call => call.Method == relay);
    Assert.Contains(unused.Body!.Descendants().OfType<CallStmt>(), call => call.Method == relay);
    var random = ContractGeneratorProof.ExtractPinnedPbtRandomSource();
    var raw = await Parse(proof.Sources, resolve: false);
    var proofGenerator = Method(proof.Program, "M.Generate");
    var failure = ContractGeneratorProofAudit.AuditRawProgram(raw, proof.Sources, proofGenerator.Origin.Uri,
      proofGenerator.Name, goal.FullDafnyName, random);
    Assert.Null(failure);
    var audit = ContractGeneratorProofAudit.BindResolved(proof.Program, proof.Sources, failure, random);
    var scopes = ContractGeneratorProof.ProofScopes(proof.Program, proof.Sources, goal, proofGenerator, random);
    Assert.All(scopes, scope => Assert.Null(scope.Failure));
    Assert.DoesNotContain(scopes, scope => scope.ContainsDeclaration(relay));
    Assert.True(audit.IsBoundTo(proof.Program, proof.Sources));
  }

  // Every retained ambient logical function remains a proof root, including its newly introduced proof-method calls.
  [Fact]
  public async Task PreservesAmbientLogicalProofRoots() {
    const string source = "module M { function Ambient(x: int): int lemma AmbientProof(x: int) " +
      "method Goal(x: int) requires x >= 0 {} }";
    var prepared = await Prepare(source, [
      Draft("M.Ambient", "function {:pbt_draft \"M.Ambient\"} Ambient(x: int): int { AmbientProof(x); x }"),
      Draft("M.AmbientProof", "lemma {:pbt_draft \"M.AmbientProof\"} AmbientProof(x: int) {}")
    ], proof: true);

    Assert.Null(prepared.ProofPreparationFailure);
    Assert.Equal(new[] { "M.Ambient", "M.AmbientProof" }, prepared.Preparation.InstalledDraftSymbols.OrderBy(symbol => symbol));
    var authoredSources = WithRuntime(prepared.Preparation.Sources);
    var authored = await Parse(authoredSources);
    var goal = Method(authored, "M.Goal");
    var generator = ContractRuntimeGeneratorSignature.Select(authored, goal, prepared.Preparation.GeneratorMethodName);
    var random = ContractGeneratorProof.ExtractPinnedPbtRandomSource();
    var build = ContractGeneratorProof.PrepareProofSources(authored, authoredSources, goal, generator, random, out var failure);
    Assert.Null(failure);
    Assert.NotNull(build);
    var proofProgram = await Parse(build!.Sources);
    var scopes = ContractGeneratorProof.ProofScopes(proofProgram, build.Sources, Method(proofProgram, "M.Goal"),
      Method(proofProgram, "M.Generate"), random);
    Assert.Contains(scopes, scope => scope.ContainsDeclaration(Method(proofProgram, "M.AmbientProof")));
  }

  // A visible mutable-field requirement stops proof preparation after the reusable runtime resolve.
  [Fact]
  public async Task RejectsVisibleHeapProofBeforeAuthoredPreparation() {
    const string source = "module M { class Cell { var value: int } const cell: Cell? " +
      "method Goal(x: int) requires cell == null || cell.value >= 0 {} }";
    var phases = new List<(string Phase, string State)>();
    var prepared = await Prepare(source, [], proof: true,
      phaseObserver: (phase, state) => phases.Add((phase, state)));
    var report = Assert.IsType<ContractGeneratorProofReport>(prepared.ProofPreparationFailure);

    Assert.Equal(ContractGeneratorProofStatus.Unsupported, report.Status);
    Assert.Contains("mutable heap fields", report.Diagnostics, StringComparison.Ordinal);
    Assert.Equal(1, phases.Count(phase => phase == ("resolve", "started")));
    Assert.Same(prepared.Preparation, prepared.Runtime.Preparation);
    Assert.Same(Method(prepared.Runtime.RuntimeProgram, "M.Goal"),
      ContractCallableSelector.SelectMethod(prepared.Runtime.RuntimeProgram, new("M.Goal"),
        requireConcreteReceiver: false));
  }

  // An instance receiver stops proof preparation after the reusable runtime resolve.
  [Fact]
  public async Task RejectsReceiverProofBeforeAuthoredPreparation() {
    const string source = "module M { class C { constructor() {} method Goal(x: int) requires x >= 0 {} } }";
    const string generator = "method {:pbt_generator \"M.C.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (receiver: C, x: int) { receiver := new C(); x := 0; }";
    var phases = new List<(string Phase, string State)>();
    var prepared = await Prepare(source, [], generator, proof: true, entry: new("M.C.Goal"),
      phaseObserver: (phase, state) => phases.Add((phase, state)));
    var report = Assert.IsType<ContractGeneratorProofReport>(prepared.ProofPreparationFailure);

    Assert.Equal(ContractGeneratorProofStatus.Unsupported, report.Status);
    Assert.Contains("receiver and heap proofs", report.Diagnostics, StringComparison.Ordinal);
    Assert.Equal(1, phases.Count(phase => phase == ("resolve", "started")));
    Assert.Same(prepared.Preparation, prepared.Runtime.Preparation);
  }

  // Cancellation reported by the final runtime resolve takes precedence over an early unsupported receiver result.
  [Fact]
  public async Task PreservesCancellationBeforeEarlyProofRejection() {
    const string source = "module M { class C { method Goal(x: int) requires x >= 0 {} } }";
    const string generator = "method {:pbt_generator \"M.C.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (receiver: C, x: int) { receiver := new C; x := 0; }";
    using var cancellation = new CancellationTokenSource();

    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Prepare(source, [], generator, proof: true,
      entry: new("M.C.Goal"), phaseObserver: (phase, state) => {
        if (phase == "resolve" && state == "completed") { cancellation.Cancel(); }
      }, cancellationToken: cancellation.Token));
  }

  // A heap edge hidden by runtime ghost-body erasure still reaches the authoritative authored proof check.
  [Fact]
  public async Task RetainsAuthoredHeapCheckAfterEarlyGatePasses() {
    const string source = "module M { class Cell { var value: int } const cell: Cell? " +
      "function Read(): int reads cell { if cell == null then 0 else cell.value } " +
      "lemma Proof() { assert Read() >= 0; } function Check(): bool { Proof(); true } " +
      "method Goal(x: int) requires Check() {} }";
    var phases = new List<(string Phase, string State)>();
    var prepared = await Prepare(source, [], proof: true,
      phaseObserver: (phase, state) => phases.Add((phase, state)));
    var report = Assert.IsType<ContractGeneratorProofReport>(prepared.ProofPreparationFailure);

    Assert.Equal(ContractGeneratorProofStatus.Unsupported, report.Status);
    Assert.Contains("requirement functions", report.Diagnostics, StringComparison.Ordinal);
    Assert.Equal(2, phases.Count(phase => phase == ("resolve", "started")));
    Assert.Same(prepared.Preparation, prepared.Runtime.Preparation);
  }

  // Invalid proof-only syntax produces explicit failure evidence while the valid runtime retains its entry condition.
  [Fact]
  public async Task RollsBackMalformedProofOnlyPacketAndKeepsEntryChecks() {
    const string source = "module M { lemma Proof(x: int) method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) ensures x >= 0 " +
      "{ x := 2; Proof(x); }";
    var prepared = await Prepare(source, [Draft("M.Proof", "lemma invalid (")], generator, proof: true);
    var report = Assert.IsType<ContractGeneratorProofReport>(prepared.ProofPreparationFailure);

    Assert.Equal(ContractGeneratorProofStatus.Failed, report.Status);
    Assert.Contains("M.Proof.draft.dfy", report.Diagnostics, StringComparison.Ordinal);
    Assert.Empty(report.RequiredNativeChecks);
    Assert.Empty(report.CoveredNativeChecks);
    Assert.Null(report.VerifiedCertificate);
    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    var goal = Method(prepared.Runtime.RuntimeProgram, "M.Goal");
    var generated = ContractRuntimeGeneratorSignature.Select(prepared.Runtime.RuntimeProgram, goal,
      prepared.Preparation.GeneratorMethodName);
    var transformed = new ContractRuntimeObligationTransformer(prepared.Runtime.RuntimeProgram,
      prepared.Runtime.RuntimeSources, goal,
      prepared.Preparation.SourceMap, generatorProof: report, selectedGenerator: generated).Transform();
    Assert.False(transformed.EntryRequiresOmitted);
    Assert.Contains(transformed.Clauses, clause => clause.Obligation.Kind == ContractRuntimeObligationKind.EntryPrecondition && !clause.TypeConstraint);
  }

  // An unrelated runtime function is still proof-in-scope, so its malformed packet fails the proof rather than disappearing.
  [Fact]
  public async Task ReportsMalformedAmbientProofPacketWithoutBlockingRuntime() {
    const string source = "module M { function Ambient(x: int): int method Goal(x: int) requires x >= 0 {} }";
    var prepared = await Prepare(source, [Draft("M.Ambient", "function invalid (")], proof: true);

    Assert.Equal(ContractGeneratorProofStatus.Failed, prepared.ProofPreparationFailure!.Status);
    Assert.Contains("M.Ambient.draft.dfy", prepared.ProofPreparationFailure.Diagnostics, StringComparison.Ordinal);
    Assert.Null(prepared.ProofPreparationFailure.VerifiedCertificate);
    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    await Runtime(prepared.Preparation);
  }

  // A selected proof body's unresolved newly introduced call fails after authored resolution and restores the runtime snapshot.
  [Fact]
  public async Task ReportsUnresolvedProofOnlyBodyAtDraftOrigin() {
    const string source = "module M { lemma Proof(x: int) method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) ensures x >= 0 " +
      "{ x := 2; Proof(x); }";
    var prepared = await Prepare(source, [
      Draft("M.Proof", "lemma {:pbt_draft \"M.Proof\"} Proof(x: int) { Undefined(x); }")
    ], generator, proof: true);

    Assert.Equal(ContractGeneratorProofStatus.Failed, prepared.ProofPreparationFailure!.Status);
    Assert.Contains("M.Proof.draft.dfy", prepared.ProofPreparationFailure.Diagnostics, StringComparison.Ordinal);
    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    Assert.Null(prepared.ProofPreparationFailure.VerifiedCertificate);
  }

  // A proof-only sibling collision with a generator helper fails its packet transaction and preserves the runtime snapshot.
  [Fact]
  public async Task RollsBackProofHelperCollisionWithGeneratorSibling() {
    const string source = "module M { lemma Proof(x: int) method Goal(x: int) requires x >= 0 {} }";
    const string generator = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) returns (x: int) ensures x >= 0 " +
      "{ x := 2; Proof(x); } lemma Existing() {}";
    var prepared = await Prepare(source, [
      Draft("M.Proof", "lemma {:pbt_draft \"M.Proof\"} Proof(x: int) {} lemma Existing() {}")
    ], generator, proof: true);

    Assert.Equal(ContractGeneratorProofStatus.Failed, prepared.ProofPreparationFailure!.Status);
    Assert.Contains("M.Proof.draft.dfy", prepared.ProofPreparationFailure.Diagnostics, StringComparison.Ordinal);
    Assert.Contains("collides", prepared.ProofPreparationFailure.Diagnostics, StringComparison.Ordinal);
    Assert.Empty(prepared.Preparation.InstalledDraftSymbols);
    await Runtime(prepared.Preparation);
  }
}
