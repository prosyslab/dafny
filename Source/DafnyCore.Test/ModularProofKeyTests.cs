using System.CommandLine;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Keys = Microsoft.Dafny.DefinitionAnalysis.ModularProofKeys;
using Program = Microsoft.Dafny.Program;

namespace DafnyCore.Test;

/// <summary>
/// Modular (schema 2 and later) proof inputs: per-implementation keys over the lifted Boogie program and the pruned solver input.
/// Translation and splitting are real; no solver runs and nothing touches the filesystem.
/// </summary>
[Collection("Proof input translation")]
public class ModularProofKeyTests {
  private const string Toolchain = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
  private const string Path = "/workspace/tmp/modular-proof-keys/source.dfy";

  // A fixture with calls, functions, opaque reveals, datatypes, quantifiers, lambdas and loops.
  private const string Fixture = """
    module M {
      datatype Shape = Dot | Box(w: nat, h: nat)
      function Area(s: Shape): nat { match s case Dot => 0 case Box(w, h) => w * h }
      opaque function Twice(x: int): int { 2 * x }
      predicate AllPositive(xs: seq<int>) { forall i :: 0 <= i < |xs| ==> xs[i] > 0 }
      function Count(xs: seq<int>, n: nat): nat { |set q: nat | q < n && q < |xs| && xs[q] > 0| }
      lemma TwiceGrows(x: nat) ensures Twice(x) >= x { reveal Twice(); }
      method Scale(s: Shape, k: nat) returns (r: Shape)
        requires s.Box?
        ensures r.Box? && Area(r) == Area(s) * k * k
      {
        r := Box(s.w * k, s.h * k);
      }
      method Sum(xs: seq<int>) returns (t: int)
        requires AllPositive(xs)
        ensures |xs| > 0 ==> t > 0
      {
        t := 0;
        var i := 0;
        while i < |xs|
          invariant 0 <= i <= |xs|
          invariant i > 0 ==> t > 0
        {
          t := t + xs[i];
          i := i + 1;
        }
      }
      method Use(x: nat, xs: seq<int>) returns (y: int)
        requires AllPositive(xs)
      {
        TwiceGrows(x);
        var s := Scale(Box(1, 2), 3);
        assert Area(s) == 18;
        var f := (z: int) => z + x;
        assert f(1) == x + 1;
        assert Count(xs, 0) == 0;
        y := Sum(xs);
      }
    }
    """;

  // Every split's declared solver input is a subsequence of the computed live set (superset, order kept).
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task LiveSetContainsEverySplitsPrunedDeclarations(bool isolate) {
    var checkedSplits = await AssertSupersets(Fixture, isolate);
    Assert.True(checkedSplits > 5, $"only {checkedSplits} splits");
  }

  // The superset property also holds for quantifier-heavy helpers in isolation mode.
  [Fact]
  public async Task QuantifiedHelperSplitsAreContained() {
    var source = """
      module Q {
        lemma GeneratorRange(prefix: seq<int>, z: int)
          requires forall i: int :: 0 <= i < |prefix| ==> 0 <= prefix[i] <= 4
          requires 0 <= z <= 4
          ensures forall i: int :: 0 <= i < |prefix + [z]| ==> 0 <= (prefix + [z])[i] <= 4
        {
          forall i: int | 0 <= i < |prefix + [z]|
            ensures 0 <= (prefix + [z])[i] <= 4
          {
            if i < |prefix| { assert (prefix + [z])[i] == prefix[i]; } else { assert (prefix + [z])[i] == z; }
          }
        }
      }
      """;
    Assert.True(await AssertSupersets(source, true) > 0);
  }

  // Boogie's axiom visitor reads earlier quantifier positions (they matter for {:include_dep} axioms). Computing
  // keys must leave the engine's own dependency graph equal to a one-shot run, or the engine could declare an
  // axiom the key never saw.
  [Fact]
  public async Task KeyComputationLeavesTheEngineDependencyGraphUnchanged() {
    const string text = """
      function F(x: int): bool;
      function G(x: int): bool;
      axiom {:include_dep} !(exists x: int :: {F(x)} G(x));
      procedure P(y: int);
      implementation P(y: int) { assert G(y); }
      """;
    var options = BoogieOptions();
    var program = ParseBoogie(text, options);
    var keys = Keys.Compute(options, program);
    var live = Assert.Single(keys.Implementations.Values).Live;
    Assert.DoesNotContain(live, declaration => declaration is Bpl.Axiom);
    using var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(options);
    var task = Assert.Single(await engine.GetVerificationTasks(program));
    Assert.DoesNotContain(task.Split.PrunedDeclarations, declaration => declaration is Bpl.Axiom);
  }

  // Pins the Boogie behaviour above: a second graph computation over the same objects reaches the axiom.
  [Fact]
  public void BoogieDependencyGraphDependsOnEarlierComputations() {
    const string text = """
      function F(x: int): bool;
      function G(x: int): bool;
      axiom {:include_dep} !(exists x: int :: {F(x)} G(x));
      procedure P(y: int);
      implementation P(y: int) { assert G(y); }
      """;
    var options = BoogieOptions();
    var program = ParseBoogie(text, options);
    var blocks = program.Implementations.Single().Blocks;
    bool AxiomLive() {
      program.DeclarationDependencies = Bpl.Pruner.ComputeDeclarationDependencies(options, program);
      return Bpl.Pruner.GetLiveDeclarations(options, program, blocks).LiveDeclarations.Any(d => d is Bpl.Axiom);
    }
    Assert.False(AxiomLive());
    Assert.True(AxiomLive());
  }

  // Each of these edits changes what the solver may see for A, so A's key must change (a native cache miss).
  [Theory]
  [InlineData("callee-requires",
    "method B(x: int) returns (y: int) requires x > 0 ensures y > x { y := x + 1; }\nmethod A(x: int) returns (y: int) requires x > 0 { y := B(x); }",
    "requires x > 0 ensures", "requires x > -1 ensures")]
  [InlineData("callee-ensures",
    "method B(x: int) returns (y: int) ensures y > x { y := x + 1; }\nmethod A(x: int) returns (y: int) { y := B(x); }",
    "ensures y > x", "ensures y >= x")]
  [InlineData("callee-where-clause",
    "method B(x: int) returns (z: int) { z := 0; }\nmethod A(x: int) returns (y: int) { y := B(x); }",
    "returns (z: int)", "returns (z: nat)")]
  [InlineData("visible-function-body",
    "function F(x: int): int { x + 1 }\nmethod A(x: int) { assert F(x) > x; }", "x + 1", "x + 2")]
  [InlineData("revealed-opaque-body",
    "opaque function F(x: int): int { x + 1 }\nmethod A(x: int) { reveal F(); assert F(x) > x; }", "x + 1", "x + 2")]
  [InlineData("unrevealed-opaque-body-conservative",
    "opaque function F(x: int): int { x + 1 }\nmethod A(x: int) { assert F(x) == F(x); }", "x + 1", "x + 2")]
  [InlineData("reveal-added",
    "opaque function F(x: int): int { x + 1 }\nmethod A(x: int) { assert F(x) == F(x); }", "{ assert", "{ reveal F(); assert")]
  [InlineData("opacity",
    "function F(x: int): int { x + 1 }\nmethod A(x: int) { assert F(x) == F(x); }", "function F", "opaque function F")]
  [InlineData("datatype-constructor",
    "datatype D = P | Q\nmethod A(d: D) { assert d.P? || d.Q? || true; }", "P | Q", "P | Q | R")]
  [InlineData("datatype-constructor-unnamed",
    "datatype D = P | Q\nmethod A(d: D) { assert d == d; }", "P | Q", "P | Q | R")]
  [InlineData("axiom-function-contract",
    "function {:axiom} F(x: int): int ensures F(x) > x\nmethod A(x: int) { assert F(x) > x; }", "F(x) > x\n", "F(x) >= x\n")]
  [InlineData("axiom-lemma-contract",
    "lemma {:axiom} L(x: int) ensures x * x >= 0\nmethod A(x: int) { L(x); assert x * x >= 0; }", "ensures x * x >= 0", "ensures x * x > -1")]
  [InlineData("method-isolate-assertions",
    "method A(x: int) { assert x == x; }", "method A", "method {:isolate_assertions} A")]
  [InlineData("method-split-on-every-assert",
    "method A(x: int) { assert x == x; }", "method A", "method {:vcs_split_on_every_assert} A")]
  [InlineData("method-time-limit",
    "method A(x: int) { assert x == x; }", "method A", "method {:timeLimit 7} A")]
  [InlineData("method-resource-limit",
    "method A(x: int) { assert x == x; }", "method A", "method {:rlimit 100} A")]
  public async Task SolverInputEditsChangeTheKey(string name, string source, string from, string to) {
    var edited = source.Replace(from, to);
    Assert.NotEqual(source, edited);
    var before = await Inputs(source);
    var after = await Inputs(edited);
    Assert.True(Sha(before, "A") != Sha(after, "A"), name);
  }

  // Library sources are not verified, but their function and axiom declarations are solver input.
  [Theory]
  [InlineData("module Lib { function F(x: int): int { x + 1 } }", "x + 1", "x + 2")]
  [InlineData("module Lib { function F(x: int): int lemma {:axiom} Ax(x: int) ensures F(x) > x }", "F(x) > x", "F(x) >= x")]
  public async Task LibrarySourceChangesTheKey(string library, string from, string to) {
    const string user = "module User { import Lib method A(x: int) { Lib.Ax(x); assert Lib.F(x) > x; } }";
    var source = library.Contains("Ax") ? user : user.Replace("Lib.Ax(x); ", "");
    var before = await LibraryInputs(source, library);
    var after = await LibraryInputs(source, library.Replace(from, to));
    Assert.DoesNotContain(before.Definitions, definition => definition.SourcePath == LibraryPath);
    Assert.NotEqual(Sha(before, "User.A"), Sha(after, "User.A"));
    Assert.Contains(Assert.Single(before.Definitions, definition => definition.FullName == "User.A").ClosureOrigins!.Sources,
      origin => origin.SourcePath == LibraryPath);
  }

  // Effective options, seed and limits are part of every key.
  [Theory]
  [InlineData("seed")]
  [InlineData("stable-seed")]
  [InlineData("isolate")]
  [InlineData("time-limit")]
  [InlineData("resource-limit")]
  public async Task OptionChangesChangeTheKey(string option) {
    const string source = "method A(x: int) { assert x == x; }";
    var before = await Inputs(source);
    var after = await Inputs(source, options => {
      switch (option) {
        case "seed":
          options.RandomSeed = 42;
          break;
        case "stable-seed":
          Set(options, BoogieOptionBag.BoogieArguments, new[] { "/randomSeed:42" }.AsEnumerable());
          Assert.Equal(42, options.StableRandomSeed);
          break;
        case "isolate":
          Set(options, BoogieOptionBag.IsolateAssertions, true);
          break;
        case "time-limit":
          Set(options, BoogieOptionBag.VerificationTimeLimit, 7U);
          break;
        default:
          Set(options, BoogieOptionBag.SolverResourceLimit, 1000U);
          break;
      }
    });
    Assert.NotEqual(before.OptionsSha256, after.OptionsSha256);
    Assert.NotEqual(Sha(before, "A"), Sha(after, "A"));
  }

  // The toolchain binds the producer and the solver binary; either change misses, and an unknown solver
  // yields no toolchain (and so no proof inputs).
  [Fact]
  public async Task ToolchainAndSolverIdentityChangeTheKey() {
    const string source = "method A(x: int) { assert x == x; }";
    var solverA = DefinitionAnalysis.ProofToolchainHash("assemblies", "z3:a");
    var solverB = DefinitionAnalysis.ProofToolchainHash("assemblies", "z3:b");
    Assert.NotNull(solverA);
    Assert.NotEqual(solverA, solverB);
    Assert.NotEqual(solverA, DefinitionAnalysis.ProofToolchainHash("other-assemblies", "z3:a"));
    Assert.Null(DefinitionAnalysis.ProofToolchainHash("assemblies", null));
    Assert.Null(DefinitionAnalysis.ProofToolchainHash(null, "z3:a"));
    var before = await Inputs(source, toolchain: solverA!);
    var after = await Inputs(source, toolchain: solverB!);
    Assert.NotEqual(Sha(before, "A"), Sha(after, "A"));
  }

  // The hashed solver is the one that runs: one explicit path (repeated is fine) is used; several distinct paths,
  // a missing file or a non-Z3 solver give no identity. An existing file stands in for the executable.
  [Fact]
  public void SolverIdentityRequiresOneResolvableZ3() {
    var standIn = typeof(ModularProofKeyTests).Assembly.Location;
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ProverOptions.Add("PROVER_PATH=" + standIn);
    options.ProverOptions.Add("PROVER_PATH=" + standIn);
    Assert.Equal(standIn, options.ResolveZ3ExecutablePath());
    options.ProverOptions.Add("PROVER_PATH=" + typeof(DafnyOptions).Assembly.Location);
    Assert.Null(options.ResolveZ3ExecutablePath());
    Assert.Null(DefinitionAnalysis.ProofToolchainIdentity(options));
    var missing = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    missing.ProverOptions.Add("PROVER_PATH=/workspace/tmp/modular-proof-keys/missing-z3");
    Assert.Null(missing.ResolveZ3ExecutablePath());
    Assert.Null(DefinitionAnalysis.ProofToolchainIdentity(missing));
    missing.ProverOptions.Add("SOLVER=cvc5");
    Assert.Null(DefinitionAnalysis.ProofToolchainIdentity(missing));
  }

  // Boogie also reads PROVER_PATH:p and a bare PROVER_PATH; the resolution sees them, so a path the options hash
  // drops can never run unseen by the toolchain identity.
  [Fact]
  public void SolverIdentitySeesEveryProverPathForm() {
    var standIn = typeof(ModularProofKeyTests).Assembly.Location;
    var colon = DafnyOptionsFor(options => options.ProverOptions.Add("PROVER_PATH:" + standIn));
    Assert.Equal(standIn, colon.ResolveZ3ExecutablePath());
    var conflicting = DafnyOptionsFor(options => {
      options.ProverOptions.Add("PROVER_PATH=" + standIn);
      options.ProverOptions.Add("PROVER_PATH:" + typeof(Microsoft.BaseTypes.BigNum).Assembly.Location);
    });
    Assert.Null(conflicting.ResolveZ3ExecutablePath());
    var bare = DafnyOptionsFor(options => options.ProverOptions.Add("PROVER_PATH"));
    Assert.Null(bare.ResolveZ3ExecutablePath());
    Assert.Null(DafnyOptions.ProverPathValue("PROVER_NAME=z3"));
    Assert.Null(DafnyOptions.ProverPathValue("PROVER_PATHS=x"));
  }

  // Options that differ only in where the solver, its log or its inspector live keep the options hash, the
  // definition hash and the bound native checksum, so certificates and cached results move between install paths.
  [Theory]
  [InlineData("prover-path")]
  [InlineData("prover-path-colon")]
  [InlineData("solver-path")]
  [InlineData("solver-option")]
  [InlineData("logs")]
  public async Task SolverLocationDoesNotChangeTheKey(string change) {
    const string source = "method A(x: int) { assert x == x; }";
    const string implementation = "Impl$$_module.__default.A";
    void First(DafnyOptions options) => options.ProverOptions.Add("PROVER_PATH=/opt/first/Binaries/z3/bin/z3-4.12.1");
    void Second(DafnyOptions options) {
      switch (change) {
        case "prover-path":
          options.ProverOptions.Add("PROVER_PATH=/home/second/copy/Binaries/z3/bin/z3-4.12.1");
          break;
        case "prover-path-colon":
          options.ProverOptions.Add("PROVER_PATH:/home/second/z3");
          break;
        case "solver-path":
          Set(options, BoogieOptionBag.SolverPath, new FileInfo("/home/second/z3"));
          break;
        case "solver-option":
          Set(options, BoogieOptionBag.SolverOption, new List<string> { "PROVER_PATH=/home/second/z3", "LOG_FILE=/home/second/@PROC@.smt2" });
          break;
        default:
          First(options);
          options.ProverOptions.Add("LOG_FILE=/home/second/query.smt2");
          options.ProverOptions.Add("INSPECTOR=/home/second/inspector");
          Set(options, BoogieOptionBag.SolverLog, "/home/second/solver.smt2");
          break;
      }
    }
    var before = await Inputs(source, First);
    var after = await Inputs(source, Second);
    Assert.Equal(before.OptionsSha256, after.OptionsSha256);
    Assert.Equal(Sha(before, "A"), Sha(after, "A"));
    Assert.Equal((await Checksums(source, configure: First))[implementation],
      (await Checksums(source, configure: Second))[implementation]);
  }

  // Semantic solver options still partition the key; only location options are dropped.
  [Fact]
  public async Task SemanticSolverOptionChangesTheKey() {
    const string source = "method A(x: int) { assert x == x; }";
    var before = await Inputs(source);
    var after = await Inputs(source, options => options.ProverOptions.Add("O:smt.qi.eager_threshold=100"));
    Assert.NotEqual(before.OptionsSha256, after.OptionsSha256);
    Assert.NotEqual(Sha(before, "A"), Sha(after, "A"));
  }

  // A solver binary is identified by its bytes in the toolchain: equal content at another path keeps it, other content
  // changes it, and the proof options never see the path. Existing files stand in; content is injected, except for
  // the last check, where two real files with different bytes give different toolchains.
  [Fact]
  public void SolverBinaryIsIdentifiedByContent() {
    var standIn = typeof(ModularProofKeyTests).Assembly.Location;
    var other = typeof(Microsoft.BaseTypes.BigNum).Assembly.Location;
    DafnyOptions WithSolver(string path) => DafnyOptionsFor(options => options.ProverOptions.Add("PROVER_PATH=" + path));
    var (first, moved) = (WithSolver(standIn), WithSolver(other));
    string? Toolchain(DafnyOptions options, string content) => DefinitionAnalysis.ProofToolchainIdentity(options, _ => content);
    Assert.Equal(DefinitionAnalysis.ProofOptionsHash(first), DefinitionAnalysis.ProofOptionsHash(moved));
    Assert.NotNull(Toolchain(first, "bytes"));
    Assert.Equal(Toolchain(first, "bytes"), Toolchain(moved, "bytes"));
    Assert.NotEqual(Toolchain(first, "bytes"), Toolchain(moved, "other-bytes"));
    Assert.NotEqual(DefinitionAnalysis.ProofToolchainIdentity(first), DefinitionAnalysis.ProofToolchainIdentity(moved));
  }

  // The context that owns an engine binds each solver by path and by content (the verifier's fake-solver case: equal
  // bytes at another path must not reuse an engine that starts the first path). Proof options stay path-free.
  // Content hashes are injected; nothing is read.
  [Fact]
  public void ContextIdentityBindsSolverPathAndContent() {
    DafnyOptions With(params string[] paths) => DafnyOptionsFor(options => {
      foreach (var path in paths) {
        options.ProverOptions.Add("PROVER_PATH=" + path);
      }
    });
    string Identity(DafnyOptions options, string content = "equal-bytes") =>
      DefinitionAnalysis.ContextOptionsIdentity(options, _ => content);
    var (a, b) = (With("/opt/a/z3"), With("/opt/b/z3"));
    Assert.Equal(DefinitionAnalysis.ProofOptionsHash(a), DefinitionAnalysis.ProofOptionsHash(b));
    Assert.NotEqual(Identity(a), Identity(b));
    Assert.NotEqual(Identity(a), Identity(a, "other-bytes"));
    Assert.NotEqual(Identity(a), DefinitionAnalysis.ContextOptionsIdentity(a, _ => null));
    // One solver given twice (--solver-path and solver processing both add it) is the same solver.
    Assert.Equal(Identity(a), Identity(With("/opt/a/z3", "/opt/a/z3")));
    // Boogie starts the last entry, so lists that end differently never share a context.
    Assert.NotEqual(Identity(With("/opt/a/z3", "/opt/b/z3")), Identity(With("/opt/a/z3", "/opt/b/z3", "/opt/a/z3")));
    // Relative or unnormalized paths are never read: the started file need not be the read one.
    var read = new List<string>();
    foreach (var inexact in new[] { "z3/bin/z3", "/opt/a/./z3", "/opt/link/../z3" }) {
      Assert.NotEqual(Identity(a), DefinitionAnalysis.ContextOptionsIdentity(With(inexact), path => {
        read.Add(path);
        return "equal-bytes";
      }));
    }
    Assert.Empty(read);
  }

  // A relative or unnormalized solver path gives no solver identity (no proof inputs), even when the file exists: the
  // process start tries the executable's directory first for a relative path and resolves ".." after symbolic links,
  // while file reads resolve against the current directory and collapse ".." lexically.
  [Fact]
  public void InexactSolverPathHasNoIdentity() {
    var standIn = typeof(ModularProofKeyTests).Assembly.Location;
    var directory = System.IO.Path.GetDirectoryName(standIn)!;
    var relative = System.IO.Path.GetRelativePath(Directory.GetCurrentDirectory(), standIn);
    var dotted = System.IO.Path.Combine(directory, ".", System.IO.Path.GetFileName(standIn));
    var parent = System.IO.Path.Combine(directory, "..", System.IO.Path.GetFileName(directory), System.IO.Path.GetFileName(standIn));
    foreach (var inexact in new[] { relative, dotted, parent }) {
      Assert.True(File.Exists(inexact), inexact);
      Assert.False(DafnyOptions.IsExactSolverPath(inexact), inexact);
      var options = DafnyOptionsFor(options => options.ProverOptions.Add("PROVER_PATH=" + inexact));
      Assert.Null(options.ResolveZ3ExecutablePath());
      Assert.Null(DefinitionAnalysis.ProofToolchainIdentity(options));
    }
    var absolute = DafnyOptionsFor(options => options.ProverOptions.Add("PROVER_PATH=" + standIn));
    Assert.Equal(standIn, absolute.ResolveZ3ExecutablePath());
  }

  // Every Boogie and Dafny assembly the verifier loads is part of the toolchain identity, so changing any one of them
  // (SMT emission, abstract interpretation, ...) changes it; order and directories do not. Content is injected.
  [Fact]
  public void ToolchainCoversEveryBoogieAndDafnyAssembly() {
    var files = DefinitionAnalysis.ToolchainAssemblyFiles();
    Assert.NotNull(files);
    var names = files!.Select(file => file.Name).ToHashSet();
    foreach (var required in new[] {
               "DafnyCore.dll", "Boogie.Core.dll", "Boogie.ExecutionEngine.dll", "Boogie.VCExpr.dll",
               "Boogie.VCGeneration.dll", "Boogie.BaseTypes.dll", "Boogie.Provers.SMTLib.dll",
               "Boogie.AbstractInterpretation.dll", "Boogie.Graph.dll", "Boogie.CodeContractsExtender.dll",
               "Boogie.Houdini.dll", "Boogie.Concurrency.dll", "Boogie.Model.dll"
             }) {
      Assert.Contains(required, names);
    }
    string Content(string path) => "bytes-of-" + System.IO.Path.GetFileName(path);
    var baseline = DefinitionAnalysis.ToolchainAssemblyHash(files, Content);
    Assert.NotNull(baseline);
    foreach (var file in files) {
      Assert.NotEqual(baseline, DefinitionAnalysis.ToolchainAssemblyHash(files,
        path => path == file.Path ? "changed" : Content(path)));
    }
    Assert.Equal(baseline, DefinitionAnalysis.ToolchainAssemblyHash(files.Reverse(), Content));
    Assert.Equal(baseline, DefinitionAnalysis.ToolchainAssemblyHash(
      files.Select(file => (file.Name, "/elsewhere/install/" + file.Name)), Content));
    Assert.Null(DefinitionAnalysis.ToolchainAssemblyHash(files, _ => null));
  }

  // A file rewritten in place with the same size and write time (cp -p, touch -r) is read again because its change
  // time moved; an unchanged stamp is served from the cache, and a just-changed file is not cached. Stamps and reads
  // are injected for an existing stand-in path.
  [Fact]
  public void ToolFileHashFollowsInPlaceReplacement() {
    var path = typeof(ModularProofKeyTests).Assembly.Location;
    var written = new DateTime(2026, 1, 1, 0, 0, 0, DateTimeKind.Utc);
    var stamp = new DefinitionAnalysis.FileStamp(100, written, written, "8:1:42");
    var content = "first";
    var reads = 0;
    var now = written.AddMinutes(1);
    var hashes = new DefinitionAnalysis.ToolFileHashes(_ => stamp, _ => {
      reads++;
      return content;
    }, () => now);
    Assert.Equal("first", hashes.Hash(path));
    Assert.Equal("first", hashes.Hash(path));
    Assert.Equal(1, reads);
    content = "second";
    stamp = stamp with { Changed = written.AddSeconds(30) };
    Assert.Equal("second", hashes.Hash(path));
    content = "third";
    stamp = stamp with { Node = "8:1:43" };
    Assert.Equal("third", hashes.Hash(path));
    Assert.Equal(3, reads);
    stamp = stamp with { Changed = now.AddSeconds(-1) };
    hashes.Hash(path);
    hashes.Hash(path);
    Assert.Equal(5, reads);
  }

  // On Linux the real stamp carries the device and inode, so the change-time check is active.
  [Fact]
  public void ToolFileStampHasInodeOnLinux() {
    var stamp = DefinitionAnalysis.ToolFileHashes.ReadStamp(typeof(ModularProofKeyTests).Assembly.Location);
    Assert.NotNull(stamp);
    Assert.Equal(OperatingSystem.IsLinux(), stamp!.Node != null);
  }

  // A solver plugin enters the options hash by its bytes, not its path. The binding is not applied (it would load
  // the plugin); the effective option value is what the hash reads.
  [Fact]
  public void SolverPluginIsIdentifiedByContent() {
    var standIn = typeof(ModularProofKeyTests).Assembly.Location;
    var alias = System.IO.Path.Combine(System.IO.Path.GetDirectoryName(standIn)!, ".", System.IO.Path.GetFileName(standIn));
    string WithPlugin(string? path) => DefinitionAnalysis.ProofOptionsHash(DafnyOptionsFor(options => {
      if (path != null) {
        options.Set(BoogieOptionBag.SolverPlugin, path);
      }
    }));
    Assert.Equal(WithPlugin(standIn), WithPlugin(alias));
    Assert.NotEqual(WithPlugin(standIn), WithPlugin(typeof(Microsoft.BaseTypes.BigNum).Assembly.Location));
    Assert.NotEqual(WithPlugin(null), WithPlugin(standIn));
  }

  // No option whose value names a file or directory enters the options hash. A new path-typed option must be
  // represented by content (toolchain identity, translated declarations) or excluded as a destination.
  [Fact]
  public void ProofOptionsHaveNoPathTypedArgument() {
    static bool PathTyped(System.Type type) => typeof(FileSystemInfo).IsAssignableFrom(type) ||
      type.IsGenericType && type.GetGenericArguments().Any(PathTyped);
    Assert.Empty(DefinitionAnalysis.ProofOptionArguments.Where(option => PathTyped(option.ValueType)).Select(option => option.Name));
  }

  // Edits outside what the solver can see for A keep A's key (a native cache hit after an unrelated merge).
  [Theory]
  [InlineData("position-shift", "", "\n\n// moved down\n")]
  [InlineData("whitespace", "{ y := B(x); }", "{\n\n   y :=   B(x);\n}")]
  [InlineData("unrelated-function", "", "function U(x: int): int { x * 3 }\n")]
  [InlineData("unrelated-lemma-with-assertions", "", "lemma U(x: int) ensures x * 2 == x + x { assert x * 2 == x + x; }\n")]
  [InlineData("callee-body", "{ y := x + 1; }", "{ y := x + 2; assert y > x; }")]
  [InlineData("unused-helper-body", "function H(x: int): int { x }", "function H(x: int): int { x + 7 }")]
  public async Task UnrelatedEditsKeepTheKey(string name, string from, string to) {
    const string source = """
      function H(x: int): int { x }
      method B(x: int) returns (y: int) ensures y > x { y := x + 1; }
      method A(x: int) returns (y: int) ensures y > x { y := B(x); }
      """;
    var edited = from.Length == 0 ? to + source : source.Replace(from, to);
    Assert.NotEqual(source, edited);
    var before = await Inputs(source);
    var after = await Inputs(edited);
    Assert.True(Sha(before, "A") == Sha(after, "A"), name);
  }

  // An unrelated lambda lifted earlier renumbers the target's lifted lambda; the key does not change.
  [Fact]
  public void LambdaRenumberingKeepsTheKey() {
    const string target = """
      function F(m: [int]bool): int;
      procedure P(n: int) returns (r: int);
      implementation P(n: int) returns (r: int) { r := F((lambda q: int :: q < n)); assert r == F((lambda q: int :: q < n)); }
      """;
    const string earlier = """
      procedure Q(n: int) returns (r: int);
      implementation Q(n: int) returns (r: int) { r := F((lambda q: int :: q > n + 5)); }
      """;
    var (before, beforeLive) = KeyOf(target, "P");
    var (after, afterLive) = KeyOf(target.Replace("procedure P", earlier + "procedure P"), "P");
    Assert.Equal(before, after);
    // The counter-generated name did change, so the content-derived naming is what keeps the key.
    Assert.NotEqual(LambdaName(beforeLive), LambdaName(afterLive));
    static string LambdaName(IReadOnlyList<Bpl.Declaration> live) =>
      Assert.Single(live.OfType<Bpl.Function>(), function => function.Name.StartsWith("lambda#")).Name;
  }

  // A Dafny lambda lifts into a body function plus helper functions that every one-argument lambda shares. An
  // earlier unrelated lambda lifts the shared helpers first and moves the target's functions in program order; the
  // order-insensitive key still hits.
  [Fact]
  public async Task EarlierDafnyLambdaKeepsTheKey() {
    const string source = "method A(x: int) { var f := (z: int) => z + x; assert f(1) == x + 1; }";
    const string earlier = "method U(x: int) { var g := (z: int) => z * x; assert g(1) == x; }\n";
    Assert.Equal(Sha(await Inputs(source), "A"), Sha(await Inputs(earlier + source), "A"));
    Assert.Equal(Sha(await Inputs(source), "A"), Sha(await Inputs(source + "\n" + earlier), "A"));
  }

  // Per-implementation Boogie attributes that steer the solver are in the implementation text.
  [Theory]
  [InlineData("{:isolate_assertions}")]
  [InlineData("{:vcs_split_on_every_assert}")]
  [InlineData("{:timeLimit 7}")]
  [InlineData("{:rlimit 100}")]
  public void ImplementationSolverAttributesChangeTheKey(string attribute) {
    const string text = """
      procedure P(y: int);
      implementation P(y: int) { assert y == y; }
      """;
    var (before, _) = KeyOf(text, "P");
    var (after, _) = KeyOf(text.Replace("implementation P", "implementation " + attribute + " P"), "P");
    Assert.NotEqual(before, after);
  }

  // Boogie shuffles the whole pruned list for an implementation with its own seed, so it gets no key.
  [Fact]
  public void BoogieSeededImplementationIsUnsupported() {
    const string text = """
      procedure P(y: int);
      implementation {:random_seed 3} P(y: int) { assert y == y; }
      """;
    var options = BoogieOptions();
    var keys = Keys.Compute(options, ParseBoogie(text, options));
    Assert.Null(keys.Unsupported);
    var key = Assert.Single(keys.Implementations.Values);
    Assert.Null(key.Content);
    Assert.Contains("random seed", key.Unsupported);
  }

  // Boogie's randomized iterations (measure-complexity's mutations) draw per-iteration seeds: no proof inputs.
  [Fact]
  public async Task RandomizedIterationsHaveNoProofInputs() {
    var options = DafnyOptionsFor(options => options.RandomizeVcIterations = 3);
    var program = await ProofInputRepeatabilityTests.Parse("method A(x: int) { assert x == x; }", options, Path);
    Assert.Null(DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      ProofInputRepeatabilityTests.Translate, () => Toolchain));
  }

  // Changing the lambda body still changes the key.
  [Fact]
  public async Task LambdaBodyChangesTheKey() {
    const string source = "method A(x: int) { var f := (z: int) => z + x; assert f(1) == x + 1 || true; }";
    var before = await Inputs(source);
    var after = await Inputs(source.Replace("z + x", "z - x"));
    Assert.NotEqual(Sha(before, "A"), Sha(after, "A"));
  }

  // Program order is not part of the key: Boogie shuffles the whole pruned list anyway, so an equal key means an
  // equal formula set. Swapping two used declarations keeps the key.
  [Fact]
  public async Task ProgramOrderIsNotPartOfTheKey() {
    const string source = "function F(x: int): int { x + 1 }\nfunction G(x: int): int { x + 2 }\nmethod A(x: int) { assert F(x) < G(x); }";
    var swapped = "function G(x: int): int { x + 2 }\nfunction F(x: int): int { x + 1 }\nmethod A(x: int) { assert F(x) < G(x); }";
    Assert.Equal(Sha(await Inputs(source), "A"), Sha(await Inputs(swapped), "A"));
  }

  // The release-skeleton shape root measured on Cat: a given declaration keeps its key when an empty proof module
  // is filled in and another declaration of its module starts calling it. Filling the module gives it imports,
  // which changes the module translation order, so the blocks of two unchanged modules the given method uses swap
  // places in program order (on Cat: `CatProof` gains imports and `BenchItem` moves after `CatSchema`).
  [Fact]
  public async Task GivenDeclarationKeepsItsKeyWhenProofsAreFilledIn() {
    const string given = """
      module Lib {
        function Lift(x: nat): nat { x + 1 }
      }
      module Spec {
        datatype Raw = Raw(n: nat)
      }
      module Given {
        import P
        import Lib
        import Spec
        class Item {
          constructor () { }
          method Name(r: Spec.Raw) returns (n: nat)
            ensures n == r.n
          {
            n := r.n;
            assert Lib.Lift(n) == n + 1;
          }
          method RunCore(r: Spec.Raw) {
          }
        }
      }
      """;
    var skeleton = "module P {\n}\n" + given;
    var reference = """
      module P {
        import Spec
        predicate Ok(r: Spec.Raw) { r.n >= 0 }
        lemma Use(r: Spec.Raw) ensures Ok(r) { }
      }

      """ + given.Replace("method RunCore(r: Spec.Raw) {\n    }", "method RunCore(r: Spec.Raw) {\n      P.Use(r);\n    }");
    Assert.Contains("P.Use(r);", reference);
    var before = await NamedKey(skeleton, "Impl$$Given.Item.Name");
    var after = await NamedKey(reference, "Impl$$Given.Item.Name");
    // The shape exercises order: the same live declarations appear in a different program order.
    Assert.NotEqual(before.Order, after.Order);
    Assert.Equal(Sorted(before.Order), Sorted(after.Order));
    Assert.Equal(before.Sha, after.Sha);
    Assert.Equal(Sha(await Inputs(skeleton), "Given.Item.Name"), Sha(await Inputs(reference), "Given.Item.Name"));
    Assert.NotEqual(Sha(await Inputs(skeleton), "Given.Item.RunCore"), Sha(await Inputs(reference), "Given.Item.RunCore"));
    static string Sorted(string order) => string.Join(",", order.Split(',').OrderBy(item => item, StringComparer.Ordinal));
  }

  // A trigger-tuple axiom joins the live set only when every term of one trigger is reachable.
  [Fact]
  public void TriggerTupleAxiomJoinsOnlyWhenEveryTermIsReachable() {
    const string template = """
      function F(x: int): bool;
      function G(x: int): bool;
      function H(x: int): bool;
      function K(x: int): bool;
      axiom (forall x: int :: {F(x), G(x)} H(x));
      axiom (forall x: int :: {K(x)} K(x) == DEFINITION);
      procedure P(y: int);
      implementation P(y: int) { assert F(y) ==> K(y); }
      procedure Q(y: int);
      implementation Q(y: int) { assert y == y; }
      """;
    var (oneTerm, oneTermLive) = KeyOf(template.Replace("DEFINITION", "true"), "P");
    var (bothTerms, bothTermsLive) = KeyOf(template.Replace("DEFINITION", "G(x)"), "P");
    Assert.DoesNotContain(oneTermLive, IsTupleAxiom);
    Assert.Contains(bothTermsLive, IsTupleAxiom);
    Assert.NotEqual(oneTerm, bothTerms);
    // With one term reachable, a change to the tuple axiom is outside P's input.
    var (changedTuple, _) = KeyOf(template.Replace("DEFINITION", "true").Replace("H(x));", "!H(x));"), "P");
    Assert.Equal(oneTerm, changedTuple);
    static bool IsTupleAxiom(Bpl.Declaration declaration) =>
      declaration is Bpl.Axiom axiom && axiom.Expr is Bpl.ForallExpr { Triggers.Tr.Count: 2 };
  }

  // Unprinted CanHide flags change which axioms a split declares, so they are part of the key.
  [Fact]
  public void CanHideFlagChangesTheKey() {
    const string text = """
      function F(x: int): int;
      axiom (forall x: int :: {F(x)} F(x) > x);
      procedure P(y: int);
      implementation P(y: int) { assert F(y) > y; }
      """;
    var (plain, _) = KeyOf(text, "P");
    var (hideable, _) = KeyOf(text, "P", program => program.Axioms.Single().CanHide = true);
    Assert.NotEqual(plain, hideable);
  }

  // Inlined callees put another body into the verification condition; the caller is unsupported.
  [Fact]
  public void InlinedCalleeIsUnsupported() {
    const string text = """
      procedure {:inline 1} Q(y: int) returns (r: int);
      implementation {:inline 1} Q(y: int) returns (r: int) { r := y; }
      procedure P(y: int);
      implementation P(y: int) { var r: int; call r := Q(y); assert r == y; }
      """;
    var options = BoogieOptions();
    var keys = Keys.Compute(options, ParseBoogie(text, options));
    var caller = keys.Implementations.Values.Single(key => key.Implementation.Name == "P");
    Assert.Null(caller.Content);
    Assert.Contains("inlined", caller.Unsupported);
  }

  // Declarations without obligations have no Boogie implementation; their translation certifies them.
  [Theory]
  [InlineData("function F(x: int): int { x }", "F")]
  [InlineData("predicate P(x: int) { x > 0 }", "P")]
  [InlineData("lemma L(x: int) { }", "L")]
  [InlineData("method N() { }", "N")]
  public async Task ZeroObligationTargetsAreCertified(string source, string name) {
    var inputs = await Inputs(source);
    var row = Assert.Single(inputs.Definitions, definition => definition.FullName == name);
    Assert.Equal(0, row.Implementations);
    Assert.NotNull(row.ClosureOrigins);
    Assert.Empty(row.ClosureOrigins!.Sources);
  }

  // A zero-obligation function that gains an obligation gets an implementation and a new fingerprint.
  [Fact]
  public async Task ZeroObligationFunctionGainingAnObligationChangesTheKey() {
    const string source = "function F(x: int): int { x }";
    var before = await Inputs(source);
    var after = await Inputs("function F(x: int): int requires x != 0 { 10 / x }");
    Assert.Equal(0, Assert.Single(before.Definitions).Implementations);
    Assert.Equal(1, Assert.Single(after.Definitions).Implementations);
    Assert.NotEqual(Sha(before, "F"), Sha(after, "F"));
  }

  // Closure origins name the target's and callee's source ranges and count token-free declarations.
  [Fact]
  public async Task ClosureOriginsCoverTargetAndCalleeSources() {
    const string source = "method B(x: int) returns (y: int) ensures y > x { y := x + 1; }\nmethod A(x: int) returns (y: int) ensures y > x { y := B(x); }";
    var inputs = await Inputs(source);
    var row = Assert.Single(inputs.Definitions, definition => definition.FullName == "A");
    Assert.True(row.Implementations >= 1);
    var origins = row.ClosureOrigins!;
    var file = Assert.Single(origins.Sources);
    Assert.Equal(Path, file.SourcePath);
    var calleeContract = source.IndexOf("ensures y > x", StringComparison.Ordinal);
    var target = source.IndexOf("method A", StringComparison.Ordinal);
    Assert.Contains(file.Spans, span => span.Start <= calleeContract && calleeContract < span.End);
    Assert.Contains(file.Spans, span => span.Start <= target && target < span.End);
    Assert.All(file.Spans, span => Assert.True(span.Start < span.End && span.End <= source.Length + 1));
    Assert.True(origins.Toolchain > 0);
  }

  // Native checksums follow the keys: an unrelated edit keeps the target's checksum, its own edit changes it.
  [Fact]
  public async Task NativeChecksumsFollowTheModularKeys() {
    const string source = """
      method B(x: int) returns (y: int) ensures y > x { y := x + 1; }
      method A(x: int) returns (y: int) ensures y > x { y := B(x); }
      """;
    var original = await Checksums(source);
    var bodyEdit = await Checksums(source.Replace("{ y := x + 1; }", "{ y := x + 2; }"));
    Assert.Equal(original["Impl$$_module.__default.A"], bodyEdit["Impl$$_module.__default.A"]);
    Assert.NotEqual(original["Impl$$_module.__default.B"], bodyEdit["Impl$$_module.__default.B"]);
    var contractEdit = await Checksums(source.Replace("ensures y > x { y := x + 1; }", "ensures y >= x { y := x + 1; }"));
    Assert.NotEqual(original["Impl$$_module.__default.A"], contractEdit["Impl$$_module.__default.A"]);
  }

  // Boogie's result cache also compares a dependency identity. For key-bound implementations it is derived from the
  // bound checksum alone, so it follows the key: equal after an unrelated edit, different after a relevant edit or
  // an option change. Without proof inputs Boogie keeps its own identity.
  [Fact]
  public async Task DependencyIdentityFollowsTheModularKey() {
    const string source = """
      method B(x: int) returns (y: int) ensures y > x { y := x + 1; }
      method A(x: int) returns (y: int) ensures y > x { y := B(x); }
      """;
    const string a = "Impl$$_module.__default.A";
    var original = await Dependencies(source);
    var unrelated = await Dependencies(source.Replace("{ y := x + 1; }", "{ y := x + 2; }"));
    var contract = await Dependencies(source.Replace("ensures y > x { y := x + 1; }", "ensures y >= x { y := x + 1; }"));
    var seeded = await Dependencies(source, options => options.RandomSeed = 7);
    var unkeyed = await Dependencies(source, withInputs: false);
    Assert.NotNull(original[a]);
    Assert.Equal(original[a], unrelated[a]);
    Assert.NotEqual(original[a], contract[a]);
    Assert.NotEqual(original[a], seeded[a]);
    Assert.Null(unkeyed[a]);
  }

  // Unsupported programs and implementations get a fresh checksum every time.
  [Fact]
  public async Task MissingProofInputsBindFreshChecksums() {
    const string source = "method A(x: int) { assert x == x; }";
    var first = await Checksums(source, withInputs: false);
    var second = await Checksums(source, withInputs: false);
    Assert.NotEqual(first["Impl$$_module.__default.A"], second["Impl$$_module.__default.A"]);
  }

  private static async Task<int> AssertSupersets(string source, bool isolate) {
    var options = DafnyOptionsFor(options => {
      if (isolate) {
        Set(options, BoogieOptionBag.IsolateAssertions, true);
      }
    });
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    using var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(options);
    var splits = 0;
    foreach (var (_, boogie) in ProofInputRepeatabilityTests.Translate(program).ToList()) {
      var keys = Keys.Compute(options, boogie);
      Assert.Null(keys.Unsupported);
      foreach (var task in await engine.GetVerificationTasks(boogie)) {
        var key = keys.Implementations[task.Split.Implementation];
        Assert.NotNull(key.Content);
        var declared = task.Split.PrunedDeclarations.Where(declaration =>
          declaration is Bpl.TypeCtorDecl or Bpl.Constant or Bpl.Function or Bpl.Axiom or Bpl.GlobalVariable).ToList();
        AssertSubsequence(declared, key.Live, task.Split.Implementation.Name);
        splits++;
      }
    }
    return splits;
  }

  private static void AssertSubsequence(IReadOnlyList<Bpl.Declaration> declared, IReadOnlyList<Bpl.Declaration> live, string name) {
    var position = 0;
    foreach (var declaration in declared) {
      while (position < live.Count && !ReferenceEquals(live[position], declaration)) {
        position++;
      }
      Assert.True(position < live.Count, $"{name}: {declaration} is declared to the solver but not in the live set (or out of order)");
      position++;
    }
  }

  private static (string Content, IReadOnlyList<Bpl.Declaration> Live) KeyOf(string text, string implementation,
    Action<Bpl.Program>? edit = null) {
    var options = BoogieOptions();
    var program = ParseBoogie(text, options);
    edit?.Invoke(program);
    var keys = Keys.Compute(options, program);
    Assert.Null(keys.Unsupported);
    var key = keys.Implementations.Values.Single(key => key.Implementation.Name == implementation);
    Assert.NotNull(key.Content);
    return (key.Content!, key.Live);
  }

  private static DafnyOptions BoogieOptions() => DafnyOptions.CreateUsingOldParser(TextWriter.Null);

  private static Bpl.Program ParseBoogie(string text, DafnyOptions options) {
    Assert.Equal(0, Bpl.Parser.Parse(text, "keys.bpl", out var program));
    Assert.Equal(0, program.Resolve(options));
    Assert.Equal(0, program.Typecheck(options));
    return program;
  }

  private static DafnyOptions DafnyOptionsFor(Action<DafnyOptions>? configure) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    configure?.Invoke(options);
    return options;
  }

  private static void Set<T>(DafnyOptions options, Option<T> option, T value) {
    options.Set(option, value);
    options.ApplyBinding(option);
  }

  private static async Task<DafnyProofInputs> Inputs(string source, Action<DafnyOptions>? configure = null,
    string toolchain = Toolchain) {
    var options = DafnyOptionsFor(configure);
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    var inputs = DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      ProofInputRepeatabilityTests.Translate, () => toolchain);
    Assert.Equal(0, program.Reporter.ErrorCount);
    Assert.NotNull(inputs);
    Assert.Equal(3, inputs!.SchemaVersion);
    return inputs;
  }

  private const string LibraryPath = "/workspace/tmp/modular-proof-keys/library.dfy";

  private static async Task<DafnyProofInputs> LibraryInputs(string source, string library) {
    var options = DafnyOptionsFor(null);
    var uri = new Uri(Path);
    var libraryUri = new Uri(LibraryPath);
    options.CliRootSourceUris.Add(uri);
    var fileSystem = new MemoryFileSystem(new Dictionary<Uri, string> { [uri] = source, [libraryUri] = library });
    var reporter = new BatchErrorReporter(options);
    var parser = new ProgramParser(Microsoft.Extensions.Logging.Abstractions.NullLogger<ProgramParser>.Instance, fileSystem);
    var files = new[] {
      DafnyFile.HandleDafnyFile(fileSystem, reporter, options, uri, Token.NoToken)!,
      DafnyFile.HandleDafnyFile(fileSystem, reporter, options, libraryUri, Token.NoToken, asLibrary: true)!
    };
    Microsoft.Dafny.Type.ResetScopes();
    var parsed = await parser.ParseFiles(uri.ToString(), files, reporter, CancellationToken.None);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var program = parsed.Program;
    var inputs = DefinitionAnalysis.ProofInputsFor(program, new HashSet<Uri> { uri, libraryUri },
      ProofInputRepeatabilityTests.Translate, () => Toolchain);
    Assert.NotNull(inputs);
    return inputs!;
  }

  private sealed class MemoryFileSystem(IReadOnlyDictionary<Uri, string> files) : IFileSystem {
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(files[uri]), null);
    public bool Exists(Uri uri) => files.ContainsKey(uri)
      ? true : throw new InvalidOperationException("Unexpected filesystem lookup: " + uri);
    public Microsoft.Extensions.FileSystemGlobbing.Abstractions.DirectoryInfoBase GetDirectoryInfoBase(string root) =>
      throw new InvalidOperationException("Unexpected directory lookup.");
  }

  private static string Sha(DafnyProofInputs inputs, string name) =>
    Assert.Single(inputs.Definitions, definition => definition.FullName == name).Sha256;

  private static async Task<Dictionary<string, string?>> Dependencies(string source, Action<DafnyOptions>? configure = null,
    bool withInputs = true) {
    var options = DafnyOptionsFor(configure);
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    var inputs = withInputs
      ? DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(), _ => translations, () => Toolchain)
      : null;
    DefinitionAnalysis.BindNativeVerificationChecksums(translations, inputs);
    return translations.SelectMany(translation => translation.Item2.Implementations).ToDictionary(
      implementation => implementation.Name,
      implementation => implementation.MD5DependencyChecksum_ == null ? null : Convert.ToHexString(implementation.MD5DependencyChecksum_));
  }

  // The content key of one implementation and the program order of its live declarations (lambda names masked).
  private static async Task<(string Sha, string Order)> NamedKey(string source, string implementation) {
    var options = DafnyOptionsFor(null);
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    Assert.NotNull(DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(),
      _ => translations, () => Toolchain));
    var key = translations.Select(translation => Keys.Existing(translation.Item2)!)
      .SelectMany(keys => keys.Implementations.Values).Single(key => key.Implementation.Name == implementation);
    Assert.NotNull(key.Content);
    var order = string.Join(",", key.Live.Select(declaration => declaration switch {
      Bpl.NamedDeclaration named when named.Name.StartsWith("lambda#") => "lambda:" + DefinitionAnalysis.ProofDeclarationHash(
        options, declaration, token => token.StartsWith("lambda#") ? "lambda" : token)[..8],
      Bpl.NamedDeclaration named => named.Name,
      _ => DefinitionAnalysis.ProofDeclarationHash(options, declaration,
        token => token.StartsWith("lambda#") ? "lambda" : token)[..8]
    }));
    return (key.Content!, order);
  }

  private static async Task<Dictionary<string, string>> Checksums(string source, bool withInputs = true,
    Action<DafnyOptions>? configure = null) {
    var options = DafnyOptionsFor(configure);
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    var translations = ProofInputRepeatabilityTests.Translate(program).ToList();
    var inputs = withInputs
      ? DefinitionAnalysis.ProofInputsFor(program, program.Compilation.RootSourceUris.ToHashSet(), _ => translations, () => Toolchain)
      : null;
    DefinitionAnalysis.BindNativeVerificationChecksums(translations, inputs);
    return translations.SelectMany(translation => translation.Item2.Implementations)
      .ToDictionary(implementation => implementation.Name, implementation => implementation.Checksum);
  }
}
