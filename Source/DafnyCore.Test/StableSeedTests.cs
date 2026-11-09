using System.Text;
using Microsoft.Dafny;
using Bpl = Microsoft.Boogie;

namespace DafnyCore.Test;

/// <summary>
/// The stable seeded order (a non-zero <c>/randomSeed</c> in <c>--boogie</c>): option handling and the exact solver
/// input of a target, captured in memory from a no-op solver. Translation and VC generation are real; no solver
/// process runs and nothing touches the filesystem.
/// </summary>
[Collection("Proof input translation")]
public class StableSeedTests {
  private const string Path = "/workspace/tmp/stable-seed/source.dfy";

  private const string Base = """
    function Double(x: int): int { 2 * x }
    function Sum(s: seq<int>): int { if |s| == 0 then 0 else s[0] + Sum(s[1..]) }
    predicate AllPos(s: seq<int>) { forall i :: 0 <= i < |s| ==> s[i] > 0 }
    method Target(a: int, s: seq<int>) returns (r: int)
      requires a > 0 && AllPos(s)
      ensures r > a
    {
      r := Double(a);
      assert r == a + a;
      assert Sum([]) == 0;
      if |s| > 0 {
        assert s[0] > 0;
      }
    }

    """;

  private const string Unrelated = """
    datatype Color = Red | Green | Blue
    function Rank(c: Color): nat { match c case Red => 0 case Green => 1 case Blue => 2 }
    lemma RankBound(c: Color) ensures Rank(c) <= 2 { }
    method Unrelated(b: bool) returns (y: nat) ensures y >= 1 { y := if b then 1 else 2; }

    """;

  // The target and a sibling use the same function handle and alpha-equivalent lambdas, which Boogie lifts into
  // one function named after whichever it meets first.
  private const string Handles = """
    function Inc(x: int): int { x + 1 }
    function Twice(f: int -> int, x: int): int { f(f(x)) }
    method Target(s: seq<int>) returns (t: seq<int>)
      ensures |t| == |s|
      ensures forall i :: 0 <= i < |s| ==> t[i] == Twice(Inc, s[i])
    {
      t := seq(|s|, i requires 0 <= i < |s| => Twice(Inc, s[i]));
      assert |t| == |s|;
      var g := (z: int) => z * 3;
      assert Twice(g, 1) == 9;
    }

    """;

  private const string HandleSibling = """
    method Sib(s: seq<int>) returns (t: seq<int>) ensures |t| == |s| {
      t := seq(|s|, i requires 0 <= i < |s| => Twice(Inc, s[i]) + Twice(y => y * 3, i));
    }

    """;

  // Handle axioms of Inc and Dec have equal structure (Boogie's ContentHash ties); the sibling emits Dec's first.
  private const string TiedHandles = """
    function Inc(x: int): int { x + 1 }
    function Dec(x: int): int { x - 1 }
    function Apply(f: int -> int, x: int): int { f(x) }
    method Target(x: int) returns (y: int)
      ensures y == x
    {
      var a := Apply(Inc, x);
      var b := Apply(Dec, a);
      assert a == x + 1;
      assert b == x;
      y := b;
    }

    """;

  private const string TiedSibling = """
    method Sib(x: int) returns (y: int) ensures y == Apply(Dec, x) { y := Apply(Dec, x); }

    """;

  // A non-zero seed in --boogie is hidden from Boogie and handed to Z3, first among the prover options.
  [Fact]
  public void BoogieSeedSelectsTheStableOrder() {
    var options = Options("/randomSeed:42");
    Assert.Equal(42, options.StableRandomSeed);
    Assert.Null(options.RandomSeed);
    Assert.False(options.NormalizeDeclarationOrder);
    Assert.Equal(new[] { "O:smt.random_seed=42", "O:sat.random_seed=42" }, options.ProverOptions.Take(2));
  }

  // Seed 0 and several Boogie iterations keep Boogie's own handling of the seed.
  [Theory]
  [InlineData("/randomSeed:0", 0)]
  [InlineData("/randomSeed:42 /randomizeVcIterations:3", 42)]
  public void OtherBoogieSeedsStayBoogies(string arguments, int seed) {
    var options = Options(arguments);
    Assert.Null(options.StableRandomSeed);
    Assert.Equal(seed, options.RandomSeed);
    Assert.True(options.NormalizeDeclarationOrder);
    Assert.DoesNotContain(options.ProverOptions, option => option.Contains("random_seed"));
  }

  // A seed from another option (measure-complexity's --random-seed) stays Boogie's when --boogie sets none.
  [Fact]
  public void SeedFromAnotherOptionStaysBoogies() {
    var options = Options("/vcsCores:1", configure: options => options.RandomSeed = 5);
    Assert.Null(options.StableRandomSeed);
    Assert.Equal(5, options.RandomSeed);
    Assert.True(options.NormalizeDeclarationOrder);
  }

  // Applying the Boogie arguments again replaces the stable seed; seed 0 restores Boogie's handling.
  [Fact]
  public void ReappliedBoogieArgumentsReplaceTheStableSeed() {
    var options = Options("/randomSeed:42");
    Apply(options, "/randomSeed:7");
    Assert.Equal(7, options.StableRandomSeed);
    Assert.Equal(new[] { "O:smt.random_seed=7", "O:sat.random_seed=7" },
      options.ProverOptions.Where(option => option.Contains("random_seed")));
    Apply(options, "/randomSeed:0");
    Assert.Null(options.StableRandomSeed);
    Assert.Equal(0, options.RandomSeed);
    Assert.True(options.NormalizeDeclarationOrder);
    Assert.DoesNotContain(options.ProverOptions, option => option.Contains("random_seed"));
  }

  // Unrelated declarations before or after the target leave every byte of its solver input unchanged.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task UnrelatedDeclarationsKeepTheSolverInput(bool before) {
    var alone = await SolverInput(Base, 42);
    Assert.Contains("(set-option :smt.random_seed 42)", alone);
    Assert.Contains("(set-option :sat.random_seed 42)", alone);
    Assert.Equal(alone, await SolverInput(before ? Unrelated + Base : Base + Unrelated, 42));
  }

  // A sibling sharing a handle and an alpha-equivalent lambda, before or after the target, keeps its solver input.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task SharedLambdaSiblingKeepsTheSolverInput(bool before) {
    var alone = await SolverInput(Handles, 42);
    Assert.Equal(alone, await SolverInput(before ? HandleSibling + Handles : Handles + HandleSibling, 42));
  }

  // Declarations with equal structure are told apart by their content, not by the order the sibling emits them in.
  [Fact]
  public async Task TiedHandlesKeepTheSolverInput() {
    Assert.Equal(await SolverInput(TiedHandles, 42), await SolverInput(TiedSibling + TiedHandles, 42));
  }

  // Pins the cause: Boogie's own seeded randomization shuffles the whole program, so the sibling changes the input.
  [Fact]
  public async Task BoogieSeededShuffleDependsOnUnrelatedDeclarations() {
    var alone = await SolverInput(Base, 42, boogieSeed: true);
    Assert.NotEqual(alone, await SolverInput(Unrelated + Base, 42, boogieSeed: true));
  }

  // Another seed still changes more than the seed options: the declaration order.
  [Fact]
  public async Task SeedChangesTheDeclarationOrder() {
    static string WithoutSeedOptions(string input) => string.Join("\n", input.Split('\n')
      .Where(line => !line.StartsWith("(set-option :smt.random_seed") && !line.StartsWith("(set-option :sat.random_seed")));
    var seed42 = await SolverInput(Base, 42);
    var seed7 = await SolverInput(Base, 7);
    Assert.NotEqual(WithoutSeedOptions(seed42), WithoutSeedOptions(seed7));
  }

  // Boogie numbers the basic types in the order a whole-program visit meets them; the reorder keeps that order.
  [Fact]
  public async Task OrderKeepsTheBasicTypeOrder() {
    var options = Options("/randomSeed:42");
    var program = await ProofInputRepeatabilityTests.Parse(Unrelated + Base, options, Path);
    foreach (var (_, boogie) in ProofInputRepeatabilityTests.Translate(program).ToList()) {
      static List<string> BasicTypes(Bpl.Program boogie) =>
        new Bpl.BasicTypeVisitor(boogie, node => node is not Bpl.Implementation).GetBasicTypes()
          .Select(type => type.ToString()).ToList();
      var before = BasicTypes(boogie);
      var unordered = boogie.TopLevelDeclarations.ToList();
      DefinitionAnalysis.ApplyStableSeededOrder(options, boogie);
      Assert.Equal(before, BasicTypes(boogie));
      Assert.NotEqual(unordered, boogie.TopLevelDeclarations.Where(unordered.Contains));
    }
  }

  // A Boogie implementation with its own seed keeps Boogie's randomization: random names, and Z3 ends with its seed.
  [Fact]
  public async Task OwnBoogieSeedKeepsBoogiesRandomization() {
    const string text = """
      function F(x: int): int;
      axiom (forall x: int :: F(x) > x);
      procedure P(y: int);
      implementation {:random_seed 3} P(y: int) { assert F(y) > y; }
      """;
    var options = Options("/randomSeed:42");
    var log = new StringBuilder();
    options.CreateSolver = (_, _) => new CapturingSolver(log);
    Assert.Equal(0, Bpl.Parser.Parse(text, "seed.bpl", out var program));
    Assert.Equal(0, program.Resolve(options));
    Assert.Equal(0, program.Typecheck(options));
    DefinitionAnalysis.ApplyStableSeededOrder(options, program);
    using var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(options);
    await RunToEnd(Assert.Single(await engine.GetVerificationTasks(program)));
    string input;
    lock (log) {
      input = log.ToString();
    }
    var vc = input[input.LastIndexOf("; did a full reset", StringComparison.Ordinal)..];
    vc = vc[..vc.IndexOf("(check-sat)", StringComparison.Ordinal)];
    var seeds = vc.Split('\n').Where(line => line.StartsWith("(set-option :smt.random_seed")).ToList();
    // Per VC: Boogie's own seed line, the global stable seed option, then the repeat, which Z3 applies last.
    Assert.Equal(new[] { "3", "42", "3" }, seeds.TakeLast(3).Select(line => line.TrimEnd()[29..^1]));
    Assert.Contains("(declare-fun random", vc);
  }

  private static DafnyOptions Options(string arguments, Action<DafnyOptions>? configure = null) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    configure?.Invoke(options);
    Apply(options, arguments);
    return options;
  }

  private static void Apply(DafnyOptions options, string arguments) {
    options.Set(BoogieOptionBag.BoogieArguments, arguments.Split(' ').AsEnumerable());
    options.ApplyBinding(BoogieOptionBag.BoogieArguments);
  }

  /// <summary>
  /// Everything sent to the solver for the target's tasks, run one at a time. With <paramref name="boogieSeed"/> the
  /// seed goes to Boogie directly, as before the stable order.
  /// </summary>
  private static async Task<string> SolverInput(string source, int seed, bool boogieSeed = false) {
    var options = boogieSeed
      ? Options("/vcsCores:1", configure: options => options.RandomSeed = seed)
      : Options("/randomSeed:" + seed);
    var log = new StringBuilder();
    options.CreateSolver = (_, _) => new CapturingSolver(log);
    var program = await ProofInputRepeatabilityTests.Parse(source, options, Path);
    using var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(options);
    var runs = 0;
    foreach (var (_, boogie) in ProofInputRepeatabilityTests.Translate(program).ToList()) {
      DefinitionAnalysis.ApplyStableSeededOrder(options, boogie);
      foreach (var task in await engine.GetVerificationTasks(boogie)) {
        if (task.Split.Implementation.Name.EndsWith(".Target")) {
          await RunToEnd(task);
          runs++;
        }
      }
    }
    Assert.True(runs > 0, "no target task");
    lock (log) {
      return log.ToString();
    }
  }

  private static Task RunToEnd(Bpl.IVerificationTask task) {
    var done = new TaskCompletionSource();
    var run = task.TryRun();
    Assert.NotNull(run);
    run!.Subscribe(new CompletionObserver(done));
    return done.Task;
  }

  private sealed class CompletionObserver(TaskCompletionSource done) : IObserver<Bpl.IVerificationStatus> {
    public void OnNext(Bpl.IVerificationStatus value) { }
    public void OnError(Exception error) => done.TrySetException(error);
    public void OnCompleted() => done.TrySetResult();
  }

  /// <summary>A no-op solver (every check is unknown) that records every command it receives.</summary>
  private sealed class CapturingSolver(StringBuilder log) : Bpl.SMTLib.NoopSolver {
    public override void Send(string cmd) {
      lock (log) {
        log.AppendLine(cmd);
      }
      base.Send(cmd);
    }
  }
}
