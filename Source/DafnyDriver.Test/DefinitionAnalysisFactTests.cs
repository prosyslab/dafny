using DafnyDriver.Commands;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging.Abstractions;
using Xunit;
using Program = Microsoft.Dafny.Program;

namespace DafnyDriver.Test;

[Collection("Proof input translation")]
public class DefinitionAnalysisFactTests {
  private const string Cwd = "/workspace/analysis-facts";
  private const string Path = Cwd + "/root.dfy";
  private static readonly Uri Root = new("file://" + Path);

  // An assumption is trusted wherever it is written, not only as a statement of a method body.
  [Fact]
  public async Task AssumptionsInsideExpressionsAreReported() {
    var facts = await Analyze("""
      module A {
        function Shortcut(): () ensures false { assume {:axiom} false; () }
        lemma UsesFunction() ensures false { var _ := Shortcut(); }
        method InExpression(x: int) returns (r: int) ensures r > 0 { r := (assume {:axiom} x > 0; x); }
        lemma InAssert(x: int) ensures x * x == 7 { assert (assume {:axiom} x * x == 7; true); }
        lemma SuchThat() ensures false { var x: int :| assume {:axiom} false; }
        const C: int := (assume {:axiom} false; 0)
        type Small = x: int | (assume {:axiom} x < 10; true)
        function Split(x: int): int { x } by method { assume {:axiom} true; return x; }
        class K { method Plain() { assume {:axiom} true; } }
      }
      """);
    Assert.All(new[] { "A.Shortcut", "A.InExpression", "A.InAssert", "A.SuchThat", "A.C", "A.Small", "A.Split#by-method", "A.K.Plain" },
      name => Assert.True(facts[name].HasAssumeStatement, name));
    Assert.All(new[] { "A.UsesFunction", "A.Split", "A.K" },
      name => Assert.False(facts[name].HasAssumeStatement, name));
  }

  // A refining module reports the resolved member behind each authored declaration.
  [Fact]
  public async Task RefinedMembersKeepResolvedFactsAndAuthoredSpans() {
    const string source = """
      abstract module Abs {
        function Zero(): int
        lemma L(x: int) ensures Zero() == Zero()
        method M(x: int) returns (y: int) ensures y >= x
      }
      module Impl refines Abs {
        function Zero(): int { Helper(0) }
        function Helper(x: int): int { x }
        lemma L ... { }
        method M(x: int) returns (y: int) ensures y >= x { y := Helper(x); L(x); }
      }
      """;
    var facts = await Analyze(source);
    Assert.Equal(["Impl.Helper"], facts["Impl.Zero"].Callees);
    Assert.Equal(["Impl.Helper", "Impl.L"], facts["Impl.M"].Callees);
    Assert.Contains("Impl.Helper", facts["Impl.M"].Dependencies);
    Assert.NotNull(facts["Impl.M"].BodyVisibility);
    Assert.Equal(source.IndexOf("{ y := Helper", StringComparison.Ordinal), facts["Impl.M"].BodyStart);
    Assert.Equal("method M(x: int) returns (y: int) ensures y >= x", facts["Impl.M"].ContractHeaderWithoutAxiom);
  }

  // A lemma called from a statement expression is a callee, so recursion through it is visible.
  [Fact]
  public async Task CallsInStatementExpressionsAreCallees() {
    var facts = await Analyze("""
      module S {
        lemma G(n: nat) ensures F(n) >= 0 decreases n, 0 { if n > 0 { var _ := F(n - 1); } }
        function F(n: nat): int decreases n, 1 { G(n); n }
        const C: int := (G(3); F(3))
      }
      """);
    Assert.Equal(["S.G"], facts["S.F"].Callees);
    Assert.Equal(["S.G"], facts["S.F"].CallSites.Select(site => site.TargetFullName));
    Assert.True(facts["S.F"].Recursive);
    Assert.Equal(["S.F", "S.G"], facts["S.F"].RecursiveGroup);
    Assert.Equal(["S.F", "S.G"], facts["S.C"].Callees);
  }

  // Every branch of a match is reported once, under the pattern its author wrote.
  [Fact]
  public async Task MatchBranchesReportAuthoredPatterns() {
    var facts = await Analyze("""
      module Mt {
        datatype T = A | B(x: int) | C(l: T, r: T)
        method P(i: int) { }
        method Top(t: T) { match t { case A => P(0); case B(x) => P(1); case C(l, r) => P(2); } }
        method Nested(t: T) { match t { case C(A, B(y)) => P(10); case C(B(z), _) => P(11); case _ => P(12); } }
        method Literal(n: int) { match n { case 0 => P(20); case 1 => P(21); case _ => P(22); } }
      }
      """, statements: true);
    Assert.Equal(["0:A", "1:B(x)", "2:C(l, r)"], Branches(facts["Mt.Top"]));
    Assert.Equal(["0:C(A, B(y))", "1:C(B(z), _)", "2:_"], Branches(facts["Mt.Nested"]));
    Assert.Equal(["0:0", "1:1", "2:_"], Branches(facts["Mt.Literal"]));
    Assert.Equal(3, facts["Mt.Nested"].CallSequence.Count);

    static IEnumerable<string> Branches(DefinitionAnalysisResult definition) => definition.CallSites.Select(site => {
      var context = Assert.Single(site.ControlPath);
      Assert.Equal("match", context.Kind);
      return $"{context.BranchIndex}:{context.Guard}";
    });
  }

  // An export set and a declaration of the same name are distinct definitions.
  [Fact]
  public async Task ExportSetsNeverShareADeclarationName() {
    var facts = await Analyze("""
      module Stack {
        export provides Stack, Empty
        export Empty provides Stack
        datatype Stack = Nil | Cons(int, Stack)
        function Empty(): Stack { Nil }
      }
      """);
    Assert.Equal("export", facts["Stack.Stack#export"].Kind);
    Assert.Equal("export", facts["Stack.Empty#export"].Kind);
    Assert.Equal("datatype", facts["Stack.Stack"].Kind);
    Assert.Equal("function", facts["Stack.Empty"].Kind);
  }

  // Initializers, frame clauses and overridden members are part of what a definition depends on.
  [Fact]
  public async Task InitializersFramesAndOverridesAreDependencies() {
    var facts = await Analyze("""
      module Fr {
        function Zero(): int { 0 }
        const K: int := Zero() + 1
        class Cell { var v: int }
        function Rep(c: Cell): set<object> { {c} }
        method Mod(c: Cell) modifies Rep(c) { c.v := 1; }
        trait Tr { method Run() returns (r: int) }
        class Im extends Tr { method Run() returns (r: int) { r := 7; } }
      }
      """);
    Assert.Equal(["Fr.Zero"], facts["Fr.K"].Callees);
    Assert.Equal(["Fr.Rep"], facts["Fr.Mod"].Callees);
    Assert.Contains("Fr.Tr.Run", facts["Fr.Im.Run"].Dependencies);
  }

  // reveal F() exposes a body; it is not a call of a declared lemma.
  [Fact]
  public async Task RevealIsNotACall() {
    var facts = await Analyze("""
      module R {
        opaque function Op(n: nat): nat { n + 1 }
        lemma Uses(n: nat) ensures Op(n) > n { reveal Op(); }
      }
      """, statements: true);
    Assert.Empty(facts["R.Uses"].CallSites);
    Assert.All(facts["R.Uses"].Statements, statement => Assert.Empty(statement.DirectCallTargets));
    Assert.Equal(["R.Op"], facts["R.Uses"].BodyVisibility!.RevealedFunctions);
  }

  // Reveal exposure follows calls through a cycle and stops at its boundary.
  [Fact]
  public async Task BodyVisibilityFollowsCallCycles() {
    var facts = await Analyze("""
      module Cy {
        opaque function Size(n: nat): nat { n }
        opaque function Other(n: nat): nat { n }
        lemma A(n: nat) { reveal Size(); B(n); }
        lemma B(n: nat) decreases n, 1 { if n > 0 { C(n - 1); } }
        lemma C(n: nat) decreases n, 0 { reveal Other(); B(n); }
        lemma D() { }
      }
      """);
    Assert.Equal(["Cy.Other", "Cy.Size"], facts["Cy.A"].BodyVisibility!.RevealedFunctions);
    Assert.Equal(["Cy.Other"], facts["Cy.B"].BodyVisibility!.RevealedFunctions);
    Assert.Equal(["Cy.Other"], facts["Cy.C"].BodyVisibility!.RevealedFunctions);
    Assert.Empty(facts["Cy.D"].BodyVisibility!.RevealedFunctions);
    Assert.Contains("Cy.C", facts["Cy.A"].BodyVisibility!.ReferencedDeclarations);
    Assert.DoesNotContain("Cy.A", facts["Cy.B"].BodyVisibility!.ReferencedDeclarations);
  }

  // Parse-level spans read the authored @Axiom, which only resolution turns into {:axiom}.
  [Fact]
  public async Task SpansReportAuthoredAxiomAttributes() {
    var program = await Compile("""
      module R {
        @Axiom lemma At() ensures false
        lemma {:axiom} Brace() ensures false
        lemma Plain() ensures true { }
      }
      """, resolve: false);
    var spans = DefinitionAnalysis.AnalyzeSpans(program, new HashSet<Uri> { Root })
      .ToDictionary(definition => definition.FullName);
    Assert.True(spans["R.At"].HasAxiomAttribute);
    Assert.True(spans["R.Brace"].HasAxiomAttribute);
    Assert.False(spans["R.Plain"].HasAxiomAttribute);
  }

  // A session analyzes any expression the resolver accepts, however deeply it nests.
  [Fact]
  public async Task SessionAnalyzesDeeplyNestedExpressions() {
    var sum = string.Join(" + ", Enumerable.Repeat("g(x)", 12000));
    var source = $"module M {{ function g(x: int): int {{ x }} function f(x: int): int {{ {sum} }} }}";
    using var session = new AnalysisSessionCommand.Session();
    var response = await session.Execute(new AnalysisSessionCommand.Request("deep", ["definition-analysis", Path], Cwd,
      "default", new Dictionary<string, string> { [Path] = source }), CancellationToken.None);
    Assert.True(response.Returncode == 0, response.Stderr);
    Assert.Contains("\"M.f\"", response.Stdout);
  }

  private static async Task<Dictionary<string, DefinitionAnalysisResult>> Analyze(string source, bool statements = false) {
    var program = await Compile(source, resolve: true);
    return DefinitionAnalysis.Analyze(program, new HashSet<Uri> { Root }, statements)
      .ToDictionary(definition => definition.FullName);
  }

  private static async Task<Program> Compile(string source, bool resolve) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var files = new MemoryFiles(source);
    var reporter = new BatchErrorReporter(options);
    var rootFile = DafnyFile.HandleDafnyFile(files, reporter, options, Root, Token.NoToken)!;
    var parsed = await new ProgramParser(NullLogger<ProgramParser>.Instance, files)
      .ParseFiles(Root.ToString(), [rootFile], reporter, CancellationToken.None);
    if (resolve) {
      Microsoft.Dafny.Type.ResetScopes();
      await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    }
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return parsed.Program;
  }

  private sealed class MemoryFiles(string source) : IFileSystem {
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(source), null);
    public bool Exists(Uri path) => path == Root;
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }
}
