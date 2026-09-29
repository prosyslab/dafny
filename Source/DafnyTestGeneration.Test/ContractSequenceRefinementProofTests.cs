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
using Bpl = Microsoft.Boogie;

namespace DafnyTestGeneration.Test;

public class ContractSequenceRefinementProofTests {
  // Original result membership still rejects non-byte characters, including supplementary Unicode.
  [Theory]
  [InlineData("\"A\" + \"\\nB\"", true)]
  [InlineData("\"é\"", true)]
  [InlineData("\"Ā\"", false)]
  [InlineData("\"🙂\"", false)]
  [InlineData("@\"A\"\"B\"", true)]
  [InlineData("\"\"", true)]
  public async Task ChecksOriginalLiteralResultRefinement(string body, bool expected) {
    var parsed = await Parse(RefinedSource(body));
    var result = await Check(parsed);
    Assert.Equal(expected, result.Verified);
    Assert.Equal(expected, parsed.Checker.Accept(parsed.Scope));
    Assert.Equal(ContractRuntimeTypeEvidence.SourceSetHash(parsed.Sources), result.SourceSetHash);
    AssertInventory(result);
    Assert.True(result.SequenceRefinement!.Implementations.Sum(item => item.AddedAssertionIds.Count) > 0);
    if (!expected) { Assert.True(result.ErrorCount > 0); }
  }

  // Checked prefix facts help an unchanged long concatenation rather than a rewritten literal or body.
  [Fact]
  public async Task ChecksLongOriginalConcatenation() {
    var body = string.Join(" + ", Enumerable.Repeat("\"abcdefghijklmnop\\n\"", 24));
    var parsed = await Parse(RefinedSource(body));
    var result = await Check(parsed);
    Assert.True(result.Verified, result.Diagnostics);
    Assert.True(parsed.Checker.Accept(parsed.Scope));
    AssertInventory(result);
    Assert.True(result.SequenceRefinement!.Implementations.Sum(item => item.AddedAssertionIds.Count) > 24);
  }

  // Arbitrary element constraints remain native obligations, including an empty element type.
  [Theory]
  [InlineData("x >= 2", "2", "[2, 3]", true)]
  [InlineData("x >= 2", "2", "[2, 1]", false)]
  [InlineData("false", "*", "[]", true)]
  [InlineData("false", "*", "[0]", false)]
  public async Task ChecksArbitraryElementRefinements(string constraint, string witness, string body, bool expected) {
    var parsed = await Parse("module Model { type Element = x:int | " + constraint + " witness " + witness +
      " function Root():seq<Element> { " + body + " } }");
    var result = await Check(parsed);
    Assert.Equal(expected, result.Verified);
    Assert.Equal(expected, parsed.Checker.Accept(parsed.Scope));
    AssertInventory(result, allowAssertionFree: body == "[]");
  }

  // Unknown generic-call inputs cannot acquire a refinement without the original required premise.
  [Theory]
  [InlineData("", false)]
  [InlineData("requires x >= 0", true)]
  public async Task KeepsUnknownElementObligation(string requirement, bool expected) {
    var parsed = await Parse("module Model { function Root<T>(x:int, tag:T):seq<nat> " + requirement + " { [x] } }");
    var result = await Check(parsed);
    Assert.Equal(expected, result.Verified);
    Assert.Equal(expected, parsed.Checker.Accept(parsed.Scope));
    AssertInventory(result);
  }

  // Every original command and assertion survives alongside the additional checked proof steps.
  [Fact]
  public async Task PreservesOriginalNativeCommandsAndImplicitAssertions() {
    var parsed = await Parse(RefinedSource("\"AB\" + \"CD\""));
    var translated = Translate(parsed);
    var implementations = translated.Implementations.ToList();
    var commands = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).ToList();
    var marked = commands.OfType<Bpl.AssertCmd>().First();
    var priorAttributes = marked.Attributes;
    marked.Attributes = new Bpl.QKeyValue(marked.tok, "msg", new List<object> { "original Ω" }, priorAttributes);
    var originals = commands.OfType<Bpl.AssertCmd>().ToDictionary(assertion => assertion,
      assertion => (assertion.Expr, assertion.tok, assertion.tok.filename, assertion.tok.line, assertion.tok.col,
        assertion.Attributes));
    Assert.NotEmpty(originals);
    var result = ContractSequenceRefinementProof.Apply(translated, implementations, CancellationToken.None);
    Assert.True(result.Preserved, result.Failure);
    var after = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).ToList();
    Assert.Equal(commands, after.Where(commands.Contains));
    Assert.All(originals, pair => {
      Assert.Contains(pair.Key, after);
      Assert.Same(pair.Value.Expr, pair.Key.Expr);
      Assert.Same(pair.Value.tok, pair.Key.tok);
      Assert.Equal(pair.Value.filename, pair.Key.tok.filename);
      Assert.Equal(pair.Value.line, pair.Key.tok.line);
      Assert.Equal(pair.Value.col, pair.Key.tok.col);
      Assert.Same(pair.Value.Attributes, pair.Key.Attributes);
    });
    Assert.Equal("msg", marked.Attributes.Key);
    Assert.Equal("original Ω", Assert.Single(marked.Attributes.Params));
    Assert.Same(priorAttributes, marked.Attributes.Next);
    var added = after.Except(commands).ToList();
    Assert.NotEmpty(added);
    Assert.All(added, command => Assert.IsType<Bpl.AssertCmd>(command));
    Assert.Equal(originals.Count, result.Implementations.Sum(item => item.RetainedAssertions));
    Assert.Equal(added.Count, result.Implementations.Sum(item => item.AddedAssertionIds.Count));
  }

  // A false inserted assertion must fail native verification even when later original assertions are unchanged.
  [Fact]
  public async Task FalseAddedAssertionCannotBeAccepted() {
    var parsed = await Parse(RefinedSource("\"AB\""));
    var translated = Translate(parsed);
    var implementations = translated.Implementations.ToList();
    var originals = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).ToHashSet();
    var result = ContractSequenceRefinementProof.Apply(translated, implementations, CancellationToken.None);
    Assert.True(result.Preserved);
    var added = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds)
      .OfType<Bpl.AssertCmd>().First(assertion => !originals.Contains(assertion));
    added.Expr = Bpl.Expr.False;
    using var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(parsed.Options);
    using var output = new StringWriter();
    using var timeout = new CancellationTokenSource(10000);
    var (_, statistics) = await DafnyMain.BoogieOnce(parsed.Reporter, parsed.Options, output, engine,
      "sequence-false-step", "Model", translated, null, timeout.Token);
    Assert.True(statistics.ErrorCount > 0, output.ToString());
    Assert.False(parsed.Checker.Accept(parsed.Scope));
  }

  // Duplicate or non-prelude declarations never authorize interpreting a symbol as native sequence membership.
  [Theory]
  [InlineData(true)]
  [InlineData(false)]
  public async Task RejectsAmbiguousOrNonPreludeIdentity(bool duplicate) {
    var parsed = await Parse(RefinedSource("\"AB\""));
    var translated = Translate(parsed);
    var function = translated.TopLevelDeclarations.OfType<Bpl.Function>().Single(item => item.Name == "$Is");
    if (duplicate) { translated.AddTopLevelDeclaration(function); } else { function.AlwaysRevealed = false; }
    var implementations = translated.Implementations.ToList();
    var commands = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).ToList();
    var result = ContractSequenceRefinementProof.Apply(translated, implementations, CancellationToken.None);
    Assert.True(result.Preserved);
    Assert.All(result.Implementations, item => Assert.Empty(item.AddedAssertionIds));
    Assert.Equal(commands, implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds));
  }

  // A bound same-name function from another native program is not the selected prelude declaration.
  [Fact]
  public async Task RejectsBoundLookalikeDeclaration() {
    var parsed = await Parse(RefinedSource("\"AB\""));
    var translated = Translate(parsed);
    var alien = Translate(parsed).TopLevelDeclarations.OfType<Bpl.Function>().Single(function => function.Name == "$Is");
    var implementations = translated.Implementations.ToList();
    foreach (var assertion in implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).OfType<Bpl.AssertCmd>()) {
      if (assertion.Expr is Bpl.NAryExpr { Fun: Bpl.FunctionCall { FunctionName: "$Is" } } membership) {
        assertion.Expr = new Bpl.NAryExpr(membership.tok, new Bpl.FunctionCall(alien), membership.Args.ToList()) { Type = Bpl.Type.Bool };
      }
    }
    var result = ContractSequenceRefinementProof.Apply(translated, implementations, CancellationToken.None);
    Assert.True(result.Preserved);
    Assert.All(result.Implementations, item => Assert.Empty(item.AddedAssertionIds));
  }

  // Unsupported sequence expressions retain the original proof obligation and still reject invalid results.
  [Fact]
  public async Task UnsupportedTermStillRequiresOriginalProof() {
    var parsed = await Parse("module Model { function Root(values:seq<int>):seq<nat> { values } }");
    var result = await Check(parsed);
    Assert.False(result.Verified);
    Assert.False(parsed.Checker.Accept(parsed.Scope));
    AssertInventory(result);
    Assert.True(result.SequenceRefinement!.Implementations.Sum(item => item.UnsupportedAssertions) > 0);
    Assert.All(result.SequenceRefinement.Implementations, item => Assert.Empty(item.AddedAssertionIds));
  }

  // Checked cuts do not reveal an imported function body hidden by its original export view.
  [Theory]
  [InlineData("provides", false)]
  [InlineData("reveals", true)]
  public async Task PreservesOriginalImportVisibility(string visibility, bool expected) {
    var parsed = await Parse("module Library { export " + visibility + " Values " +
      "function Values():seq<int> { [1, 2] } } " +
      "module Model { import L = Library function Root():seq<nat> { L.Values() } }");
    var result = await Check(parsed);
    Assert.Equal(expected, result.Verified);
    AssertInventory(result);
    Assert.All(result.SequenceRefinement!.Implementations, item => Assert.Empty(item.AddedAssertionIds));
    Assert.False(parsed.Checker.Accept(parsed.Scope));
  }

  // Exhaustion leaves every original assertion intact instead of publishing partial proof evidence.
  [Fact]
  public async Task ExhaustionRetainsOriginalAssertions() {
    var parsed = await Parse(RefinedSource("\"AB\""));
    var translated = Translate(parsed);
    var implementation = translated.Implementations.First(item => item.Blocks.SelectMany(block => block.Cmds)
      .OfType<Bpl.AssertCmd>().Any(IsSequenceMembership));
    var block = implementation.Blocks.First(item => item.Cmds.OfType<Bpl.AssertCmd>().Any(IsSequenceMembership));
    var template = block.Cmds.OfType<Bpl.AssertCmd>().First(IsSequenceMembership);
    var copies = Enumerable.Range(0, (int)ContractReductionBudget.DefaultExpressionNodeLimit)
      .Select(_ => new Bpl.AssertCmd(template.tok, template.Expr)).ToList();
    block.Cmds.InsertRange(block.Cmds.IndexOf(template), copies);
    var result = ContractSequenceRefinementProof.Apply(translated, [implementation], CancellationToken.None);
    Assert.True(result.Preserved, result.Failure);
    Assert.True(Assert.Single(result.Implementations).ExhaustedAssertions > 0);
    Assert.All(copies, assertion => Assert.Contains(assertion, block.Cmds));
    Assert.False(parsed.Checker.Accept(parsed.Scope));
  }

  // Cancellation before proof-step insertion preserves the original code and cannot publish a certificate.
  [Fact]
  public async Task CancellationPreservesOriginalCode() {
    var parsed = await Parse(RefinedSource("\"AB\""));
    var translated = Translate(parsed);
    var implementations = translated.Implementations.ToList();
    var before = implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds).ToList();
    using var timeout = new CancellationTokenSource();
    await timeout.CancelAsync();
    Assert.ThrowsAny<OperationCanceledException>(() => ContractSequenceRefinementProof.Apply(translated, implementations, timeout.Token));
    Assert.Equal(before, implementations.SelectMany(implementation => implementation.Blocks).SelectMany(block => block.Cmds));
    Assert.False(parsed.Checker.Accept(parsed.Scope));
  }

  private static void AssertInventory(ContractSpecificationResult result, bool allowAssertionFree = false) {
    Assert.NotNull(result.SequenceRefinement);
    Assert.True(result.SequenceRefinement.Preserved, result.SequenceRefinement.Failure);
    if (allowAssertionFree) {
      Assert.Empty(result.SequenceRefinement.Implementations);
      Assert.Contains("Model.Root", result.AssertionFreeDeclarations);
      Assert.Equal(0, result.VerifiedCount);
    } else {
      Assert.NotEmpty(result.SequenceRefinement.Implementations);
    }
    Assert.All(result.SequenceRefinement.Implementations, item => {
      Assert.Equal(item.OriginalCommands, item.RetainedCommands);
      Assert.Equal(item.OriginalAssertions.Count, item.RetainedAssertions);
      Assert.All(item.OriginalAssertions, assertion => Assert.Equal(64, assertion.PredicateHash.Length));
    });
  }

  private static string RefinedSource(string body) => "module Model { type Byte = c:char | (c as int) < 256 witness 'a' " +
    "type Bytes = seq<Byte> function Root():Bytes { " + body + " } }";

  private static bool IsSequenceMembership(Bpl.AssertCmd assertion) => assertion.Expr is Bpl.NAryExpr {
    Fun: Bpl.FunctionCall { FunctionName: "$Is" }, Args: [_, Bpl.NAryExpr { Fun: Bpl.FunctionCall { FunctionName: "TSeq" } }]
  };

  private sealed record Parsed(Program Program, BatchErrorReporter Reporter, DafnyOptions Options,
    IReadOnlyList<ContractSource> Sources, ContractSpecificationChecker Checker, ContractSpecificationScope Scope);

  private static async Task<Parsed> Parse(string source) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 10;
    options.ProcsToCheck = ["*"];
    options.ProcsToIgnore = [];
    var sources = new[] { new ContractSource("sequence-proof.dfy", source, ContractHarnessBuilder.Hash(source)) };
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var root = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
      .SelectMany(type => type.Members).OfType<Function>().Single(function => function.Name == "Root");
    var checker = new ContractSpecificationChecker(program, sources, options);
    return new(program, reporter, options, sources, checker, checker.Scope([root]));
  }

  private static Bpl.Program Translate(Parsed parsed) {
    var module = BoogieGenerator.VerifiableModules(parsed.Program).Single(item => item.Name == "Model");
    Microsoft.Dafny.Type.ResetScopes();
    return new BoogieGenerator(parsed.Reporter, parsed.Program.ProofDependencyManager).DoTranslation(parsed.Program, module);
  }

  private static async Task<ContractSpecificationResult> Check(Parsed parsed) {
    using var timeout = new CancellationTokenSource(10000);
    return await parsed.Checker.CheckModuleAsync(parsed.Scope, "Model", timeout.Token,
      deadlineTimestamp: ContractQueryDeadline.AfterMilliseconds(10000));
  }
}
