using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NaturalLanguageResolverTest {
  private const string FullFilePath = "untitled:NaturalLanguageResolverTest";
  private static async Task<(Program Program, BatchErrorReporter Reporter)> ParseAndResolve(string dafnyProgramText,
    DafnyOptions options) {
    var rootUri = new Uri(FullFilePath);
    Microsoft.Dafny.Type.ResetScopes();
    var reporter = new BatchErrorReporter(options);
    var parseResult = await ProgramParser.Parse(dafnyProgramText, rootUri, reporter);
    var resolver = new ProgramResolver(parseResult.Program);
    await resolver.Resolve(CancellationToken.None);
    return (parseResult.Program, reporter);
  }

  private static Method GetMethod(Program program, string methodName) {
    var defaultClass = Assert.Single(program.DefaultModuleDef.TopLevelDecls.OfType<DefaultClassDecl>());
    return Assert.Single(defaultClass.Members.OfType<Method>().Where(method => method.Name == methodName));
  }

  private static IEnumerable<Statement> DescendantStatements(Statement root) {
    var stack = new Stack<Statement>();
    stack.Push(root);

    while (stack.Count > 0) {
      var current = stack.Pop();
      yield return current;
      foreach (var child in current.SubStatements) {
        stack.Push(child);
      }
    }
  }

  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NaturalLanguageBlocks_DoNotReportPlaceholderWarnings_InLegacyAndPreType(bool typeSystemRefresh) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.NaturalLanguageBlocks, true);
    options.Set(CommonOptionBag.TypeSystemRefresh, typeSystemRefresh);

    var (_, reporter) = await ParseAndResolve(@"
method UsesNaturalLanguageBlocks() {
  assert ``pick a deterministic integer`` == 0;
  ``increment x in a human-readable way``;
}
", options);

    var diagnostics = reporter.AllMessages
      .Where(message => message.Level == ErrorLevel.Warning)
      .Where(message => message.Source == MessageSource.Resolver)
      .ToList();

    Assert.Equal(0, reporter.ErrorCount);
    Assert.Empty(diagnostics);
  }

  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NaturalLanguageExpression_InfersTypesFromContext_InLegacyAndPreType(bool typeSystemRefresh) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.NaturalLanguageBlocks, true);
    options.Set(CommonOptionBag.TypeSystemRefresh, typeSystemRefresh);

    var (program, reporter) = await ParseAndResolve(@"
method InferFromContext() {
  if ``decide whether to proceed`` {
    assert ``guard for implication`` ==> true;
  }

  var next := ``step increment`` + 1;
  var extendedSeq := [0] + ``tail sequence from nlp``;
  var unionSet := {0} + ``incremental set from nlp``;
  var mergedMap := map[0 := true] + ``incoming map from nlp``;
  var nestedSeq := [{0}] + ``extra groups from nlp``;
  var lookedUp := (map[0 := true] + ``lookup source map from nlp``)[``lookup key from nlp``];

  assert next >= 0;
  assert |extendedSeq| >= 1;
  assert 0 in unionSet;
  assert 0 in mergedMap;
  assert |nestedSeq| >= 1;
  assert lookedUp || !lookedUp;
}
", options);

    Assert.Equal(0, reporter.ErrorCount);

    var method = GetMethod(program, "InferFromContext");
    var expressions = DescendantStatements(method.Body!)
      .SelectMany(statement => statement.SubExpressions)
      .SelectMany(expression => (expression.Resolved ?? expression).DescendantsAndSelf.OfType<NaturalLanguageExpression>())
      .ToDictionary(expression => expression.RawContent, expression => expression);

    Assert.Equal(9, expressions.Count);
    Assert.True(expressions["decide whether to proceed"].Type.IsBoolType);
    Assert.True(expressions["guard for implication"].Type.IsBoolType);
    Assert.True(expressions["step increment"].Type.IsIntegerType);

    var seqType = expressions["tail sequence from nlp"].Type.AsSeqType;
    Assert.NotNull(seqType);
    Assert.True(seqType!.Arg.IsIntegerType);

    var setType = expressions["incremental set from nlp"].Type.AsSetType;
    Assert.NotNull(setType);
    Assert.True(setType!.Finite);
    Assert.True(setType.Arg.IsIntegerType);

    var mapType = expressions["incoming map from nlp"].Type.AsMapType;
    Assert.NotNull(mapType);
    Assert.True(mapType!.Finite);
    Assert.True(mapType.Domain.IsIntegerType);
    Assert.True(mapType.Range.IsBoolType);

    var nestedType = expressions["extra groups from nlp"].Type.AsSeqType;
    Assert.NotNull(nestedType);
    var nestedElementType = nestedType!.Arg.AsSetType;
    Assert.NotNull(nestedElementType);
    Assert.True(nestedElementType!.Finite);
    Assert.True(nestedElementType.Arg.IsIntegerType);

    var lookupMapType = expressions["lookup source map from nlp"].Type.AsMapType;
    Assert.NotNull(lookupMapType);
    Assert.True(lookupMapType!.Finite);
    Assert.True(lookupMapType.Domain.IsIntegerType);
    Assert.True(lookupMapType.Range.IsBoolType);
    Assert.True(expressions["lookup key from nlp"].Type.IsIntegerType);
  }

  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NaturalLanguageExpression_ReportsUnderspecifiedType_WhenContextDoesNotConstrainIt(bool typeSystemRefresh) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(CommonOptionBag.NaturalLanguageBlocks, true);
    options.Set(CommonOptionBag.TypeSystemRefresh, typeSystemRefresh);

    var (_, reporter) = await ParseAndResolve(@"
method MissingNaturalLanguageTypeContext() {
  assert ``left operand has no type context`` == ``right operand has no type context``;
}
", options);

    Assert.True(reporter.ErrorCount > 0);
    Assert.Contains(reporter.AllMessages,
      message => message.Level == ErrorLevel.Error &&
                 message.Source == MessageSource.Resolver &&
                 message.ErrorId == ResolutionErrors.ErrorId.r_var_type_undetermined.ToString() &&
                 message.Message.Contains("natural-language expression") &&
                 message.Message.Contains("underspecified"));
  }
}
