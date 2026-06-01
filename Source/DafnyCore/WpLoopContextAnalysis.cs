#nullable enable
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public static class WpLoopContextAnalysis {
  public static WpLoopContextResult Analyze(
    Program program,
    string sourcePath,
    string sourceText,
    int targetLine,
    int targetColumn,
    int? loopLine,
    DafnyOptions options) {
    var sourceFullPath = Path.GetFullPath(sourcePath);
    var lineStarts = WpContextSourceTools.LineStartOffsets(sourceText);
    if (targetLine <= 0 || targetColumn <= 0 || targetLine > lineStarts.Count) {
      throw new WpContextAnalysisException("target line and column must be positive 1-based values within the source file.");
    }
    if (loopLine is { } selectedLoopLine && (selectedLoopLine <= 0 || selectedLoopLine > lineStarts.Count)) {
      throw new WpContextAnalysisException("--loop-line must be a positive 1-based line within the source file.");
    }

    var target = WpContextAnalysis.FindTargetAssertion(program, sourceFullPath, targetLine, targetColumn);
    var loop = SelectLoop(target.Method, sourceFullPath, target.Assert, loopLine);
    if (loop.Guard == null) {
      throw new WpContextAnalysisException("selected while loop must have an explicit guard.");
    }
    if (loop.Body == null) {
      throw new WpContextAnalysisException("selected while loop must have a body.");
    }

    var relation = target.Assert.StartToken.line > loop.EndToken.line ? "after_loop" : "inside_loop_body";
    return new WpLoopContextResult(
      SourcePath: sourceFullPath,
      TargetLine: target.Assert.StartToken.line,
      TargetColumn: target.Assert.StartToken.col,
      TargetAssertionSpan: WpContextSourceTools.SourceSpan(target.Assert)!,
      EnclosingDeclaration: target.Method.FullDafnyName,
      EnclosingKind: target.Method.WhatKind,
      AssertionExpression: Printer.ExprToString(options, target.Assert.Expr),
      TargetRelation: relation,
      Loop: LoopContext(loop, relation, sourceText, lineStarts, target.Method, options),
      StatementSpans: StatementsBetween(loop, target, relation, sourceText, lineStarts),
      InScopeLocals: WpContextSourceTools.InScopeLocals(target.Method, loop.StartToken.line),
      VisibleDeclarations: WpContextAnalysis.VisibleDeclarations(program, sourceFullPath, sourceText)
    );
  }

  private static WhileStmt SelectLoop(
    MethodOrConstructor method,
    string sourceFullPath,
    AssertStmt targetAssert,
    int? loopLine) {
    var loops = method.Body!.DescendantsAndSelf
      .OfType<WhileStmt>()
      .Where(loop => WpContextSourceTools.SameFile(loop, sourceFullPath))
      .Where(loop => loop.Body != null)
      .ToList();
    if (loopLine != null) {
      var loopLineMatches = loops
        .Where(loop => WpContextSourceTools.ContainsLine(loop, loopLine.Value))
        .OrderBy(loop => loop.StartToken.line == loopLine.Value ? 0 : 1)
        .ThenBy(WpContextSourceTools.SpanLength)
        .ToList();
      return loopLineMatches.Count switch {
        0 => throw new WpContextAnalysisException("no while loop found at the requested --loop-line."),
        _ => loopLineMatches[0]
      };
    }

    var candidates = loops
      .Where(loop => targetAssert.StartToken.line > loop.EndToken.line || WpContextSourceTools.ContainsLine(loop, targetAssert.StartToken.line))
      .ToList();
    return candidates.Count switch {
      0 => throw new WpContextAnalysisException("no while loop found for the requested target assertion."),
      1 => candidates[0],
      _ => throw new WpContextAnalysisException("multiple while loops could explain the target assertion; pass --loop-line.")
    };
  }

  private static IReadOnlyList<WpStatementContext> StatementsBetween(
    WhileStmt loop,
    TargetAssertion target,
    string relation,
    string sourceText,
    IReadOnlyList<int> lineStarts) {
    IEnumerable<Statement> statements = relation == "after_loop"
      ? target.Method.Body!.Body
        .Where(statement => loop.EndToken.line < statement.StartToken.line && statement.EndToken.line < target.Assert.StartToken.line)
      : loop.Body!.Body
        .Where(statement => statement.EndToken.line < target.Assert.StartToken.line);

    return statements
      .Select(statement => WpContextSourceTools.StatementContext(
        statement,
        sourceText,
        lineStarts,
        target.Method,
        reachesLoopBoundary: relation == "after_loop" && ReferenceEquals(statement, loop)))
      .ToList();
  }

  private static WpLoopContext LoopContext(
    WhileStmt loop,
    string relation,
    string sourceText,
    IReadOnlyList<int> lineStarts,
    MethodOrConstructor method,
    DafnyOptions options) {
    var body = loop.Body!;
    var sourceSpan = WpContextSourceTools.SourceSpan(loop)
      ?? throw new WpContextAnalysisException("selected loop is missing source span.");
    var bodySpan = WpContextSourceTools.SourceSpan(body)
      ?? throw new WpContextAnalysisException("selected loop body is missing source span.");
    var invariantInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, body.StartToken.line);
    var definitionInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, method.StartToken.line);
    var initializationInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, loop.StartToken.line);
    var preservationInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, body.EndToken.line);
    var exitInsertLine = loop.EndToken.line < lineStarts.Count ? loop.EndToken.line + 1 : loop.EndToken.line;
    var exitInsertOffset = loop.EndToken.line < lineStarts.Count
      ? WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, exitInsertLine)
      : WpContextSourceTools.EndOffset(loop);

    return new WpLoopContext(
      Relation: relation,
      Guard: Printer.ExprToString(options, loop.Guard!),
      SourceSpan: sourceSpan,
      BodySpan: bodySpan,
      ExistingInvariants: loop.Invariants.Select(invariant => Printer.ExprToString(options, invariant.E)).ToList(),
      InvariantInsertLine: body.StartToken.line,
      InvariantInsertColumn: WpContextSourceTools.ColumnForOffset(lineStarts, body.StartToken.line, invariantInsertOffset),
      InvariantInsertOffset: invariantInsertOffset,
      DefinitionInsertOffset: definitionInsertOffset,
      InitializationInsertOffset: initializationInsertOffset,
      PreservationInsertOffset: preservationInsertOffset,
      ExitInsertOffset: exitInsertOffset,
      HasBreakOrContinue: body.DescendantsAndSelf.OfType<BreakOrContinueStmt>().Any()
    );
  }
}
