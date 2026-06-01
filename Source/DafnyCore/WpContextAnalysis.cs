#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny;

public class WpContextAnalysisException(string message) : Exception(message);

internal sealed record TargetAssertion(MethodOrConstructor Method, AssertStmt Assert);

public static class WpContextAnalysis {
  public static WpContextResult Analyze(
    Program program,
    string sourcePath,
    string sourceText,
    int targetLine,
    int targetColumn,
    int codeFromLine,
    int codeToLine,
    DafnyOptions options) {
    ValidatePositive("target line", targetLine);
    ValidatePositive("target column", targetColumn);
    ValidatePositive("code-from line", codeFromLine);
    ValidatePositive("code-to line", codeToLine);
    if (codeToLine < codeFromLine) {
      throw new WpContextAnalysisException("--code-to-line must be greater than or equal to --code-from-line.");
    }

    var lineStarts = WpContextSourceTools.LineStartOffsets(sourceText);
    if (targetLine > lineStarts.Count || codeFromLine > lineStarts.Count || codeToLine > lineStarts.Count) {
      throw new WpContextAnalysisException("target and code span lines must be within the source file.");
    }

    var sourceFullPath = Path.GetFullPath(sourcePath);
    var target = FindTargetAssertion(program, sourceFullPath, targetLine, targetColumn);
    if (codeToLine >= target.Assert.StartToken.line) {
      throw new WpContextAnalysisException("the selected code span must end before the target assertion.");
    }
    if (codeFromLine <= target.Method.BodyStartTok.line || codeToLine >= target.Method.EndToken.line) {
      throw new WpContextAnalysisException("the selected code span must stay inside the enclosing declaration body.");
    }

    var selectedStatements = target.Method.Body!.DescendantsAndSelf
      .Where(statement => !ReferenceEquals(statement, target.Assert))
      .Where(statement => WpContextSourceTools.SameFile(statement, sourceFullPath))
      .Where(statement => codeFromLine <= statement.StartToken.line && statement.EndToken.line <= codeToLine)
      .ToList();
    if (!selectedStatements.Any()) {
      throw new WpContextAnalysisException("the selected code span must contain at least one Dafny statement.");
    }

    var insertOffset = WpContextSourceTools.OffsetForLineAndIndent(sourceText, lineStarts, codeFromLine);
    var definitionInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(
      sourceText,
      lineStarts,
      target.Method.StartToken.line);
    return new WpContextResult(
      SourcePath: sourceFullPath,
      TargetLine: target.Assert.StartToken.line,
      TargetColumn: target.Assert.StartToken.col,
      TargetAssertionSpan: WpContextSourceTools.SourceSpan(target.Assert)!,
      EnclosingDeclaration: target.Method.FullDafnyName,
      EnclosingKind: target.Method.WhatKind,
      AssertionExpression: Printer.ExprToString(options, target.Assert.Expr),
      CodeFromLine: codeFromLine,
      CodeToLine: codeToLine,
      CodeText: WpContextSourceTools.SliceLines(sourceText, lineStarts, codeFromLine, codeToLine),
      InsertLine: codeFromLine,
      InsertColumn: WpContextSourceTools.ColumnForOffset(lineStarts, codeFromLine, insertOffset),
      InsertOffset: insertOffset,
      StatementSpans: selectedStatements
        .Select(statement => WpContextSourceTools.StatementContext(
          statement,
          sourceText,
          lineStarts,
          target.Method,
          reachesLoopBoundary: statement is WhileStmt))
        .ToList(),
      DefinitionInsertLine: target.Method.StartToken.line,
      DefinitionInsertColumn: WpContextSourceTools.ColumnForOffset(lineStarts, target.Method.StartToken.line, definitionInsertOffset),
      DefinitionInsertOffset: definitionInsertOffset,
      InScopeLocals: WpContextSourceTools.InScopeLocals(target.Method, codeFromLine),
      VisibleDeclarations: VisibleDeclarations(program, sourceFullPath, sourceText)
    );
  }

  internal static TargetAssertion FindTargetAssertion(
    Program program,
    string sourceFullPath,
    int targetLine,
    int targetColumn) {
    var matches = RootSourceMethods(program)
      .Where(method => method.Body != null)
      .SelectMany(method => method.Body!.DescendantsAndSelf
        .OfType<AssertStmt>()
        .Where(assertStmt => WpContextSourceTools.SameFile(assertStmt, sourceFullPath))
        .Where(assertStmt => WpContextSourceTools.ContainsLineColumn(assertStmt, targetLine, targetColumn))
        .Select(assertStmt => new TargetAssertion(method, assertStmt)))
      .OrderBy(match => WpContextSourceTools.SpanLength(match.Assert))
      .ToList();

    return matches.Count switch {
      0 => throw new WpContextAnalysisException("no assert statement found at the requested target location."),
      1 => matches[0],
      _ => throw new WpContextAnalysisException("multiple assert statements match the requested target location.")
    };
  }

  internal static IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations(
    Program program,
    string sourceFullPath,
    string sourceText) {
    var functions = program.Modules()
      .SelectMany(moduleDefinition => moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>())
      .SelectMany(topLevelDecl => topLevelDecl.Members.OfType<Function>())
      .Where(function => function.StartToken.ActualFilename != null)
      .Where(function => function.WhatKind is "function" or "predicate")
      .OrderBy(function => function.FullDafnyName)
      .Select(function => VisibleFunction(sourceFullPath, sourceText, function));

    var methods = program.Modules()
      .SelectMany(moduleDefinition => moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>())
      .SelectMany(topLevelDecl => topLevelDecl.Members.OfType<MethodOrConstructor>())
      .Where(method => method.StartToken.ActualFilename != null)
      .Where(method => WpContextSourceTools.SameFile(method, sourceFullPath))
      .OrderBy(method => method.FullDafnyName)
      .Select(method => VisibleMethod(sourceText, method));

    return functions.Concat(methods).ToList();
  }

  private static void ValidatePositive(string label, int value) {
    if (value <= 0) {
      throw new WpContextAnalysisException($"{label} must be a positive 1-based value.");
    }
  }

  private static IEnumerable<MethodOrConstructor> RootSourceMethods(Program program) {
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var member in topLevelDecl.Members.OfType<MethodOrConstructor>().OrderBy(member => member.Origin.pos)) {
          if (!member.Origin.FromIncludeDirective(program)) {
            yield return member;
          }
        }
      }
    }
  }

  private static WpVisibleDeclaration VisibleFunction(string sourceFullPath, string sourceText, Function function) {
    var sourcePath = Path.GetFullPath(function.StartToken.ActualFilename!);
    var signature = WpContextSourceTools.SameFile(function, sourceFullPath)
      ? NormalizedSignature(sourceText, function)
      : NormalizedSignature(function);
    return new WpVisibleDeclaration(
      Name: function.Name,
      FullName: function.FullDafnyName,
      Kind: function.WhatKind,
      Line: function.Origin.line,
      Column: function.Origin.col,
      Ghost: function.IsGhost,
      Signature: signature,
      SourcePath: sourcePath,
      DeclarationSpan: WpContextSourceTools.SourceSpan(function),
      ContractSpan: WpContextSourceTools.HeaderSpan(function),
      BodySpan: WpContextSourceTools.BodySpan(function)
    );
  }

  private static WpVisibleDeclaration VisibleMethod(string sourceText, MethodOrConstructor method) {
    return new WpVisibleDeclaration(
      Name: method.Name,
      FullName: method.FullDafnyName,
      Kind: method.WhatKind,
      Line: method.Origin.line,
      Column: method.Origin.col,
      Ghost: method.IsGhost,
      Signature: NormalizedSignature(sourceText, method),
      SourcePath: Path.GetFullPath(method.StartToken.ActualFilename!),
      DeclarationSpan: WpContextSourceTools.SourceSpan(method),
      ContractSpan: WpContextSourceTools.HeaderSpan(method),
      BodySpan: WpContextSourceTools.BodySpan(method)
    );
  }

  private static string NormalizedSignature(string sourceText, Function function) {
    var end = function.BodyStartTok == Token.NoToken ? function.EndToken.pos : function.BodyStartTok.pos;
    if (end <= function.StartToken.pos || end > sourceText.Length) {
      return function.Name;
    }
    return string.Join(" ", sourceText[function.StartToken.pos..end].Split(default(string[]), StringSplitOptions.RemoveEmptyEntries));
  }

  private static string NormalizedSignature(Function function) {
    if (function.BodyStartTok == Token.NoToken) {
      return function.Name;
    }

    var builder = new StringBuilder();
    for (var token = function.StartToken; token != null && token.pos < function.BodyStartTok.pos; token = token.Next) {
      builder.Append(token.LeadingTrivia);
      builder.Append(token.val);
      builder.Append(token.TrailingTrivia);
    }
    return string.Join(" ", builder.ToString().Split(default(string[]), StringSplitOptions.RemoveEmptyEntries));
  }

  private static string NormalizedSignature(string sourceText, MethodOrConstructor method) {
    var end = method.BodyStartTok == Token.NoToken ? WpContextSourceTools.EndOffset(method) : method.BodyStartTok.pos;
    if (end <= method.StartToken.pos || end > sourceText.Length) {
      return method.Name;
    }
    return string.Join(" ", sourceText[method.StartToken.pos..end].Split(default(string[]), StringSplitOptions.RemoveEmptyEntries));
  }
}
