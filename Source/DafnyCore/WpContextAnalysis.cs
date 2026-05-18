#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny;

public record WpVisibleDeclaration(
  string Name,
  string FullName,
  string Kind,
  int Line,
  int Column,
  bool Ghost,
  string Signature,
  string? SourcePath,
  WpSourceSpan? DeclarationSpan,
  WpSourceSpan? ContractSpan,
  WpSourceSpan? BodySpan
);

public record WpInScopeLocal(
  string Name,
  string Type,
  string Kind,
  int Line,
  int Column,
  bool Ghost
);

public record WpSourceSpan(
  string SourcePath,
  int StartLine,
  int EndLine,
  int StartOffset,
  int EndOffset
);

public record WpContextResult(
  string SourcePath,
  int TargetLine,
  int TargetColumn,
  string EnclosingDeclaration,
  string EnclosingKind,
  string AssertionExpression,
  int CodeFromLine,
  int CodeToLine,
  string CodeText,
  int InsertLine,
  int InsertColumn,
  int InsertOffset,
  IReadOnlyList<WpInScopeLocal> InScopeLocals,
  IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations
);

public class WpContextAnalysisException(string message) : Exception(message);

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

    var lineStarts = LineStartOffsets(sourceText);
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
      .Where(statement => SameFile(statement, sourceFullPath))
      .Where(statement => codeFromLine <= statement.StartToken.line && statement.EndToken.line <= codeToLine)
      .ToList();
    if (!selectedStatements.Any()) {
      throw new WpContextAnalysisException("the selected code span must contain at least one Dafny statement.");
    }

    var insertOffset = OffsetForLineAndIndent(sourceText, lineStarts, codeFromLine);
    var insertColumn = insertOffset - lineStarts[codeFromLine - 1] + 1;
    return new WpContextResult(
      SourcePath: sourceFullPath,
      TargetLine: target.Assert.StartToken.line,
      TargetColumn: target.Assert.StartToken.col,
      EnclosingDeclaration: target.Method.FullDafnyName,
      EnclosingKind: target.Method.WhatKind,
      AssertionExpression: Printer.ExprToString(options, target.Assert.Expr),
      CodeFromLine: codeFromLine,
      CodeToLine: codeToLine,
      CodeText: SliceLines(sourceText, lineStarts, codeFromLine, codeToLine),
      InsertLine: codeFromLine,
      InsertColumn: insertColumn,
      InsertOffset: insertOffset,
      InScopeLocals: InScopeLocals(target.Method, codeFromLine),
      VisibleDeclarations: VisibleDeclarations(program, sourceFullPath, sourceText)
    );
  }

  private static void ValidatePositive(string label, int value) {
    if (value <= 0) {
      throw new WpContextAnalysisException($"{label} must be a positive 1-based value.");
    }
  }

  private static TargetAssertion FindTargetAssertion(
    Program program,
    string sourceFullPath,
    int targetLine,
    int targetColumn) {
    var matches = RootSourceMethods(program)
      .Where(method => method.Body != null)
      .SelectMany(method => method.Body!.DescendantsAndSelf
        .OfType<AssertStmt>()
        .Where(assertStmt => SameFile(assertStmt, sourceFullPath))
        .Where(assertStmt => ContainsLineColumn(assertStmt, targetLine, targetColumn))
        .Select(assertStmt => new TargetAssertion(method, assertStmt)))
      .OrderBy(match => SpanLength(match.Assert))
      .ToList();

    return matches.Count switch {
      0 => throw new WpContextAnalysisException("no assert statement found at the requested target location."),
      1 => matches[0],
      _ => throw new WpContextAnalysisException("multiple assert statements match the requested target location.")
    };
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

  private static IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations(
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
      .Where(method => SameFile(method, sourceFullPath))
      .OrderBy(method => method.FullDafnyName)
      .Select(method => VisibleMethod(sourceText, method));

    return functions.Concat(methods).ToList();
  }

  private static WpVisibleDeclaration VisibleFunction(string sourceFullPath, string sourceText, Function function) {
    var sourcePath = Path.GetFullPath(function.StartToken.ActualFilename!);
    var signature = SameFile(function, sourceFullPath)
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
      DeclarationSpan: SourceSpan(function),
      ContractSpan: HeaderSpan(function),
      BodySpan: BodySpan(function)
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
      DeclarationSpan: SourceSpan(method),
      ContractSpan: HeaderSpan(method),
      BodySpan: BodySpan(method)
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
    var end = method.BodyStartTok == Token.NoToken ? EndOffset(method) : method.BodyStartTok.pos;
    if (end <= method.StartToken.pos || end > sourceText.Length) {
      return method.Name;
    }
    return string.Join(" ", sourceText[method.StartToken.pos..end].Split(default(string[]), StringSplitOptions.RemoveEmptyEntries));
  }

  private static IReadOnlyList<WpInScopeLocal> InScopeLocals(MethodOrConstructor method, int insertLine) {
    var locals = new List<WpInScopeLocal>();
    foreach (var formal in method.Ins.Concat(method.Outs).Where(formal => formal.HasName)) {
      locals.Add(LocalFromVariable(formal, formal.InParam ? "parameter" : "return"));
    }
    if (method.Body != null) {
      AddBlockLocals(method.Body.Body, insertLine, locals);
    }
    return locals
      .GroupBy(local => local.Name)
      .Select(group => group.Last())
      .OrderBy(local => local.Name)
      .ToList();
  }

  private static bool AddBlockLocals(
    IEnumerable<Statement> statements,
    int insertLine,
    List<WpInScopeLocal> locals) {
    foreach (var statement in statements) {
      if (statement.EndToken.line < insertLine) {
        if (statement is VarDeclStmt varDeclStmt) {
          AddVarDeclLocals(varDeclStmt, locals);
        }
        continue;
      }
      if (ContainsLine(statement, insertLine)) {
        return AddNestedScopeLocals(statement, insertLine, locals);
      }
      return true;
    }
    return true;
  }

  private static bool AddNestedScopeLocals(
    Statement statement,
    int insertLine,
    List<WpInScopeLocal> locals) {
    switch (statement) {
      case BlockStmt blockStmt:
        return AddBlockLocals(blockStmt.Body, insertLine, locals);
      case OneBodyLoopStmt { Body: { } body }:
        return AddBlockLocals(body.Body, insertLine, locals);
      case IfStmt ifStmt:
        if (ContainsLine(ifStmt.Thn, insertLine)) {
          return AddBlockLocals(ifStmt.Thn.Body, insertLine, locals);
        }
        if (ifStmt.Els != null && ContainsLine(ifStmt.Els, insertLine)) {
          return AddNestedScopeLocals(ifStmt.Els, insertLine, locals);
        }
        return true;
      case NestedMatchStmt matchStmt:
        foreach (var matchCase in matchStmt.Cases) {
          if (ContainsLine(matchCase, insertLine)) {
            return AddBlockLocals(matchCase.Body, insertLine, locals);
          }
        }
        return true;
      default:
        return true;
    }
  }

  private static void AddVarDeclLocals(VarDeclStmt varDeclStmt, List<WpInScopeLocal> locals) {
    foreach (var local in varDeclStmt.Locals.Where(local => !LocalVariable.HasWildcardName(local))) {
      locals.Add(LocalFromVariable(local, "local"));
    }
  }

  private static WpInScopeLocal LocalFromVariable(IVariable variable, string kind) {
    var origin = variable is NodeWithOrigin node ? node.Origin : Token.NoToken;
    return new WpInScopeLocal(
      Name: variable.Name,
      Type: variable.Type.ToString(),
      Kind: kind,
      Line: origin.line,
      Column: origin.col,
      Ghost: variable.IsGhost
    );
  }

  private static bool ContainsLine(INode node, int line) {
    return node.StartToken.line <= line && line <= node.EndToken.line;
  }

  private static WpSourceSpan? SourceSpan(INode node) {
    return SpanFromTokens(node.StartToken, node.EndToken);
  }

  private static WpSourceSpan? HeaderSpan(Function function) {
    return function.BodyStartTok == Token.NoToken
      ? SourceSpan(function)
      : SpanFromOffsets(function.StartToken, function.BodyStartTok.pos, function.BodyStartTok.line);
  }

  private static WpSourceSpan? HeaderSpan(MethodOrConstructor method) {
    return method.BodyStartTok == Token.NoToken
      ? SourceSpan(method)
      : SpanFromOffsets(method.StartToken, method.BodyStartTok.pos, method.BodyStartTok.line);
  }

  private static WpSourceSpan? BodySpan(Function function) {
    return function.BodyStartTok == Token.NoToken ? null : SpanFromTokens(function.BodyStartTok, function.EndToken);
  }

  private static WpSourceSpan? BodySpan(MethodOrConstructor method) {
    return method.BodyStartTok == Token.NoToken ? null : SpanFromTokens(method.BodyStartTok, method.EndToken);
  }

  private static WpSourceSpan? SpanFromTokens(IOrigin start, IOrigin end) {
    return SpanFromOffsets(start, end.pos + end.val.Length, end.line);
  }

  private static WpSourceSpan? SpanFromOffsets(IOrigin start, int endOffset, int endLine) {
    if (start.ActualFilename == null) {
      return null;
    }
    return new WpSourceSpan(
      SourcePath: Path.GetFullPath(start.ActualFilename),
      StartLine: start.line,
      EndLine: endLine,
      StartOffset: start.pos,
      EndOffset: endOffset
    );
  }

  private static int EndOffset(INode node) {
    return node.EndToken.pos + node.EndToken.val.Length;
  }

  private static bool SameFile(INode node, string sourceFullPath) {
    var actual = node.StartToken.ActualFilename;
    return actual != null && Path.GetFullPath(actual) == sourceFullPath;
  }

  private static bool ContainsLineColumn(INode node, int line, int column) {
    var start = node.StartToken;
    var end = node.EndToken;
    if (line < start.line || end.line < line) {
      return false;
    }
    if (line == start.line && column < start.col) {
      return false;
    }
    return line != end.line || column <= end.col + end.val.Length;
  }

  private static int SpanLength(INode node) {
    return node.EndToken.pos - node.StartToken.pos;
  }

  private static List<int> LineStartOffsets(string text) {
    var offsets = new List<int> { 0 };
    for (var index = 0; index < text.Length; index++) {
      if (text[index] == '\n') {
        offsets.Add(index + 1);
      }
    }
    return offsets;
  }

  private static int OffsetForLineAndIndent(string text, IReadOnlyList<int> lineStarts, int line) {
    var offset = lineStarts[line - 1];
    while (offset < text.Length && text[offset] is ' ' or '\t') {
      offset++;
    }
    return offset;
  }

  private static string SliceLines(string text, IReadOnlyList<int> lineStarts, int fromLine, int toLine) {
    var start = lineStarts[fromLine - 1];
    var end = toLine < lineStarts.Count ? lineStarts[toLine] : text.Length;
    return text[start..end];
  }

  private sealed record TargetAssertion(MethodOrConstructor Method, AssertStmt Assert);
}
