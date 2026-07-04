#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

internal static class WpContextSourceTools {
  public static int ColumnForOffset(IReadOnlyList<int> lineStarts, int line, int offset) {
    return offset - lineStarts[line - 1] + 1;
  }

  public static bool SameFile(INode node, string sourceFullPath) {
    var actual = node.StartToken.ActualFilename;
    return actual != null && Path.GetFullPath(actual) == sourceFullPath;
  }

  public static bool ContainsLine(INode node, int line) {
    return node.StartToken.line <= line && line <= node.EndToken.line;
  }

  public static bool ContainsLineColumn(INode node, int line, int column) {
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

  public static WpSourceSpan? SourceSpan(INode node) {
    return SpanFromTokens(node.StartToken, node.EndToken);
  }

  public static WpSourceSpan? HeaderSpan(Function function) {
    return function.BodyStartTok == Token.NoToken
      ? SourceSpan(function)
      : SpanFromOffsets(function.StartToken, function.BodyStartTok.pos, function.BodyStartTok.line);
  }

  public static WpSourceSpan? HeaderSpan(MethodOrConstructor method) {
    return method.BodyStartTok == Token.NoToken
      ? SourceSpan(method)
      : SpanFromOffsets(method.StartToken, method.BodyStartTok.pos, method.BodyStartTok.line);
  }

  public static WpSourceSpan? BodySpan(Function function) {
    return function.BodyStartTok == Token.NoToken ? null : SpanFromTokens(function.BodyStartTok, function.EndToken);
  }

  public static WpSourceSpan? BodySpan(MethodOrConstructor method) {
    return method.BodyStartTok == Token.NoToken ? null : SpanFromTokens(method.BodyStartTok, method.EndToken);
  }

  public static WpSourceSpan? SpanFromTokens(IOrigin start, IOrigin end) {
    return SpanFromOffsets(start, end.pos + end.val.Length, end.line);
  }

  public static WpSourceSpan? SpanFromOffsets(IOrigin start, int endOffset, int endLine) {
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

  public static int EndOffset(INode node) {
    return node.EndToken.pos + node.EndToken.val.Length;
  }

  public static int SpanLength(INode node) {
    return node.EndToken.pos - node.StartToken.pos;
  }

  public static List<int> LineStartOffsets(string text) {
    var offsets = new List<int> { 0 };
    for (var index = 0; index < text.Length; index++) {
      if (text[index] == '\n') {
        offsets.Add(index + 1);
      }
    }
    return offsets;
  }

  public static int OffsetForLineAndIndent(string text, IReadOnlyList<int> lineStarts, int line) {
    var offset = lineStarts[line - 1];
    while (offset < text.Length && text[offset] is ' ' or '\t') {
      offset++;
    }
    return offset;
  }

  public static string SliceLines(string text, IReadOnlyList<int> lineStarts, int fromLine, int toLine) {
    var start = lineStarts[fromLine - 1];
    var end = toLine < lineStarts.Count ? lineStarts[toLine] : text.Length;
    return text[start..end];
  }

  public static string StatementKind(Statement statement) => statement switch {
    AssignStatement => "assign",
    VarDeclStmt => "var_decl",
    CallStmt => "call",
    AssertStmt => "assert",
    IfStmt => "if",
    NestedMatchStmt => "match",
    WhileStmt => "while",
    BreakOrContinueStmt breakOrContinue => breakOrContinue.IsContinue ? "continue" : "break",
    _ => statement.GetType().Name,
  };

  public static WpStatementContext StatementContext(
    Statement statement,
    string sourceText,
    IReadOnlyList<int> lineStarts,
    MethodOrConstructor method,
    bool reachesLoopBoundary,
    DafnyOptions? options = null) {
    var insertOffset = OffsetForLineAndIndent(sourceText, lineStarts, statement.StartToken.line);
    var sourceSpan = SourceSpan(statement);
    if (sourceSpan == null) {
      throw new WpContextAnalysisException("selected statement is missing source span.");
    }
    return new WpStatementContext(
      SourceSpan: sourceSpan,
      StatementKind: StatementKind(statement),
      Text: SliceLines(sourceText, lineStarts, statement.StartToken.line, statement.EndToken.line),
      InsertLine: statement.StartToken.line,
      InsertColumn: ColumnForOffset(lineStarts, statement.StartToken.line, insertOffset),
      InsertOffset: insertOffset,
      InScopeLocals: InScopeLocals(method, statement.StartToken.line),
      ReachesLoopBoundary: reachesLoopBoundary,
      Branches: options == null
        ? new List<WpStatementBranch>()
        : StatementBranches(statement, sourceText, lineStarts, method, options)
    );
  }

  public static bool ContainsLoop(Statement statement) {
    return statement is LoopStmt || statement.SubStatements.Any(ContainsLoop);
  }

  private static IReadOnlyList<WpStatementBranch> StatementBranches(
    Statement statement,
    string sourceText,
    IReadOnlyList<int> lineStarts,
    MethodOrConstructor method,
    DafnyOptions options) {
    var branches = new List<WpStatementBranch>();
    switch (statement) {
      case IfStmt ifStmt: {
          var guard = ifStmt.Guard == null ? null : Printer.ExprToString(options, ifStmt.Guard);
          branches.Add(Branch("then", guard, ifStmt.Thn.Body, sourceText, lineStarts, method, options));
          switch (ifStmt.Els) {
            case BlockStmt elseBlock:
              branches.Add(Branch("else", null, elseBlock.Body, sourceText, lineStarts, method, options));
              break;
            case Statement elseStatement:
              branches.Add(Branch(
                "else", null, new List<Statement> { elseStatement }, sourceText, lineStarts, method, options));
              break;
          }
          break;
        }
      case OneBodyLoopStmt loopStmt when loopStmt.Body != null: {
          var guard = loopStmt is WhileStmt { Guard: { } whileGuard }
            ? Printer.ExprToString(options, whileGuard)
            : null;
          branches.Add(Branch("body", guard, loopStmt.Body.Body, sourceText, lineStarts, method, options));
          break;
        }
      case NestedMatchStmt matchStmt: {
          foreach (var matchCase in matchStmt.Cases) {
            var label = PatternLabel(matchCase.Pat, options);
            var body = matchCase.Body.Count == 1 && matchCase.Body[0] is BlockStmt caseBlock
              ? caseBlock.Body
              : matchCase.Body;
            branches.Add(Branch(
              $"case {label}", label, body, sourceText, lineStarts, method, options));
          }
          break;
        }
      case BlockStmt blockStmt:
        branches.Add(Branch("block", null, blockStmt.Body, sourceText, lineStarts, method, options));
        break;
    }
    return branches;
  }

  private static WpStatementBranch Branch(
    string label,
    string? guard,
    IEnumerable<Statement> statements,
    string sourceText,
    IReadOnlyList<int> lineStarts,
    MethodOrConstructor method,
    DafnyOptions options) {
    return new WpStatementBranch(
      Label: label,
      Guard: guard,
      Statements: statements
        .Select(child => StatementContext(child, sourceText, lineStarts, method, ContainsLoop(child), options))
        .ToList()
    );
  }

  private static string PatternLabel(ExtendedPattern pattern, DafnyOptions options) {
    return pattern switch {
      IdPattern idPattern => idPattern.Id,
      LitPattern litPattern => Printer.ExprToString(options, litPattern.OrigLit),
      _ => pattern.GetType().Name,
    };
  }

  public static IReadOnlyList<WpInScopeLocal> InScopeLocals(MethodOrConstructor method, int insertLine) {
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
}
