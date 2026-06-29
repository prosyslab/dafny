#nullable enable
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public static class MethodSegmentContextAnalysis {
  public static MethodSegmentContextResult Analyze(
    Program program,
    string sourcePath,
    string sourceText,
    string? methodName) {
    if (string.IsNullOrWhiteSpace(methodName)) {
      throw new WpContextAnalysisException("--method-name must not be empty.");
    }

    var sourceFullPath = Path.GetFullPath(sourcePath);
    var methods = RootSourceMethods(program, sourceFullPath)
      .Where(candidate => candidate.Name == methodName || candidate.FullDafnyName == methodName)
      .OrderBy(candidate => candidate.Origin.pos)
      .ToList();

    if (methods.Count == 0) {
      throw new WpContextAnalysisException($"no method found for --method-name {methodName}.");
    }
    if (methods.Count > 1) {
      throw new WpContextAnalysisException($"multiple methods found for --method-name {methodName}.");
    }
    if (methods[0].Body == null) {
      throw new WpContextAnalysisException($"method {methodName} has no body.");
    }

    var target = methods[0];
    var lineStarts = WpContextSourceTools.LineStartOffsets(sourceText);
    var definitionInsertOffset = WpContextSourceTools.OffsetForLineAndIndent(
      sourceText,
      lineStarts,
      target.StartToken.line);
    var bodySpan = WpContextSourceTools.BodySpan(target);
    if (bodySpan == null) {
      throw new WpContextAnalysisException($"method {methodName} has no body span.");
    }

    return new MethodSegmentContextResult(
      SourcePath: sourceFullPath,
      MethodName: target.Name,
      EnclosingDeclaration: target.FullDafnyName,
      EnclosingKind: target.WhatKind,
      BodySpan: bodySpan,
      DefinitionInsertLine: target.StartToken.line,
      DefinitionInsertColumn: WpContextSourceTools.ColumnForOffset(
        lineStarts,
        target.StartToken.line,
        definitionInsertOffset),
      DefinitionInsertOffset: definitionInsertOffset,
      StatementSpans: target.Body!.Body
        .Where(statement => WpContextSourceTools.SameFile(statement, sourceFullPath))
        .Select(statement => WpContextSourceTools.StatementContext(
          statement,
          sourceText,
          lineStarts,
          target,
          reachesLoopBoundary: statement is WhileStmt))
        .ToList(),
      InScopeLocals: WpContextSourceTools.InScopeLocals(target, target.BodyStartTok.line),
      VisibleDeclarations: WpContextAnalysis.VisibleDeclarations(program, sourceFullPath, sourceText)
    );
  }

  private static IEnumerable<MethodOrConstructor> RootSourceMethods(Program program, string sourceFullPath) {
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
        foreach (var member in topLevelDecl.Members.OfType<MethodOrConstructor>().OrderBy(member => member.Origin.pos)) {
          if (!member.Origin.FromIncludeDirective(program) &&
              WpContextSourceTools.SameFile(member, sourceFullPath)) {
            yield return member;
          }
        }
      }
    }
  }
}
