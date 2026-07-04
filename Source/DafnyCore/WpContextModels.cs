#nullable enable
using System.Collections.Generic;

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

public record WpStatementContext(
  WpSourceSpan SourceSpan,
  string StatementKind,
  string Text,
  int InsertLine,
  int InsertColumn,
  int InsertOffset,
  IReadOnlyList<WpInScopeLocal> InScopeLocals,
  bool ReachesLoopBoundary,
  IReadOnlyList<WpStatementBranch> Branches
);

public record WpStatementBranch(
  string Label,
  string? Guard,
  IReadOnlyList<WpStatementContext> Statements
);

public record WpLoopContext(
  string Relation,
  string Guard,
  WpSourceSpan SourceSpan,
  WpSourceSpan BodySpan,
  IReadOnlyList<string> ExistingInvariants,
  int InvariantInsertLine,
  int InvariantInsertColumn,
  int InvariantInsertOffset,
  int DefinitionInsertOffset,
  int InitializationInsertOffset,
  int PreservationInsertOffset,
  int ExitInsertOffset,
  bool HasBreakOrContinue
);

public record WpContextResult(
  string SourcePath,
  int TargetLine,
  int TargetColumn,
  WpSourceSpan TargetAssertionSpan,
  string EnclosingDeclaration,
  string EnclosingKind,
  string AssertionExpression,
  int CodeFromLine,
  int CodeToLine,
  string CodeText,
  int InsertLine,
  int InsertColumn,
  int InsertOffset,
  IReadOnlyList<WpStatementContext> StatementSpans,
  int DefinitionInsertLine,
  int DefinitionInsertColumn,
  int DefinitionInsertOffset,
  IReadOnlyList<WpInScopeLocal> InScopeLocals,
  IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations
);

public record WpLoopContextResult(
  string SourcePath,
  int TargetLine,
  int TargetColumn,
  WpSourceSpan TargetAssertionSpan,
  string EnclosingDeclaration,
  string EnclosingKind,
  string AssertionExpression,
  string TargetRelation,
  WpLoopContext? Loop,
  IReadOnlyList<WpStatementContext> StatementSpans,
  IReadOnlyList<WpInScopeLocal> InScopeLocals,
  IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations
);
