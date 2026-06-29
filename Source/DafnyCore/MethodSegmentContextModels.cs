#nullable enable
using System.Collections.Generic;

namespace Microsoft.Dafny;

public record MethodSegmentContextResult(
  string SourcePath,
  string MethodName,
  string EnclosingDeclaration,
  string EnclosingKind,
  WpSourceSpan BodySpan,
  int DefinitionInsertLine,
  int DefinitionInsertColumn,
  int DefinitionInsertOffset,
  IReadOnlyList<WpStatementContext> StatementSpans,
  IReadOnlyList<WpInScopeLocal> InScopeLocals,
  IReadOnlyList<WpVisibleDeclaration> VisibleDeclarations
);
