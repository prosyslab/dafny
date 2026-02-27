#nullable enable
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents an experimental natural-language block statement delimited by double backticks.
/// The parser stores raw content and delimiter origins, and later phases currently treat it as a semantic placeholder.
/// </summary>
public class NaturalLanguageStatement : Statement, ICloneable<NaturalLanguageStatement> {
  public string RawContent = null!;
  public IOrigin OpeningDelimiter = null!;
  public IOrigin ClosingDelimiter = null!;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(RawContent != null);
    Contract.Invariant(OpeningDelimiter != null);
    Contract.Invariant(ClosingDelimiter != null);
  }

  [SyntaxConstructor]
  public NaturalLanguageStatement(IOrigin origin, string rawContent, IOrigin openingDelimiter, IOrigin closingDelimiter, Attributes? attributes = null)
    : base(origin, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(rawContent != null);
    Contract.Requires(openingDelimiter != null);
    Contract.Requires(closingDelimiter != null);
    RawContent = rawContent!;
    OpeningDelimiter = openingDelimiter!;
    ClosingDelimiter = closingDelimiter!;
  }

  public NaturalLanguageStatement(Cloner cloner, NaturalLanguageStatement original) : base(cloner, original) {
    RawContent = original.RawContent!;
    OpeningDelimiter = cloner.Origin(original.OpeningDelimiter)!;
    ClosingDelimiter = cloner.Origin(original.ClosingDelimiter)!;
  }

  public NaturalLanguageStatement Clone(Cloner cloner) {
    return new NaturalLanguageStatement(cloner, this);
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string? proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;
  }
}
