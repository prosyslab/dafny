#nullable enable
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents an experimental natural-language block expression delimited by double backticks.
/// The parser records the raw block content and delimiter origins for diagnostics and printing.
/// </summary>
public class NaturalLanguageExpression : Expression, ICloneable<NaturalLanguageExpression> {
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
  public NaturalLanguageExpression(IOrigin origin, string rawContent, IOrigin openingDelimiter, IOrigin closingDelimiter)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(rawContent != null);
    Contract.Requires(openingDelimiter != null);
    Contract.Requires(closingDelimiter != null);
    RawContent = rawContent!;
    OpeningDelimiter = openingDelimiter!;
    ClosingDelimiter = closingDelimiter!;
  }

  public NaturalLanguageExpression(Cloner cloner, NaturalLanguageExpression original) : base(cloner, original) {
    RawContent = original.RawContent!;
    OpeningDelimiter = cloner.Origin(original.OpeningDelimiter)!;
    ClosingDelimiter = cloner.Origin(original.ClosingDelimiter)!;
  }

  public NaturalLanguageExpression Clone(Cloner cloner) {
    return new NaturalLanguageExpression(cloner, this);
  }
}
