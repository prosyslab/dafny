using System.Linq;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NaturalLanguageAstTest {
  [Fact]
  public void NaturalLanguageExpressionPreservesPayloadAndDelimitersAcrossClone() {
    var openDelimiter = new Token(3, 5) { val = "``" };
    var closeDelimiter = new Token(3, 24) { val = "``" };
    var origin = new SourceOrigin(openDelimiter, closeDelimiter);
    var expression = new NaturalLanguageExpression(origin, "raw payload", openDelimiter, closeDelimiter);

    Assert.Equal("raw payload", expression.RawContent);
    Assert.Same(openDelimiter, expression.OpeningDelimiter);
    Assert.Same(closeDelimiter, expression.ClosingDelimiter);
    Assert.Same(origin, expression.Origin);
    Assert.Empty(expression.SubExpressions);
    Assert.Empty(expression.Children);

    var clone = expression.Clone(new Cloner());

    Assert.NotSame(expression, clone);
    Assert.Equal(expression.RawContent, clone.RawContent);
    Assert.Same(expression.OpeningDelimiter, clone.OpeningDelimiter);
    Assert.Same(expression.ClosingDelimiter, clone.ClosingDelimiter);
    Assert.Same(expression.Origin, clone.Origin);
  }

  [Fact]
  public void NaturalLanguageStatementPreservesPayloadTraversalAndCloneData() {
    var openDelimiter = new Token(10, 1) { val = "``" };
    var closeDelimiter = new Token(12, 1) { val = "``" };
    var origin = new SourceOrigin(openDelimiter, closeDelimiter);
    var statement = new NaturalLanguageStatement(origin, "step one\nstep two", openDelimiter, closeDelimiter);

    Assert.Equal("step one\nstep two", statement.RawContent);
    Assert.Same(openDelimiter, statement.OpeningDelimiter);
    Assert.Same(closeDelimiter, statement.ClosingDelimiter);
    Assert.Same(origin, statement.Origin);
    Assert.Empty(statement.SubStatements);
    Assert.Empty(statement.SubExpressions);
    Assert.Empty(statement.SubExpressionsIncludingTransitiveSubStatements);
    Assert.False(statement.Children.Any());

    var clone = statement.Clone(new Cloner());

    Assert.NotSame(statement, clone);
    Assert.Equal(statement.RawContent, clone.RawContent);
    Assert.Same(statement.OpeningDelimiter, clone.OpeningDelimiter);
    Assert.Same(statement.ClosingDelimiter, clone.ClosingDelimiter);
    Assert.Same(statement.Origin, clone.Origin);
  }
}
