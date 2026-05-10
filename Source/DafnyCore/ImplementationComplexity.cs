#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public record ImplementationComplexityResult(
  IOrigin Origin,
  string Kind,
  string FullDafnyName,
  int Score
);

public static class ImplementationComplexity {
  public static IReadOnlyList<ImplementationComplexityResult> Analyze(Program program) {
    var results = new List<ImplementationComplexityResult>();
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var member in topLevelDeclWithMembers.Members.OrderBy(member => member.Origin.pos)) {
          if (member.Origin.FromIncludeDirective(program)) {
            continue;
          }

          switch (member) {
            case MethodOrConstructor { Body: { } body } method when !method.IsGhost:
              results.Add(new ImplementationComplexityResult(
                method.Origin,
                method is Constructor ? "constructor" : "method",
                method.FullDafnyName,
                BodyScorer.ScoreMethodBody(method, body)));
              break;
            case Function { ByMethodBody: { } byMethodBody } function when !function.IsGhost:
              results.Add(new ImplementationComplexityResult(
                function.ByMethodTok ?? function.Origin,
                "function-by-method",
                function.FullDafnyName,
                BodyScorer.ScoreByMethodBody(function, byMethodBody)));
              break;
          }
        }
      }
    }

    return results;
  }

  private sealed class BodyScorer {
    private readonly MethodOrConstructor? currentMethod;
    private readonly Function? currentFunction;

    private BodyScorer(MethodOrConstructor? currentMethod, Function? currentFunction) {
      this.currentMethod = currentMethod;
      this.currentFunction = currentFunction;
    }

    public static int ScoreMethodBody(MethodOrConstructor method, BlockLikeStmt body) {
      return new BodyScorer(method, null).ScoreBlock(body, 0);
    }

    public static int ScoreByMethodBody(Function function, BlockStmt body) {
      return new BodyScorer(null, function).ScoreBlock(body, 0);
    }

    private int ScoreBlock(BlockLikeStmt block, int nesting) {
      return block.Body.Sum(statement => ScoreStatement(statement, nesting));
    }

    private int ScoreStatements(IEnumerable<Statement> statements, int nesting) {
      return statements.Sum(statement => ScoreStatement(statement, nesting));
    }

    private int ScoreStatement(Statement statement, int nesting) {
      if (statement is BlockByProofStmt blockByProofStmt) {
        return statement.IsGhost ? 0 : ScoreStatement(blockByProofStmt.Body, nesting);
      }

      if (statement.IsGhost) {
        return 0;
      }

      return statement switch {
        BlockLikeStmt block => ScoreBlock(block, nesting),
        IfStmt ifStmt => ScoreIf(ifStmt, nesting),
        WhileStmt whileStmt => ScoreWhile(whileStmt, nesting),
        ForLoopStmt forLoopStmt => ScoreForLoop(forLoopStmt, nesting),
        AlternativeStmt alternativeStmt => ScoreAlternatives(alternativeStmt.Alternatives, nesting),
        AlternativeLoopStmt alternativeLoopStmt => ScoreAlternativeLoop(alternativeLoopStmt, nesting),
        ForallStmt forallStmt => ScoreForall(forallStmt, nesting),
        MatchStmt matchStmt => ScoreMatch(matchStmt, nesting),
        NestedMatchStmt nestedMatchStmt => ScoreNestedMatch(nestedMatchStmt, nesting),
        CallStmt callStmt => ScoreCall(callStmt, nesting),
        _ => ScoreStatementContents(statement, nesting)
      };
    }

    private int ScoreStatementContents(Statement statement, int nesting) {
      return statement.NonSpecificationSubExpressions.Sum(expression => ScoreExpression(expression, nesting)) +
             ScoreStatements(statement.SubStatements, nesting);
    }

    private int ScoreIf(IfStmt ifStmt, int nesting) {
      var score = StructuralIncrement(nesting) +
                  ScoreOptionalExpression(ifStmt.Guard, nesting) +
                  ScoreBlock(ifStmt.Thn, nesting + 1);
      if (ifStmt.Els is IfStmt elseIf) {
        score += ScoreIf(elseIf, nesting);
      } else if (ifStmt.Els != null) {
        score += ScoreStatement(ifStmt.Els, nesting + 1);
      }

      return score;
    }

    private int ScoreWhile(WhileStmt whileStmt, int nesting) {
      var score = StructuralIncrement(nesting) + ScoreOptionalExpression(whileStmt.Guard, nesting);
      if (whileStmt.Body != null) {
        score += ScoreBlock(whileStmt.Body, nesting + 1);
      }

      return score;
    }

    private int ScoreForLoop(ForLoopStmt forLoopStmt, int nesting) {
      var score = StructuralIncrement(nesting) +
                  ScoreExpression(forLoopStmt.Start, nesting) +
                  ScoreOptionalExpression(forLoopStmt.End, nesting);
      if (forLoopStmt.Body != null) {
        score += ScoreBlock(forLoopStmt.Body, nesting + 1);
      }

      return score;
    }

    private int ScoreAlternativeLoop(AlternativeLoopStmt alternativeLoopStmt, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreAlternatives(alternativeLoopStmt.Alternatives, nesting + 1);
    }

    private int ScoreAlternatives(IEnumerable<GuardedAlternative> alternatives, int nesting) {
      return alternatives.Sum(alternative =>
        StructuralIncrement(nesting) +
        ScoreExpression(alternative.Guard, nesting) +
        ScoreStatements(alternative.Body, nesting + 1));
    }

    private int ScoreForall(ForallStmt forallStmt, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(forallStmt.Range, nesting) +
             (forallStmt.Body == null ? 0 : ScoreStatement(forallStmt.Body, nesting + 1));
    }

    private int ScoreMatch(MatchStmt matchStmt, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(matchStmt.Source, nesting) +
             matchStmt.Cases.Sum(matchCase => ScoreStatements(matchCase.Body, nesting + 1));
    }

    private int ScoreNestedMatch(NestedMatchStmt nestedMatchStmt, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(nestedMatchStmt.Source, nesting) +
             nestedMatchStmt.Cases.Sum(matchCase => ScoreStatements(matchCase.Body, nesting + 1));
    }

    private int ScoreCall(CallStmt callStmt, int nesting) {
      var score = callStmt.Method == currentMethod ? 1 : 0;
      score += callStmt.NonSpecificationSubExpressions.Sum(expression => ScoreExpression(expression, nesting));
      return score;
    }

    private int ScoreOptionalExpression(Expression? expression, int nesting) {
      return expression == null ? 0 : ScoreExpression(expression, nesting);
    }

    private int ScoreExpression(Expression expression, int nesting) {
      return ScoreExpression(expression, nesting, null);
    }

    private int ScoreExpression(
      Expression expression,
      int nesting,
      BinaryExpr.Opcode? enclosingLogicalOperator) {
      return expression switch {
        ITEExpr iteExpr => ScoreIteExpression(iteExpr, nesting),
        MatchExpr matchExpr => ScoreMatchExpression(matchExpr, nesting),
        NestedMatchExpr nestedMatchExpr => ScoreNestedMatchExpression(nestedMatchExpr, nesting),
        StmtExpr stmtExpr => ScoreStatement(stmtExpr.S, nesting) + ScoreExpression(stmtExpr.E, nesting),
        FunctionCallExpr functionCallExpr => ScoreFunctionCall(functionCallExpr, nesting),
        BinaryExpr binaryExpr => ScoreBinaryExpression(binaryExpr, nesting, enclosingLogicalOperator),
        QuantifierExpr quantifierExpr => StructuralIncrement(nesting) + ScoreExpressionContents(quantifierExpr, nesting),
        _ => ScoreExpressionContents(expression, nesting)
      };
    }

    private int ScoreIteExpression(ITEExpr iteExpr, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(iteExpr.Test, nesting) +
             ScoreExpression(iteExpr.Thn, nesting + 1) +
             ScoreExpression(iteExpr.Els, nesting + 1);
    }

    private int ScoreMatchExpression(MatchExpr matchExpr, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(matchExpr.Source, nesting) +
             matchExpr.Cases.Sum(matchCase => ScoreExpression(matchCase.Body, nesting + 1));
    }

    private int ScoreNestedMatchExpression(NestedMatchExpr nestedMatchExpr, int nesting) {
      return StructuralIncrement(nesting) +
             ScoreExpression(nestedMatchExpr.Source, nesting) +
             nestedMatchExpr.Cases.Sum(matchCase => ScoreExpression(matchCase.Body, nesting + 1));
    }

    private int ScoreFunctionCall(FunctionCallExpr functionCallExpr, int nesting) {
      var score = functionCallExpr.Function == currentFunction ? 1 : 0;
      score += ScoreExpressionContents(functionCallExpr, nesting);
      return score;
    }

    private int ScoreBinaryExpression(
      BinaryExpr binaryExpr,
      int nesting,
      BinaryExpr.Opcode? enclosingLogicalOperator) {
      if (!IsLogicalOperator(binaryExpr.Op)) {
        return ScoreExpressionContents(binaryExpr, nesting);
      }

      var score = enclosingLogicalOperator == binaryExpr.Op ? 0 : 1;
      score += ScoreExpression(binaryExpr.E0, nesting, binaryExpr.Op);
      score += ScoreExpression(binaryExpr.E1, nesting, binaryExpr.Op);
      return score;
    }

    private int ScoreExpressionContents(Expression expression, int nesting) {
      return expression.SubExpressions.Sum(subExpression => ScoreExpression(subExpression, nesting));
    }

    private static int StructuralIncrement(int nesting) {
      return 1 + nesting;
    }

    private static bool IsLogicalOperator(BinaryExpr.Opcode op) {
      return op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or or
        BinaryExpr.Opcode.Imp or BinaryExpr.Opcode.Exp or BinaryExpr.Opcode.Iff;
    }
  }
}
