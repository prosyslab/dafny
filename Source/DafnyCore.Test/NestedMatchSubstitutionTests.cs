using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NestedMatchSubstitutionTests {
  // Substitution retains resolved match data while keeping each pattern binding local to its case.
  [Fact]
  public void SubstitutesResolvedNestedStatementMatchWithScopedPatternVariables() {
    var origin = Token.NoToken;
    var typeParameter = new TypeParameter(origin, new Name(origin, "T"), TPVarianceSyntax.NonVariant_Strict);
    var typeParameterType = new UserDefinedType(typeParameter);
    var sourceVariable = new BoundVar(origin, "source", typeParameterType);
    var sourceReplacement = new LiteralExpr(origin, 7) { Type = Microsoft.Dafny.Type.Int };
    var patternVariable = new BoundVar(origin, "value", typeParameterType);
    var shadowedPatternReplacement = new LiteralExpr(origin, 99) { Type = Microsoft.Dafny.Type.Int };
    var caseLocal = new LocalVariable(origin, "caseLocal", typeParameterType, true);
    var innerConstructor = new DatatypeCtor(origin, new Name(origin, "Inner"), false, [], null);
    var outerConstructor = new DatatypeCtor(origin, new Name(origin, "Outer"), false, [], null);

    var patternVariablePattern = new IdPattern(origin, patternVariable.Name, patternVariable.Type, null) {
      BoundVar = patternVariable
    };
    var innerPattern = new IdPattern(origin, innerConstructor.Name,
      [patternVariablePattern]) { Ctor = innerConstructor };
    var outerPattern = new IdPattern(origin, outerConstructor.Name,
      [innerPattern]) { Ctor = outerConstructor };
    var bodyExpression = Equality(origin, patternVariable, sourceVariable);
    var caseAttributes = new Attributes("case_attribute",
      [new IdentifierExpr(origin, patternVariable), new IdentifierExpr(origin, sourceVariable)], null);
    var nestedCase = new NestedMatchCaseStmt(origin, outerPattern,
      [new VarDeclStmt(origin, [caseLocal], null), new AssertStmt(origin, bodyExpression, null, null)],
      caseAttributes);
    var rootAttributes = new Attributes("root_attribute", [new IdentifierExpr(origin, sourceVariable)], null);
    var nestedMatch = new NestedMatchStmt(origin, new IdentifierExpr(origin, sourceVariable), [nestedCase], false,
      rootAttributes) {
      Flattened = new AssertStmt(origin, Equality(origin, sourceVariable, sourceVariable), null, null),
      IsGhost = true
    };
    var substituter = new StatementSubstituter(
      new Dictionary<IVariable, Expression> {
        [sourceVariable] = sourceReplacement,
        [patternVariable] = shadowedPatternReplacement
      },
      new Dictionary<TypeParameter, Microsoft.Dafny.Type> { [typeParameter] = Microsoft.Dafny.Type.Int });

    var result = Assert.IsType<NestedMatchStmt>(substituter.SubstituteStatement(nestedMatch));

    Assert.Same(sourceReplacement, result.Source);
    Assert.True(result.IsGhost);
    Assert.Same(sourceReplacement, Assert.Single(result.Attributes!.Args));
    var substitutedCase = Assert.Single(result.Cases);
    var substitutedOuterPattern = Assert.IsType<IdPattern>(substitutedCase.Pat);
    Assert.Same(outerConstructor, substitutedOuterPattern.Ctor);
    var substitutedInnerPattern = Assert.IsType<IdPattern>(Assert.Single(substitutedOuterPattern.Arguments!));
    Assert.Same(innerConstructor, substitutedInnerPattern.Ctor);
    var substitutedVariablePattern = Assert.IsType<IdPattern>(Assert.Single(substitutedInnerPattern.Arguments!));
    var substitutedPatternVariable = Assert.IsType<BoundVar>(substitutedVariablePattern.BoundVar);
    Assert.NotSame(patternVariable, substitutedPatternVariable);
    Assert.Same(Microsoft.Dafny.Type.Int, substitutedPatternVariable.Type);

    var substitutedDeclaration = Assert.IsType<VarDeclStmt>(substitutedCase.Body[0]);
    var substitutedCaseLocal = Assert.Single(substitutedDeclaration.Locals);
    Assert.NotSame(caseLocal, substitutedCaseLocal);
    Assert.Same(Microsoft.Dafny.Type.Int, substitutedCaseLocal.Type);
    var substitutedBody = Assert.IsType<AssertStmt>(substitutedCase.Body[1]);
    var substitutedBodyEquality = Assert.IsType<BinaryExpr>(substitutedBody.Expr);
    Assert.Same(substitutedPatternVariable, Assert.IsType<IdentifierExpr>(substitutedBodyEquality.E0).Var);
    Assert.Same(sourceReplacement, substitutedBodyEquality.E1);
    var substitutedCaseAttributes = Attributes.Find(substitutedCase.Attributes, "case_attribute");
    Assert.NotNull(substitutedCaseAttributes);
    Assert.Same(substitutedPatternVariable,
      Assert.IsType<IdentifierExpr>(substitutedCaseAttributes!.Args[0]).Var);
    Assert.Same(sourceReplacement, substitutedCaseAttributes.Args[1]);

    var substitutedFlattened = Assert.IsType<AssertStmt>(result.Flattened);
    var substitutedFlattenedEquality = Assert.IsType<BinaryExpr>(substitutedFlattened.Expr);
    Assert.Same(sourceReplacement, substitutedFlattenedEquality.E0);
    Assert.Same(sourceReplacement, substitutedFlattenedEquality.E1);
    Assert.False(substituter.substMap.ContainsKey(caseLocal));
    Assert.Same(shadowedPatternReplacement, substituter.substMap[patternVariable]);
    Assert.Same(sourceReplacement, substituter.substMap[sourceVariable]);
  }

  private static BinaryExpr Equality(IOrigin origin, IVariable left, IVariable right) {
    return new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.EqCommon,
      new IdentifierExpr(origin, left), new IdentifierExpr(origin, right)) {
      Type = Microsoft.Dafny.Type.Bool
    };
  }

  private sealed class StatementSubstituter : Substituter {
    public StatementSubstituter(Dictionary<IVariable, Expression> substitutions,
      Dictionary<TypeParameter, Microsoft.Dafny.Type> typeSubstitutions)
      : base(null, substitutions, typeSubstitutions) {
    }

    public Statement SubstituteStatement(Statement statement) {
      return SubstStmt(statement);
    }
  }
}
