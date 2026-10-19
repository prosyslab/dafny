using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Microsoft.Dafny.Triggers;

namespace DafnyCore.Test;

public class MatchTriggerVariableScopeTests {
  // Match candidates that use no case-local variable retain their original identity.
  [Theory]
  [InlineData(false, 0)]
  [InlineData(false, 1)]
  [InlineData(false, 2)]
  [InlineData(true, 0)]
  [InlineData(true, 1)]
  [InlineData(true, 2)]
  public void InScopeMatchCandidatesKeepTheirIdentity(bool flattened, int localCount) {
    var (collector, quantifier, candidate) = CreateMatchCandidate(flattened, localCount, false);
    Assert.Same(candidate, Assert.Single(collector.CollectTriggers(quantifier)).Expr);
  }

  // Mentioning one of several case-local variables prevents a term from escaping.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public void CandidateUsingOneOfSeveralMatchLocalsStaysPrivate(bool flattened) {
    var (collector, quantifier, _) = CreateMatchCandidate(flattened, 2, true);
    Assert.Empty(collector.CollectTriggers(quantifier));
  }

  // A trigger outside a match must not refer to a binder from any of its cases.
  [Theory]
  [InlineData("forall")]
  [InlineData("exists")]
  public async Task MatchCaseVariablesDoNotEscapeIntoQuantifierTriggers(string binder) {
    var (options, quantifier) = await ResolvePostcondition(
      "datatype Choice = Left(value: int) | Right(value: int)",
      "predicate Related(choice: Choice, value: int) { true }",
      binder + " choice: Choice :: match choice " +
      "case Left(leftValue) => Related(choice, leftValue) " +
      "case Right(rightValue) => Related(choice, rightValue)");

    Assert.All(QuantifierTriggers(quantifier), trigger =>
      Assert.All(FreeVariablesUtil.ComputeFreeVariables(options, trigger),
        variable => Assert.Contains(variable, quantifier.BoundVars)));
  }

  // A match may export a term that depends only on the enclosing quantifier.
  [Fact]
  public async Task InScopeCandidatesSurviveMatchCaseFiltering() {
    var (options, quantifier) = await ResolvePostcondition(
      "datatype Choice = Left(value: int) | Right(value: int)",
      "predicate Related(choice: Choice, value: int) { true }",
      "forall choice: Choice :: match choice " +
      "case Left(leftValue) => Related(choice, 0) " +
      "case Right(rightValue) => Related(choice, 0)");

    var triggers = QuantifierTriggers(quantifier).ToList();
    Assert.NotEmpty(triggers);
    Assert.All(triggers, trigger =>
      Assert.Equal(quantifier.BoundVars.Cast<IVariable>(),
        FreeVariablesUtil.ComputeFreeVariables(options, trigger)));
  }

  // A match with no pattern variables still exports valid enclosing-scope terms.
  [Fact]
  public async Task ConstructorOnlyCasesKeepInScopeCandidates() {
    var (options, quantifier) = await ResolvePostcondition(
      "datatype Signal = First | Second",
      "predicate Observed(signal: Signal) { true }",
      "forall signal: Signal :: match signal " +
      "case First => Observed(signal) case Second => Observed(signal)");

    var triggers = QuantifierTriggers(quantifier).ToList();
    Assert.NotEmpty(triggers);
    Assert.All(triggers, trigger =>
      Assert.Equal(quantifier.BoundVars.Cast<IVariable>(),
        FreeVariablesUtil.ComputeFreeVariables(options, trigger)));
  }

  private static System.Collections.Generic.IEnumerable<Expression> QuantifierTriggers(QuantifierExpr quantifier) {
    var quantifiers = quantifier.SplitQuantifier?.Cast<QuantifierExpr>() ?? [quantifier];
    return quantifiers.SelectMany(part => part.Attributes.AsEnumerable())
      .Where(attribute => attribute.Name == "trigger")
      .SelectMany(attribute => attribute.Args);
  }

  private static (TriggersCollector, QuantifierExpr, Expression) CreateMatchCandidate(
    bool flattened, int localCount, bool usesLocal) {
    var origin = Token.NoToken;
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var module = new ModuleDefinition(origin, new Name(origin, "Scope"), [],
      ModuleKindEnum.Concrete, false, null, null, null);
    var sequenceType = new SeqType(Microsoft.Dafny.Type.Int);
    var locals = Enumerable.Range(0, localCount)
      .Select(index => new BoundVar(origin, "local" + index, sequenceType)).ToList();
    var constructor = new DatatypeCtor(origin, new Name(origin, "Case"), false,
      locals.Select(local => new Formal(origin, local.Name, local.Type, true, false, null)).ToList(), null);
    var datatype = new IndDatatypeDecl(origin, new Name(origin, "Choice"), module,
      [], [constructor], [], [], null, false);
    constructor.EnclosingDatatype = datatype;
    var source = new IdentifierExpr(origin, new BoundVar(origin, "choice",
      new UserDefinedType(origin, "Choice", null) { ResolvedClass = datatype }));
    var indexVariable = new BoundVar(origin, "index", Microsoft.Dafny.Type.Int);
    var sequence = usesLocal ? locals[0] : new BoundVar(origin, "values", sequenceType);
    var candidate = new SeqSelectExpr(origin, true,
      new IdentifierExpr(origin, sequence), new IdentifierExpr(origin, indexVariable), null) {
      Type = Microsoft.Dafny.Type.Int
    };
    var body = new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.EqCommon,
      candidate, new LiteralExpr(origin, 0) { Type = Microsoft.Dafny.Type.Int });
    Expression match;
    if (flattened) {
      match = new MatchExpr(origin, source,
        [new MatchCaseExpr(origin, constructor, false, locals, body)], false) {
        Type = Microsoft.Dafny.Type.Bool
      };
    } else {
      var pattern = new IdPattern(origin, "Case",
        locals.Select(local => (ExtendedPattern)new IdPattern(origin, local.Name, local.Type, null) {
          BoundVar = local
        }).ToList()) { Ctor = constructor };
      match = new NestedMatchExpr(origin, source,
        [new NestedMatchCaseExpr(origin, pattern, body)], false) { Type = Microsoft.Dafny.Type.Bool };
    }
    var quantifier = new ForallExpr(origin, [indexVariable], null, match) { Type = Microsoft.Dafny.Type.Bool };
    return (new TriggersCollector(new(), options, module), quantifier, candidate);
  }

  private static async Task<(DafnyOptions, QuantifierExpr)> ResolvePostcondition(
    string datatype, string predicate, string condition) {
    Microsoft.Dafny.Type.ResetScopes();
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var source = datatype + "\n" + predicate + "\nmethod Check() ensures " + condition + " {}";
    var parsed = await ProgramParser.Parse(source, new Uri("untitled:match-trigger-variable-scope"), reporter);
    Assert.Equal(0, reporter.ErrorCount);
    await new ProgramResolver(parsed.Program).Resolve(CancellationToken.None);
    Assert.Equal(0, reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error));
    var method = ModuleDefinition.AllCallablesIncludingPrefixDeclarations(parsed.Program.DefaultModuleDef.TopLevelDecls)
      .OfType<Method>().Single();
    return (options, Assert.IsAssignableFrom<QuantifierExpr>(method.Ens.Single().E.Resolved));
  }
}
