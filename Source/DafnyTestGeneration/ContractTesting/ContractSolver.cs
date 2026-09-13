using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractSolver {
  public static async Task<ContractQueryResult> CheckAsync(string source, ContractQueryKind kind,
    DafnyOptions baseOptions, CancellationToken cancellationToken, bool captureModel = false,
    string queryName = ContractQueryBuilder.QueryName,
    IReadOnlyList<ContractSource>? sourceSnapshots = null, string? sourcePath = null) {
    var log = new StringWriter();
    var options = new DafnyOptions(baseOptions, useNullWriters: true) {
      Compile = false,
      RunningBoogieFromCommandLine = true,
      DisallowIncludes = sourceSnapshots == null,
      ProcsToCheck = ["*" + queryName + "*"]
    };
    // The library option default is NullPrinter; the counterexample and its model
    // must go to this query's writer even when the outer command uses JSON output.
    options.Printer = new DafnyConsolePrinter(options);
    if (captureModel) {
      options.NormalizeNames = false;
      options.EmitDebugInformation = true;
      options.ErrorTrace = 1;
      options.EnhancedErrorMessages = 1;
      options.ModelViewFile = "-";
    }
    var reporter = new BatchErrorReporter(options);
    // ParseFiles records the source as a verification root; parsing an isolated text
    // fragment alone leaves named modules outside the translation scope.
    Microsoft.Dafny.Program programSource;
    if (sourceSnapshots != null) {
      if (sourcePath == null) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error,
          "Snapshot-backed queries require the exact replaced source path.");
      }
      programSource = await ContractSourceSnapshot.ParseAsync(reporter,
        ContractSourceSnapshot.Replace(sourceSnapshots, sourcePath, source), cancellationToken);
    } else {
      programSource = await Utils.Parse(reporter, source, resolve: false,
        uri: new Uri(Path.Combine(Path.GetTempPath(), "contract-query-" + Guid.NewGuid().ToString("N") + ".dfy")),
        cancellationToken: cancellationToken);
      if (programSource.DefaultModuleDef.Includes.Count > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error,
          "Diagnostic includes require supplied immutable source snapshots.");
      }
      if (reporter.ErrorCount == 0) {
        await new ProgramResolver(programSource).Resolve(cancellationToken);
      }
    }
    if (reporter.ErrorCount != 0) {
      return new ContractQueryResult(kind, ContractQueryOutcome.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    // An implemented function may still have an incorrect, unproved contract. Its
    // ensures cannot become axioms that make the premise inconsistent or prove the
    // property currently being tested. External definitions are additionally erased:
    // diagnostic queries model them only through the original P/Q explicitly rendered
    // into the selected query, never through a Dafny or native implementation body.
    // This program is a fresh diagnostic parse; source contracts and the separately
    // asserted original property remain unchanged. Bodyless function contracts are
    // the explicit abstract-model relation and must remain available.
    foreach (var function in programSource.RawModules().SelectMany(module => module.TopLevelDecls)
               .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Microsoft.Dafny.Function>()
               .Where(function => function.Body != null || Attributes.Contains(function.Attributes, "extern"))) {
      function.Ens.Clear();
      if (Attributes.Contains(function.Attributes, "extern")) {
        function.Body = null;
        function.ByMethodBody = null;
      }
    }
    // Negated quantified assertions need witnesses that E-matching may not supply.
    // Enable model-based instantiation for this polarity check, while keeping model
    // generation on the existing counterexample path. Neither changes the domain.
    var hasQuantifiedAssertion = programSource.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Method>()
      .Where(method => method.Name == queryName && method.Body != null)
      .SelectMany(method => method.Body!.Descendants().OfType<AssertStmt>())
      .Any(assertion => assertion.Expr.Resolved is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } &&
                        assertion.Expr.Descendants().OfType<Microsoft.Dafny.QuantifierExpr>().Any());
    if (hasQuantifiedAssertion && options.IsUsingZ3()) {
      options.ProverOptions.RemoveAll(option => option.StartsWith("O:smt.mbqi=", StringComparison.Ordinal));
      options.ProverOptions.Add("O:smt.mbqi=true");
    }
    if (!captureModel && kind != ContractQueryKind.PremiseConsistency) {
      ReduceConcreteAssertion(programSource, log, queryName);
    }
    options.ProcessSolverOptions(reporter, Microsoft.Dafny.Token.NoToken);
    if (reporter.ErrorCount != 0) {
      return new ContractQueryResult(kind, ContractQueryOutcome.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var verified = 0;
    var errors = 0;
    var selectedModules = new System.Collections.Generic.List<string>();
    foreach (var (module, program) in BoogieGenerator.Translate(programSource, reporter)) {
      selectedModules.Add(module + "[" + string.Join(", ", program.Implementations.Select(implementation => implementation.Name)) + "]");
      cancellationToken.ThrowIfCancellationRequested();
      var (outcome, stats) = await DafnyMain.BoogieOnce(reporter, options, log, engine,
        "contract-query", module, program, null);
      if (stats.TimeoutCount > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Timeout, log.ToString());
      }
      if (stats.InconclusiveCount + stats.OutOfResourceCount + stats.OutOfMemoryCount > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Unknown, log.ToString());
      }
      if (stats.SolverExceptionCount > 0 || outcome is not (PipelineOutcome.Done or PipelineOutcome.VerificationCompleted)) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error, log.ToString());
      }
      verified += stats.VerifiedCount;
      errors += stats.ErrorCount;
    }
    var diagnostics = log.ToString();
    // Dafny can split one original conjunction into several assertion obligations.
    // Every failure must be from the diagnostic property, including its reduction;
    // a separate well-definedness or call error must never masquerade as SAT.
    var targetErrors = diagnostics.Split('\n').Count(line => line.TrimEnd('\r').EndsWith(
      ": Error: " + ContractQueryBuilder.TargetMarker, StringComparison.Ordinal));
    if (errors > 0 && targetErrors == errors) {
      return new ContractQueryResult(kind, ContractQueryOutcome.Sat, diagnostics);
    }
    if (errors == 0 && verified > 0) {
      return new ContractQueryResult(kind, ContractQueryOutcome.Unsat, diagnostics);
    }
    return new ContractQueryResult(kind, ContractQueryOutcome.Error,
      "Query did not isolate its target assertion (verified=" + verified + ", errors=" + errors +
      ", modules=" + string.Join("; ", selectedModules) + "): " + diagnostics);
  }

  private static void ReduceConcreteAssertion(Microsoft.Dafny.Program program, TextWriter log, string queryName) {
    foreach (var method in program.RawModules().SelectMany(module => module.TopLevelDecls)
               .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Method>()
               .Where(method => method.Name == queryName)) {
      // Substituting initial bindings after an executable assignment would be wrong.
      // Path and heap-transition queries retain their original translation here.
      if (method.Body?.Body.Count != 1 || method.Body.Body[0] is not AssertStmt assertion) {
        continue;
      }
      var bindings = new Dictionary<IVariable, Expression>();
      foreach (var clause in method.Req) {
        if (clause.E.Resolved is BinaryExpr { Op: BinaryExpr.Opcode.Eq } equality &&
            equality.E0.Resolved is Microsoft.Dafny.IdentifierExpr identifier && IsConcreteValue(equality.E1)) {
          bindings.TryAdd(identifier.Var, equality.E1);
        }
      }
      var reducer = new ContractExpressionReducer(program.Options,
        method.EnclosingClass.EnclosingModuleDefinition, program.SystemModuleManager);
      var reduction = reducer.Reduce(assertion.Expr, bindings);
      // Keep the complete original assertion as a conjunct. Reduction supplies
      // concrete instances to the same solver obligation; it never supplies an
      // assumption or independently establishes a verdict on the original contract.
      assertion.Expr = Expression.CreateAnd(assertion.Expr, reduction.ReducedExpression, allowSimplification: false);
      log.WriteLine("Contract reduction: decision=" + reduction.Decision + ", residual=" + reduction.ResidualKind +
        ", quantifierInstances=" + reduction.QuantifierInstancesUsed + "/" + reduction.QuantifierInstanceLimit +
        ", exhaustion=" + string.Join(",", reduction.ExhaustionReasons) + "; original assertion retained.");
    }
  }

  private static bool IsConcreteValue(Expression expression) => expression.Resolved switch {
    Microsoft.Dafny.LiteralExpr => true,
    SeqDisplayExpr sequence => sequence.Elements.TrueForAll(IsConcreteValue),
    DatatypeValue datatype => datatype.Arguments.TrueForAll(IsConcreteValue),
    _ => false
  };
}
