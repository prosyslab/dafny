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
  public static Task<ContractQueryResult> CheckAsync(string source, ContractQueryKind kind,
    DafnyOptions baseOptions, CancellationToken cancellationToken, bool captureModel = false,
    string queryName = ContractQueryBuilder.QueryName,
    IReadOnlyList<ContractSource>? sourceSnapshots = null, string? sourcePath = null,
    Action<string, string>? phaseObserver = null, long? deadlineTimestamp = null) =>
    CheckCoreAsync(source, kind, baseOptions, cancellationToken, captureModel, queryName,
      sourceSnapshots, sourcePath, phaseObserver, deadlineTimestamp, null, null);

  internal static async Task<(ContractQueryResult Result, string? OptionsIdentity, string? QueryIdentity)> CheckScreenAsync(
    ContractScreenQuery query, IReadOnlyList<ContractSource> sources, DafnyOptions options,
    CancellationToken cancellationToken, long deadlineTimestamp, Action<string, string>? phaseObserver = null) {
    string? identity = null;
    var result = await CheckCoreAsync(query.Source, ContractQueryKind.ClosedClause, options, cancellationToken,
      false, query.Name, sources, query.SourcePath, phaseObserver, deadlineTimestamp, query, value => identity = value);
    string? queryIdentity = null;
    if (identity != null) {
      var bytes = System.Text.Encoding.UTF8.GetBytes(query.Source);
      var declaration = System.Text.Encoding.UTF8.GetString(bytes, query.Start, query.End - query.Start);
      queryIdentity = ContractHarnessBuilder.Hash(System.Text.Json.JsonSerializer.Serialize(new {
        query.Name,
        query.SourcePath,
        query.Start,
        query.End,
        sourceSha256 = ContractHarnessBuilder.Hash(query.Source),
        sourceSetHash = ContractRuntimeTypeEvidence.SourceSetHash(ContractSourceSnapshot.Replace(sources, query.SourcePath, query.Source)),
        querySha256 = ContractHarnessBuilder.Hash(declaration),
        effectiveOptionsIdentity = identity
      }, ContractJson.Options));
    }
    return (result, identity, queryIdentity);
  }

  private static async Task<ContractQueryResult> CheckCoreAsync(string source, ContractQueryKind kind,
    DafnyOptions baseOptions, CancellationToken cancellationToken, bool captureModel,
    string queryName, IReadOnlyList<ContractSource>? sourceSnapshots, string? sourcePath,
    Action<string, string>? phaseObserver, long? deadlineTimestamp, ContractScreenQuery? screenQuery,
    Action<string>? effectiveOptions) {
    void CheckQueryBoundary() => ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    CheckQueryBoundary();
    var log = new StringWriter();
    var proofOnly = !captureModel && kind is ContractQueryKind.ClosedClause or ContractQueryKind.ObservedPostcondition;
    var options = new DafnyOptions(baseOptions, useNullWriters: true) {
      Compile = false,
      RunningBoogieFromCommandLine = true,
      DisallowIncludes = sourceSnapshots == null,
      ProcsToCheck = ["*" + queryName + "*"],
      ProcsToIgnore = [],
      // Removing unused axioms weakens the premise, so a native UNSAT proof remains
      // sound. State/model queries must retain every axiom; pruned target failures
      // are only nonproofs and never establish a realizable state or violation.
      Prune = proofOnly
    };
    if (proofOnly) { log.GetStringBuilder().AppendLine("Native proof-only pruning: target counterexamples are not state or model certificates."); }
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
      var snapshots = ContractSourceSnapshot.Replace(sourceSnapshots, sourcePath, source);
      programSource = screenQuery == null
        ? await ContractSourceSnapshot.ParseAsync(reporter, snapshots, cancellationToken, phaseObserver: phaseObserver)
        : (await ContractScreenSourcePreparation.ParseAsync(reporter, snapshots, cancellationToken,
          screenQuery, phaseObserver, screenQuery.Projection)).Program;
    } else {
      programSource = await ContractPhaseRecorder.MeasureAsync(phaseObserver, "parse", cancellationToken,
        () => Utils.Parse(reporter, source, resolve: false,
          uri: new Uri(Path.Combine(Path.GetTempPath(), "contract-query-" + Guid.NewGuid().ToString("N") + ".dfy")),
          cancellationToken: cancellationToken));
      if (programSource.DefaultModuleDef.Includes.Count > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error,
          "Diagnostic includes require supplied immutable source snapshots.");
      }
      if (reporter.ErrorCount == 0) {
        await ContractPhaseRecorder.MeasureAsync(phaseObserver, "resolve", cancellationToken,
          () => new ProgramResolver(programSource).Resolve(cancellationToken));
      }
    }
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
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
    // Preserve the legacy negated-quantifier profile. Positive screen existentials
    // receive model-based instantiation only after complete concrete reduction has
    // emitted a witness assertion; this is solver guidance, never a proof result.
    var hasQuantifiedAssertion = programSource.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Method>()
      .Where(method => method.Name == queryName && method.Body != null)
      .SelectMany(method => method.Body!.Descendants().OfType<AssertStmt>())
      .Any(assertion => assertion.Expr.Resolved is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } &&
                        (ContractReductionTraversal.LogicalNodes(assertion.Expr, CheckQueryBoundary).OfType<Microsoft.Dafny.QuantifierExpr>().Any() ||
                         HasLogicalUniversalQuantifier(assertion.Expr, CheckQueryBoundary)));
    var concretePositiveWitness = false;
    if (!captureModel && kind != ContractQueryKind.PremiseConsistency) {
      concretePositiveWitness = ContractPhaseRecorder.Measure(phaseObserver, "reduction", cancellationToken, () => {
        CheckQueryBoundary();
        var guidance = ReduceConcreteAssertionCore(programSource, log, queryName, CheckQueryBoundary);
        CheckQueryBoundary();
        return guidance;
      });
    }
    CheckQueryBoundary();
    if ((hasQuantifiedAssertion || screenQuery != null && concretePositiveWitness) && options.IsUsingZ3()) {
      options.ProverOptions.RemoveAll(option => option.StartsWith("O:smt.mbqi=", StringComparison.Ordinal));
      options.ProverOptions.Add("O:smt.mbqi=true");
    }
    options.ProcessSolverOptions(reporter, Microsoft.Dafny.Token.NoToken);
    effectiveOptions?.Invoke(DefinitionAnalysis.ContextOptionsIdentity(options));
    if (reporter.ErrorCount != 0) {
      return new ContractQueryResult(kind, ContractQueryOutcome.Error,
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    CheckQueryBoundary();
    using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
    var verified = 0;
    var errors = 0;
    var selectedModules = new System.Collections.Generic.List<string>();
    // Translation keeps thread-static type-scope state, so it finishes on this thread before any awaited verification.
    CheckQueryBoundary();
    var translated = ContractPhaseRecorder.Measure(phaseObserver, "translation", cancellationToken, () => {
      // Every native module translation includes its complete visible declaration/import closure.
      // Only modules owning the selected diagnostic can contribute a verified target assertion;
      // translating the other modules duplicates that closure before ProcsToCheck is applied.
      var queryModules = BoogieGenerator.VerifiableModules(programSource)
        .Where(module => QueryMethods(module, queryName).Any());
      Microsoft.Dafny.Type.ResetScopes();
      return queryModules.Select(module => Tuple.Create(module.SanitizedName,
        new BoogieGenerator(reporter, programSource.ProofDependencyManager).DoTranslation(programSource, module))).ToList();
    });
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    foreach (var (module, program) in translated) {
      if (proofOnly) {
        log.GetStringBuilder().AppendLine(ContractGlobalAssumptions.RemoveAbstractConstantAxioms(programSource, program));
      }
      var diagnosticMethods = programSource.RawModules().Where(owner => owner.SanitizedName == module)
        .SelectMany(owner => QueryMethods(owner, queryName)).ToList();
      var diagnosticNames = diagnosticMethods.SelectMany(method => new[] { method.FullDafnyName + " (well-formedness)", method.FullDafnyName + " (correctness)",
          method.FullDafnyName + " (override check)" }).ToHashSet(StringComparer.Ordinal);
      // The native routine filter runs after CFG preprocessing. Avoid preprocessing
      // unrelated implementations while retaining every original procedure and axiom.
      program.RemoveTopLevelDeclarations(declaration => declaration is Implementation implementation &&
        !diagnosticNames.Contains(implementation.VerboseName));
      var expectedImplementations = program.Implementations.Count();
      if (diagnosticMethods.Count != 1 || program.Implementations.Count(implementation =>
            implementation.VerboseName == diagnosticMethods[0].FullDafnyName + " (correctness)") != 1) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error, "Native diagnostic correctness coverage is missing or ambiguous.");
      }
      selectedModules.Add(module + "[" + string.Join(", ", program.Implementations.Select(implementation => implementation.Name)) + "]");
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      var logStart = log.GetStringBuilder().Length;
      var (outcome, stats) = await ContractPhaseRecorder.MeasureAsync(phaseObserver, "boogie:" + module,
        cancellationToken, () => DafnyMain.BoogieOnce(reporter, options, log, engine,
          "contract-query", module, program, null, cancellationToken));
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      if (stats.TimeoutCount > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Timeout, log.ToString());
      }
      if (stats.InconclusiveCount + stats.OutOfResourceCount + stats.OutOfMemoryCount > 0) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Unknown, log.ToString());
      }
      if (stats.SolverExceptionCount > 0 || outcome is not (PipelineOutcome.Done or PipelineOutcome.VerificationCompleted)) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error, log.ToString());
      }
      var moduleDiagnostics = log.GetStringBuilder().ToString(logStart, log.GetStringBuilder().Length - logStart);
      var moduleTargetErrors = CountTargetErrors(moduleDiagnostics);
      // Counterexamples may contain several target errors in one correctness body.
      // Every other selected implementation must have verified, including all WD checks.
      var complete = stats.ErrorCount == 0 ? stats.VerifiedCount == expectedImplementations :
        moduleTargetErrors == stats.ErrorCount && stats.VerifiedCount == expectedImplementations - 1;
      if (!complete) {
        return new ContractQueryResult(kind, ContractQueryOutcome.Error, "Native diagnostic verification coverage is incomplete: " + log);
      }
      verified += stats.VerifiedCount;
      errors += stats.ErrorCount;
    }
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var diagnostics = log.ToString();
    // Dafny can split one original conjunction into several assertion obligations.
    // Every failure must be from the diagnostic property, including its reduction;
    // a separate well-definedness or call error must never masquerade as SAT.
    var targetErrors = CountTargetErrors(diagnostics);
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
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

  private static bool HasLogicalUniversalQuantifier(Expression expression, System.Action cancellationCheck) {
    var functions = new HashSet<Microsoft.Dafny.Function>();
    var pending = new Stack<Expression>();
    pending.Push(expression);
    while (pending.TryPop(out var current)) {
      cancellationCheck();
      foreach (var node in ContractReductionTraversal.LogicalNodes(current, cancellationCheck).OfType<Expression>()) {
        cancellationCheck();
        // A negated universal definition needs a witness; an existential definition alone does not.
        if (node.Resolved is Microsoft.Dafny.ForallExpr) { return true; }
        // Inspect only original logical bodies; this selects a solver option without revealing or assuming definitions.
        if (ContractRuntimeObligationTransformer.FunctionReference(node.Resolved) is { Body: { } body } function &&
            functions.Add(function)) {
          pending.Push(body);
        }
      }
    }
    return false;
  }

  private static IEnumerable<Method> QueryMethods(ModuleDefinition module, string queryName) =>
    module.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Method>()
      .Where(method => method.Name == queryName && method.Body != null);

  private static int CountTargetErrors(string diagnostics) => diagnostics.Split('\n').Count(line =>
    line.TrimEnd('\r').EndsWith(": Error: " + ContractQueryBuilder.TargetMarker, StringComparison.Ordinal));

  /// <summary>Stages checked proof steps off-tree and publishes them only after the final query-boundary check.</summary>
  public static void ReduceConcreteAssertion(Microsoft.Dafny.Program program, TextWriter log, string queryName,
    System.Action cancellationCheck) {
    _ = ReduceConcreteAssertionCore(program, log, queryName, cancellationCheck);
  }

  private static bool ReduceConcreteAssertionCore(Microsoft.Dafny.Program program, TextWriter log, string queryName,
    System.Action cancellationCheck) {
    var methodsProcessed = 0;
    var concretePositiveWitness = false;
    foreach (var method in program.RawModules().SelectMany(module => module.TopLevelDecls)
               .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Method>()
               .Where(method => method.Name == queryName)) {
      cancellationCheck();
      methodsProcessed++;
      if (ContractQueryHeapReduction.TryApply(program, method, log, cancellationCheck)) { continue; }
      // Substituting initial bindings after an executable assignment would be wrong.
      // Path and heap-transition queries retain their original translation here.
      if (method.Body?.Body.Count != 1 || method.Body.Body[0] is not AssertStmt assertion) {
        continue;
      }
      var originalIsExistential = assertion.Expr.Resolved is Microsoft.Dafny.ExistsExpr;
      var bindings = new Dictionary<IVariable, Expression>();
      foreach (var clause in method.Req) {
        cancellationCheck();
        if (clause.E.Resolved is BinaryExpr { Op: BinaryExpr.Opcode.Eq } equality &&
            equality.E0.Resolved is Microsoft.Dafny.IdentifierExpr identifier && ContractExpressionReducer.IsConcreteValue(equality.E1, cancellationCheck)) {
          bindings.TryAdd(identifier.Var, equality.E1);
        }
      }
      var owner = method.EnclosingClass.EnclosingModuleDefinition;
      var reducer = new ContractExpressionReducer(program.Options,
        owner, program.SystemModuleManager, program.ModuleSigs[owner].VisibilityScope);
      var reduction = reducer.ReduceForNativeProofComposition(assertion.Expr, bindings,
        cancellationCheck: cancellationCheck);
      var added = new List<Statement>();
      foreach (var obligation in reduction.ProofObligations) {
        cancellationCheck();
        var markerName = obligation.Kind switch {
          ContractReductionProofKind.Witness => "contract_reduction_witness",
          ContractReductionProofKind.Prerequisite => "contract_reduction_prerequisite",
          ContractReductionProofKind.Predicate => "contract_reduction_predicate",
          _ => throw new ArgumentOutOfRangeException()
        };
        var marker = new StringLiteralExpr(assertion.Origin, markerName, false) {
          Type = new SeqType(Microsoft.Dafny.Type.Char)
        };
        added.Add(new AssertStmt(assertion.Origin, obligation.Expression, null,
          new Attributes("error", [marker], null)));
      }
      // Keep the complete original assertion as a conjunct. Reduction supplies
      // concrete instances to the same solver obligation; it never supplies an
      // assumption or independently establishes a verdict on the original contract.
      var replacement = Expression.CreateAnd(assertion.Expr, reduction.ReducedExpression, allowSimplification: false);
      cancellationCheck();
      method.Body.Body.InsertRange(method.Body.Body.Count - 1, added);
      assertion.Expr = replacement;
      // The full original and every staged assertion are now published. A concrete
      // reduction only chooses a solver profile; all native proof/WD gates still run.
      concretePositiveWitness |= originalIsExistential && reduction.Decision == ContractReductionDecision.True &&
        Expression.IsBoolLiteral(reduction.ReducedExpression, out var holds) && holds && !reduction.BudgetExhausted &&
        reduction.ProofWitnesses.Any(witness => reduction.ProofObligations.Any(obligation =>
          obligation.Kind == ContractReductionProofKind.Witness && ReferenceEquals(obligation.Expression, witness)));
      log.WriteLine("Contract reduction: decision=" + reduction.Decision + ", residual=" + reduction.ResidualKind +
        ", quantifierInstances=" + reduction.QuantifierInstancesUsed + "/" + reduction.QuantifierInstanceLimit +
        ", exhaustion=" + string.Join(",", reduction.ExhaustionReasons) +
        ", checkedWitnesses=" + reduction.ProofWitnesses.Count +
        ", proofSteps=" + reduction.ProofObligations.Count +
        ", proofNodes=" + reduction.ProofCompositionNodesAdmitted + "/" +
        reduction.ProofCompositionNodesConsidered + "; original assertion retained.");
    }
    return methodsProcessed == 1 && concretePositiveWitness;
  }

}
