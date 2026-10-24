#nullable enable
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

[assembly: System.Runtime.CompilerServices.InternalsVisibleTo("DafnyTestGeneration.Test")]

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractScreenInspection(ContractScreenBinding Binding, ContractScreenCapability Capability);
public sealed record ContractScreenCertification(ContractSpecificationResult Result, IReadOnlyList<string> OptionsIdentities);

/// <summary>Separates orchestration from native effects so memory tests never parse, hash assemblies or run solvers.</summary>
public interface IContractScreenBackend {
  Task<ContractScreenInspection> InspectAsync(ContractScreenRequest request, CancellationToken cancellationToken);
  Task<ContractScreenCertification> CertifyAsync(CancellationToken cancellationToken, long deadlineTimestamp);
  Task<ContractScreenCaseResult> CheckCaseAsync(ContractScreenCase item, ContractScreenQuestion question,
    int queryMilliseconds, CancellationToken cancellationToken, long deadlineTimestamp);
}

/// <summary>Runs finite contract diagnostics independently of generators, compilation and implementation proofs.</summary>
public sealed class ContractScreenService(IContractScreenBackend backend) {
  /// <summary>Uses the ordinary native snapshot, checker and solver implementation.</summary>
  public static Task<ContractScreenResult> RunAsync(ContractScreenRequest request, DafnyOptions options,
    CancellationToken cancellationToken) {
    var diagnostics = new ScreenDiagnostics();
    return new ContractScreenService(new NativeBackend(options, diagnostics)).ExecuteAsync(request, cancellationToken, diagnostics);
  }

  /// <summary>Preserves all requested cases and their typed states through unsupported work and interruption.</summary>
  public Task<ContractScreenResult> ExecuteAsync(ContractScreenRequest request, CancellationToken cancellationToken) =>
    ExecuteAsync(request, cancellationToken, new ScreenDiagnostics());

  internal async Task<ContractScreenResult> ExecuteAsync(ContractScreenRequest request, CancellationToken cancellationToken,
    ScreenDiagnostics diagnostics) {
    ContractScreenInspection? inspection = null;
    var results = new List<ContractScreenCaseResult>();
    var dependencyOptions = new List<string>();
    var status = ContractScreenStatus.Completed;
    IReadOnlyList<ContractScreenCase> cases = request?.Cases is { Count: <= ContractScreenValidation.MaximumCases } boundedCases ? boundedCases : [];
    CancellationTokenSource? attempt = null;
    try {
      ContractScreenValidation.Validate(request!);
      // Own a detached copy before the first await; callers cannot mutate an accepted snapshot.
      request = JsonSerializer.Deserialize<ContractScreenRequest>(JsonSerializer.SerializeToUtf8Bytes(request, ContractJson.Options), ContractJson.Options)!;
      cases = request.Cases ?? [];
      var budgets = request.Budgets ?? new();
      var deadline = ContractQueryDeadline.AfterMilliseconds(budgets.AttemptMilliseconds);
      attempt = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      attempt.CancelAfter(budgets.AttemptMilliseconds);
      ContractQueryDeadline.Check(deadline, attempt.Token);
      if (request.Question == ContractScreenQuestion.CallerSufficiency) {
        throw new NotSupportedException("native_caller_obligation_unavailable");
      }
      inspection = await backend.InspectAsync(request, attempt.Token);
      ContractQueryDeadline.Check(deadline, attempt.Token);
      if (!inspection.Capability.Supported) { throw new NotSupportedException(string.Join(",", inspection.Capability.ReasonCodes)); }
      if (request.Action == ContractScreenAction.Screen) {
        if (request.Binding != inspection.Binding) { throw new ArgumentException("stale_binding"); }
        var certification = await backend.CertifyAsync(attempt.Token, deadline);
        dependencyOptions.AddRange(certification.OptionsIdentities);
        var certificate = certification.Result;
        ContractQueryDeadline.Check(deadline, attempt.Token);
        AddDiagnostic(certificate.Diagnostics);
        if (!certificate.Verified || certificate.Outcome != ContractSpecificationOutcome.Verified) {
          status = certificate.Outcome switch {
            ContractSpecificationOutcome.Unsupported => ContractScreenStatus.Unsupported,
            ContractSpecificationOutcome.Timeout => ContractScreenStatus.Timeout,
            ContractSpecificationOutcome.Error => ContractScreenStatus.Error,
            _ => ContractScreenStatus.Partial
          };
          var domain = certificate.Outcome switch {
            ContractSpecificationOutcome.Unsupported => ContractScreenDomain.Unsupported,
            ContractSpecificationOutcome.Timeout => ContractScreenDomain.Timeout,
            ContractSpecificationOutcome.Error => ContractScreenDomain.Error,
            _ => ContractScreenDomain.Unknown
          };
          results.AddRange(cases.Select(item => Unchecked(item, domain, "logical_dependencies_not_certified")));
        } else {
          inspection = inspection with { Capability = inspection.Capability with { CertificationPending = false } };
          foreach (var item in cases) {
            ContractQueryDeadline.Check(deadline, attempt.Token);
            var result = await backend.CheckCaseAsync(item, request.Question, budgets.QueryMilliseconds, attempt.Token, deadline);
            results.Add(result);
            ContractQueryDeadline.Check(deadline, attempt.Token);
          }
          if (results.Any(item => item.Domain == ContractScreenDomain.Cancelled || item.Property == ContractScreenProperty.Cancelled)) {
            status = ContractScreenStatus.Cancelled;
          } else if (results.Any(item => item.Domain is ContractScreenDomain.Unknown or ContractScreenDomain.Timeout or
                ContractScreenDomain.Unsupported or ContractScreenDomain.Error or ContractScreenDomain.PremiseInconsistent ||
                item.Property is ContractScreenProperty.Unknown or ContractScreenProperty.Timeout or
                  ContractScreenProperty.Unsupported or ContractScreenProperty.Error)) {
            status = ContractScreenStatus.Partial;
          }
        }
      }
    } catch (OperationCanceledException) {
      status = cancellationToken.IsCancellationRequested ? ContractScreenStatus.Cancelled : ContractScreenStatus.Timeout;
      Fill(status == ContractScreenStatus.Cancelled ? ContractScreenDomain.Cancelled : ContractScreenDomain.Timeout,
        status == ContractScreenStatus.Cancelled ? "caller_cancelled" : "attempt_deadline");
    } catch (NotSupportedException error) {
      status = ContractScreenStatus.Unsupported;
      AddDiagnostic(error.Message);
      Fill(ContractScreenDomain.Unsupported, error.Message);
    } catch (ArgumentException error) {
      status = ContractScreenStatus.InvalidInput;
      AddDiagnostic(error.Message);
      Fill(ContractScreenDomain.InvalidInput, error.Message);
    } catch (IOException error) {
      status = ContractScreenStatus.Error;
      AddDiagnostic(error.Message);
      Fill(ContractScreenDomain.Error, "native_io_error");
    }
    finally {
      attempt?.Dispose();
    }
    var decided = results.Count(item => item.Property is ContractScreenProperty.Realizable or ContractScreenProperty.Unrealizable or
      ContractScreenProperty.ImplicationHolds or ContractScreenProperty.ImplicationViolated);
    return new(1, request?.Action ?? ContractScreenAction.Screen, request?.Question ?? ContractScreenQuestion.InputDomain,
      status, inspection?.Binding,
      inspection?.Capability ?? new(false, diagnostics.Messages, ContractScreenSourcePreparation.Features, true), results,
      new(cases.Count, results.Count(item => item.Domain == ContractScreenDomain.Admissible),
        results.Count(item => item.Domain == ContractScreenDomain.PreconditionRejected), decided, cases.Count - decided), diagnostics.Messages, dependencyOptions);

    void AddDiagnostic(string text) {
      diagnostics.Add(text);
    }
    void Fill(ContractScreenDomain domain, string reason) {
      foreach (var item in cases.Skip(results.Count).Where(item => item != null && item.Inputs != null)) {
        results.Add(Unchecked(item, domain, reason));
      }
    }
  }

  private static ContractScreenCaseResult Unchecked(ContractScreenCase item, ContractScreenDomain domain, string reason) =>
    new(item.Id, domain, ContractScreenProperty.NotChecked, [reason[..Math.Min(reason.Length, 256)]], [], item.Inputs, []);

  /// <summary>Bounds request-local text while reserving an explicit aggregate truncation marker.</summary>
  internal sealed class ScreenDiagnostics {
    internal const string TruncationMarker = "screen_query_diagnostics_truncated";
    private readonly List<string> messages = [];
    private int characters;
    private bool truncated;

    internal IReadOnlyList<string> Messages => truncated ? [.. messages, TruncationMarker] : messages;

    internal void Add(string text) {
      var remaining = ContractScreenValidation.MaximumDiagnosticCharacters - TruncationMarker.Length - characters;
      var retained = Math.Min(remaining, text.Length);
      if (retained > 0) {
        messages.Add(text[..retained]);
        characters += retained;
      }
      truncated |= retained < text.Length;
    }

    /// <summary>Keeps each query compact so verbose early solver output cannot hide the eight-query fixture's last query.</summary>
    internal sealed class Query(ScreenDiagnostics owner, string caseId, bool domain, bool negate, Func<double> elapsed) {
      private readonly List<object[]> phases = [];
      private bool truncated = caseId.Length > 64;

      internal void Phase(string phase, string state) {
        truncated |= phase.Length > 32 || state.Length > 16;
        if (phases.Count == 16) {
          phases.RemoveAt(0);
          truncated = true;
        }
        phases.Add([phase[..Math.Min(phase.Length, 32)], state[..Math.Min(state.Length, 16)], Milliseconds()]);
      }

      internal void Complete(ContractQueryResult? result, string terminal) {
        var text = result?.Diagnostics ?? "";
        truncated |= text.Length > 256;
        text = text[..Math.Min(text.Length, 256)];
        var record = Serialize();
        while (record.Length > 1536 && text.Length > 0) {
          text = text[..(text.Length / 2)];
          truncated = true;
          record = Serialize();
        }
        while (record.Length > 1536 && phases.Count > 0) {
          phases.RemoveAt(0);
          truncated = true;
          record = Serialize();
        }
        owner.Add(record);
        owner.truncated |= truncated;

        string Serialize() => JsonSerializer.Serialize(new {
          caseId = caseId[..Math.Min(caseId.Length, 64)],
          query = domain ? "domain" : "property",
          polarity = negate ? "negative" : "positive",
          elapsedMilliseconds = Milliseconds(),
          terminal,
          phases,
          diagnostics = text,
          truncated
        }, ContractJson.Options);
      }

      private long Milliseconds() => Math.Max(0, (long)Math.Round(elapsed()));
    }
  }

  /// <summary>Observes the actual query boundary while retaining its timeout, cancellation and identity rules.</summary>
  internal static async Task<(ContractQueryResult Result, string? OptionsIdentity, string? QueryIdentity)> ObserveQueryAsync(
    ScreenDiagnostics diagnostics, string caseId, bool domain, bool negate,
    CancellationToken cancellationToken, CancellationToken queryCancellationToken,
    Func<Action<string, string>, Task<(ContractQueryResult Result, string? OptionsIdentity, string? QueryIdentity)>> operation,
    Func<double> elapsed) {
    var observation = new ScreenDiagnostics.Query(diagnostics, caseId, domain, negate, elapsed);
    ContractQueryResult? completed = null;
    try {
      var result = await operation(observation.Phase);
      completed = result.Result;
      return result;
    } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
      completed = new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Timeout, "query_deadline");
      return (completed, null, null);
    }
    finally {
      observation.Complete(completed, completed?.Outcome.ToString().ToLowerInvariant() ??
        (queryCancellationToken.IsCancellationRequested ? "cancelled" : "failed"));
    }
  }

  private sealed class NativeBackend : IContractScreenBackend {
    private readonly DafnyOptions options;
    private readonly ScreenDiagnostics diagnostics;
    private ContractPreparedProgram? prepared;
    private ContractSpecificationChecker? checker;
    private ContractSpecificationScope? scope;
    private ContractScreenProjection? projection;
    private int queryMilliseconds;
    private bool contextCertified;

    internal NativeBackend(DafnyOptions baseOptions, ScreenDiagnostics diagnostics) {
      this.diagnostics = diagnostics;
      options = new DafnyOptions(baseOptions, useNullWriters: true) {
        Compile = false,
        RunningBoogieFromCommandLine = true,
        VerifyAllModules = true
      };
      options.Set(CommonOptionBag.UnicodeCharacters, true);
    }

    public async Task<ContractScreenInspection> InspectAsync(ContractScreenRequest request, CancellationToken cancellationToken) {
      contextCertified = false;
      queryMilliseconds = (request.Budgets ?? new()).QueryMilliseconds;
      var reporter = new BatchErrorReporter(options);
      var parsed = await ContractScreenSourcePreparation.ParseAsync(reporter, request.Sources, cancellationToken, target: request.Target);
      if (reporter.ErrorCount != 0) {
        throw new ArgumentException("source_parse_or_resolution: " + string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
      }
      var program = parsed.Program;
      projection = parsed.Projection ?? throw new NotSupportedException("projection_unavailable");
      var method = ContractCallableSelector.SelectMethod(program, request.Target, allowLemmaContract: true);
      if (method.GetType() != typeof(Method) && method.GetType() != typeof(Lemma) || !method.IsStatic) {
        throw new NotSupportedException("target_not_ordinary_method_or_lemma");
      }
      if (request.Question == ContractScreenQuestion.MethodRealizability && method is Lemma ||
          request.Question == ContractScreenQuestion.LemmaImplication && method is not Lemma) {
        throw new NotSupportedException("question_target_mismatch");
      }
      var source = ContractSourceSnapshot.Find(request.Sources, method.Origin.Uri);
      prepared = new(program, method, source,
        new(source.Path, method.Origin.line, method.Origin.col, method.FullDafnyName, source.Sha256), Sources: request.Sources);
      checker = new(program, request.Sources, options) { ScreenProjection = projection };
      var functions = program.RawModules().Where(module => module != program.SystemModuleManager.SystemModule)
        .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
        .SelectMany(owner => owner.Members).OfType<Function>().Cast<MethodOrFunction>().ToList();
      // All retained logical definitions are roots, including unrelated definitions.
      scope = checker.LogicalScope(functions, method.Ins.Concat(method.Outs).Select(formal => formal.Type));
      if (scope.ContainsDeclaration(method)) { throw new NotSupportedException("target_dependency"); }
      if (scope.Failure != null) { throw new NotSupportedException(scope.Failure); }
      var matchingSpans = parsed.OriginalSpans.Where(definition => ContractSourceSnapshot.UriFor(definition.SourcePath) == method.Origin.Uri &&
        definition.Start == method.StartToken.pos && definition.Name == method.Name).ToList();
      if (matchingSpans.Count != 1) { throw new NotSupportedException("target_span_identity"); }
      var span = matchingSpans[0];
      var fingerprintRequest = new SourceFingerprintRequest([
        new("declaration", source.Path, new(span.Start, span.End), []),
        new("contract", source.Path, new(span.Start, span.BodyStart ?? span.End), [])
      ]);
      var fingerprints = SourceFingerprint.Compute(options, fingerprintRequest,
        request.Sources.ToDictionary(item => item.Path, item => item.Content), out var failure)
        ?? throw new NotSupportedException(failure ?? "fingerprint_unavailable");
      var sourceHash = ContractRuntimeTypeEvidence.SourceSetHash(request.Sources);
      var toolchain = DefinitionAnalysis.ContextToolchainIdentity() ?? throw new NotSupportedException("toolchain_identity_unavailable");
      string producer;
      using (var stream = File.OpenRead(typeof(ContractScreenService).Assembly.Location)) {
        producer = Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
      }
      var optionsIdentity = DefinitionAnalysis.ContextOptionsIdentity(options);
      var context = ContractHarnessBuilder.Hash(JsonSerializer.Serialize(new {
        sourceHash,
        request.Target,
        request.Dependencies,
        request.Question,
        toolchain,
        producer,
        optionsIdentity,
        policy = ContractScreenSourcePreparation.PolicyVersion,
        omitted = parsed.OmittedBodies,
        retainedMembers = projection.Members,
        retainedModules = projection.Modules,
        references = projection.References.Select(pair => new { declaration = pair.Key, identity = pair.Value }),
        logicalScope = scope.Symbols,
        checks = scope.RequiredNativeChecks
      }, ContractJson.Options));
      var binding = new ContractScreenBinding(sourceHash, method.FullDafnyName,
        fingerprints.Fingerprints.Single(item => item.Id == "declaration").Sha256,
        fingerprints.Fingerprints.Single(item => item.Id == "contract").Sha256,
        context, ContractScreenSourcePreparation.PolicyVersion, ContractHarnessBuilder.Hash(toolchain + ":" + producer), optionsIdentity);
      var module = method.EnclosingClass.EnclosingModuleDefinition;
      ContractScreenFormal Describe(Formal formal) => new(formal.Name,
        ContractQueryBuilder.QualifiedType(program, module, formal.Type), formal.IsGhost);
      var descriptor = new ContractScreenTargetDescriptor(method.FullDafnyName, method is Lemma ? "lemma" : "method",
        method.Ins.Select(Describe).ToList(), method.Outs.Select(Describe).ToList(),
        method.Req.Select(clause => ContractQueryBuilder.RenderExpression(prepared, clause.E)).ToList(),
        method.Ens.Select(clause => ContractQueryBuilder.RenderExpression(prepared, clause.E)).ToList());
      return new(binding, new(true, [], ContractScreenSourcePreparation.Features, true, descriptor));
    }

    public async Task<ContractScreenCertification> CertifyAsync(CancellationToken cancellationToken, long deadlineTimestamp) {
      contextCertified = false;
      if (checker == null || scope == null || prepared == null) { throw new InvalidOperationException("Inspect before certification."); }
      var identities = new List<string>();
      foreach (var module in checker.PendingModules(scope)) {
        using var queryCancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        queryCancellation.CancelAfter(queryMilliseconds);
        var queryDeadline = Math.Min(deadlineTimestamp, ContractQueryDeadline.AfterMilliseconds(queryMilliseconds));
        ContractSpecificationResult result;
        try {
          result = await checker.CheckModuleAsync(scope, module, queryCancellation.Token, deadlineTimestamp: queryDeadline);
        } catch (OperationCanceledException) when (!cancellationToken.IsCancellationRequested) {
          return new(new(false, "dependency_query_deadline", [], []) { Outcome = ContractSpecificationOutcome.Timeout }, identities);
        }
        if (result.EffectiveOptionsIdentity != null) { identities.Add(result.EffectiveOptionsIdentity); }
        if (!result.Verified || result.Outcome != ContractSpecificationOutcome.Verified) { return new(result, identities); }
      }
      if (!checker.Accept(scope) || checker.IndependentGlobals(prepared.Program, prepared.SourceSnapshots) == null) {
        return new(new(false, "independent_ambient_admission_unavailable", [], []) { Outcome = ContractSpecificationOutcome.Unsupported }, identities);
      }
      contextCertified = true;
      return new(new(true, "All retained logical definitions certified; pure input carriers and independent globals remain separately checked.", [], []), identities);
    }

    public async Task<ContractScreenCaseResult> CheckCaseAsync(ContractScreenCase item, ContractScreenQuestion question,
      int queryMilliseconds, CancellationToken cancellationToken, long deadlineTimestamp) {
      if (prepared == null || checker == null) { throw new InvalidOperationException("Inspect before checking cases."); }
      if (!contextCertified) { throw new InvalidOperationException("Certify the projected context before checking cases."); }
      try {
        var membership = ContractInitialTypeProof.CheckScreenInputs(prepared, item.Inputs, checker);
        if (membership != true) { return Unchecked(item, membership == false ? ContractScreenDomain.InvalidInput : ContractScreenDomain.Unknown, "input_membership"); }
      } catch (ArgumentException) {
        return Unchecked(item, ContractScreenDomain.InvalidInput, "invalid_concrete_input");
      } catch (NotSupportedException) {
        return Unchecked(item, ContractScreenDomain.InvalidInput, "invalid_concrete_value");
      }
      return await DecideCertifiedCaseAsync(item, question, async (domain, negate) => {
        var queryDeadline = Math.Min(deadlineTimestamp, ContractQueryDeadline.AfterMilliseconds(queryMilliseconds));
        using var queryCancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        queryCancellation.CancelAfter(queryMilliseconds);
        var clock = Stopwatch.StartNew();
        return await ObserveQueryAsync(diagnostics, item.Id, domain, negate, cancellationToken, queryCancellation.Token,
          async observer => {
            ContractQueryDeadline.Check(queryDeadline, queryCancellation.Token);
            var query = ContractPhaseRecorder.Measure(observer, "query_build", queryCancellation.Token,
              () => ContractQueryBuilder.BuildScreen(prepared, item.Inputs, domain, negate) with { Projection = projection });
            return await ContractSolver.CheckScreenAsync(query, prepared.SourceSnapshots, options, queryCancellation.Token, queryDeadline,
              observer);
          }, () => clock.Elapsed.TotalMilliseconds);
      });
    }
  }

  /// <summary>
  /// Classifies proofs only after complete projected logical/termination/definedness certification and
  /// constructive input membership. The query boundary must retain native original-assertion, WD,
  /// coverage and provenance checks. A failed assertion alone never establishes a negative decision.
  /// </summary>
  internal static async Task<ContractScreenCaseResult> DecideCertifiedCaseAsync(ContractScreenCase item, ContractScreenQuestion question,
    Func<bool, bool, Task<(ContractQueryResult Result, string? OptionsIdentity, string? QueryIdentity)>> query) {
    var identities = new List<string>();
    var queries = new List<string>();
    var reasons = new List<string>();
    var domain = await Pair(true);
    if (domain.Failure != null) {
      reasons.Add("domain_not_decided");
      return new(item.Id, domain.Failure.Value, ContractScreenProperty.NotChecked, reasons, identities, item.Inputs, queries);
    }
    if (!domain.Positive) { return new(item.Id, ContractScreenDomain.PreconditionRejected, ContractScreenProperty.NotChecked, reasons, identities, item.Inputs, queries); }
    if (question == ContractScreenQuestion.InputDomain) { return new(item.Id, ContractScreenDomain.Admissible, ContractScreenProperty.NotChecked, reasons, identities, item.Inputs, queries); }
    var property = await Pair(false);
    if (property.Failure != null) {
      var state = property.Failure switch {
        ContractScreenDomain.Timeout => ContractScreenProperty.Timeout,
        ContractScreenDomain.Cancelled => ContractScreenProperty.Cancelled,
        ContractScreenDomain.Error => ContractScreenProperty.Error,
        _ => ContractScreenProperty.Unknown
      };
      reasons.Add("property_not_decided");
      return new(item.Id, ContractScreenDomain.Admissible, state, reasons, identities, item.Inputs, queries);
    }
    return new(item.Id, ContractScreenDomain.Admissible,
      question == ContractScreenQuestion.LemmaImplication
        ? property.Positive ? ContractScreenProperty.ImplicationHolds : ContractScreenProperty.ImplicationViolated
        : property.Positive ? ContractScreenProperty.Realizable : ContractScreenProperty.Unrealizable,
      reasons, identities, item.Inputs, queries);

    async Task<(bool Positive, ContractScreenDomain? Failure)> Pair(bool isDomain) {
      var positive = await Attempt(isDomain, false);
      if (positive.Result == null) { return (false, ContractScreenDomain.Cancelled); }
      if ((positive.Result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Unsat) &&
          (positive.OptionsIdentity == null || positive.QueryIdentity == null)) { return (false, ContractScreenDomain.Error); }
      // Certified ambient consistency and constructive legal inputs justify a completed positive proof.
      // Its unstarted opposite contributes no consistency certificate and has no outcome to record.
      if (positive.Result.Outcome == ContractQueryOutcome.Unsat) { return (true, null); }
      if (positive.Result.Outcome != ContractQueryOutcome.Sat) {
        return (false, Failure(positive.Result.Outcome));
      }
      var negative = await Attempt(isDomain, true);
      if (negative.Result == null) { return (false, ContractScreenDomain.Cancelled); }
      if ((negative.Result.Outcome is ContractQueryOutcome.Sat or ContractQueryOutcome.Unsat) &&
          (negative.OptionsIdentity == null || negative.QueryIdentity == null)) { return (false, ContractScreenDomain.Error); }
      return negative.Result.Outcome == ContractQueryOutcome.Unsat ? (false, null) : (false, Failure(negative.Result.Outcome));
    }

    async Task<(ContractQueryResult? Result, string? OptionsIdentity, string? QueryIdentity)> Attempt(bool isDomain, bool negate) {
      var prefix = "query_" + (isDomain ? "domain_" : "property_") + (negate ? "negative_" : "positive_");
      try {
        var result = await query(isDomain, negate);
        reasons.Add(prefix + (result.Result.Outcome switch {
          ContractQueryOutcome.Unsat => "unsat",
          ContractQueryOutcome.Sat => "sat",
          ContractQueryOutcome.Unknown => "unknown",
          ContractQueryOutcome.Timeout => "timeout",
          _ => "error"
        }));
        if (result.OptionsIdentity != null && result.QueryIdentity != null) {
          identities.Add(result.OptionsIdentity);
          queries.Add(result.QueryIdentity);
        }
        return result;
      } catch (OperationCanceledException) {
        reasons.Add(prefix + "cancelled");
        return (null, null, null);
      }
    }

    static ContractScreenDomain Failure(ContractQueryOutcome outcome) => outcome switch {
      ContractQueryOutcome.Timeout => ContractScreenDomain.Timeout,
      ContractQueryOutcome.Sat or ContractQueryOutcome.Unknown => ContractScreenDomain.Unknown,
      _ => ContractScreenDomain.Error
    };
  }
}
