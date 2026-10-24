using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractScreenServiceTests {
  // Safe verifier defaults reach the in-memory snapshot-integrity boundary.
  [Fact]
  public async Task DefaultVerifierOptionsReachSourceValidation() {
    var failure = await Assert.ThrowsAsync<ArgumentException>(() => PrepareWithStaleSnapshot(ScreenOptions()));
    Assert.Equal("Source snapshots require paths, content and matching hashes.", failure.Message);
  }

  // Unsafe verifier modes stop before snapshot validation, parsing or classification.
  [Theory]
  [InlineData("assume_div")]
  [InlineData("assume_index")]
  [InlineData("skip_verify")]
  [InlineData("skip_dafny_verify")]
  [InlineData("skip_resolve")]
  [InlineData("skip_typecheck")]
  [InlineData("overlook_type_errors")]
  [InlineData("free_loop_invariants")]
  [InlineData("trust_mover_types")]
  [InlineData("trust_noninterference")]
  [InlineData("trust_refinement")]
  [InlineData("trust_sequentialization")]
  [InlineData("trust_lower_layers")]
  [InlineData("trust_upper_layers")]
  public async Task UnsafeVerifierOptionsStopBeforeSourcePreparation(string setting) {
    var options = ScreenOptions();
    switch (setting) {
      case "assume_div": options.Set(CommonOptionBag.AssumeWellFormedDiv, true); break;
      case "assume_index": options.Set(CommonOptionBag.AssumeWellFormedIndex, true); break;
      case "skip_verify": options.Verify = false; break;
      case "skip_dafny_verify": options.DafnyVerify = false; break;
      case "skip_resolve": options.NoResolve = true; break;
      case "skip_typecheck": options.NoTypecheck = true; break;
      case "overlook_type_errors": options.OverlookBoogieTypeErrors = true; break;
      case "free_loop_invariants": options.AlwaysAssumeFreeLoopInvariants = true; break;
      case "trust_mover_types": options.TrustMoverTypes = true; break;
      case "trust_noninterference": options.TrustNoninterference = true; break;
      case "trust_refinement": options.TrustRefinement = true; break;
      case "trust_sequentialization": options.TrustSequentialization = true; break;
      case "trust_lower_layers": options.TrustLayersUpto = 0; break;
      case "trust_upper_layers": options.TrustLayersDownto = 0; break;
      default: throw new ArgumentException("Unknown verifier setting.", nameof(setting));
    }
    var failure = await Assert.ThrowsAsync<NotSupportedException>(() => PrepareWithStaleSnapshot(options));
    Assert.Equal("unsupported_options", failure.Message);
  }

  // A failed positive assertion and a failed negative assertion supply no semantic counterexample.
  [Fact]
  public async Task FailedProofsRemainUnknown() {
    var result = await Decide(ContractQueryOutcome.Sat, ContractQueryOutcome.Sat);
    Assert.Equal(ContractScreenDomain.Unknown, result.Domain);
    Assert.Equal(ContractScreenProperty.NotChecked, result.Property);
  }

  // Certified positive proofs finish without launching either opposite query.
  [Fact]
  public async Task CertifiedPositiveProofsDoNotLaunchOpposites() {
    var calls = new List<(bool Domain, bool Negate)>();
    var result = await ContractScreenService.DecideCertifiedCaseAsync(Case("one"), ContractScreenQuestion.MethodRealizability,
      (domain, negate) => {
        Assert.False(negate);
        calls.Add((domain, negate));
        return Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Unsat, ""),
          (string?)new string('a', 64), (string?)calls.Count.ToString("x64")));
      });
    Assert.Equal(new[] { (true, false), (false, false) }, calls);
    Assert.Equal(ContractScreenProperty.Realizable, result.Property);
    Assert.Equal(2, result.QueryIdentities.Count);
    Assert.Equal(new[] { "query_domain_positive_unsat", "query_property_positive_unsat" }, result.ReasonCodes);
  }

  // A failed positive proof followed by a timed-out negative query remains undecided.
  [Fact]
  public async Task OppositePolarityTimeoutCannotBecomePositive() {
    var result = await Decide(ContractQueryOutcome.Sat, ContractQueryOutcome.Timeout);
    Assert.Equal(ContractScreenDomain.Timeout, result.Domain);
    Assert.Equal(ContractScreenProperty.NotChecked, result.Property);
    Assert.Contains("query_domain_negative_timeout", result.ReasonCodes);
  }

  // A proved negated joint-output assertion reports unrealizability only after admissibility proved.
  [Fact]
  public async Task JointPropertyUsesNativeNegativeProof() {
    var result = await Decide(ContractQueryOutcome.Unsat, ContractQueryOutcome.Sat, ContractQueryOutcome.Unsat);
    Assert.Equal(ContractScreenDomain.Admissible, result.Domain);
    Assert.Equal(ContractScreenProperty.Unrealizable, result.Property);
    Assert.Equal(3, result.QueryIdentities.Count);
    Assert.Equal(new[] { "query_domain_positive_unsat", "query_property_positive_sat", "query_property_negative_unsat" }, result.ReasonCodes);
  }

  // Domain-only admission consumes exactly its completed positive proof.
  [Fact]
  public async Task DomainAdmissionUsesOneProof() {
    var result = await ContractScreenService.DecideCertifiedCaseAsync(Case("one"), ContractScreenQuestion.InputDomain,
      (domain, negate) => {
        Assert.True(domain);
        Assert.False(negate);
        return Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Unsat, ""),
          (string?)new string('a', 64), (string?)new string('b', 64)));
      });
    Assert.Equal(ContractScreenDomain.Admissible, result.Domain);
    Assert.Equal(ContractScreenProperty.NotChecked, result.Property);
    Assert.Single(result.QueryIdentities);
  }

  // A rejected precondition needs its negative proof after the positive assertion failed.
  [Fact]
  public async Task RejectedPreconditionUsesNegativeProof() {
    var result = await Decide(ContractQueryOutcome.Sat, ContractQueryOutcome.Unsat);
    Assert.Equal(ContractScreenDomain.PreconditionRejected, result.Domain);
    Assert.Equal(2, result.QueryIdentities.Count);
    Assert.Equal(new[] { "query_domain_positive_sat", "query_domain_negative_unsat" }, result.ReasonCodes);
  }

  // An attempted unknown stops without consuming a later proof or inventing its provenance.
  [Fact]
  public async Task UnknownRemainsVisibleWithoutOpposite() {
    var result = await Decide(ContractQueryOutcome.Unknown);
    Assert.Equal(ContractScreenDomain.Unknown, result.Domain);
    Assert.Single(result.QueryIdentities);
    Assert.Contains("query_domain_positive_unknown", result.ReasonCodes);
  }

  // An actual property error preserves admission and the attempted-query outcome.
  [Fact]
  public async Task PropertyErrorPreservesAdmission() {
    var result = await Decide(ContractQueryOutcome.Unsat, ContractQueryOutcome.Error);
    Assert.Equal(ContractScreenDomain.Admissible, result.Domain);
    Assert.Equal(ContractScreenProperty.Error, result.Property);
    Assert.Contains("query_property_positive_error", result.ReasonCodes);
  }

  // Cancellation of a property attempt retains the completed domain proof without fabricated hashes.
  [Fact]
  public async Task QueryCancellationPreservesEarlierEvidence() {
    var result = await ContractScreenService.DecideCertifiedCaseAsync(Case("one"), ContractScreenQuestion.MethodRealizability,
      (domain, _) => domain
        ? Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Unsat, ""),
          (string?)new string('a', 64), (string?)new string('b', 64)))
        : Task.FromException<(ContractQueryResult, string?, string?)>(new OperationCanceledException()));
    Assert.Equal(ContractScreenDomain.Admissible, result.Domain);
    Assert.Equal(ContractScreenProperty.Cancelled, result.Property);
    Assert.Single(result.QueryIdentities);
    Assert.Equal(new[] { "query_domain_positive_unsat", "query_property_positive_cancelled", "property_not_decided" }, result.ReasonCodes);
  }

  // Inspection never invokes certification or a per-case native query.
  [Fact]
  public async Task InspectIsSolverFree() {
    var backend = new FakeBackend();
    var result = await new ContractScreenService(backend).ExecuteAsync(Request(ContractScreenAction.Inspect), CancellationToken.None);
    Assert.Equal(ContractScreenStatus.Completed, result.Status);
    Assert.True(result.Capability.CertificationPending);
    Assert.Equal(0, backend.CertificationCalls);
    Assert.Equal(0, backend.CaseCalls);
  }

  // A stale binding stops before dependency certification and retains the requested case identity and inputs.
  [Fact]
  public async Task StaleBindingStopsBeforeCertification() {
    var backend = new FakeBackend();
    var request = Request() with { Binding = Binding() with { SourceSetHash = "stale" } };
    var result = await new ContractScreenService(backend).ExecuteAsync(request, CancellationToken.None);
    Assert.Equal(ContractScreenStatus.InvalidInput, result.Status);
    Assert.Contains("stale_binding", result.Diagnostics);
    Assert.Equal(0, backend.CertificationCalls);
    Assert.Equal("7", Assert.Single(result.Cases).Inputs["x"].Value);
  }

  // A dependency timeout cannot produce a ready capability or start property queries.
  [Fact]
  public async Task DependencyTimeoutRemainsExplicit() {
    var optionsIdentity = new string('a', 64);
    var backend = new FakeBackend {
      Certificate = new(false, "timeout", [], []) {
        Outcome = ContractSpecificationOutcome.Timeout,
        EffectiveOptionsIdentity = optionsIdentity
      }
    };
    var result = await new ContractScreenService(backend).ExecuteAsync(Request(), CancellationToken.None);
    Assert.Equal(ContractScreenStatus.Timeout, result.Status);
    Assert.True(result.Capability.CertificationPending);
    Assert.Equal(ContractScreenDomain.Timeout, Assert.Single(result.Cases).Domain);
    Assert.Equal(0, backend.CaseCalls);
    Assert.Equal(optionsIdentity, Assert.Single(result.DependencyOptionsIdentities));
  }

  // Caller cancellation preserves a finished case and explicitly accounts for every remaining case.
  [Fact]
  public async Task CancellationPreservesCompletedCases() {
    using var cancellation = new CancellationTokenSource();
    var backend = new FakeBackend { AfterCase = cancellation.Cancel };
    var request = Request() with { Cases = [Case("first"), Case("second")] };
    var result = await new ContractScreenService(backend).ExecuteAsync(request, cancellation.Token);
    Assert.Equal(ContractScreenStatus.Cancelled, result.Status);
    Assert.Equal(2, result.Cases.Count);
    Assert.Equal(ContractScreenProperty.Realizable, result.Cases[0].Property);
    Assert.Equal(ContractScreenDomain.Cancelled, result.Cases[1].Domain);
    Assert.Equal(1, result.Counts.Decided);
    Assert.Equal(1, backend.CaseCalls);
  }

  // Caller sufficiency cannot enter an injected native backend that lacks native caller obligations.
  [Fact]
  public async Task CallerSufficiencyIsUnsupportedBeforeNativeWork() {
    var backend = new FakeBackend();
    var result = await new ContractScreenService(backend).ExecuteAsync(Request() with {
      Question = ContractScreenQuestion.CallerSufficiency
    }, CancellationToken.None);
    Assert.Equal(ContractScreenStatus.Unsupported, result.Status);
    Assert.Equal(0, backend.InspectionCalls);
  }

  // A proof result without emitted-query identity cannot become semantic evidence.
  [Fact]
  public async Task MissingQueryIdentityFailsClosed() {
    var result = await ContractScreenService.DecideCertifiedCaseAsync(Case("one"), ContractScreenQuestion.MethodRealizability,
      (_, _) => Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Unsat, ""), (string?)new string('a', 64), (string?)null)));
    Assert.Equal(ContractScreenDomain.Error, result.Domain);
    Assert.Equal(ContractScreenProperty.NotChecked, result.Property);
  }

  // Completed query text and phase facts reach the existing result without changing semantic evidence.
  [Fact]
  public async Task CompletedQueryDiagnosticsReachOverallResult() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    var elapsed = 1.0;
    var native = new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Sat, "retained reduction diagnostics");
    var returned = await ContractScreenService.ObserveQueryAsync(diagnostics, "one", false, false,
      CancellationToken.None, CancellationToken.None,
      observer => ContractPhaseRecorder.MeasureAsync(observer, "reduction", CancellationToken.None, () => {
        elapsed = 12.0;
        return Task.FromResult((native, (string?)"options", (string?)"query"));
      }), () => elapsed);
    Assert.Same(native, returned.Result);
    Assert.Equal("options", returned.OptionsIdentity);
    Assert.Equal("query", returned.QueryIdentity);
    var result = await new ContractScreenService(new FakeBackend()).ExecuteAsync(Request(), CancellationToken.None, diagnostics);
    using var document = JsonDocument.Parse(Assert.Single(result.Diagnostics));
    var observed = document.RootElement;
    Assert.Equal("one", observed.GetProperty("caseId").GetString());
    Assert.Equal("property", observed.GetProperty("query").GetString());
    Assert.Equal("positive", observed.GetProperty("polarity").GetString());
    Assert.Equal("sat", observed.GetProperty("terminal").GetString());
    Assert.Equal(12, observed.GetProperty("elapsedMilliseconds").GetInt64());
    Assert.Equal("retained reduction diagnostics", observed.GetProperty("diagnostics").GetString());
    Assert.Equal(2, observed.GetProperty("phases").GetArrayLength());
    Assert.Equal(ContractScreenProperty.Realizable, Assert.Single(result.Cases).Property);
    Assert.Equal(new[] { new string('b', 64), new string('c', 64) }, result.Cases[0].QueryIdentities);
  }

  // Cancellation preserves the interrupted phase and terminal state while the original exception still propagates.
  [Fact]
  public async Task CancelledPhaseRetainsTerminalObservation() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    using var cancellation = new CancellationTokenSource();
    cancellation.Cancel();
    var original = new OperationCanceledException();
    var returned = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractScreenService.ObserveQueryAsync(
      diagnostics, "one", false, true, cancellation.Token, cancellation.Token,
      observer => ContractPhaseRecorder.MeasureAsync(observer, "boogie:ScreenControl", cancellation.Token,
        () => Task.FromException<(ContractQueryResult, string?, string?)>(original)), () => 3000));
    Assert.Same(original, returned);
    using var document = JsonDocument.Parse(Assert.Single(diagnostics.Messages));
    var observed = document.RootElement;
    Assert.Equal("negative", observed.GetProperty("polarity").GetString());
    Assert.Equal("cancelled", observed.GetProperty("terminal").GetString());
    var phases = observed.GetProperty("phases");
    Assert.Equal("boogie:ScreenControl", phases[1][0].GetString());
    Assert.Equal("cancelled", phases[1][1].GetString());
    Assert.Equal(3000, phases[1][2].GetInt64());
  }

  // Failed phases retain their final boundary without catching or replacing programming failures.
  [Fact]
  public async Task FailedPhaseRetainsOriginalException() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    var original = new InvalidOperationException("original failure");
    var returned = await Assert.ThrowsAsync<InvalidOperationException>(() => ContractScreenService.ObserveQueryAsync(
      diagnostics, "one", false, true, CancellationToken.None, CancellationToken.None,
      observer => ContractPhaseRecorder.MeasureAsync(observer, "translation", CancellationToken.None,
        () => Task.FromException<(ContractQueryResult, string?, string?)>(original)), () => 4));
    Assert.Same(original, returned);
    using var document = JsonDocument.Parse(Assert.Single(diagnostics.Messages));
    Assert.Equal("failed", document.RootElement.GetProperty("terminal").GetString());
    Assert.Equal("failed", document.RootElement.GetProperty("phases")[1][1].GetString());
  }

  // Per-query prefixes keep the target negative property and tail query visible under the aggregate cap.
  [Fact]
  public async Task VerboseEarlyQueriesCannotHideTargetOrTail() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    diagnostics.Add("Certified public context.");
    var verbose = new string('x', 20_000);
    for (var ordinal = 0; ordinal < 8; ordinal++) {
      using var cancellation = new CancellationTokenSource();
      if (ordinal == 5) { cancellation.Cancel(); }
      var returned = await ContractScreenService.ObserveQueryAsync(diagnostics,
        ordinal < 3 ? "zero" : ordinal < 6 ? "one" : "negative", ordinal is 0 or 3 or 6 or 7,
        ordinal is 2 or 5 or 7, CancellationToken.None, cancellation.Token,
        observer => {
          foreach (var phase in new[] { "query_build", "parse", "project", "resolve", "reduction", "translation" }) {
            ContractPhaseRecorder.Measure(observer, phase, CancellationToken.None, () => 0);
          }
          return ContractPhaseRecorder.MeasureAsync(observer, "boogie:ScreenControl", cancellation.Token,
            () => ordinal == 5
              ? Task.FromException<(ContractQueryResult, string?, string?)>(new OperationCanceledException())
              : Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause,
                ordinal is 0 or 2 or 3 or 7 ? ContractQueryOutcome.Unsat : ContractQueryOutcome.Sat, verbose),
                (string?)"options", (string?)"query")));
        }, () => 5000);
      if (ordinal == 5) {
        Assert.Equal(ContractQueryOutcome.Timeout, returned.Result.Outcome);
        Assert.Null(returned.OptionsIdentity);
        Assert.Null(returned.QueryIdentity);
      }
    }
    Assert.True(diagnostics.Messages.Sum(message => message.Length) <= ContractScreenValidation.MaximumDiagnosticCharacters);
    Assert.Contains(ContractScreenService.ScreenDiagnostics.TruncationMarker, diagnostics.Messages);
    var records = diagnostics.Messages.Where(message => message.StartsWith("{", StringComparison.Ordinal)).ToList();
    Assert.Equal(8, records.Count);
    using var document = JsonDocument.Parse(records[5]);
    var observed = document.RootElement;
    Assert.Equal("one", observed.GetProperty("caseId").GetString());
    Assert.Equal("property", observed.GetProperty("query").GetString());
    Assert.Equal("negative", observed.GetProperty("polarity").GetString());
    Assert.Equal("timeout", observed.GetProperty("terminal").GetString());
    var phases = observed.GetProperty("phases");
    Assert.Equal("boogie:ScreenControl", phases[phases.GetArrayLength() - 1][0].GetString());
    Assert.Equal("cancelled", phases[phases.GetArrayLength() - 1][1].GetString());
    Assert.Equal("query_deadline", observed.GetProperty("diagnostics").GetString());
    using var early = JsonDocument.Parse(records[0]);
    Assert.True(early.RootElement.GetProperty("truncated").GetBoolean());
    Assert.InRange(early.RootElement.GetProperty("diagnostics").GetString()!.Length, 1, 256);
    using var tail = JsonDocument.Parse(records[7]);
    Assert.Equal("negative", tail.RootElement.GetProperty("caseId").GetString());
    Assert.Equal("domain", tail.RootElement.GetProperty("query").GetString());
    Assert.Equal("negative", tail.RootElement.GetProperty("polarity").GetString());
  }

  // Aggregate overflow keeps an explicit marker within the unchanged protocol character bound.
  [Fact]
  public void AggregateDiagnosticOverflowIsExplicit() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    diagnostics.Add(new string('x', 2 * ContractScreenValidation.MaximumDiagnosticCharacters));
    diagnostics.Add("later text");
    Assert.Equal(ContractScreenValidation.MaximumDiagnosticCharacters, diagnostics.Messages.Sum(message => message.Length));
    Assert.Equal(ContractScreenService.ScreenDiagnostics.TruncationMarker, diagnostics.Messages[^1]);
  }

  // Phase overflow retains the latest boundary and marks the bounded query record as truncated.
  [Fact]
  public async Task PhaseOverflowKeepsLastBoundary() {
    var diagnostics = new ContractScreenService.ScreenDiagnostics();
    await ContractScreenService.ObserveQueryAsync(diagnostics, "one", false, true,
      CancellationToken.None, CancellationToken.None, observer => {
        for (var ordinal = 0; ordinal < 33; ordinal++) {
          ContractPhaseRecorder.Measure(observer, "phase" + ordinal, CancellationToken.None, () => 0);
        }
        return Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, ContractQueryOutcome.Timeout, "query_deadline"),
          (string?)"options", (string?)"query"));
      }, () => 5000);
    using var document = JsonDocument.Parse(diagnostics.Messages[0]);
    var phases = document.RootElement.GetProperty("phases");
    Assert.InRange(phases.GetArrayLength(), 1, 16);
    Assert.Equal("phase32", phases[phases.GetArrayLength() - 1][0].GetString());
    Assert.True(document.RootElement.GetProperty("truncated").GetBoolean());
    Assert.Contains(ContractScreenService.ScreenDiagnostics.TruncationMarker, diagnostics.Messages);
  }

  private static DafnyOptions ScreenOptions() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    return options;
  }

  private static Task<ContractScreenParsed> PrepareWithStaleSnapshot(DafnyOptions options) {
    const string source = "method Child(x: int) returns (y: int) ensures y == x";
    // An invalid digest stops accepted options before the parser or any external boundary.
    return ContractScreenSourcePreparation.ParseAsync(new BatchErrorReporter(options),
      [new("input.dfy", source, "stale")], CancellationToken.None, target: new("Child"));
  }

  private static Task<ContractScreenCaseResult> Decide(params ContractQueryOutcome[] outcomes) {
    var queue = new Queue<ContractQueryOutcome>(outcomes);
    var ordinal = 0;
    return ContractScreenService.DecideCertifiedCaseAsync(Case("one"), ContractScreenQuestion.MethodRealizability,
      (_, _) => Task.FromResult((new ContractQueryResult(ContractQueryKind.ClosedClause, queue.Dequeue(), ""),
        (string?)new string('a', 64), (string?)(++ordinal).ToString("x64"))));
  }

  private static ContractScreenBinding Binding() => new("sources", "Child", "declaration", "contract", "context", "policy", "producer", "options");
  private static ContractScreenCase Case(string id) => new(id, new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "7") });
  private static ContractScreenRequest Request(ContractScreenAction action = ContractScreenAction.Screen) {
    const string source = "method Child(x: int) returns (y: int) ensures y == x";
    return new(1, action, [new("input.dfy", source, ContractHarnessBuilder.Hash(source))], new("Child"), [],
      ContractScreenQuestion.MethodRealizability, action == ContractScreenAction.Screen ? Binding() : null,
      action == ContractScreenAction.Screen ? [Case("one")] : []);
  }

  private sealed class FakeBackend : IContractScreenBackend {
    public int InspectionCalls { get; private set; }
    public int CertificationCalls { get; private set; }
    public int CaseCalls { get; private set; }
    public Action? AfterCase { get; init; }
    public ContractSpecificationResult Certificate { get; init; } = new(true, "", [], []);
    public Task<ContractScreenInspection> InspectAsync(ContractScreenRequest request, CancellationToken cancellationToken) {
      InspectionCalls++;
      return Task.FromResult(new ContractScreenInspection(Binding(), new(true, [], ["int"], true)));
    }
    public Task<ContractScreenCertification> CertifyAsync(CancellationToken cancellationToken, long deadlineTimestamp) {
      CertificationCalls++;
      return Task.FromResult(new ContractScreenCertification(Certificate,
        Certificate.EffectiveOptionsIdentity == null ? [] : [Certificate.EffectiveOptionsIdentity]));
    }
    public Task<ContractScreenCaseResult> CheckCaseAsync(ContractScreenCase item, ContractScreenQuestion question,
      int queryMilliseconds, CancellationToken cancellationToken, long deadlineTimestamp) {
      CaseCalls++;
      AfterCase?.Invoke();
      return Task.FromResult(new ContractScreenCaseResult(item.Id, ContractScreenDomain.Admissible,
        ContractScreenProperty.Realizable, ["query_domain_positive_unsat", "query_property_positive_unsat"],
        [new string('a', 64), new string('a', 64)], item.Inputs, [new string('b', 64), new string('c', 64)]));
    }
  }
}
