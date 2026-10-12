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

public class ContractPhaseTimingTests {
  private const string Source = """
    method ContractDiagnosticQuery(x: int)
      requires x == 3
    { assert {:error "contract_query_target"} x == 3; }
    """;

  private static DafnyOptions Options() {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.TimeLimit = 5;
    return options;
  }

  // Cancellation stops a running native proof before its solver limit and cannot publish a certificate or verdict.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task NativeCancellationStopsQueryAndCertificate(bool certificate) {
    const int count = 40;
    var variables = Enumerable.Range(0, count).Select(index => "x" + index).ToList();
    var parameters = string.Join(", ", variables.Select(variable => variable + ":int"));
    var requirements = string.Join("\n", variables.Select(variable =>
      "requires 0 <= " + variable + " < " + (count - 1)).Concat(
      from left in Enumerable.Range(0, count)
      from right in Enumerable.Range(left + 1, count - left - 1)
      select "requires " + variables[left] + " != " + variables[right]));
    var declaration = certificate
      ? "function Root(" + parameters + "):(result:int)\n" + requirements + "\nensures false { 0 }"
      : "method ContractDiagnosticQuery(" + parameters + ")\n" + requirements +
        "\n{ assert {:error \"contract_query_target\"} false; }";
    var source = "module Model { " + declaration + " }";
    var options = Options();
    options.TimeLimit = 10;
    using var cancellation = new CancellationTokenSource();
    var nativeElapsed = new System.Diagnostics.Stopwatch();
    if (certificate) {
      var snapshots = new[] { new ContractSource("cancel.dfy", source, ContractHarnessBuilder.Hash(source)) };
      var reporter = new BatchErrorReporter(options);
      var program = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, CancellationToken.None);
      Assert.Equal(0, reporter.ErrorCount);
      var checker = new ContractSpecificationChecker(program, snapshots, options);
      var root = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
        .SelectMany(type => type.Members).OfType<Function>().Single(function => function.Name == "Root");
      var scope = checker.Scope([root]);
      await Assert.ThrowsAnyAsync<OperationCanceledException>(() =>
        checker.CheckModuleAsync(scope, "Model", cancellation.Token, Observe));
      Assert.False(checker.Accept(scope));
      Assert.False(checker.IsValidated(root));
    } else {
      await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(source,
        ContractQueryKind.PremiseConsistency, options, cancellation.Token, phaseObserver: Observe));
    }
    nativeElapsed.Stop();
    Assert.True(nativeElapsed.Elapsed > TimeSpan.Zero);
    Assert.True(nativeElapsed.Elapsed < TimeSpan.FromSeconds(5), "Native cancellation took " + nativeElapsed.Elapsed);

    void Observe(string phase, string state) {
      if (phase.StartsWith("boogie:", StringComparison.Ordinal) && state == "started") {
        nativeElapsed.Start();
        cancellation.CancelAfter(500);
      }
    }
  }

  // A completed native query retains distinguishable frontend, reduction and solver timings.
  [Fact]
  public async Task SuccessfulQueryPersistsCompletedPhases() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-phase-test-" + Guid.NewGuid().ToString("N"));
    var path = Path.Combine(directory, "phases.jsonl");
    try {
      var recorder = new ContractPhaseRecorder(path);
      var result = await ContractSolver.CheckAsync(Source, ContractQueryKind.ClosedClause,
        Options(), CancellationToken.None, phaseObserver: recorder.Record);
      Assert.Equal(ContractQueryOutcome.Unsat, result.Outcome);
      var records = File.ReadLines(path).Select(line => JsonSerializer.Deserialize<PhaseEvent>(line, ContractJson.Options)!).ToList();
      foreach (var phase in new[] { "parse", "resolve", "reduction", "translation" }) {
        Assert.Equal(new[] { "started", "completed" }, records.Where(record => record.Phase == phase).Select(record => record.State));
      }
      Assert.Contains(records, record => record.Phase.StartsWith("boogie:", StringComparison.Ordinal) && record.State == "completed");
      Assert.All(records, record => Assert.True(record.ElapsedMilliseconds >= 0));
      Assert.Equal(records.Select(record => record.ElapsedMilliseconds).OrderBy(value => value), records.Select(record => record.ElapsedMilliseconds));
    }
    finally {
      if (Directory.Exists(directory)) { Directory.Delete(directory, recursive: true); }
    }
  }

  // Aggregate profiles replace one deterministic sidecar while retaining every completed measurement.
  [Fact]
  public void AggregateProfilePersistsSortedMetrics() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-profile-test-" + Guid.NewGuid().ToString("N"));
    var path = Path.Combine(directory, "profile.json");
    try {
      var recorder = new ContractProfileRecorder(path);
      Assert.Equal(3, recorder.Measure("sample_process", () => 3));
      Assert.Equal(4, recorder.Measure("result_classification", () => 4));
      Assert.Equal(5, recorder.Measure("sample_process", () => 5));
      recorder.Flush();

      var profile = JsonSerializer.Deserialize<ContractProfile>(File.ReadAllText(path), ContractJson.Options)!;
      Assert.Equal(ContractJson.SchemaVersion, profile.SchemaVersion);
      Assert.Equal("Stopwatch", profile.Clock);
      Assert.Equal(new[] { "result_classification", "sample_process" }, profile.Metrics.Select(metric => metric.Name));
      Assert.Equal(new long[] { 1, 2 }, profile.Metrics.Select(metric => metric.Count));
      Assert.All(profile.Metrics, metric => Assert.True(metric.ElapsedMilliseconds >= 0));
    }
    finally {
      if (Directory.Exists(directory)) { Directory.Delete(directory, recursive: true); }
    }
  }

  // A failed measured operation retains its spent time without changing the propagated exception.
  [Fact]
  public async Task AggregateProfileMeasuresFailure() {
    var directory = Path.Combine(Path.GetTempPath(), "contract-profile-failure-test-" + Guid.NewGuid().ToString("N"));
    var path = Path.Combine(directory, "profile.json");
    try {
      var recorder = new ContractProfileRecorder(path);
      await Assert.ThrowsAsync<InvalidOperationException>(() => recorder.MeasureAsync("result_classification",
        () => Task.FromException<bool>(new InvalidOperationException("classification failed"))));
      recorder.Flush();

      var profile = JsonSerializer.Deserialize<ContractProfile>(File.ReadAllText(path), ContractJson.Options)!;
      var metric = Assert.Single(profile.Metrics);
      Assert.Equal("result_classification", metric.Name);
      Assert.Equal(1, metric.Count);
      Assert.True(metric.ElapsedMilliseconds >= 0);
    }
    finally {
      if (Directory.Exists(directory)) { Directory.Delete(directory, recursive: true); }
    }
  }

  // Cancellation during original-source resolution preserves its terminal phase instead of a false completion.
  [Fact]
  public async Task CancelledResolutionRetainsPhaseBoundary() {
    using var cancellation = new CancellationTokenSource();
    var completedCancellation = Task.CompletedTask;
    var events = new List<(string Phase, string State)>();
    var sources = new[] { new ContractSource("query.dfy", Source, ContractHarnessBuilder.Hash(Source)) };
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(Source,
      ContractQueryKind.ClosedClause, Options(), cancellation.Token,
      sourceSnapshots: sources, sourcePath: "query.dfy", phaseObserver: Observe));
    await completedCancellation;
    Assert.Contains(("parse", "completed"), events);
    Assert.Contains(("resolve", "cancelled"), events);
    Assert.DoesNotContain(("resolve", "completed"), events);
    Assert.DoesNotContain(events, item => item.Phase is "reduction" or "translation" || item.Phase.StartsWith("boogie:", StringComparison.Ordinal));

    void Observe(string phase, string state) {
      events.Add((phase, state));
      if (phase == "resolve" && state == "started") { completedCancellation = cancellation.CancelAsync(); }
    }
  }

  // A resolution error remains an error and never acquires reduction or solver completion events.
  [Fact]
  public async Task InvalidQueryDoesNotClaimSolverWork() {
    var events = new List<(string Phase, string State)>();
    var result = await ContractSolver.CheckAsync("method ContractDiagnosticQuery() { assert missing; }",
      ContractQueryKind.ClosedClause, Options(), CancellationToken.None,
      phaseObserver: (phase, state) => events.Add((phase, state)));
    Assert.Equal(ContractQueryOutcome.Error, result.Outcome);
    Assert.Contains(("resolve", "completed"), events);
    Assert.DoesNotContain(events, item => item.Phase is "reduction" or "translation" || item.Phase.StartsWith("boogie:", StringComparison.Ordinal));
  }

  // A monotonic deadline rejects a query even if no cancellation callback has fired.
  [Fact]
  public async Task ExpiredDeadlineRejectsQueryBeforeFrontend() {
    var events = new List<(string Phase, string State)>();
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(Source,
      ContractQueryKind.ClosedClause, Options(), CancellationToken.None,
      phaseObserver: (phase, state) => events.Add((phase, state)), deadlineTimestamp: 0));
    Assert.Empty(events);
  }

  // Token cancellation at reduction start records cancellation and starts no later native phase.
  [Fact]
  public async Task CancellationAtReductionStartStopsBeforeTranslation() {
    using var cancellation = new CancellationTokenSource();
    var events = new List<(string Phase, string State)>();

    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(Source,
      ContractQueryKind.ClosedClause, Options(), cancellation.Token, phaseObserver: Observe));

    Assert.Contains(("parse", "completed"), events);
    Assert.Contains(("resolve", "completed"), events);
    Assert.Contains(("reduction", "started"), events);
    Assert.Contains(("reduction", "cancelled"), events);
    Assert.DoesNotContain(("reduction", "completed"), events);
    Assert.DoesNotContain(events, item => item.Phase == "translation" ||
      item.Phase.StartsWith("boogie:", StringComparison.Ordinal));

    void Observe(string phase, string state) {
      events.Add((phase, state));
      if (phase == "reduction" && state == "started") { cancellation.Cancel(); }
    }
  }

  // Monotonic expiry at reduction start records failure with an uncancelled token and starts no later phase.
  [Fact]
  public async Task DeadlineAtReductionStartStopsBeforeTranslation() {
    var events = new List<(string Phase, string State)>();
    var deadline = ContractQueryDeadline.AfterMilliseconds(3000);

    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(Source,
      ContractQueryKind.ClosedClause, Options(), CancellationToken.None,
      phaseObserver: Observe, deadlineTimestamp: deadline));

    Assert.Contains(("parse", "completed"), events);
    Assert.Contains(("resolve", "completed"), events);
    Assert.Contains(("reduction", "started"), events);
    Assert.Contains(("reduction", "failed"), events);
    Assert.DoesNotContain(("reduction", "completed"), events);
    Assert.DoesNotContain(events, item => item.Phase == "translation" ||
      item.Phase.StartsWith("boogie:", StringComparison.Ordinal));

    void Observe(string phase, string state) {
      events.Add((phase, state));
      if (phase == "reduction" && state == "started") {
        while (System.Diagnostics.Stopwatch.GetTimestamp() < deadline) { Thread.Sleep(1); }
      }
    }
  }

  // A native result arriving after the wall-clock limit cannot become a verdict through a delayed timer callback.
  [Fact]
  public async Task NativeCompletionAfterDeadlineDoesNotReturnVerdict() {
    var deadline = ContractQueryDeadline.AfterMilliseconds(3000);
    var sawSolver = false;
    await Assert.ThrowsAnyAsync<OperationCanceledException>(() => ContractSolver.CheckAsync(Source,
      ContractQueryKind.ClosedClause, Options(), CancellationToken.None, phaseObserver: (phase, state) => {
        if (phase.StartsWith("boogie:", StringComparison.Ordinal) && state == "completed") {
          sawSolver = true;
          while (System.Diagnostics.Stopwatch.GetTimestamp() < deadline) { Thread.Sleep(5); }
        }
      }, deadlineTimestamp: deadline));
    Assert.True(sawSolver);
  }

  private sealed record PhaseEvent(string Phase, string State, double ElapsedMilliseconds);
}
