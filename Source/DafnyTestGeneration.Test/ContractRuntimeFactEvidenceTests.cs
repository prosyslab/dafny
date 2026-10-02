using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Text.Json;
using System.Threading;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeFactEvidenceTests {
  private static ContractNativeFactIdentity Identity(string query = "assert P;", string source = "predicate P() { true }") =>
    new(query, [new("M.dfy", "file:///workspace/M.dfy", source)], "M.dfy", "file:///workspace/M.dfy", "M.Query");

  // A timeout, error, unknown or unproved target leaves the exact fact available for a later successful proof attempt.
  [Theory]
  [InlineData(ContractQueryOutcome.Timeout)]
  [InlineData(ContractQueryOutcome.Error)]
  [InlineData(ContractQueryOutcome.Unknown)]
  [InlineData(ContractQueryOutcome.Sat)]
  public void UnsuccessfulClauseAttemptDoesNotPreventRetry(ContractQueryOutcome outcome) {
    var cache = new ContractNativeFactCache<string>();
    var identity = Identity();
    Assert.False(cache.Record(identity, ContractQueryKind.ObservedPostcondition, outcome, "failed", CancellationToken.None, null));
    Assert.False(cache.TryReuse(identity, ContractQueryKind.ObservedPostcondition, CancellationToken.None, null, out _));
    Assert.True(cache.Record(identity, ContractQueryKind.ObservedPostcondition, ContractQueryOutcome.Unsat, "proved", CancellationToken.None, null));
    Assert.True(cache.TryReuse(identity, ContractQueryKind.ObservedPostcondition, CancellationToken.None, null, out var proof));
    Assert.Equal("proved", proof);
  }

  // An inconsistent premise is not a reusable state-admission fact, while a checked satisfiable premise is.
  [Fact]
  public void PremiseFactsRequireSatisfiability() {
    var cache = new ContractNativeFactCache<string>();
    Assert.False(cache.Record(Identity(), ContractQueryKind.PremiseConsistency, ContractQueryOutcome.Unsat, "inconsistent", CancellationToken.None, null));
    Assert.False(cache.TryReuse(Identity(), ContractQueryKind.PremiseConsistency, CancellationToken.None, null, out _));
    Assert.True(cache.Record(Identity(), ContractQueryKind.PremiseConsistency, ContractQueryOutcome.Sat, "consistent", CancellationToken.None, null));
    Assert.True(cache.TryReuse(Identity(), ContractQueryKind.PremiseConsistency, CancellationToken.None, null, out var proof));
    Assert.Equal("consistent", proof);
  }

  // Role, clause polarity, source bytes and query context all distinguish otherwise equal reusable evidence.
  [Theory]
  [InlineData("kind")]
  [InlineData("negative")]
  [InlineData("source")]
  [InlineData("name")]
  [InlineData("path")]
  public void ExactFactIdentityRejectsChangedContext(string change) {
    var cache = new ContractNativeFactCache<string>();
    var original = Identity();
    Assert.True(cache.Record(original, ContractQueryKind.ObservedPostcondition, ContractQueryOutcome.Unsat, "original", CancellationToken.None, null));
    var changed = change switch {
      "negative" => Identity("assert !P;"),
      "source" => Identity(source: "predicate P() { false }"),
      "name" => original with { QueryName = "Other.Query" },
      "path" => original with { CanonicalSourcePath = "file:///workspace/other/M.dfy" },
      _ => original
    };
    var kind = change == "kind" ? ContractQueryKind.PremiseConsistency : ContractQueryKind.ObservedPostcondition;
    Assert.False(cache.TryReuse(changed, kind, CancellationToken.None, null, out _));
    Assert.True(cache.TryReuse(original, ContractQueryKind.ObservedPostcondition, CancellationToken.None, null, out _));
  }

  // Cancellation and expired wall-clock deadlines prevent returning a fact that was successfully proved earlier.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public void SuccessfulCacheHitHonorsCurrentCancellation(bool deadline) {
    var cache = new ContractNativeFactCache<string>();
    Assert.True(cache.Record(Identity(), ContractQueryKind.ObservedPostcondition, ContractQueryOutcome.Unsat, "proved", CancellationToken.None, null));
    using var cancellation = new CancellationTokenSource();
    if (!deadline) { cancellation.Cancel(); }
    Assert.Throws<OperationCanceledException>(() => cache.TryReuse(Identity(), ContractQueryKind.ObservedPostcondition,
      cancellation.Token, deadline ? ContractQueryDeadline.AfterMilliseconds(-1) : null, out _));
    Assert.True(cache.TryReuse(Identity(), ContractQueryKind.ObservedPostcondition, CancellationToken.None, null, out _));
  }

  // A completed nested invocation selects its own entry and return while its caller remains open.
  [Fact]
  public void NestedCaptureUsesExactInvocationPrefix() {
    var records = new[] { Capture("call_entry", 1), Capture("call_entry", 2), Capture("call_return", 2) };
    var result = ContractRuntimeHeapChecking.MatchCallCaptures(records, "M.Step", 2);
    Assert.NotNull(result);
    Assert.Equal(2, result.Value.Entry.GetProperty("invocation").GetInt32());
    Assert.Equal(2, result.Value.Return.GetProperty("invocation").GetInt32());
    Assert.Null(ContractRuntimeHeapChecking.MatchCallCaptures(records, "M.Step", 1));
  }

  // Missing, malformed, repeated and crossed capture boundaries cannot supply old/current state for a checkpoint.
  [Theory]
  [InlineData("missing_return")]
  [InlineData("missing_entry")]
  [InlineData("duplicate_entry")]
  [InlineData("duplicate_return")]
  [InlineData("wrong_scope")]
  [InlineData("wrong_invocation")]
  [InlineData("crossed_nested")]
  [InlineData("null_heap")]
  [InlineData("missing_inputs")]
  [InlineData("string_invocation")]
  [InlineData("overflow_invocation")]
  public void MalformedCallCaptureStaysUnavailable(string scenario) {
    var entry = Capture("call_entry", 1);
    var returned = Capture("call_return", 1);
    var records = scenario switch {
      "missing_return" => new[] { entry },
      "missing_entry" => new[] { returned },
      "duplicate_entry" => new[] { entry, entry, returned },
      "duplicate_return" => new[] { entry, returned, returned },
      "wrong_scope" => new[] { entry, Capture("call_return", 1, "M.Other") },
      "wrong_invocation" => new[] { entry, Capture("call_return", 2) },
      "crossed_nested" => new[] { entry, Capture("call_entry", 2), returned, Capture("call_return", 2) },
      "null_heap" => new[] { Parse(entry.GetRawText().Replace("\"heap\":[]", "\"heap\":null")), returned },
      "missing_inputs" => new[] { Parse(entry.GetRawText().Replace("\"inputs\":{}", "\"other\":{}")), returned },
      "string_invocation" => new[] { Parse(entry.GetRawText().Replace("\"invocation\":1", "\"invocation\":\"1\"")), returned },
      "overflow_invocation" => new[] { Parse(entry.GetRawText().Replace("\"invocation\":1", "\"invocation\":999999999999")), returned },
      _ => throw new ArgumentOutOfRangeException(nameof(scenario))
    };
    Assert.Null(ContractRuntimeHeapChecking.MatchCallCaptures(records, "M.Step", 1));
  }

  // A later return cannot retroactively close an invocation at an earlier checkpoint prefix.
  [Fact]
  public void LaterReturnCannotSupplyEarlierCheckpoint() {
    var records = new[] { Capture("call_entry", 1), Parse("{\"kind\":\"checkpoint\",\"call_invocation\":1}"), Capture("call_return", 1) };
    Assert.Null(ContractRuntimeHeapChecking.MatchCallCaptures(records.Take(2).ToList(), "M.Step", 1));
    Assert.NotNull(ContractRuntimeHeapChecking.MatchCallCaptures(records, "M.Step", 1));
  }

  // Caller cancellation during a real cache hit propagates before evidence can be consumed or another query charged.
  [Fact]
  public void CampaignMemoHitRejectsCancellationDuringLookup() {
    using var cancellation = new CancellationTokenSource();
    var cache = new AfterLookupDictionary<bool>(new Dictionary<string, bool> { ["proved"] = true }, cancellation.Cancel);
    var nativeQueries = 0;
    var exception = Assert.Throws<OperationCanceledException>(() => {
      if (!ContractQueryDeadline.TryReadCached(cache, "proved",
            () => ContractQueryDeadline.Check(null, cancellation.Token), out _)) { nativeQueries++; }
    });
    Assert.Equal(cancellation.Token, exception.CancellationToken);
    Assert.Equal(1, cache.Lookups);
    Assert.Equal(0, nativeQueries);
  }

  // A hit that finishes after the monotonic deadline cannot publish its earlier proof as a current result.
  [Fact]
  public void CampaignMemoHitRejectsDeadlineDuringLookup() {
    long? deadline = null;
    void RequireCurrentBoundary() {
      if (deadline == null) {
        deadline = ContractQueryDeadline.AfterMilliseconds(1);
        return;
      }
      ContractQueryDeadline.Check(deadline, CancellationToken.None);
    }
    var cache = new AfterLookupDictionary<bool>(new Dictionary<string, bool> { ["proved"] = true },
      () => SpinWait.SpinUntil(() => Stopwatch.GetTimestamp() >= deadline!.Value));
    var nativeQueries = 0;
    Assert.Throws<OperationCanceledException>(() => {
      if (!ContractQueryDeadline.TryReadCached(cache, "proved", RequireCurrentBoundary, out _)) { nativeQueries++; }
    });
    Assert.Equal(1, cache.Lookups);
    Assert.Equal(0, nativeQueries);
  }

  // A boundary already closed prevents even reading the successful cached value.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public void CampaignMemoRejectsClosedBoundaryBeforeLookup(bool deadline) {
    using var cancellation = new CancellationTokenSource();
    if (!deadline) { cancellation.Cancel(); }
    var cache = new AfterLookupDictionary<bool>(new Dictionary<string, bool> { ["proved"] = true }, () => { });
    var expired = deadline ? ContractQueryDeadline.AfterMilliseconds(-1) : (long?)null;
    Assert.Throws<OperationCanceledException>(() => ContractQueryDeadline.TryReadCached(cache, "proved",
      () => ContractQueryDeadline.Check(expired, cancellation.Token), out _));
    Assert.Equal(0, cache.Lookups);
  }

  // A live cache read retains both successful-hit and ordinary-miss behavior without changing admission evidence.
  [Theory]
  [InlineData("proved", true)]
  [InlineData("missing", false)]
  public void CampaignMemoKeepsLiveLookupBehavior(string key, bool hit) {
    var boundaries = 0;
    var cache = new Dictionary<string, bool> { ["proved"] = true };
    Assert.Equal(hit, ContractQueryDeadline.TryReadCached(cache, key, () => boundaries++, out var passed));
    Assert.Equal(hit, passed);
    Assert.Equal(2, boundaries);
  }

  private sealed class AfterLookupDictionary<T>(IReadOnlyDictionary<string, T> values, Action afterLookup)
    : IReadOnlyDictionary<string, T> {
    public int Lookups { get; private set; }
    public bool TryGetValue(string key, [MaybeNullWhen(false)] out T value) {
      var found = values.TryGetValue(key, out value);
      Lookups++;
      afterLookup();
      return found;
    }
    public T this[string key] => values[key];
    public IEnumerable<string> Keys => values.Keys;
    public IEnumerable<T> Values => values.Values;
    public int Count => values.Count;
    public bool ContainsKey(string key) => values.ContainsKey(key);
    public IEnumerator<KeyValuePair<string, T>> GetEnumerator() => values.GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
  }

  private static JsonElement Capture(string phase, int invocation, string scope = "M.Step") => Parse(
    "{\"kind\":\"heap_capture\",\"phase\":\"" + phase + "\",\"scope\":\"" + scope + "\",\"invocation\":" + invocation +
    ",\"heap\":[],\"" + (phase == "call_entry" ? "inputs" : "outputs") + "\":{}}");

  private static JsonElement Parse(string text) {
    using var document = JsonDocument.Parse(text);
    return document.RootElement.Clone();
  }
}
