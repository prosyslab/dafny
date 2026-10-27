#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using DafnyPbtRandom;
using DafnyPbtRuntime;
using Xunit;

namespace DafnyTestGeneration.Test;

public class PbtContractModelSearchTests {
  private sealed class State {
    internal BigInteger Count;
    internal bool Enabled;
  }

  private static ContractModels.SearchResult Search(Source random, bool[] kinds, BigInteger lower,
      BigInteger upper, BigInteger cap, Func<Dafny.ISequence<BigInteger>, bool> predicate) {
    var cardinality = ContractModels.DomainCardinality(kinds, lower, upper, cap);
    return ContractModels.Find(kinds, lower, upper, cap, random.Index(cardinality), predicate);
  }

  // A model can initialize receiver state and carry that concrete state through two old-state transitions.
  [Fact]
  public void InitializationAndChainedTransitionsUseCommittedOldState() {
    var random = new Source(29, 4);
    var state = new State();
    var initial = Search(random, [false, true], -2, 4, 14,
      values => values.Select(0) == 0 && values.Select(1) == 0);
    Assert.True(initial.Found);
    state.Count = initial.Values.Select(0);
    state.Enabled = initial.Values.Select(1) == 1;

    BigInteger Transition() {
      var oldCount = state.Count;
      var oldEnabled = state.Enabled;
      var result = Search(random, [false, true, false], -2, 4, 98, values =>
        values.Select(0) == oldCount + 1 &&
        (values.Select(1) == 1) == !oldEnabled &&
        values.Select(2) == oldCount + values.Select(0));
      Assert.True(result.Found);
      state.Count = result.Values.Select(0);
      state.Enabled = result.Values.Select(1) == 1;
      return result.Values.Select(2);
    }

    Assert.Equal(BigInteger.One, Transition());
    Assert.Equal(new BigInteger(3), Transition());
    Assert.Equal(new BigInteger(2), state.Count);
    Assert.False(state.Enabled);
  }

  // A contradictory joint predicate exhausts the domain and exposes no candidate that callers could commit.
  [Fact]
  public void ContradictoryPredicateReturnsNoValues() {
    var result = ContractModels.Find([false, true], -1, 1, 6, 0,
      values => values.Select(0) < 0 && values.Select(0) > 0 && values.Select(1) == 1);
    Assert.False(result.Found);
    Assert.Empty(result.Values);
    Assert.Equal(new BigInteger(6), result.DomainCardinality);
  }

  // Boolean slots enumerate exactly zero and one in the mixed integer representation.
  [Fact]
  public void BooleanDomainContainsEveryCombination() {
    var seen = new HashSet<string>();
    var result = ContractModels.Find([true, true], -100, 100, 4, 3, values => {
      seen.Add(string.Join(",", values));
      return false;
    });
    Assert.False(result.Found);
    Assert.True(seen.SetEquals(["0,0", "0,1", "1,0", "1,1"]));
  }

  // Inclusive integer bounds make both negative and positive endpoints available to predicates.
  [Fact]
  public void IntegerDomainIncludesBothEndpoints() {
    var seen = new List<BigInteger>();
    var result = ContractModels.Find([false], -2, 2, 5, 2, values => {
      seen.Add(values.Select(0));
      return false;
    });
    Assert.False(result.Found);
    Assert.Contains(new BigInteger(-2), seen);
    Assert.Contains(new BigInteger(2), seen);
    Assert.Equal(5, seen.Count);
  }

  // The documented maximum accepts a complete 4096-candidate Boolean product.
  [Fact]
  public void MaximumCandidateCapIsAccepted() {
    Assert.Equal(new BigInteger(4096), ContractModels.DomainCardinality(Enumerable.Repeat(true, 12), 0, 0, 4096));
  }

  // A Cartesian product larger than its explicit candidate cap is rejected before enumeration.
  [Fact]
  public void ProductAboveCandidateCapIsRejected() {
    Assert.Throws<ArgumentOutOfRangeException>(() =>
      ContractModels.DomainCardinality([true, true, true], 0, 0, 7));
  }

  // Arbitrarily large integer bounds are compared as BigInteger products without narrowing overflow.
  [Fact]
  public void HugeIntegerDomainIsRejectedByTheBigIntegerGuard() {
    var endpoint = BigInteger.One << 1024;
    Assert.Throws<ArgumentOutOfRangeException>(() =>
      ContractModels.DomainCardinality([false], -endpoint, endpoint, 4096));
  }

  // Candidate caps outside the runtime's fixed safety range are rejected.
  [Theory]
  [InlineData(0)]
  [InlineData(4097)]
  public void InvalidCandidateCapIsRejected(int cap) {
    Assert.Throws<ArgumentOutOfRangeException>(() =>
      ContractModels.DomainCardinality([false], 0, 0, cap));
  }

  // An inverted integer interval is rejected even when the model contains only Boolean slots.
  [Fact]
  public void InvertedIntegerBoundsAreRejected() {
    Assert.Throws<ArgumentOutOfRangeException>(() =>
      ContractModels.DomainCardinality([true], 1, 0, 2));
  }

  // Reusing the established seeded stream yields the same varied first candidate on replay.
  [Fact]
  public void SeededStartSelectionIsReproducible() {
    var first = Search(new Source(0xABCDEF, 7), [false, true], -3, 3, 14, _ => true);
    var replay = Search(new Source(0xABCDEF, 7), [false, true], -3, 3, 14, _ => true);
    Assert.True(first.Found);
    Assert.Equal(first.Values.ToArray(), replay.Values.ToArray());
  }

  // Failed joint evaluation leaves the caller's old state untouched because the engine owns no commit path.
  [Fact]
  public void ExhaustedTransitionDoesNotPartiallyCommitState() {
    var state = new State { Count = 3, Enabled = true };
    var oldCount = state.Count;
    var oldEnabled = state.Enabled;
    var result = ContractModels.Find([false, true], 0, 4, 10, 0, values =>
      values.Select(0) == oldCount + 1 && (values.Select(1) == 1) == oldEnabled && values.Select(0) < oldCount);
    Assert.False(result.Found);
    Assert.Equal(new BigInteger(3), state.Count);
    Assert.True(state.Enabled);
  }
}
