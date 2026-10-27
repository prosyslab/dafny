namespace DafnyPbtRuntime {
  /// <summary>Enumerates one bounded Cartesian model domain without mutating modeled state.</summary>
  public static class ContractModels {
    public const int MaximumCandidates = 4096;

    public sealed class SearchResult {
      internal SearchResult(bool found, Dafny.ISequence<System.Numerics.BigInteger> values,
          System.Numerics.BigInteger domainCardinality) {
        Found = found;
        Values = values;
        DomainCardinality = domainCardinality;
      }
      public bool Found { get; }
      public Dafny.ISequence<System.Numerics.BigInteger> Values { get; }
      public System.Numerics.BigInteger DomainCardinality { get; }
    }

    /// <summary>Returns the complete mixed bool/int domain size, rejecting invalid or oversized bounds.</summary>
    public static System.Numerics.BigInteger DomainCardinality(System.Collections.Generic.IEnumerable<bool> kinds,
        System.Numerics.BigInteger lower, System.Numerics.BigInteger upper) =>
      DomainCardinality(kinds, lower, upper, MaximumCandidates);

    public static System.Numerics.BigInteger DomainCardinality(System.Collections.Generic.IEnumerable<bool> kinds,
        System.Numerics.BigInteger lower, System.Numerics.BigInteger upper, System.Numerics.BigInteger cap) {
      if (kinds == null) { throw new System.ArgumentNullException(nameof(kinds)); }
      if (lower > upper) { throw new System.ArgumentOutOfRangeException(nameof(lower), "The integer lower bound must not exceed the upper bound."); }
      if (cap < System.Numerics.BigInteger.One || cap > MaximumCandidates) {
        throw new System.ArgumentOutOfRangeException(nameof(cap), $"The candidate cap must be between 1 and {MaximumCandidates}.");
      }
      var integerWidth = upper - lower + System.Numerics.BigInteger.One;
      var cardinality = System.Numerics.BigInteger.One;
      foreach (var isBoolean in kinds) {
        var factor = isBoolean ? new System.Numerics.BigInteger(2) : integerWidth;
        // Divide before multiplying so the configured cap guards every Cartesian product step.
        if (cardinality > cap / factor) {
          throw new System.ArgumentOutOfRangeException(nameof(cap), "The complete model domain exceeds the candidate cap.");
        }
        cardinality *= factor;
      }
      return cardinality;
    }

    /// <summary>Searches every candidate once, beginning at an explicit reproducible domain index.</summary>
    public static SearchResult Find(System.Collections.Generic.IEnumerable<bool> kinds,
        System.Numerics.BigInteger lower, System.Numerics.BigInteger upper, System.Numerics.BigInteger cap,
        System.Numerics.BigInteger startIndex,
        System.Func<Dafny.ISequence<System.Numerics.BigInteger>, bool> predicate) {
      if (kinds == null) { throw new System.ArgumentNullException(nameof(kinds)); }
      if (predicate == null) { throw new System.ArgumentNullException(nameof(predicate)); }
      var shape = System.Linq.Enumerable.ToArray(kinds);
      var cardinality = DomainCardinality(shape, lower, upper, cap);
      if (startIndex < System.Numerics.BigInteger.Zero || startIndex >= cardinality) {
        throw new System.ArgumentOutOfRangeException(nameof(startIndex));
      }
      for (var offset = System.Numerics.BigInteger.Zero; offset < cardinality; offset++) {
        var ordinal = (startIndex + offset) % cardinality;
        var candidate = Decode(shape, lower, upper, ordinal);
        var snapshot = Dafny.Sequence<System.Numerics.BigInteger>.FromArray(candidate);
        if (predicate(snapshot)) {
          return new SearchResult(true, snapshot, cardinality);
        }
      }
      return new SearchResult(false, Dafny.Sequence<System.Numerics.BigInteger>.Empty, cardinality);
    }

    private static System.Numerics.BigInteger[] Decode(bool[] kinds, System.Numerics.BigInteger lower,
        System.Numerics.BigInteger upper, System.Numerics.BigInteger ordinal) {
      var candidate = new System.Numerics.BigInteger[kinds.Length];
      var integerWidth = upper - lower + System.Numerics.BigInteger.One;
      for (var index = kinds.Length - 1; index >= 0; index--) {
        var width = kinds[index] ? new System.Numerics.BigInteger(2) : integerWidth;
        var digit = ordinal % width;
        ordinal /= width;
        candidate[index] = kinds[index] ? digit : lower + digit;
      }
      return candidate;
    }
  }

  public static partial class Checks {
    private static readonly object ModelRandomLock = new();
    private static DafnyPbtRandom.Source modelRandom;

    public static void SetModelRandom(DafnyPbtRandom.Source random) {
      if (random == null) { throw new System.ArgumentNullException(nameof(random)); }
      lock (ModelRandomLock) {
        if (modelRandom != null) { throw new System.InvalidOperationException("The model random source is already initialized."); }
        modelRandom = random;
      }
    }

    public static void FindModel(Dafny.ISequence<bool> kinds, System.Numerics.BigInteger lower,
        System.Numerics.BigInteger upper, System.Numerics.BigInteger cap,
        System.Func<Dafny.ISequence<System.Numerics.BigInteger>, bool> predicate,
        out bool found, out Dafny.ISequence<System.Numerics.BigInteger> values) {
      var cardinality = ContractModels.DomainCardinality(kinds, lower, upper, cap);
      System.Numerics.BigInteger startIndex;
      lock (ModelRandomLock) {
        if (modelRandom == null) { throw new System.InvalidOperationException("The model random source is not initialized."); }
        startIndex = modelRandom.Index(cardinality);
      }
      var result = ContractModels.Find(kinds, lower, upper, cap, startIndex, predicate);
      found = result.Found;
      values = result.Values;
    }
  }
}
