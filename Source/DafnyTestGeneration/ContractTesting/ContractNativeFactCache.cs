using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Text.Json;
using System.Threading;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Identifies every source byte and query context supporting a reusable native fact.</summary>
public sealed record ContractNativeFactIdentity(string Query, IReadOnlyList<ContractNativeFactSource> Sources,
  string SourcePath, string CanonicalSourcePath, string QueryName) {
  /// <summary>Separates query roles even when their generated source text happens to coincide.</summary>
  public string Material(ContractQueryKind kind) => kind + ":" + JsonSerializer.Serialize(this, ContractJson.Options);
}

/// <summary>Retains the exact source text and canonical location used by a native query.</summary>
public sealed record ContractNativeFactSource(string Path, string CanonicalPath, string Content);

/// <summary>Reuses successful native query evidence only while the current caller remains authorized to proceed.</summary>
public sealed class ContractNativeFactCache<TProof> {
  private readonly Dictionary<string, TProof> proofs = new();

  /// <summary>Looks up exact prior evidence after checking the current cancellation and wall-clock boundary.</summary>
  public bool TryReuse(ContractNativeFactIdentity identity, ContractQueryKind kind,
    CancellationToken cancellationToken, long? deadlineTimestamp,
    [MaybeNullWhen(false)] out TProof proof) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var material = identity.Material(kind);
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    return proofs.TryGetValue(material, out proof);
  }

  /// <summary>Publishes only satisfiable premises or proved clauses; unsuccessful attempts leave retries possible.</summary>
  public bool Record(ContractNativeFactIdentity identity, ContractQueryKind kind, ContractQueryOutcome outcome, TProof proof,
    CancellationToken cancellationToken, long? deadlineTimestamp) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var successful = kind == ContractQueryKind.PremiseConsistency
      ? outcome == ContractQueryOutcome.Sat : outcome == ContractQueryOutcome.Unsat;
    if (!successful) { return false; }
    var material = identity.Material(kind);
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    return proofs.TryAdd(material, proof);
  }
}
