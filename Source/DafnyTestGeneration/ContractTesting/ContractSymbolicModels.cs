using System.Collections.Generic;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractSymbolicScope { EntryImplementation, ReachableImplementations }

public enum ContractSymbolicStatus {
  Verified,
  InconsistentPremise,
  ObligationFailed,
  Unknown,
  Timeout,
  Cancelled,
  InvalidInput,
  Error
}

public enum ContractSymbolicObligationKind { PremiseConsistency, Implementation }

public sealed record ContractSymbolicEntry(
  [property: JsonRequired] string Symbol,
  ContractSymbolicScope Scope = ContractSymbolicScope.ReachableImplementations);

public sealed record ContractSymbolicRequest(
  [property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] IReadOnlyList<ContractSource> Sources,
  [property: JsonRequired] ContractSymbolicEntry Entry,
  IReadOnlyList<ContractDependency>? Dependencies = null,
  int TimeoutMilliseconds = 30000);

public sealed record ContractSymbolicDependency(
  [property: JsonRequired] string Symbol,
  [property: JsonRequired] string Kind,
  [property: JsonRequired] string Reason);

public sealed record ContractSymbolicObligation(
  [property: JsonRequired] ContractSymbolicObligationKind Kind,
  [property: JsonRequired] ContractSymbolicStatus Status,
  [property: JsonRequired] string Description);

public sealed record ContractSymbolicResult(
  [property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] ContractSymbolicStatus Status,
  [property: JsonRequired] string Reason,
  ContractSourceLocation? Entry = null,
  IReadOnlyList<string>? CheckedSymbols = null,
  IReadOnlyList<string>? SummarizedExternSymbols = null,
  IReadOnlyList<ContractSymbolicDependency>? TrustDependencies = null,
  IReadOnlyList<ContractSymbolicObligation>? Obligations = null,
  IReadOnlyList<string>? Diagnostics = null,
  IReadOnlyList<ContractDependency>? SourceSnapshots = null);
