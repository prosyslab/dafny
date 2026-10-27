#nullable enable
using System.Collections.Generic;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Explicit finite bounds; absence selects ordinary runtime execution.</summary>
public sealed record ContractRuntimeFeasibilityModelPolicy(
  [property: JsonRequired] string Goal, [property: JsonRequired] string Lower,
  [property: JsonRequired] string Upper, [property: JsonRequired] int MaxCandidates);

/// <summary>A source-only capability request: no generator, draft, compiler or solver inputs.</summary>
public sealed record ContractRuntimeFeasibilityRequest(
  [property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] IReadOnlyList<ContractSource> Sources,
  [property: JsonRequired] ContractEntry Entry,
  [property: JsonRequired] IReadOnlyList<ContractDependency> Dependencies,
  int TimeoutMilliseconds = 30000,
  IReadOnlyList<ContractDependency>? TrustedSources = null,
  ContractRuntimeExternExecution ExternExecution = ContractRuntimeExternExecution.Draft,
  ContractRuntimeFeasibilityModelPolicy? ContractModelPolicy = null);

/// <summary>Exact original source, target, request and native policy identities.</summary>
public sealed record ContractRuntimeFeasibilityBinding(string SourceSetHash, string TargetIdentity,
  string RequestIdentity, string PreparationPolicyVersion, string ProducerIdentity,
  string OptionsIdentity, ContractRuntimeExternExecution ExternExecution);

/// <summary>Possible means known support gates pass, never successful execution or proof.</summary>
public sealed record ContractRuntimeFeasibilityResult(int SchemaVersion, bool Possible,
  IReadOnlyList<string> ReasonCodes, IReadOnlyList<string> Diagnostics,
  ContractRuntimeFeasibilityBinding Binding, IReadOnlyList<string> RequiredDraftSymbols);

/// <summary>One resolved support blocker, independent of authoring and campaign statuses.</summary>
public sealed record ContractRuntimeFeasibilityBlocker(string Code, string Diagnostic);
