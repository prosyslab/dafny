using System.Collections.Generic;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractRuntimeStatus { ViolationFound, NoViolationFound, DraftsRequired, GeneratorRequired, Inconclusive, Unsupported, Error }
public enum ContractRuntimeObligationKind { Postcondition, Assertion, LoopInvariantEntry, LoopInvariantMaintenance, CallPrecondition, EntryPrecondition, CalleePostcondition }
public enum ContractRuntimeDecisionMethod { Runtime, ClosedSmt, Unchecked }
public enum ContractRuntimeDraftKind { Method, Function, ExternMethod }


/// <summary>Names the legacy and optional proved-input runtime wire versions.</summary>
public static class ContractRuntimeCampaignSchema {
  public const int LegacyRequestVersion = 2;
  public const int ProvedInputRequestVersion = 4;
  public const int LegacyResultVersion = 1;
  public const int ProvedInputResultVersion = 3;

  /// <summary>Selects the request schema for the proof option.</summary>
  public static int RequestVersion(bool proveGeneratorPreconditions) =>
    proveGeneratorPreconditions ? ProvedInputRequestVersion : LegacyRequestVersion;

  /// <summary>Selects the result schema for the proof option.</summary>
  public static int ResultVersion(bool proveGeneratorPreconditions) =>
    proveGeneratorPreconditions ? ProvedInputResultVersion : LegacyResultVersion;
}

/// <summary>Classifies the optional proof attempt used by an ordinary runtime campaign.</summary>
public enum ContractRuntimeGeneratorProofStatus { NotAttempted, Verified, Failed, Unsupported, TimedOut, Cancelled }

/// <summary>Reports proof observations without granting execution authority through JSON.</summary>
public sealed record ContractRuntimeGeneratorProofResult(ContractRuntimeGeneratorProofStatus Status, string Diagnostics,
  bool EntryRequiresOmitted, int RequiredChecks, int CoveredChecks, int ElapsedMilliseconds);

public sealed record ContractRuntimeDraft(string Symbol, string Path, string Content, string Sha256);
/// <summary>Defines the immutable source set and policy for one runtime campaign.</summary>
public sealed record ContractRuntimeCampaignRequest(int SchemaVersion, IReadOnlyList<ContractSource> Sources,
  ContractEntry Entry, string Seed, IReadOnlyList<ContractDependency>? Dependencies = null,
  IReadOnlyList<ContractRuntimeDraft>? Drafts = null, ContractSource? Generator = null, int SampleCount = 64,
  int SampleTimeoutMilliseconds = 5000, int TimeoutMilliseconds = 240000,
  int ClosedQueryTimeoutMilliseconds = 10000, int MaxViolationsPerObligation = 3, int? ReplayOrdinal = null,
  IReadOnlyList<ContractDependency>? TrustedSources = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] bool ProveGeneratorPreconditions = false);
public sealed record ContractRuntimePopulation(int Generated = 0, int PreconditionRejected = 0,
  int PreconditionUnchecked = 0, int Executed = 0, int Valid = 0, int CalleeContractViolations = 0,
  int CalleeContractUnchecked = 0, int RuntimeErrors = 0, int Timeouts = 0, int ViolatingSamples = 0);
public sealed record ContractRuntimeEvaluations(int Runtime = 0, int ClosedSmt = 0, int Unchecked = 0);
public sealed record ContractRuntimeObligation(string Id, ContractRuntimeObligationKind Kind, string Path,
  int Line, int Column, string Clause, string? Callee, ContractRuntimeDecisionMethod DecisionMethod,
  string? UncheckedReason, ContractRuntimeEvaluations Evaluations, int Violations = 0);
public sealed record ContractRuntimeViolation(string ObligationId, ContractRuntimeObligationKind Kind,
  int SampleOrdinal, int? Iteration, ContractRuntimeDecisionMethod DecisionMethod,
  IReadOnlyDictionary<string, ContractValue> Inputs, IReadOnlyDictionary<string, ContractValue> Values);
public sealed record ContractRuntimeCalleeViolation(string ObligationId, string Callee, bool Draft,
  int SampleOrdinal, IReadOnlyDictionary<string, ContractValue> Inputs, IReadOnlyDictionary<string, ContractValue> Values);
public sealed record ContractRuntimeMissingDraft(string Symbol, ContractRuntimeDraftKind Kind, string Path,
  int Line, string Signature, string Contract);
public sealed record ContractRuntimeMissingGenerator(string Symbol, string Signature);
public sealed record ContractRuntimeDeghostExclusion(string Symbol, string Reason);
public sealed record ContractRuntimeError(int SampleOrdinal, string Message, string? Location = null);
public sealed record ContractRuntimeCampaignResult(int SchemaVersion, ContractRuntimeStatus Status, string Reason,
  string Seed, ContractRuntimePopulation Population, IReadOnlyList<ContractRuntimeObligation> Obligations,
  IReadOnlyList<ContractRuntimeViolation> Violations, IReadOnlyList<ContractRuntimeCalleeViolation> CalleeViolations,
  IReadOnlyList<ContractRuntimeMissingDraft> MissingDrafts, ContractRuntimeMissingGenerator? MissingGenerator,
  IReadOnlyList<ContractRuntimeDeghostExclusion> DeghostExclusions, IReadOnlyList<ContractRuntimeError> RuntimeErrors,
  string Diagnostics = "",
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractRuntimeGeneratorProofResult? GeneratorProof = null);
