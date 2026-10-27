using System;
using System.Collections.Generic;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractRuntimeStatus { ViolationFound, NoViolationFound, DraftsRequired, GeneratorRequired, Inconclusive, Unsupported, Error }
public enum ContractRuntimeObligationKind { Postcondition, Assertion, LoopInvariantEntry, LoopInvariantMaintenance, CallPrecondition, EntryPrecondition, CalleePostcondition }
public enum ContractRuntimeDecisionMethod { Runtime, ClosedSmt, Unchecked }
public enum ContractRuntimeDraftKind { Method, Function, ExternMethod }
public enum ContractRuntimeExternExecution { Draft, Native }
public enum ContractRuntimeTerminalStage { Input, SourcePreparation, Transformation, Compilation, Sampling, Classification, Supervision }
public enum ContractRuntimeNoValidSampleReason {
  PipelineNotReached, SamplingBudgetExpired, RequiresRejected, RequiresUnchecked,
  CalleeContractRejected, CalleeContractUnchecked, RuntimeError, SampleTimeout,
  WorkerResultUnavailable, CampaignDeadline, Cancelled
}


/// <summary>Names the legacy and optional proved-input runtime wire versions.</summary>
public static class ContractRuntimeCampaignSchema {
  public const int LegacyRequestVersion = 2;
  public const int ProvedInputRequestVersion = 4;
  public const int NativeRequestVersion = 5;
  public const int ProvedNativeRequestVersion = 6;
  public const int StructuredRequestVersion = 7;
  public const int LegacyResultVersion = 1;
  public const int ProvedInputResultVersion = 3;
  public const int StructuredResultVersion = 4;

  /// <summary>Selects the request schema for the proof option.</summary>
  public static int RequestVersion(bool proveGeneratorPreconditions) =>
    proveGeneratorPreconditions ? ProvedInputRequestVersion : LegacyRequestVersion;

  /// <summary>Selects the request schema for the proof and extern execution policies.</summary>
  public static int RequestVersion(bool proveGeneratorPreconditions,
    ContractRuntimeExternExecution externExecution) => externExecution switch {
      ContractRuntimeExternExecution.Draft => RequestVersion(proveGeneratorPreconditions),
      ContractRuntimeExternExecution.Native => proveGeneratorPreconditions
        ? ProvedNativeRequestVersion : NativeRequestVersion,
      _ => throw new ArgumentOutOfRangeException(nameof(externExecution))
    };

  /// <summary>Selects the result schema for the proof option.</summary>
  public static int ResultVersion(bool proveGeneratorPreconditions) =>
    proveGeneratorPreconditions ? ProvedInputResultVersion : LegacyResultVersion;

  /// <summary>Selects the result schema required by an already decoded request.</summary>
  public static int ResultVersion(ContractRuntimeCampaignRequest request) => request.SchemaVersion switch {
    StructuredRequestVersion => StructuredResultVersion,
    LegacyRequestVersion or NativeRequestVersion => LegacyResultVersion,
    ProvedInputRequestVersion or ProvedNativeRequestVersion => ProvedInputResultVersion,
    _ => throw new ArgumentException("Unknown runtime request schema.")
  };

  /// <summary>Returns whether a decoded schema has a defined campaign result pairing.</summary>
  public static bool IsKnownRequestVersion(int schemaVersion) => schemaVersion is
    LegacyRequestVersion or ProvedInputRequestVersion or NativeRequestVersion or ProvedNativeRequestVersion or
    StructuredRequestVersion;

  /// <summary>Returns whether the paired result carries generator proof metadata.</summary>
  public static bool IncludesGeneratorProof(ContractRuntimeCampaignRequest request) =>
    request.SchemaVersion == StructuredRequestVersion
      ? request.ProveGeneratorPreconditions
      : ResultVersion(request) == ProvedInputResultVersion;

  /// <summary>Checks that a worker result has the versioned metadata promised by its request.</summary>
  public static bool IsCompatibleResult(ContractRuntimeCampaignRequest request,
    ContractRuntimeCampaignResult result) {
    if (result.SchemaVersion != ResultVersion(request) ||
        (result.GeneratorProof != null) != IncludesGeneratorProof(request)) {
      return false;
    }
    var structured = request.SchemaVersion == StructuredRequestVersion;
    return structured
      ? result.TerminalStage != null && result.NoValidSampleReasons != null &&
        (result.Population.Valid == 0) == (result.NoValidSampleReasons.Count > 0)
      : result.TerminalStage == null && result.NoValidSampleReasons == null;
  }
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
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] bool ProveGeneratorPreconditions = false,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  ContractRuntimeExternExecution? ExternExecution = null);
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
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractRuntimeGeneratorProofResult? GeneratorProof = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractRuntimeTerminalStage? TerminalStage = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  IReadOnlyList<ContractRuntimeNoValidSampleReason>? NoValidSampleReasons = null);
