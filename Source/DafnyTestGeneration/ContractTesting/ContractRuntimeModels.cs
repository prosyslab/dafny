using System.Collections.Generic;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractRuntimeStatus { ViolationFound, NoViolationFound, DraftsRequired, GeneratorRequired, Inconclusive, Unsupported, Error }
public enum ContractRuntimeObligationKind { Postcondition, Assertion, LoopInvariantEntry, LoopInvariantMaintenance, CallPrecondition, EntryPrecondition, CalleePostcondition }
public enum ContractRuntimeDecisionMethod { Runtime, ClosedSmt, Unchecked }
public enum ContractRuntimeDraftKind { Method, Function, ExternMethod }

public sealed record ContractRuntimeDraft(string Symbol, string Path, string Content, string Sha256);
public sealed record ContractRuntimeCampaignRequest(int SchemaVersion, IReadOnlyList<ContractSource> Sources,
  ContractEntry Entry, string Seed, IReadOnlyList<ContractDependency>? Dependencies = null,
  IReadOnlyList<ContractRuntimeDraft>? Drafts = null, ContractSource? Generator = null, int SampleCount = 64,
  int SampleTimeoutMilliseconds = 5000, int TimeoutMilliseconds = 240000,
  int ClosedQueryTimeoutMilliseconds = 10000, int MaxViolationsPerObligation = 3, int? ReplayOrdinal = null);
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
  string Diagnostics = "");
