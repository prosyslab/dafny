using System.Collections.Generic;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractTraceReplayStatus { Unvalidated, Matched, Mismatch, Unsupported }
public sealed record ContractBranchObservation(string Symbol, int Position, int Line, int Column, bool Value);
public sealed record ContractExpectedEntry(string Symbol, int Invocation, string Sha256);
public sealed record ContractPathCandidate(string GoalId, IReadOnlyList<ContractBranchObservation> ExpectedBranches,
  IReadOnlyList<string> AbstractCalls, IReadOnlyList<string> TrustDependencies,
  ContractTraceReplayStatus ReplayStatus = ContractTraceReplayStatus.Unvalidated, ContractExpectedEntry? ExpectedEntry = null);
public sealed record ContractTraceValidationResult(ContractTraceReplayStatus Status, string Reason);
