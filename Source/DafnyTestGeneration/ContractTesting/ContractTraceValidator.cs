using System.Collections.Generic;
using System.Linq;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractTraceValidator {
  public static ContractTraceValidationResult Validate(ContractPathCandidate candidate,
    IReadOnlyList<ContractBranchObservation>? observations, ContractTestResult? result = null) {
    if (candidate.ExpectedEntry is { } expectedEntry) {
      if (result?.Entry == null || result.Reachability == null) {
        return new(ContractTraceReplayStatus.Unsupported, "Original selected entry observations are unavailable.");
      }
      if (result.Entry.Symbol != expectedEntry.Symbol || result.Entry.Sha256 != expectedEntry.Sha256 ||
          result.Reachability.Invocation != expectedEntry.Invocation) {
        return new(ContractTraceReplayStatus.Mismatch, "entry_model_mismatch");
      }
    }
    if (candidate.ExpectedBranches.Count > 0 && observations == null ||
        candidate.ExpectedBranches.Count == 0 && candidate.ExpectedEntry == null) {
      return new(ContractTraceReplayStatus.Unsupported, "Original runtime branch observations are unavailable.");
    }
    // The model records the complete prefix through the target; later actual guards are allowed.
    for (var index = 0; index < candidate.ExpectedBranches.Count; index++) {
      var expected = candidate.ExpectedBranches[index];
      if (index >= observations!.Count || !SamePosition(expected, observations[index]) || observations[index].Value != expected.Value) {
        return new(ContractTraceReplayStatus.Mismatch, "path_model_mismatch");
      }
    }
    return candidate.TrustDependencies.Any()
      ? new(ContractTraceReplayStatus.Unsupported, "The path has explicit trust dependencies.")
      : new(ContractTraceReplayStatus.Matched, "Original runtime observations reached the selected path goal.");
  }

  private static bool SamePosition(ContractBranchObservation left, ContractBranchObservation right) =>
    left.Symbol == right.Symbol && left.Position == right.Position;
}
