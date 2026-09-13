using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractPathTests {
  // A branchless selected entry is validated by its exact source and invocation observation.
  [Fact]
  public void SelectedEntryNeedsExactInvocationObservation() {
    var candidate = new ContractPathCandidate("body0", [], [], [], ExpectedEntry: new("Target", 1, "sha"));
    var execution = new ContractTestResult(1, ContractTestStatus.Passed, "returned", Entry: new("file", 1, 1, "Target", "sha"),
      Reachability: new(new("file", 1, 1, "Outer", "sha"), 1, new System.Collections.Generic.Dictionary<string, ContractValue>(), null, []));
    Assert.Equal(ContractTraceReplayStatus.Matched, ContractTraceValidator.Validate(candidate, [], execution).Status);
  }

  // A result from another invocation cannot certify a selected entry even with identical branches.
  [Fact]
  public void DifferentSelectedInvocationIsMismatch() {
    var candidate = new ContractPathCandidate("body0", [], [], [], ExpectedEntry: new("Target", 1, "sha"));
    var execution = new ContractTestResult(1, ContractTestStatus.Passed, "returned", Entry: new("file", 1, 1, "Target", "sha"),
      Reachability: new(new("file", 1, 1, "Outer", "sha"), 0, new System.Collections.Generic.Dictionary<string, ContractValue>(), null, []));
    Assert.Equal(ContractTraceReplayStatus.Mismatch, ContractTraceValidator.Validate(candidate, [], execution).Status);
  }

  // A source mismatch is rejected even when the selected symbol and invocation agree.
  [Fact]
  public void DifferentSelectedSourceIsMismatch() {
    var candidate = new ContractPathCandidate("body0", [], [], [], ExpectedEntry: new("Target", 1, "sha"));
    var execution = new ContractTestResult(1, ContractTestStatus.Passed, "returned", Entry: new("file", 1, 1, "Target", "other"),
      Reachability: new(new("file", 1, 1, "Outer", "other"), 1, new System.Collections.Generic.Dictionary<string, ContractValue>(), null, []));
    Assert.Equal(ContractTraceReplayStatus.Mismatch, ContractTraceValidator.Validate(candidate, [], execution).Status);
  }

  // Runtime decisions after the selected goal do not invalidate the complete prefix.
  [Fact]
  public void RuntimeSuffixAfterGoalIsAllowed() {
    var candidate = new ContractPathCandidate("body0", [new("Entry", 12, 2, 3, true)], [], []);
    var result = ContractTraceValidator.Validate(candidate, [new("Entry", 12, 2, 3, true), new("Entry", 24, 3, 3, false)]);
    Assert.Equal(ContractTraceReplayStatus.Matched, result.Status);
  }

  // An extra earlier branch means the actual execution followed a different prefix.
  [Fact]
  public void EarlierUnexpectedGuardIsMismatch() {
    var candidate = new ContractPathCandidate("body0", [new("Entry", 12, 2, 3, true)], [], []);
    var result = ContractTraceValidator.Validate(candidate, [new("Entry", 8, 1, 3, true), new("Entry", 12, 2, 3, true)]);
    Assert.Equal(ContractTraceReplayStatus.Mismatch, result.Status);
  }

  // A disagreeing runtime branch is a path-model mismatch rather than a reached case.
  [Fact]
  public void RuntimeTraceMismatchIsExplicit() {
    var candidate = new ContractPathCandidate("body0", [new("Entry", 12, 2, 3, true)], [], []);
    var result = ContractTraceValidator.Validate(candidate, [new("Entry", 12, 2, 3, false)]);
    Assert.Equal(ContractTraceReplayStatus.Mismatch, result.Status);
  }

  // Missing original-runtime observations cannot certify a solver-generated path.
  [Fact]
  public void MissingRuntimeTraceIsUnsupported() {
    var candidate = new ContractPathCandidate("body0", [new("Entry", 12, 2, 3, true)], [], []);
    Assert.Equal(ContractTraceReplayStatus.Unsupported, ContractTraceValidator.Validate(candidate, null).Status);
  }
}
