#nullable enable

using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Xunit;

namespace DafnyTestGeneration.Test;

// Pure accounting and the bounded in-memory parser fixture: no engine, native task, fingerprint provider or solver runs.
public sealed class ContractGeneratorVerificationTests {
  private const string Generator = "M.Generate (correctness)";
  private const string Bridge = "M.Admission (correctness)";
  private const string Helper = "M.Helper (correctness)";
  private static readonly HashSet<string> Required = [Generator, Bridge, Helper, "M.Generate (well-formedness)"];
  private static readonly ContractGeneratorVerificationPart[] Parts = [new(Generator, 0), new(Bridge, 1), new(Helper, 2), new(Helper, 3)];

  private static Dictionary<ContractGeneratorVerificationPart, SolverOutcome> Successes() =>
    Parts.ToDictionary(part => part, _ => SolverOutcome.Valid);

  // Full ordinary results cover both roots, every helper part and the natively assertion-free well-formedness role.
  [Fact]
  public void CompleteEnumerationAndResultsCoverTheProof() {
    var coverage = ContractGeneratorVerification.Account(Required, Parts, Successes(), Generator, Bridge);
    Assert.True(coverage.Complete);
    Assert.Contains("M.Generate (well-formedness)", coverage.CoveredChecks);
    Assert.DoesNotContain("M.Generate (well-formedness)", coverage.VerifiedImplementationChecks);
  }

  // A wrong generator ensures cannot be accepted merely because the implication lemma succeeds.
  [Fact]
  public void GeneratorCorrectnessFailureRejectsEvidence() {
    var results = Successes();
    results[Parts[0]] = SolverOutcome.Invalid;
    Assert.False(ContractGeneratorVerification.Account(Required, Parts, results, Generator, Bridge).Complete);
  }

  // A valid generator cannot compensate for an insufficient postcondition in the implication lemma.
  [Fact]
  public void BridgeCorrectnessFailureRejectsEvidence() {
    var results = Successes();
    results[Parts[1]] = SolverOutcome.Invalid;
    Assert.False(ContractGeneratorVerification.Account(Required, Parts, results, Generator, Bridge).Complete);
  }

  // Missing one of several helper parts is incomplete evidence, never an assertion-free helper.
  [Fact]
  public void MissingHelperPartRejectsEvidence() {
    var results = Successes();
    results.Remove(Parts[3]);
    var coverage = ContractGeneratorVerification.Account(Required, Parts, results, Generator, Bridge);
    Assert.False(coverage.Complete);
    Assert.DoesNotContain(Helper, coverage.CoveredChecks);
  }

  // Timeout in a required helper prevents omission even if both proof roots completed successfully.
  [Fact]
  public void TimedOutHelperRejectsEvidence() {
    var results = Successes();
    results[Parts[2]] = SolverOutcome.TimeOut;
    Assert.False(ContractGeneratorVerification.Account(Required, Parts, results, Generator, Bridge).Complete);
  }

  // An interrupted task enumeration cannot establish assertion-free roles or any successful proof.
  [Fact]
  public void IncompleteEnumerationRejectsEvidence() {
    var coverage = ContractGeneratorVerification.Account(Required, Parts, Successes(), Generator, Bridge, false);
    Assert.False(coverage.Complete);
    Assert.Empty(coverage.CoveredChecks);
  }

  // No-task roots must retain runtime checks despite otherwise complete native enumeration.
  [Fact]
  public void EmptyRootTasksRejectEvidence() {
    Assert.False(ContractGeneratorVerification.Account(Required, [], new Dictionary<ContractGeneratorVerificationPart, SolverOutcome>(),
      Generator, Bridge).Complete);
  }

  // Unknown result identities cannot replace any enumerated required part.
  [Fact]
  public void UnexpectedPartRejectsEvidence() {
    var results = Successes();
    results.Add(new("M.Other (correctness)", 4), SolverOutcome.Valid);
    Assert.False(ContractGeneratorVerification.Account(Required, Parts, results, Generator, Bridge).Complete);
  }

  // An enumerated required helper cannot disappear through an unknown origin and become assertion-free.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task RequiredHelperWithUnboundOriginRejectsEnumeration(bool nullOrigin) {
    var fixture = await ContractGeneratorProofTests.Prepare(ContractGeneratorProofTests.Source.Replace(
      "{ x := 2; }", "{ x := Helper(); }\n method Helper() returns (x: int) { x := 2; }"));
    var helper = ContractGeneratorProofTests.Method(fixture.Program, "Helper");
    var check = new ContractSpecificationCheck(helper, ContractNativeProofRole.Correctness);
    var selection = ContractGeneratorVerification.SelectCheck([check], helper.EnclosingClass.EnclosingModuleDefinition,
      nullOrigin ? null : fixture.Goal.Origin, check.VerboseName, out var supported);
    Assert.Null(selection);
    Assert.False(supported);
    Assert.False(ContractGeneratorVerification.Account(Required, Parts, Successes(), Generator, Bridge, supported).Complete);
  }
}
