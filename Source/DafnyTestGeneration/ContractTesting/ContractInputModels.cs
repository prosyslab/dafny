using System.Collections.Generic;
using System.Text.Json.Serialization;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractInputGoalKind { Precondition, ImplementationPath, SpecificationCase, Pattern }
public enum ContractScenarioProjection { Exact, Necessary, Residual }
public sealed record ContractGenerationBounds(int MaxInputs = 20, int MaxSequenceLength = 3,
  int MaxDatatypeDepth = 2, int MaxHeapObjects = 2, int MaxCallDepth = 3,
  int MaxLoopIterations = 3, int MaxGoals = 64);
public sealed record ContractGenerationRequest(int SchemaVersion, IReadOnlyList<ContractSource> Sources,
  ContractEntry Entry, ContractGenerationBounds? Bounds = null,
  IReadOnlyList<ContractDependency>? Dependencies = null, int TimeoutMilliseconds = 30000,
  IReadOnlyDictionary<string, ContractValue>? CandidateInputs = null, string? RequiredGoalId = null,
  IReadOnlyList<ContractHeapObject>? CandidateHeap = null,
  IReadOnlyList<ContractInputGoalKind>? GoalKinds = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)]
  ContractGenerationStrategy GenerationStrategy = ContractGenerationStrategy.SolverGoals,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  ContractPatternCampaign? PatternCampaign = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  ContractCampaignFeedback? CampaignFeedback = null);
public sealed record ContractGeneratedInput(ContractTestRequest Request, string GoalId,
  ContractInputGoalKind GoalKind, IReadOnlyList<ContractQueryResult> Queries, ContractPathCandidate? Path = null,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
  ContractPatternProvenance? PatternProvenance = null);
public sealed record ContractInputGoalResult(string Id, ContractInputGoalKind Kind,
  ContractQueryOutcome Outcome, string Reason, ContractSourceLocation? Location = null);
public sealed record ContractGenerationCounts(int GoalsDiscovered, int GoalsAttempted, int InputsGenerated,
  int DuplicateInputs, int BoundedUnsat, int Unknown, int Unsupported,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] int PatternSamples = 0,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] int PatternRejected = 0,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] int PatternPreconditionFalse = 0,
  [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)] int PatternPreconditionUnknown = 0);
public sealed record ContractGenerationResult(int SchemaVersion, ContractTestStatus Status, string Reason,
  IReadOnlyList<ContractGeneratedInput> Inputs, IReadOnlyList<ContractInputGoalResult> Goals,
  IReadOnlyList<ContractBodyFrontier> Frontier, ContractGenerationCounts Counts) {
  public static ContractGenerationResult Failure(ContractTestStatus status, string reason) =>
    new(ContractJson.SchemaVersion, status, reason, [], [], [], new(0, 0, 0, 0, 0, 0, 0));
}
public sealed record ContractScenario(string Id, Expression OriginalExpression, string? InputConstraint,
  ContractScenarioProjection Projection, string Reason);
