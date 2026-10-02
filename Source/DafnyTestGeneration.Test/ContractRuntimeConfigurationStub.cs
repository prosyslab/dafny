namespace DafnyContractRuntime;

// Stands in for the per-task configuration class that ContractStubRuntime generates, so the linked library compiles here.
internal static class ContractRuntimeConfiguration {
  internal const bool RuntimeReferences = true;
  internal const bool ProfileRuntime = false;
  internal const string ObservationPath = "observations.jsonl";
  internal const string ConcreteTypes = "{}";
  internal const string HeapShapes = "[]";
  internal const string DatatypeShapes = "[]";
}
