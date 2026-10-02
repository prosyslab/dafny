using System;
using System.Text.Json;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Supplies the diagnostic-only random stream and append-only runtime check recorder.</summary>
public static class ContractRuntimeInstrumentation {
  /// <summary>Dafny declarations of the diagnostic random stream and runtime check recorder, loaded from the checked-in library.</summary>
  public static readonly string DafnySource = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");

  public static string RuntimeSource(string observationPath, ContractRuntimeTransformation transformation) =>
    ContractStubRuntime.RuntimeSource(observationPath + ".legacy", transformation.Prepared, runtimeReferences: true,
      transformation.CompiledGhostFields) + "\n" + ContractRuntimeLibrary.Read("PbtChecks.cs") + ContractRuntimeLibrary.Read("PbtRandom.cs");
}
