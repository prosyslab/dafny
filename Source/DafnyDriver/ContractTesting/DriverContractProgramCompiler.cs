using System;
using System.IO;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;

namespace Microsoft.Dafny;

public sealed class DriverContractProgramCompiler : IContractProgramCompiler {
  public async Task<ContractCompileResult> CompileAsync(ContractCompileRequest request, CancellationToken cancellationToken) {
    Directory.CreateDirectory(request.OutputDirectory);
    var requestPath = Path.Combine(request.OutputDirectory, "compile-request.json");
    var resultPath = Path.Combine(request.OutputDirectory, "compile-result.json");
    await File.WriteAllTextAsync(requestPath, JsonSerializer.Serialize(request, ContractJson.Options), cancellationToken);
    var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      requestPath,
      "--compile-worker",
      resultPath], request.OutputDirectory, cancellationToken);
    if (process.Cancelled) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Cancelled, "Compiler worker cancelled and reaped.");
    }
    if (!File.Exists(resultPath)) {
      return new ContractCompileResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Compiler worker returned no structured result. " + process.StandardError + process.StandardOutput);
    }
    var result = JsonSerializer.Deserialize<ContractCompileResult>(await File.ReadAllTextAsync(resultPath, cancellationToken), ContractJson.Options)
      ?? throw new JsonException("Compiler worker returned null.");
    return result.Status == ContractTestStatus.Passed ? result : result with {
      Reason = result.Reason + "\n" + process.StandardOutput + process.StandardError
    };
  }
}
