using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.ComponentModel;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;

namespace Microsoft.Dafny;

public static class TestContractsCommand {
  private static readonly Argument<FileInfo> Request = new("request", "Versioned contract test JSON request.");
  private static readonly Option<string> CompileWorker = new("--compile-worker") { IsHidden = true };
  private static readonly Option<string> ExecuteWorker = new("--execute-worker") { IsHidden = true };
  private static readonly Option<bool> Generate = new("--generate", "Generate inputs from the original precondition, body paths, and specification cases.");
  private static readonly Option<string> GenerateWorker = new("--generate-worker") { IsHidden = true };
  private static readonly Option<string> GenerationCheckpoint = new("--generation-checkpoint", "Atomically publish completed generation inputs to this absolute path.");
  private static readonly Option<bool> Symbolic = new("--symbolic",
    "Verify an exact entry implementation and its reachable internal implementations without execution.");
  private static readonly Option<string> SymbolicWorker = new("--symbolic-worker") { IsHidden = true };

  static TestContractsCommand() {
    OptionRegistry.RegisterOption(CompileWorker, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExecuteWorker, OptionScope.Cli);
    OptionRegistry.RegisterOption(Generate, OptionScope.Cli);
    OptionRegistry.RegisterOption(GenerateWorker, OptionScope.Cli);
    OptionRegistry.RegisterOption(GenerationCheckpoint, OptionScope.Cli);
    OptionRegistry.RegisterOption(Symbolic, OptionScope.Cli);
    OptionRegistry.RegisterOption(SymbolicWorker, OptionScope.Cli);
  }

  public static Command Create() {
    var command = new Command("test-contracts", "Execute a diagnostic copy and check original contracts on concrete observations.");
    command.AddArgument(Request);
    command.AddOption(CompileWorker);
    command.AddOption(ExecuteWorker);
    command.AddOption(Generate);
    command.AddOption(GenerateWorker);
    command.AddOption(GenerationCheckpoint);
    command.AddOption(Symbolic);
    command.AddOption(SymbolicWorker);
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, ExecuteAsync);
    return command;
  }

  private static async Task<int> ExecuteAsync(DafnyOptions options, InvocationContext context) {
    var cancellationToken = context.GetCancellationToken();
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    options.DisallowIncludes = true;
    var file = context.ParseResult.GetValueForArgument(Request);
    var compileResultPath = context.ParseResult.GetValueForOption(CompileWorker);
    var executionResultPath = context.ParseResult.GetValueForOption(ExecuteWorker);
    var generationResultPath = context.ParseResult.GetValueForOption(GenerateWorker);
    var generationCheckpointPath = context.ParseResult.GetValueForOption(GenerationCheckpoint);
    var generationRequested = context.ParseResult.GetValueForOption(Generate) || generationResultPath != null;
    var symbolicResultPath = context.ParseResult.GetValueForOption(SymbolicWorker);
    var symbolicRequested = context.ParseResult.GetValueForOption(Symbolic) || symbolicResultPath != null;
    var resultPath = compileResultPath ?? executionResultPath ?? generationResultPath ?? symbolicResultPath;
    object result;
    try {
      if (new[] { compileResultPath != null, executionResultPath != null, generationRequested, symbolicRequested }
          .Count(selected => selected) > 1) {
        throw new ArgumentException("Compilation, execution, generation, and symbolic modes are mutually exclusive.");
      }
      if (generationCheckpointPath != null && (!generationRequested || !Path.IsPathFullyQualified(generationCheckpointPath))) {
        throw new ArgumentException("A generation checkpoint requires generation mode and an absolute path.");
      }
      var json = await File.ReadAllTextAsync(file.FullName, cancellationToken);
      if (symbolicRequested) {
        var request = JsonSerializer.Deserialize<ContractSymbolicRequest>(json, ContractJson.Options)
          ?? throw new JsonException("Null symbolic contract request.");
        result = symbolicResultPath != null
          ? await ContractSymbolicChecker.CheckAsync(request, options, cancellationToken)
          : await SuperviseSymbolicAsync(request, cancellationToken);
      } else if (generationRequested) {
        var request = JsonSerializer.Deserialize<ContractGenerationRequest>(json, ContractJson.Options)
          ?? throw new JsonException("Null input generation request.");
        result = generationResultPath != null
          ? await ContractInputGenerator.GenerateAsync(request, options, cancellationToken,
            async partial => {
              if (generationCheckpointPath != null) {
                await WriteGenerationCheckpointAsync(generationCheckpointPath, partial);
              }
              await WriteGenerationCheckpointAsync(generationResultPath + ".checkpoint", partial);
            })
          : await SuperviseGenerationAsync(request, generationCheckpointPath, cancellationToken);
      } else if (compileResultPath != null) {
        var request = JsonSerializer.Deserialize<ContractCompileRequest>(json, ContractJson.Options)
          ?? throw new JsonException("Null compile request.");
        result = await ContractCompilerWorker.CompileAsync(request, options, cancellationToken);
      } else {
        var request = JsonSerializer.Deserialize<ContractTestRequest>(json, ContractJson.Options)
          ?? throw new JsonException("Null contract test request.");
        ContractHarnessBuilder.ValidateRequest(request);
        if (executionResultPath != null) {
          var prepared = await ContractCompilerWorker.ParseAsync(request, options, cancellationToken);
          result = await new ContractTestRunner(new DriverContractProgramCompiler()).RunAsync(prepared, request,
            Path.GetDirectoryName(executionResultPath)!, cancellationToken);
        } else {
          result = await SuperviseAsync(request, cancellationToken);
        }
      }
    } catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.Cancelled, "Symbolic contract checking was cancelled.")
        : Failure(ContractTestStatus.Cancelled, "Contract testing was cancelled.");
    } catch (ArgumentException error) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.InvalidInput, error.Message)
        : Failure(ContractTestStatus.InvalidInput, error.Message);
    } catch (NotSupportedException error) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.InvalidInput, error.Message)
        : Failure(ContractTestStatus.Unsupported, error.Message);
    } catch (IOException error) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.Error, error.Message)
        : Failure(ContractTestStatus.Error, error.Message);
    } catch (JsonException error) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.InvalidInput, error.Message)
        : Failure(ContractTestStatus.InvalidInput, error.Message);
    } catch (Win32Exception error) {
      result = symbolicRequested
        ? SymbolicFailure(ContractSymbolicStatus.Error, "Could not start a required local process: " + error.Message)
        : Failure(ContractTestStatus.Error, "Could not start a required local process: " + error.Message);
    }
    var output = JsonSerializer.Serialize(result, result.GetType(), ContractJson.Options);
    if (resultPath != null) {
      await File.WriteAllTextAsync(resultPath, output);
    } else {
      await options.OutputWriter.Code(output + "\n");
    }
    return 0;

    object Failure(ContractTestStatus status, string reason) => generationRequested
      ? GenerationFailure(status, reason)
      : compileResultPath == null
        ? new ContractTestResult(ContractJson.SchemaVersion, status, reason)
        : new ContractCompileResult(ContractJson.SchemaVersion, status, reason);
  }

  private static ContractGenerationResult GenerationFailure(ContractTestStatus status, string reason) =>
    new(ContractJson.SchemaVersion, status, reason, [], [], [], new ContractGenerationCounts(0, 0, 0, 0, 0, 0, 0));

  private static ContractSymbolicResult SymbolicFailure(ContractSymbolicStatus status, string reason) =>
    new(ContractJson.SchemaVersion, status, reason, CheckedSymbols: [], SummarizedExternSymbols: [],
      TrustDependencies: [], Obligations: [], Diagnostics: [], SourceSnapshots: []);

  private static async Task WriteGenerationCheckpointAsync(string checkpointPath, ContractGenerationResult result) {
    var temporary = checkpointPath + ".tmp";
    await File.WriteAllTextAsync(temporary, JsonSerializer.Serialize(result, ContractJson.Options));
    File.Move(temporary, checkpointPath, true);
  }

  private static async Task<ContractGenerationResult> SuperviseGenerationAsync(ContractGenerationRequest request,
    string checkpointPath, CancellationToken cancellationToken) {
    if (request.SchemaVersion != ContractJson.SchemaVersion || request.TimeoutMilliseconds <= 0) {
      throw new ArgumentException("Input generation requires schema version 1 and a positive deadline.");
    }
    var directory = Path.Combine(Path.GetTempPath(), "dafny-contract-generation-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var requestPath = Path.Combine(directory, "generation-request.json");
    var resultPath = Path.Combine(directory, "generation-result.json");
    await File.WriteAllTextAsync(requestPath, JsonSerializer.Serialize(request, ContractJson.Options), cancellationToken);
    using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    timeout.CancelAfter(request.TimeoutMilliseconds);
    var arguments = new List<string> { typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      requestPath,
      "--generate-worker",
      resultPath };
    if (checkpointPath != null) {
      arguments.Add("--generation-checkpoint");
      arguments.Add(checkpointPath);
    }
    var process = await ContractExecutionProcess.RunAsync("dotnet", arguments, directory, timeout.Token);
    if (process.Cancelled) {
      var status = cancellationToken.IsCancellationRequested ? ContractTestStatus.Cancelled : ContractTestStatus.Timeout;
      var reason = cancellationToken.IsCancellationRequested
          ? "Input generation cancelled; worker and solver process tree reaped."
          : "Input generation deadline expired; worker and solver process tree reaped.";
      // The worker has been reaped. A rename-published checkpoint contains only
      // complete, rechecked inputs, even when its own deadline had not yet expired.
      var checkpoint = resultPath + ".checkpoint";
      if (File.Exists(checkpoint)) {
        var partial = JsonSerializer.Deserialize<ContractGenerationResult>(await File.ReadAllTextAsync(checkpoint),
          ContractJson.Options) ?? throw new JsonException("Input generation checkpoint returned null.");
        return partial with { Status = status, Reason = reason + " Completed input proposals were preserved." };
      }
      return GenerationFailure(status, reason);
    }
    if (process.ExitCode != 0 || !File.Exists(resultPath)) {
      return GenerationFailure(ContractTestStatus.Error,
        "Input generation worker returned no successful structured result. " + process.StandardError);
    }
    return JsonSerializer.Deserialize<ContractGenerationResult>(
        await File.ReadAllTextAsync(resultPath, cancellationToken), ContractJson.Options)
      ?? throw new JsonException("Input generation worker returned null.");
  }

  private static async Task<ContractSymbolicResult> SuperviseSymbolicAsync(ContractSymbolicRequest request,
    CancellationToken cancellationToken) {
    if (request.SchemaVersion != ContractJson.SchemaVersion || request.TimeoutMilliseconds <= 0) {
      throw new ArgumentException("Symbolic checking requires schema version 1 and a positive deadline.");
    }
    var directory = Path.Combine(Path.GetTempPath(), "dafny-contract-symbolic-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var requestPath = Path.Combine(directory, "symbolic-request.json");
    var resultPath = Path.Combine(directory, "symbolic-result.json");
    await File.WriteAllTextAsync(requestPath, JsonSerializer.Serialize(request, ContractJson.Options), cancellationToken);
    using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    timeout.CancelAfter(request.TimeoutMilliseconds);
    var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      requestPath,
      "--symbolic-worker",
      resultPath], directory, timeout.Token);
    if (process.Cancelled) {
      return SymbolicFailure(
        cancellationToken.IsCancellationRequested ? ContractSymbolicStatus.Cancelled : ContractSymbolicStatus.Timeout,
        cancellationToken.IsCancellationRequested
          ? "Symbolic checking cancelled; worker and solver process tree reaped."
          : "Symbolic checking deadline expired; worker and solver process tree reaped.");
    }
    if (process.ExitCode != 0 || !File.Exists(resultPath)) {
      return SymbolicFailure(ContractSymbolicStatus.Error,
        "Symbolic checking worker returned no structured result. " + process.StandardError);
    }
    return JsonSerializer.Deserialize<ContractSymbolicResult>(
        await File.ReadAllTextAsync(resultPath, cancellationToken), ContractJson.Options)
      ?? throw new JsonException("Symbolic checking worker returned null.");
  }

  private static async Task<ContractTestResult> SuperviseAsync(ContractTestRequest request, CancellationToken cancellationToken) {
    var directory = Path.Combine(Path.GetTempPath(), "dafny-contract-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var snapshotRequestPath = Path.Combine(directory, "test-request.json");
    await File.WriteAllTextAsync(snapshotRequestPath, JsonSerializer.Serialize(request, ContractJson.Options), cancellationToken);
    var resultPath = Path.Combine(directory, "result.json");
    using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    timeout.CancelAfter(request.TimeoutMilliseconds);
    var process = await ContractExecutionProcess.RunAsync("dotnet", [typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      snapshotRequestPath,
      "--execute-worker",
      resultPath], directory, timeout.Token);
    if (process.Cancelled) {
      return new ContractTestResult(ContractJson.SchemaVersion,
        cancellationToken.IsCancellationRequested ? ContractTestStatus.Cancelled : ContractTestStatus.Timeout,
        cancellationToken.IsCancellationRequested ? "Contract testing cancelled; worker and runtime process tree reaped." :
          "Contract test deadline expired; worker and runtime process tree reaped.",
        StandardOutput: process.StandardOutput, StandardError: process.StandardError);
    }
    if (!File.Exists(resultPath)) {
      return new ContractTestResult(ContractJson.SchemaVersion, ContractTestStatus.Error,
        "Execution worker returned no structured result.", StandardOutput: process.StandardOutput, StandardError: process.StandardError);
    }
    return JsonSerializer.Deserialize<ContractTestResult>(await File.ReadAllTextAsync(resultPath), ContractJson.Options)
      ?? throw new JsonException("Execution worker returned null.");
  }
}
