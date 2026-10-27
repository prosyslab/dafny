#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.ComponentModel;
using System.Globalization;
using System.IO;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;

namespace Microsoft.Dafny;

public static class TestContractsCommand {
  private static readonly Argument<FileInfo> Request = new("request", "Versioned contract test JSON request.");
  private static readonly Option<bool> RuntimeCheck = new("--runtime-check", "Check concrete runtime obligations using a supplied generator.");
  private static readonly Option<bool> RuntimeAuthoring = new("--runtime-authoring",
    "Prepare or extract a bounded full-context runtime authoring source view.");
  private static readonly Option<bool> RuntimeFeasibility = new("--runtime-feasibility",
    "Check source-only runtime authoring support without a generator, compiler or solver.");
  private static readonly Option<bool> ScreenContract = new("--screen-contract", "Inspect or screen a proposed child contract on explicit typed inputs.");
  private static readonly Option<uint> VerificationSeed = new("--verification-seed", () => 0U,
    "Set the Boogie verification random seed (0 through 2147483647).");
  private static readonly Option<string> RuntimeWorker = new("--runtime-check-worker") { IsHidden = true };

  static TestContractsCommand() {
    OptionRegistry.RegisterOption(RuntimeCheck, OptionScope.Cli);
    OptionRegistry.RegisterOption(RuntimeAuthoring, OptionScope.Cli);
    OptionRegistry.RegisterOption(RuntimeFeasibility, OptionScope.Cli);
    OptionRegistry.RegisterOption(ScreenContract, OptionScope.Cli);
    OptionRegistry.RegisterOption(VerificationSeed, OptionScope.Cli);
    VerificationSeed.AddValidator(result => {
      if (result.GetValueOrDefault<uint>() > int.MaxValue) {
        result.ErrorMessage = "Verification seed must be at most 2147483647.";
      }
    });
    DafnyOptions.RegisterLegacyBinding(VerificationSeed, (options, seed) => options.RandomSeed = checked((int)seed));
    OptionRegistry.RegisterOption(RuntimeWorker, OptionScope.Cli);
  }

  public static Command Create() {
    var command = new Command("test-contracts", "Check original contracts on concrete runtime observations of a generator-driven campaign.");
    command.AddArgument(Request);
    command.AddOption(RuntimeCheck);
    command.AddOption(RuntimeAuthoring);
    command.AddOption(RuntimeFeasibility);
    command.AddOption(ScreenContract);
    command.AddOption(VerificationSeed);
    command.AddOption(RuntimeWorker);
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, ExecuteAsync);
    return command;
  }

  private static async Task<int> ExecuteAsync(DafnyOptions options, InvocationContext context) {
    var cancellationToken = context.GetCancellationToken();
    options.Set(CommonOptionBag.UnicodeCharacters, true);
    options.DisallowIncludes = true;
    var file = context.ParseResult.GetValueForArgument(Request);
    var runtimeResultPath = context.ParseResult.GetValueForOption(RuntimeWorker);
    var runtimeRequested = context.ParseResult.GetValueForOption(RuntimeCheck) || runtimeResultPath != null;
    var authoringRequested = context.ParseResult.GetValueForOption(RuntimeAuthoring);
    if (context.ParseResult.GetValueForOption(RuntimeFeasibility)) {
      return await ExecuteFeasibilityAsync(options, file,
        runtimeRequested || authoringRequested || context.ParseResult.GetValueForOption(ScreenContract), cancellationToken);
    }
    if (authoringRequested) {
      return await ExecuteAuthoringAsync(options, file,
        runtimeRequested || context.ParseResult.GetValueForOption(ScreenContract), cancellationToken);
    }
    if (context.ParseResult.GetValueForOption(ScreenContract)) {
      return await ExecuteScreenAsync(options, file, runtimeRequested, cancellationToken);
    }
    string runtimeSeed = "";
    var runtimeProofRequested = false;
    ContractRuntimeCampaignRequest? runtimeRequest = null;
    var runtimeRequestValidated = false;
    object result;
    try {
      if (!runtimeRequested) {
        throw new ArgumentException("Contract testing supports only --runtime-check.");
      }
      var json = await File.ReadAllTextAsync(file.FullName, cancellationToken);
      var request = JsonSerializer.Deserialize<ContractRuntimeCampaignRequest>(json, ContractJson.Options)
        ?? throw new JsonException("Null runtime campaign request.");
      runtimeRequest = request;
      runtimeSeed = request.Seed;
      runtimeProofRequested = request.ProveGeneratorPreconditions;
      ContractRuntimeCampaignRunner.ValidateRequest(request);
      runtimeRequestValidated = true;
      result = runtimeResultPath != null
        ? await ContractRuntimeCampaignRunner.RunAsync(request, options, Path.GetDirectoryName(runtimeResultPath)!, cancellationToken)
        : await SuperviseRuntimeAsync(request, options, cancellationToken);
    } catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested) {
      result = Failure(ContractTestStatus.Cancelled, "Contract testing was cancelled.");
    } catch (ArgumentException error) {
      result = Failure(ContractTestStatus.InvalidInput, error.Message);
    } catch (NotSupportedException error) {
      result = Failure(ContractTestStatus.Unsupported, error.Message);
    } catch (IOException error) {
      result = Failure(ContractTestStatus.Error, error.Message);
    } catch (JsonException error) {
      result = Failure(ContractTestStatus.InvalidInput, error.Message);
    } catch (Win32Exception error) {
      result = Failure(ContractTestStatus.Error, "Could not start a required local process: " + error.Message);
    }
    var output = JsonSerializer.Serialize(result, result.GetType(), ContractJson.Options);
    if (runtimeResultPath != null) {
      await File.WriteAllTextAsync(runtimeResultPath, output);
    } else {
      await options.OutputWriter.Code(output + "\n");
    }
    return 0;

    object Failure(ContractTestStatus status, string reason) {
      var runtimeStatus = status == ContractTestStatus.Unsupported
        ? ContractRuntimeStatus.Unsupported : ContractRuntimeStatus.Error;
      if (runtimeRequest != null &&
          ContractRuntimeCampaignSchema.IsKnownRequestVersion(runtimeRequest.SchemaVersion)) {
        var cancelled = status == ContractTestStatus.Cancelled;
        return ContractRuntimeCampaignRunner.Failure(runtimeRequest, runtimeStatus, reason,
          runtimeRequestValidated ? ContractRuntimeTerminalStage.Supervision : ContractRuntimeTerminalStage.Input,
          cancelled ? ContractRuntimeNoValidSampleReason.Cancelled : runtimeRequestValidated
            ? ContractRuntimeNoValidSampleReason.WorkerResultUnavailable
            : ContractRuntimeNoValidSampleReason.PipelineNotReached);
      }
      return ContractRuntimeCampaignRunner.Failure(runtimeStatus, reason, runtimeSeed, runtimeProofRequested);
    }
  }

  private static async Task<int> ExecuteFeasibilityAsync(DafnyOptions options, FileInfo file, bool conflictingMode,
    CancellationToken cancellationToken) {
    try {
      if (conflictingMode) { throw new ArgumentException("runtime_feasibility_requires_an_exclusive_operation"); }
      using var stream = File.OpenRead(file.FullName);
      var buffer = new byte[ContractRuntimeFeasibility.MaximumRequestBytes + 1];
      var length = 0;
      while (length < buffer.Length) {
        var read = await stream.ReadAsync(buffer.AsMemory(length), cancellationToken);
        if (read == 0) { break; }
        length += read;
      }
      if (length > ContractRuntimeFeasibility.MaximumRequestBytes) {
        throw new ArgumentException("runtime_feasibility_request_too_large");
      }
      var request = JsonSerializer.Deserialize<ContractRuntimeFeasibilityRequest>(
        buffer.AsSpan(0, length), ContractJson.Options) ?? throw new JsonException("null_runtime_feasibility_request");
      var result = await ContractRuntimeFeasibility.RunAsync(request, options, cancellationToken);
      await options.OutputWriter.Code(JsonSerializer.Serialize(result, ContractJson.Options) + "\n");
      return 0;
    } catch (OperationCanceledException) {
      return await Fail(cancellationToken.IsCancellationRequested
        ? "Runtime feasibility was cancelled." : "Runtime feasibility deadline expired.");
    } catch (Exception error) when (error is ArgumentException or IOException or JsonException or NotSupportedException) {
      return await Fail(error.Message);
    }

    async Task<int> Fail(string message) {
      // Operational failures have no support verdict and must not be cached as false.
      await options.ErrorWriter.WriteLineAsync(message.Length <= ContractRuntimeFeasibility.MaximumDiagnosticCharacters
        ? message : message[..ContractRuntimeFeasibility.MaximumDiagnosticCharacters]);
      return 1;
    }
  }

  private static async Task<int> ExecuteAuthoringAsync(DafnyOptions options, FileInfo file, bool conflictingMode,
    CancellationToken cancellationToken) {
    ContractRuntimeAuthoringRequest? request = null;
    ContractRuntimeAuthoringResult result;
    try {
      if (conflictingMode) {
        throw new ArgumentException("runtime_authoring_is_mutually_exclusive_with_runtime_check_and_screen_contract");
      }
      using var stream = File.OpenRead(file.FullName);
      var buffer = new byte[ContractRuntimeSourceAuthoring.MaximumRequestBytes + 1];
      var length = 0;
      while (length < buffer.Length) {
        var read = await stream.ReadAsync(buffer.AsMemory(length), cancellationToken);
        if (read == 0) { break; }
        length += read;
      }
      if (length > ContractRuntimeSourceAuthoring.MaximumRequestBytes) {
        throw new ArgumentException("runtime_authoring_request_too_large");
      }
      request = JsonSerializer.Deserialize<ContractRuntimeAuthoringRequest>(
        buffer.AsSpan(0, length), ContractJson.Options)
        ?? throw new JsonException("null_runtime_authoring_request");
      using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
      timeout.CancelAfter(request.TimeoutMilliseconds);
      options.DisableScopes = true;
      result = await ContractRuntimeSourceAuthoring.RunAsync(request, options, timeout.Token);
    } catch (OperationCanceledException) {
      var status = cancellationToken.IsCancellationRequested
        ? ContractRuntimeAuthoringStatus.Cancelled : ContractRuntimeAuthoringStatus.Timeout;
      result = Failure(status, status == ContractRuntimeAuthoringStatus.Cancelled
        ? "Runtime authoring was cancelled." : "Runtime authoring deadline expired.");
    } catch (ArgumentException error) {
      result = Failure(ContractRuntimeAuthoringStatus.Error, error.Message);
    } catch (NotSupportedException error) {
      result = Failure(ContractRuntimeAuthoringStatus.Unsupported, error.Message);
    } catch (IOException error) {
      result = Failure(ContractRuntimeAuthoringStatus.Error, error.Message);
    } catch (JsonException error) {
      result = Failure(ContractRuntimeAuthoringStatus.Error, error.Message);
    }
    await options.OutputWriter.Code(JsonSerializer.Serialize(result, ContractJson.Options) + "\n");
    return 0;

    ContractRuntimeAuthoringResult Failure(ContractRuntimeAuthoringStatus status, string reason) =>
      new(request?.SchemaVersion == ContractRuntimeSourceAuthoring.NativeSchemaVersion
          ? ContractRuntimeSourceAuthoring.NativeSchemaVersion : ContractRuntimeSourceAuthoring.LegacySchemaVersion,
        request?.Action ?? ContractRuntimeAuthoringAction.Prepare, status, reason);
  }

  private static async Task<int> ExecuteScreenAsync(DafnyOptions options, FileInfo file, bool conflictingMode,
    CancellationToken cancellationToken) {
    ContractScreenRequest? request = null;
    ContractScreenResult result;
    try {
      if (conflictingMode) { throw new ArgumentException("screen_contract_and_runtime_check_are_mutually_exclusive"); }
      // Read at most the protocol bound plus one sentinel byte, even if a file grows during the read.
      using var stream = File.OpenRead(file.FullName);
      var buffer = new byte[ContractScreenValidation.MaximumRequestBytes + 1];
      var length = 0;
      while (length < buffer.Length) {
        var read = await stream.ReadAsync(buffer.AsMemory(length), cancellationToken);
        if (read == 0) { break; }
        length += read;
      }
      if (length > ContractScreenValidation.MaximumRequestBytes) { throw new ArgumentException("request_too_large"); }
      request = JsonSerializer.Deserialize<ContractScreenRequest>(buffer.AsSpan(0, length), ContractJson.Options)
        ?? throw new JsonException("null_screen_request");
      result = await ContractScreenService.RunAsync(request, options, cancellationToken);
    } catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested) {
      result = Failure(ContractScreenStatus.Cancelled, "caller_cancelled");
    } catch (ArgumentException error) {
      result = Failure(ContractScreenStatus.InvalidInput, error.Message);
    } catch (JsonException error) {
      result = Failure(ContractScreenStatus.InvalidInput, error.Message);
    } catch (NotSupportedException error) {
      result = Failure(ContractScreenStatus.Unsupported, error.Message);
    } catch (IOException error) {
      result = Failure(ContractScreenStatus.Error, error.Message);
    }
    await options.OutputWriter.Code(JsonSerializer.Serialize(result, ContractJson.Options) + "\n");
    return 0;

    ContractScreenResult Failure(ContractScreenStatus status, string reason) => new(1,
      request?.Action ?? ContractScreenAction.Screen, request?.Question ?? ContractScreenQuestion.InputDomain,
      status, null, new(false, [reason], [], true), [], new(0, 0, 0, 0, 0),
      [reason[..Math.Min(reason.Length, ContractScreenValidation.MaximumDiagnosticCharacters)]], []);
  }

  private static async Task<ContractRuntimeCampaignResult> SuperviseRuntimeAsync(ContractRuntimeCampaignRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    if (request.TimeoutMilliseconds <= 0) { throw new ArgumentException("Runtime checking requires a positive deadline."); }
    var directory = Path.Combine(Path.GetTempPath(), "dafny-runtime-check-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    var requestPath = Path.Combine(directory, "request.json");
    var resultPath = Path.Combine(directory, "result.json");
    await File.WriteAllTextAsync(requestPath, JsonSerializer.Serialize(request, ContractJson.Options), cancellationToken);
    using var timeout = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    timeout.CancelAfter(request.TimeoutMilliseconds);
    var arguments = new List<string> {
      typeof(DafnyNewCli).Assembly.Location,
      "test-contracts",
      requestPath,
      "--runtime-check-worker",
      resultPath
    };
    if (options.RandomSeed is { } verificationSeed) {
      arguments.Add("--verification-seed");
      arguments.Add(verificationSeed.ToString(CultureInfo.InvariantCulture));
    }
    var process = await ContractExecutionProcess.RunAsync("dotnet", arguments, directory, timeout.Token);
    if (process.Cancelled) {
      return ContractRuntimeCampaignRunner.Failure(request, ContractRuntimeStatus.Inconclusive,
        "Runtime campaign deadline expired or was cancelled; process tree reaped.",
        ContractRuntimeTerminalStage.Supervision, cancellationToken.IsCancellationRequested
          ? ContractRuntimeNoValidSampleReason.Cancelled
          : ContractRuntimeNoValidSampleReason.CampaignDeadline);
    }
    if (process.ExitCode != 0 || !File.Exists(resultPath)) {
      return ContractRuntimeCampaignRunner.Failure(request, ContractRuntimeStatus.Error,
        "Runtime worker returned no structured result. " + process.StandardError,
        ContractRuntimeTerminalStage.Supervision, ContractRuntimeNoValidSampleReason.WorkerResultUnavailable);
    }
    var result = JsonSerializer.Deserialize<ContractRuntimeCampaignResult>(
      await File.ReadAllTextAsync(resultPath, cancellationToken), ContractJson.Options)
      ?? throw new JsonException("Runtime worker returned null.");
    if (!ContractRuntimeCampaignSchema.IsCompatibleResult(request, result)) {
      throw new JsonException("Runtime worker returned an incompatible result schema.");
    }
    return result;
  }
}
