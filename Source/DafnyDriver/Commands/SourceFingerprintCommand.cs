#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

static class SourceFingerprintCommand {
  private static readonly Argument<FileInfo> RequestArgument = new("request") {
    Description = "A JSON file describing source regions to fingerprint."
  };

  public static Command Create() {
    var command = new Command(
      "source-fingerprint",
      "Compute deterministic Dafny token hashes while excluding comments and whitespace.");
    command.AddArgument(RequestArgument);
    foreach (var option in DafnyCommands.ConsoleOutputOptions) {
      command.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, Execute);
    return command;
  }

  private static async Task<int> Execute(DafnyOptions options, InvocationContext context) {
    var requestFile = context.ParseResult.GetValueForArgument(RequestArgument);
    if (requestFile == null || !requestFile.Exists) {
      await options.ErrorWriter.WriteLineAsync("source-fingerprint request file does not exist.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    SourceFingerprintRequest? request;
    try {
      request = JsonSerializer.Deserialize<SourceFingerprintRequest>(
        await File.ReadAllTextAsync(requestFile.FullName),
        new JsonSerializerOptions { PropertyNameCaseInsensitive = true });
    } catch (IOException readError) {
      await options.ErrorWriter.WriteLineAsync($"could not read source-fingerprint request: {readError.Message}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    } catch (JsonException parseError) {
      await options.ErrorWriter.WriteLineAsync($"invalid source-fingerprint request: {parseError.Message}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    if (request?.Regions == null || request.Regions.Count == 0) {
      await options.ErrorWriter.WriteLineAsync("source-fingerprint request must contain regions.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    if (request.Regions.Any(region =>
          string.IsNullOrWhiteSpace(region.Id) || string.IsNullOrWhiteSpace(region.SourcePath)) ||
        request.Regions.Select(region => region.Id).Distinct(StringComparer.Ordinal).Count() != request.Regions.Count) {
      await options.ErrorWriter.WriteLineAsync(
        "source-fingerprint region identifiers and paths must be non-empty, and identifiers must be unique.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var document = SourceFingerprint.Compute(options, request, out var computeError);
    if (computeError != null) {
      await options.ErrorWriter.WriteLineAsync(computeError);
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    if (document == null) {
      return (int)ExitValue.DAFNY_ERROR;
    }

    var json = JsonSerializer.Serialize(
      document,
      new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase });
    await options.OutputWriter.Code(json + "\n");
    return (int)ExitValue.SUCCESS;
  }
}
