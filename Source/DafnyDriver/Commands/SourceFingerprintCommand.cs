#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

internal sealed record SourceFingerprintSpan(int Start, int End);

internal sealed record SourceFingerprintRegion(
  string Id,
  string SourcePath,
  SourceFingerprintSpan? IncludedSpan,
  IReadOnlyList<SourceFingerprintSpan> ExcludedSpans
);

internal sealed record SourceFingerprintRequest(IReadOnlyList<SourceFingerprintRegion> Regions);

internal sealed record SourceFingerprintResult(string Id, string Sha256);

internal sealed record SourceFingerprintDocument(IReadOnlyList<SourceFingerprintResult> Fingerprints);

static class SourceFingerprintCommand {
  private sealed record SemanticToken(int Kind, string Value, int Start, int End);

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
    } catch (IOException error) {
      await options.ErrorWriter.WriteLineAsync($"could not read source-fingerprint request: {error.Message}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    } catch (JsonException error) {
      await options.ErrorWriter.WriteLineAsync($"invalid source-fingerprint request: {error.Message}");
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

    var tokensBySource = new Dictionary<string, IReadOnlyList<SemanticToken>>(StringComparer.Ordinal);
    foreach (var sourcePath in request.Regions.Select(region => Path.GetFullPath(region.SourcePath))
               .Distinct(StringComparer.Ordinal)) {
      if (Path.GetExtension(sourcePath) != ".dfy" || !File.Exists(sourcePath)) {
        await options.ErrorWriter.WriteLineAsync($"source-fingerprint input is not a Dafny file: {sourcePath}");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      IReadOnlyList<SemanticToken>? tokens;
      try {
        tokens = ScanTokens(options, sourcePath);
      } catch (IOException error) {
        await options.ErrorWriter.WriteLineAsync($"could not read source-fingerprint input: {error.Message}");
        return (int)ExitValue.PREPROCESSING_ERROR;
      } catch (UnauthorizedAccessException error) {
        await options.ErrorWriter.WriteLineAsync($"could not read source-fingerprint input: {error.Message}");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      if (tokens == null) {
        return (int)ExitValue.DAFNY_ERROR;
      }
      tokensBySource[sourcePath] = tokens;
    }

    var fingerprints = new List<SourceFingerprintResult>();
    foreach (var region in request.Regions) {
      var sourcePath = Path.GetFullPath(region.SourcePath);
      var sourceLength = new FileInfo(sourcePath).Length;
      var excludedSpans = region.ExcludedSpans ?? [];
      if (!ValidSpan(region.IncludedSpan, sourceLength) ||
          excludedSpans.Any(span => !ValidSpan(span, sourceLength))) {
        await options.ErrorWriter.WriteLineAsync($"source-fingerprint region has an invalid byte span: {region.Id}");
        return (int)ExitValue.PREPROCESSING_ERROR;
      }

      var selected = new List<SemanticToken>();
      foreach (var token in tokensBySource[sourcePath]) {
        if (region.IncludedSpan != null && Overlaps(token, region.IncludedSpan) &&
            !Contains(region.IncludedSpan, token)) {
          await options.ErrorWriter.WriteLineAsync($"source-fingerprint span splits a token: {region.Id}");
          return (int)ExitValue.PREPROCESSING_ERROR;
        }
        if (excludedSpans.Any(span => Overlaps(token, span) && !Contains(span, token))) {
          await options.ErrorWriter.WriteLineAsync($"source-fingerprint exclusion splits a token: {region.Id}");
          return (int)ExitValue.PREPROCESSING_ERROR;
        }
        if ((region.IncludedSpan == null || Contains(region.IncludedSpan, token)) &&
            !excludedSpans.Any(span => Contains(span, token))) {
          selected.Add(token);
        }
      }
      fingerprints.Add(new SourceFingerprintResult(region.Id, Fingerprint(selected)));
    }

    var json = JsonSerializer.Serialize(
      new SourceFingerprintDocument(fingerprints),
      new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase });
    await options.OutputWriter.Code(json + "\n");
    return (int)ExitValue.SUCCESS;
  }

  private static IReadOnlyList<SemanticToken>? ScanTokens(DafnyOptions options, string sourcePath) {
    var uri = new Uri(sourcePath);
    var reporter = new BatchErrorReporter(options);
    var errors = new Errors(reporter);
    var firstToken = new Token { Uri = uri };
    var bytes = File.ReadAllBytes(sourcePath);
    using var stream = new MemoryStream(bytes, writable: false);
    var scanner = new Scanner(stream, errors, uri, firstToken: firstToken);
    var result = new List<SemanticToken>();
    for (var token = scanner.Scan(); token.kind != Parser._EOF; token = scanner.Scan()) {
      result.Add(new SemanticToken(
        token.kind,
        token.val,
        token.pos,
        token.pos + Encoding.UTF8.GetByteCount(token.val)));
    }
    return errors.ErrorCount == 0 ? result : null;
  }

  private static bool ValidSpan(SourceFingerprintSpan? span, long sourceLength) {
    return span == null || 0 <= span.Start && span.Start <= span.End && span.End <= sourceLength;
  }

  private static bool Contains(SourceFingerprintSpan span, SemanticToken token) {
    return span.Start <= token.Start && token.End <= span.End;
  }

  private static bool Overlaps(SemanticToken token, SourceFingerprintSpan span) {
    return token.Start < span.End && span.Start < token.End;
  }

  private static string Fingerprint(IReadOnlyList<SemanticToken> tokens) {
    using var stream = new MemoryStream();
    using (var writer = new BinaryWriter(stream, Encoding.UTF8, leaveOpen: true)) {
      foreach (var token in tokens) {
        var value = Encoding.UTF8.GetBytes(token.Value);
        writer.Write(token.Kind);
        writer.Write(value.Length);
        writer.Write(value);
      }
    }
    return Convert.ToHexString(SHA256.HashData(stream.GetBuffer().AsSpan(0, (int)stream.Length)))
      .ToLowerInvariant();
  }
}
