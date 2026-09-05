#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;

namespace Microsoft.Dafny;

public sealed record SourceFingerprintSpan(int Start, int End);

public sealed record SourceFingerprintRegion(
  string Id,
  string SourcePath,
  SourceFingerprintSpan? IncludedSpan,
  IReadOnlyList<SourceFingerprintSpan> ExcludedSpans
);

public sealed record SourceFingerprintRequest(IReadOnlyList<SourceFingerprintRegion> Regions);

public sealed record SourceFingerprintResult(string Id, string Sha256);

public sealed record SourceFingerprintDocument(IReadOnlyList<SourceFingerprintResult> Fingerprints);

/// <summary>Computes token fingerprints for source regions shared by analysis commands.</summary>
public static class SourceFingerprint {
  private sealed record SemanticToken(int Kind, string Value, int Start, int End);
  private sealed record TokenRange(int Start, int End);

  public static SourceFingerprintDocument? Compute(
    DafnyOptions options,
    SourceFingerprintRequest request,
    out string? error) {
    error = null;
    var tokensBySource = new Dictionary<string, IReadOnlyList<SemanticToken>>(StringComparer.Ordinal);
    foreach (var sourcePath in request.Regions.Select(region => Path.GetFullPath(region.SourcePath))
               .Distinct(StringComparer.Ordinal)) {
      if (Path.GetExtension(sourcePath) != ".dfy" || !File.Exists(sourcePath)) {
        error = $"source-fingerprint input is not a Dafny file: {sourcePath}";
        return null;
      }

      IReadOnlyList<SemanticToken>? tokens;
      try {
        tokens = ScanTokens(options, sourcePath);
      } catch (IOException exception) {
        error = $"could not read source-fingerprint input: {exception.Message}";
        return null;
      } catch (UnauthorizedAccessException exception) {
        error = $"could not read source-fingerprint input: {exception.Message}";
        return null;
      }
      if (tokens == null) {
        return null;
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
        error = $"source-fingerprint region has an invalid byte span: {region.Id}";
        return null;
      }

      var tokens = tokensBySource[sourcePath];
      var includedRange = region.IncludedSpan == null
        ? new TokenRange(0, tokens.Count)
        : OverlappingTokenRange(tokens, region.IncludedSpan);
      if (region.IncludedSpan != null &&
          FirstSplitTokenIndex(tokens, includedRange, region.IncludedSpan) != null) {
        error = $"source-fingerprint span splits a token: {region.Id}";
        return null;
      }

      var excludedRanges = new List<TokenRange>(excludedSpans.Count);
      foreach (var excludedSpan in excludedSpans) {
        var excludedRange = OverlappingTokenRange(tokens, excludedSpan);
        if (FirstSplitTokenIndex(tokens, excludedRange, excludedSpan) != null) {
          error = $"source-fingerprint exclusion splits a token: {region.Id}";
          return null;
        }
        excludedRanges.Add(excludedRange);
      }

      var mergedExcludedRanges = MergeRanges(excludedRanges);
      var selected = new List<SemanticToken>(includedRange.End - includedRange.Start);
      var excludedRangeIndex = 0;
      for (var tokenIndex = includedRange.Start; tokenIndex < includedRange.End; tokenIndex++) {
        while (excludedRangeIndex < mergedExcludedRanges.Count &&
               mergedExcludedRanges[excludedRangeIndex].End <= tokenIndex) {
          excludedRangeIndex++;
        }
        if (excludedRangeIndex < mergedExcludedRanges.Count &&
            mergedExcludedRanges[excludedRangeIndex].Start <= tokenIndex) {
          continue;
        }
        selected.Add(tokens[tokenIndex]);
      }
      fingerprints.Add(new SourceFingerprintResult(region.Id, Fingerprint(selected)));
    }

    return new SourceFingerprintDocument(fingerprints);
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

  private static TokenRange OverlappingTokenRange(
    IReadOnlyList<SemanticToken> tokens,
    SourceFingerprintSpan span) {
    var lower = 0;
    var upper = tokens.Count;
    while (lower < upper) {
      var middle = lower + (upper - lower) / 2;
      if (tokens[middle].End <= span.Start) {
        lower = middle + 1;
      } else {
        upper = middle;
      }
    }
    var start = lower;

    lower = start;
    upper = tokens.Count;
    while (lower < upper) {
      var middle = lower + (upper - lower) / 2;
      if (tokens[middle].Start < span.End) {
        lower = middle + 1;
      } else {
        upper = middle;
      }
    }
    return new TokenRange(start, lower);
  }

  private static int? FirstSplitTokenIndex(
    IReadOnlyList<SemanticToken> tokens,
    TokenRange range,
    SourceFingerprintSpan span) {
    for (var index = range.Start; index < range.End; index++) {
      if (!Contains(span, tokens[index])) {
        return index;
      }
    }
    return null;
  }

  private static IReadOnlyList<TokenRange> MergeRanges(IEnumerable<TokenRange> ranges) {
    var ordered = ranges
      .Where(range => range.Start < range.End)
      .OrderBy(range => range.Start)
      .ThenBy(range => range.End);
    var merged = new List<TokenRange>();
    foreach (var range in ordered) {
      if (merged.Count == 0 || merged[^1].End < range.Start) {
        merged.Add(range);
        continue;
      }
      merged[^1] = new TokenRange(merged[^1].Start, Math.Max(merged[^1].End, range.End));
    }
    return merged;
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

