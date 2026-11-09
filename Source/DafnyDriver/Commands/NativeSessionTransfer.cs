#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Dafny.LanguageServer.Language;

namespace Microsoft.Dafny;

/// <summary>
/// The strict wire document that moves reusable session caches between native processes. It holds
/// parser sources as URI and text and successful proof results as detached scalar snapshots, and nothing
/// that could carry a parent object graph. A receiving process either accepts the whole document or nothing.
/// </summary>
internal static class NativeSessionTransfer {
  internal const int SchemaVersion = 1;
  /// <summary>Room reserved in a request frame for the request id, session id and operation fields.</summary>
  internal const int FrameReserve = 4096;
  private static readonly Regex Hex64 = new("^[0-9a-f]{64}$", RegexOptions.CultureInvariant);

  internal sealed record TransferEntry([property: JsonRequired] string Uri, [property: JsonRequired] string Text);

  internal sealed record ResolverTransfer([property: JsonRequired] string Key, [property: JsonRequired] string OptionsIdentity,
    [property: JsonRequired] TransferEntry[] Entries);

  internal sealed record ResultTransfer([property: JsonRequired] string Key, [property: JsonRequired] int Compilations,
    [property: JsonRequired] NativeVerificationCache.Snapshot[] Entries);

  internal sealed record TransferDocument([property: JsonRequired] int SchemaVersion, [property: JsonRequired] string DaemonEpoch,
    [property: JsonRequired] string SessionId, [property: JsonRequired] string SessionEpoch, [property: JsonRequired] string Toolchain,
    [property: JsonRequired] ResolverTransfer[] Resolvers, [property: JsonRequired] ResultTransfer[] Results);

  internal sealed record ImportReceipt(int SchemaVersion, string DaemonEpoch, string SessionId, string SessionEpoch,
    int ParsedEntries, int VerificationEntries);

  /// <summary>The document or request is unusable; nothing was imported.</summary>
  internal sealed class TransferRejectedException(string message) : Exception(message);

  /// <summary>The document cannot be carried by one protocol frame; it is never truncated.</summary>
  internal sealed class TransferTooLargeException(string message) : Exception(message);

  private static readonly JsonSerializerOptions WireOptions = Create();

  private static JsonSerializerOptions Create() {
    var options = new JsonSerializerOptions {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      PropertyNameCaseInsensitive = false,
      UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
      Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping
    };
    options.Converters.Add(new JsonStringEnumConverter(JsonNamingPolicy.CamelCase, allowIntegerValues: false));
    return options;
  }

  internal static string Serialize(TransferDocument document) => JsonSerializer.Serialize(document, WireOptions);

  // The Python client writes request frames as UTF-8 JSON without ASCII escaping.
  private static readonly JsonSerializerOptions RequestFrameOptions = new() { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };

  /// <summary>Bytes the payload occupies in an import request frame: its JSON string as a client writes it, plus the reserve.</summary>
  internal static long RequestFrameBytes(string payload) =>
    Encoding.UTF8.GetByteCount(JsonSerializer.Serialize(payload, RequestFrameOptions)) + FrameReserve;

  /// <summary>Bytes the payload occupies in the export response frame, which this process escapes with its protocol options.</summary>
  internal static long ResponseFrameBytes(string payload) =>
    Encoding.UTF8.GetByteCount(JsonSerializer.Serialize(payload, AnalysisSessionCommand.JsonOptions)) + FrameReserve;

  /// <summary>
  /// The payload must fit both frames it travels in: the export response (<paramref name="responseLimit"/>, 128 MiB by
  /// default) and the import request (<paramref name="requestLimit"/>, eight MiB by default, the binding side).
  /// Nothing is ever truncated.
  /// </summary>
  internal static void CheckFrame(string payload, int requestLimit = AnalysisSessionCommand.RequestLimit,
    int responseLimit = AnalysisSessionCommand.ResponseLimit) {
    var request = RequestFrameBytes(payload);
    if (request > requestLimit) {
      throw new TransferTooLargeException($"The session transfer document needs {request} bytes in an import request frame; " +
                                          $"the request frame limit is {requestLimit}.");
    }
    var response = ResponseFrameBytes(payload);
    if (response > responseLimit) {
      throw new TransferTooLargeException($"The session transfer document needs {response} bytes in an export response frame; " +
                                          $"the response frame limit is {responseLimit}.");
    }
  }

  internal static TransferEntry ToEntry(CachingParser.ParsedSeed seed) {
    var canonical = seed.Uri.AbsoluteUri;
    // The cache key hashes the Uri's string form, so the transferred form must reproduce it exactly.
    if (!Uri.TryCreate(canonical, UriKind.Absolute, out var rebuilt) || rebuilt.ToString() != seed.Uri.ToString()) {
      throw new NotSupportedException("A retained source URI cannot be transferred without changing its identity: " + canonical);
    }
    return new TransferEntry(canonical, seed.Source);
  }

  internal static CachingParser.ParsedSeed ToSeed(TransferEntry entry) =>
    new(new Uri(entry.Uri, UriKind.Absolute), entry.Text);

  /// <summary>Parses and validates a document. Throws <see cref="TransferRejectedException"/> for any defect.</summary>
  internal static TransferDocument Parse(string? payload, string? localToolchain, int resolverCapacity, int resultCapacity) {
    if (string.IsNullOrEmpty(payload)) {
      throw new TransferRejectedException("The import request has no payload.");
    }
    if (RequestFrameBytes(payload) > AnalysisSessionCommand.RequestLimit) {
      throw new TransferRejectedException("The payload exceeds the request frame limit.");
    }
    TransferDocument? document;
    try {
      document = JsonSerializer.Deserialize<TransferDocument>(payload, WireOptions);
    } catch (Exception exception) when (exception is JsonException or NotSupportedException or ArgumentException or InvalidOperationException) {
      throw new TransferRejectedException("The payload is not a valid session transfer document: " + exception.Message);
    }
    if (document == null) {
      throw new TransferRejectedException("The payload is not a session transfer document.");
    }
    try {
      Validate(document, localToolchain, resolverCapacity, resultCapacity);
    } catch (FormatException exception) {
      throw new TransferRejectedException("The session transfer document is malformed: " + exception.Message);
    }
    return document;
  }

  private static void Validate(TransferDocument document, string? localToolchain, int resolverCapacity, int resultCapacity) {
    if (document.SchemaVersion != SchemaVersion) {
      throw new TransferRejectedException($"Unsupported schemaVersion {document.SchemaVersion}.");
    }
    if (document.Toolchain == null || localToolchain == null || !string.Equals(document.Toolchain, localToolchain, StringComparison.Ordinal)) {
      throw new TransferRejectedException("The native toolchain identity of the document differs from this process.");
    }
    foreach (var epoch in new[] { document.DaemonEpoch, document.SessionEpoch }) {
      if (epoch == null || !Guid.TryParseExact(epoch, "N", out _)) {
        throw new FormatException("An epoch is not a 32 digit identifier.");
      }
    }
    if (string.IsNullOrWhiteSpace(document.SessionId) || document.SessionId.Length > 256) {
      throw new FormatException("sessionId must be nonempty and at most 256 characters.");
    }
    if (document.Resolvers == null || document.Results == null || document.Resolvers.Length > resolverCapacity ||
        document.Results.Length > resultCapacity) {
      throw new FormatException("The resolver or result context list is missing or exceeds the retention capacity.");
    }
    var keys = new HashSet<string>(StringComparer.Ordinal);
    foreach (var resolver in document.Resolvers) {
      if (resolver == null || resolver.Key == null || !Hex64.IsMatch(resolver.Key) || !keys.Add(resolver.Key) ||
          resolver.OptionsIdentity == null || !Hex64.IsMatch(resolver.OptionsIdentity) || resolver.Entries == null) {
        throw new FormatException("A resolver context has a missing, malformed or duplicate key or identity.");
      }
      var seen = new HashSet<(string, string)>();
      foreach (var entry in resolver.Entries) {
        if (entry == null || entry.Uri == null || entry.Text == null ||
            !Uri.TryCreate(entry.Uri, UriKind.Absolute, out var uri) || uri.AbsoluteUri != entry.Uri) {
          throw new FormatException("A parser entry needs a canonical absolute uri and text.");
        }
        if (!seen.Add((entry.Uri, entry.Text))) {
          throw new FormatException("A parser entry is duplicated.");
        }
      }
    }
    keys.Clear();
    foreach (var result in document.Results) {
      if (result == null || result.Key == null || !Hex64.IsMatch(result.Key) || !keys.Add(result.Key) ||
          result.Compilations < 0 || result.Entries == null) {
        throw new FormatException("A result context has a missing, malformed or duplicate key or a negative count.");
      }
      var ids = new HashSet<string>(StringComparer.Ordinal);
      foreach (var snapshot in result.Entries) {
        if (snapshot == null) {
          throw new FormatException("A result entry is null.");
        }
        snapshot.Validate();
        if (!ids.Add(snapshot.Id)) {
          throw new FormatException("A result context repeats an implementation id.");
        }
      }
    }
  }
}
