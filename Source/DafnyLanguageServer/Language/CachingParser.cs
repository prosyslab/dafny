using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Language;

public class CachingParser : ProgramParser {
  private sealed record CachedParseFile(DfyParseFileResult Result, string Source);

  private readonly PruneIfNotUsedSinceLastPruneCache<byte[], CachedParseFile> parseCache;
  private readonly TelemetryPublisherBase telemetryPublisher;

  public int CachedParseCount => parseCache.Count;

  public CachingParser(ILogger<ProgramParser> logger,
    IFileSystem fileSystem,
    TelemetryPublisherBase telemetryPublisher) : this(logger, fileSystem, telemetryPublisher, new(new HashEquality())) {
  }

  private CachingParser(ILogger<ProgramParser> logger, IFileSystem fileSystem,
    TelemetryPublisherBase telemetryPublisher,
    PruneIfNotUsedSinceLastPruneCache<byte[], CachedParseFile> parseCache) : base(logger, fileSystem) {
    this.telemetryPublisher = telemetryPublisher;
    this.parseCache = parseCache;
  }

  /// <summary>One retained parse template in its transferable form: the logical URI and the exact source text.</summary>
  public sealed record ParsedSeed(Uri Uri, string Source);

  /// <summary>
  /// Requires a drained source parser and independently owned child options. Each inherited template
  /// is parsed once from retained immutable text, without consulting either filesystem. Cloner alone
  /// cannot detach token chains, module/include options, attributes and builtins delegate captures.
  /// No mutable parse template graph is shared between parsers; ordinary cache hits still clone before use.
  /// </summary>
  public CachingParser Clone(DafnyOptions options, IFileSystem fileSystem,
    TelemetryPublisherBase telemetryPublisher, CancellationToken cancellationToken = default) {
    var cache = parseCache.Clone(key => (byte[])key.Clone(),
      entry => ParseTemplate(options, entry.Result.Uri, entry.Result.Version, entry.Source, cancellationToken),
      cancellationToken);
    return new CachingParser(logger, fileSystem, telemetryPublisher, cache);
  }

  /// <summary>Lists the retained templates as URI and text. Requires a drained parser; changes nothing.</summary>
  public IReadOnlyList<ParsedSeed> ExportSeeds(CancellationToken cancellationToken = default) =>
    parseCache.Export((_, entry) => new ParsedSeed(entry.Result.Uri, entry.Source), cancellationToken);

  /// <summary>
  /// Builds a parser whose cache holds one private template per seed, parsed from the seed text with the
  /// supplied detached options, exactly as <see cref="Clone"/> rebuilds inherited templates. Keys are
  /// derived from URI and text with the same hash a parse miss uses, so a later parse of equal text hits.
  /// </summary>
  public static CachingParser FromSeeds(ILogger<ProgramParser> logger, IFileSystem fileSystem,
    TelemetryPublisherBase telemetryPublisher, IEnumerable<ParsedSeed> seeds, DafnyOptions options,
    CancellationToken cancellationToken = default) {
    var parser = new CachingParser(logger, fileSystem, telemetryPublisher);
    foreach (var seed in seeds) {
      cancellationToken.ThrowIfCancellationRequested();
      var key = ComputeKey(seed.Uri, seed.Source);
      parser.parseCache.Seed(key, parser.ParseTemplate(options, seed.Uri, null, seed.Source, cancellationToken));
    }
    return parser;
  }

  private CachedParseFile ParseTemplate(DafnyOptions options, Uri uri, int? version, string source,
    CancellationToken cancellationToken) {
    var result = base.ParseFile(options, new FileSnapshot(new StringReader(source), version), uri, cancellationToken);
    return new CachedParseFile(result, source);
  }

  private static byte[] ComputeKey(Uri uri, string source) {
    using var hashAlgorithm = SHA256.Create();
    var (reader, hash) = ComputeHashFromReader(Encoding.UTF8.GetBytes(uri + "\0"), new StringReader(source), hashAlgorithm);
    reader.Dispose();
    return hash;
  }

  public override Task<ProgramParseResult> ParseFiles(string programName, IReadOnlyList<DafnyFile> files,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken) {
    return parseCache.ProfileAndPruneCache(() =>
      base.ParseFiles(programName, files, errorReporter, cancellationToken),
      logger, telemetryPublisher, programName, "parsing", cancellationToken);
  }

  protected override DfyParseFileResult ParseFile(DafnyOptions options, FileSnapshot fileSnapshot,
    Uri uri, CancellationToken cancellationToken) {
    using var reader = fileSnapshot.Reader;

    // Add NUL delimiter to avoid collisions (otherwise hash("A" + "BC") == hash("AB" + "C"))
    var uriBytes = Encoding.UTF8.GetBytes(uri + "\0");

    using var hashAlgorithm = SHA256.Create();
    var (newReader, hash) = ComputeHashFromReader(uriBytes, reader, hashAlgorithm);
    using var bufferedReader = newReader;
    if (!parseCache.TryGet(hash, out var entry)) {
      logger.LogDebug($"Parse cache miss for {uri}");
      var source = bufferedReader.ReadToEnd();
      var parsed = base.ParseFile(options, fileSnapshot with { Reader = new StringReader(source) }, uri, cancellationToken);
      entry = new CachedParseFile(parsed, source);
      parseCache.Set(hash, entry);
    } else {
      logger.LogDebug($"Parse cache hit for {uri}");
    }

    // Clone declarations before returning them, since they are mutable and we don't want to mutate the one in the cache.
    // We should cache an immutable version of the AST instead: https://github.com/dafny-lang/dafny/issues/4086
    // These templates belong only to this parser. Forking a parser must reconstruct them, since the
    // source cloner deliberately preserves some token/options/delegate references within one parser.
    var result = entry!.Result;
    var cloner = new ParsedSourceCloner();
    var clonedResult = result with {
      Module = new FileModuleDefinition(cloner, result.Module),
      Version = fileSnapshot.Version
    };
    return clonedResult;
  }

  private sealed class ParsedSourceCloner() : Cloner(true, false) {
    public override Function CloneFunction(Function function, string? newName = null) {
      var clone = base.CloneFunction(function, newName);
      clone.SignatureEllipsis = function.SignatureEllipsis == null ? null : Origin(function.SignatureEllipsis);
      return clone;
    }
  }

  /// <summary>
  /// We read the contents of the reader and store them in memory using chunks
  /// to prevent allocating a large array of memory.
  /// </summary>
  private static (TextReader reader, byte[] hash) ComputeHashFromReader(byte[] startingBytes, TextReader reader, HashAlgorithm hashAlgorithm) {
    var result = new List<char[]>();
    const int chunkSize = 1024;
    hashAlgorithm.Initialize();
    // Add NUL delimiter to avoid collisions (otherwise hash("A" + "BC") == hash("AB" + "C"))

    // We need to include the uri as part of the hash, because the parsed AST contains tokens that refer to the filename. 
    hashAlgorithm.TransformBlock(startingBytes, 0, startingBytes.Length, null, 0);
    while (true) {
      var chunk = new char[chunkSize];
      var readCount = reader.ReadBlock(chunk, 0, chunk.Length);
      if (readCount < chunk.Length) {
        var shortenedChunk = new char[readCount];
        Array.Copy(chunk, 0, shortenedChunk, 0, readCount);
        result.Add(shortenedChunk);
        var charArray = Encoding.UTF8.GetBytes(shortenedChunk);
        hashAlgorithm.TransformFinalBlock(charArray, 0, charArray.Length);
        return (new TextReaderFromCharArrays(result), hashAlgorithm.Hash!);
      } else {
        var charArray = Encoding.UTF8.GetBytes(chunk);
        hashAlgorithm.TransformBlock(charArray, 0, charArray.Length, null, 0);
      }
      result.Add(chunk);
    }
  }
}
