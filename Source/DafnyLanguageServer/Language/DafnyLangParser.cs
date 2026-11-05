using Microsoft.Extensions.Logging;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser {
    private readonly DafnyOptions options;
    private readonly IFileSystem fileSystem;
    private readonly TelemetryPublisherBase telemetryPublisher;
    private readonly ILogger<DafnyLangParser> logger;
    private readonly ILogger<CachingParser> innerParserLogger;
    private readonly SemaphoreSlim mutex = new(1);
    private readonly ProgramParser programParser;

    public DafnyLangParser(DafnyOptions options, IFileSystem fileSystem, TelemetryPublisherBase telemetryPublisher,
      ILogger<DafnyLangParser> logger, ILogger<CachingParser> innerParserLogger)
      : this(options, fileSystem, telemetryPublisher, logger, innerParserLogger, null) {
    }

    private DafnyLangParser(DafnyOptions options, IFileSystem fileSystem, TelemetryPublisherBase telemetryPublisher,
      ILogger<DafnyLangParser> logger, ILogger<CachingParser> innerParserLogger, ProgramParser? clonedParser) {
      this.options = options;
      this.fileSystem = fileSystem;
      this.telemetryPublisher = telemetryPublisher;
      this.logger = logger;
      this.innerParserLogger = innerParserLogger;
      programParser = clonedParser ?? (options.Get(DafnyLangSymbolResolver.UseCaching)
        ? new CachingParser(innerParserLogger, fileSystem, telemetryPublisher)
        : new ProgramParser(innerParserLogger, fileSystem));
    }

    public int CachedParseCount => (programParser as CachingParser)?.CachedParseCount ?? 0;

    /// <summary>
    /// Creates an independent parser bound to the supplied child filesystem/options. The caller must
    /// fence the source against new work and supply detached child options. Existing parse templates
    /// are reconstructed from retained text once; no resolver or compilation state is inherited.
    /// </summary>
    public DafnyLangParser Clone(DafnyOptions options, IFileSystem fileSystem,
      TelemetryPublisherBase telemetryPublisher, CancellationToken cancellationToken = default) {
      if (!mutex.Wait(0, cancellationToken)) {
        throw new InvalidOperationException("Cannot clone a parser while it is in use.");
      }

      try {
        var clonedParser = options.Get(DafnyLangSymbolResolver.UseCaching) && programParser is CachingParser cached
          ? cached.Clone(options, fileSystem, telemetryPublisher, cancellationToken)
          : null;
        cancellationToken.ThrowIfCancellationRequested();
        return new DafnyLangParser(options, fileSystem, telemetryPublisher, logger, innerParserLogger, clonedParser);
      }
      finally {
        mutex.Release();
      }
    }

    public async Task<ProgramParseResult> Parse(Compilation compilation, CancellationToken cancellationToken) {
      await mutex.WaitAsync(cancellationToken);

      var beforeParsing = DateTime.Now;
      try {
        var rootFiles = await compilation.RootFiles;
        return await programParser.ParseFiles(compilation.Project.ProjectName, rootFiles, compilation.Reporter, cancellationToken);
      }
      finally {
        telemetryPublisher.PublishTime("Parse", compilation.Project.Uri.ToString(), DateTime.Now - beforeParsing);
        mutex.Release();
      }
    }
  }
}
