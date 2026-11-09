#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Parsing;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging.Abstractions;
using Bpl = Microsoft.Boogie;
using Action = System.Action;

namespace Microsoft.Dafny;

/// <summary>A host-owned process protocol; all semantic work stays in the existing native pipeline.</summary>
static class AnalysisSessionCommand {
  internal static readonly JsonSerializerOptions JsonOptions = new() {
    PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
    PropertyNameCaseInsensitive = true
  };
  internal const int RequestLimit = 8 * 1024 * 1024;
  // Bounds one response JSON line (the newline excluded). A final-gate analysis of Cat plus the core scope is 24.3 MB.
  internal const int ResponseLimit = 128 * 1024 * 1024;

  public static Command Create() {
    var command = new Command("analysis-session", "Run an execution-local incremental analysis and verification JSONL session.");
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, (options, _) => Run(options));
    return command;
  }

  internal static void RouteAnalysisDiagnostics(DafnyOptions options, string command) {
    if (command == "definition-analysis" && options.Get(DefinitionAnalysisCommand.IncludeProofInputs)) {
      // Match the one-shot certificate command: diagnostics must not prefix its JSON document.
      ((Bpl.CommandLineOptions)options).OutputWriter = options.ErrorWriter;
    }
  }

  internal sealed record Request(string Id, string[]? Arguments = null, string? Cwd = null,
    string ContextId = "default", Dictionary<string, string>? SourceSnapshots = null, int? Generation = null,
    string? SourceRoot = null, string? LogicalRoot = null, string? Operation = null, string? TargetId = null,
    string SessionId = "default", string? Payload = null);

  internal sealed record Response(string Id, int Returncode, string Stdout, string Stderr, object? NativeEvidence);

  private static async Task<int> Run(DafnyOptions startup) {
    var protocolOutput = startup.BaseOutputWriter;
    var consoleOutput = Console.Out;
    // Third-party TRX logging writes to Console.Out. The protocol owns its original writer
    // for the whole session, while ordinary console chatter has no protocol access.
    Console.SetOut(TextWriter.Null);
    try {
      return await RunProtocol(startup, protocolOutput);
    }
    finally {
      Console.SetOut(consoleOutput);
    }
  }

  internal static async Task<int> RunProtocol(DafnyOptions startup, TextWriter output,
    Func<Request, CancellationToken, Task<Response>>? execute = null, int responseLimit = ResponseLimit) {
    await using var sessions = new SessionRegistry();
    using var outputGate = new SemaphoreSlim(1);
    using var slots = new SemaphoreSlim(8);
    using var closeSlots = new SemaphoreSlim(8);
    var running = new ConcurrentDictionary<string, (string SessionId, CancellationTokenSource Cancellation, Task Task)>();
    var operationGate = new object();
    async Task Reply(Response response, Action? beforeWrite = null) {
      var line = JsonSerializer.Serialize(response, JsonOptions);
      if (Encoding.UTF8.GetByteCount(line) > responseLimit) {
        line = JsonSerializer.Serialize(new Response(response.Id, 6, "", "Native session response exceeds the output limit.", null), JsonOptions);
      }
      await outputGate.WaitAsync();
      try {
        beforeWrite?.Invoke();
        await output.WriteLineAsync(line);
        await output.FlushAsync();
      }
      finally {
        outputGate.Release();
      }
    }

    while (await ReadBoundedLine(startup.Input, RequestLimit) is { } line) {
      Request? request;
      try {
        request = JsonSerializer.Deserialize<Request>(line, JsonOptions);
      } catch (JsonException exception) {
        await Reply(new Response("", 2, "", exception.Message, null));
        continue;
      }
      if (request == null || string.IsNullOrEmpty(request.Id)) {
        await Reply(new Response("", 2, "", "A nonempty request ID is required.", null));
        continue;
      }
      if (request.Operation == "cancel") {
        var cancelled = Task.CompletedTask;
        lock (operationGate) {
          if (request.TargetId != null && running.TryGetValue(request.TargetId, out var operation) &&
              operation.SessionId == request.SessionId) {
            cancelled = operation.Cancellation.CancelAsync();
          }
        }
        await cancelled;
        await Reply(new Response(request.Id, 0, "", "", null));
        continue;
      }
      if (request.Operation == "shutdown") {
        var cancellations = new List<Task>();
        lock (operationGate) {
          foreach (var operation in running.Values) {
            cancellations.Add(operation.Cancellation.CancelAsync());
          }
        }
        await Task.WhenAll(cancellations);
#pragma warning disable VSTHRD003 // These are this method's own Task.Run workers; this CLI has no UI context.
        await Task.WhenAll(running.Values.Select(operation => operation.Task));
#pragma warning restore VSTHRD003
        await Reply(new Response(request.Id, 0, "", "", null));
        return 0;
      }
      if (running.ContainsKey(request.Id)) {
        await Reply(new Response(request.Id, 2, "", "Duplicate active request ID.", null));
        continue;
      }
      // Closing a branch must remain possible while all normal request slots are occupied.
      var requestSlots = request.Operation == "close-session" ? closeSlots : slots;
      if (!await requestSlots.WaitAsync(0)) {
        await Reply(new Response(request.Id, 6, "", "Native session pending-request limit reached.", null));
        continue;
      }
      var cancellation = new CancellationTokenSource();
      var ready = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
      var task = Task.Run(async () => {
        await ready.Task;
        var released = false;
        void Release() {
          if (!released) {
            lock (operationGate) {
              running.TryRemove(request.Id, out _);
              cancellation.Dispose();
              requestSlots.Release();
              released = true;
            }
          }
        }
        try {
          var response = await (execute ?? sessions.Execute)(request, cancellation.Token);
          await Reply(response, Release);
        }
        finally {
          Release();
        }
      });
      if (!running.TryAdd(request.Id, (request.SessionId, cancellation, task))) {
        ready.SetCanceled();
        cancellation.Dispose();
        requestSlots.Release();
        await Reply(new Response(request.Id, 2, "", "Duplicate active request ID.", null));
      } else {
        ready.SetResult();
      }
    }
    var eofCancellations = new List<Task>();
    lock (operationGate) {
      foreach (var operation in running.Values) {
        eofCancellations.Add(operation.Cancellation.CancelAsync());
      }
    }
    await Task.WhenAll(eofCancellations);
#pragma warning disable VSTHRD003 // Drain only the Task.Run workers created and owned above.
    await Task.WhenAll(running.Values.Select(operation => operation.Task));
#pragma warning restore VSTHRD003
    return 0;
  }

  internal sealed record CloneReceipt(int SchemaVersion, string DaemonEpoch, string ParentId, string ParentEpoch,
    string SessionId, string SessionEpoch, int ParsedEntries, int VerificationEntries);

  /// <summary>Branch lifetimes are independent; the protocol reader never waits for a clone or branch drain.</summary>
  internal sealed class SessionRegistry(int transferFrameLimit = RequestLimit) : IAsyncDisposable {
    private sealed class Branch(Session session) {
      public Session Session { get; } = session;
      public CancellationTokenSource Lifetime { get; } = new();
      public int Active { get; set; }
      public bool Closing { get; set; }
      public TaskCompletionSource Drained { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);
    }
    private readonly string daemonEpoch = Guid.NewGuid().ToString("N");
    private readonly object gate = new();
    private readonly List<Task> closures = new();
    private bool disposed;
    // A null value reserves a target while its cache snapshot is being constructed.
    private readonly Dictionary<string, Branch?> branches = new(StringComparer.Ordinal) {
      ["default"] = new Branch(new Session())
    };

    public async Task<Response> Execute(Request request, CancellationToken token) {
      if (string.IsNullOrWhiteSpace(request.SessionId)) {
        return new Response(request.Id, 2, "", "A nonempty sessionId is required.", null);
      }
      if (request.Operation == "close-session") {
        return await Close(request, token);
      }
      if (request.Operation is not (null or "clone" or "export-session" or "import-session")) {
        return new Response(request.Id, 7, "", "DAFNY_SESSION_UNSUPPORTED: Unknown native session operation.", null);
      }
      Branch branch;
      lock (gate) {
        if (disposed || !branches.TryGetValue(request.SessionId, out var found) || found == null || found.Closing) {
          return new Response(request.Id, 2, "", "The requested native session is unavailable.", null);
        }
        branch = found;
        branch.Active++;
      }
      using var linked = CancellationTokenSource.CreateLinkedTokenSource(token, branch.Lifetime.Token);
      try {
        if (request.Operation == "clone") {
          return await Clone(request, branch, linked.Token);
        }
        if (request.Operation == "export-session") {
          return await Export(request, branch, linked.Token);
        }
        if (request.Operation == "import-session") {
          return await Import(request, branch, linked.Token);
        }
        return await branch.Session.Execute(request, linked.Token);
      }
      finally {
        lock (gate) {
          if (--branch.Active == 0 && branch.Closing) {
            branch.Drained.TrySetResult();
          }
        }
      }
    }

    private async Task<Response> Clone(Request request, Branch parent, CancellationToken token) {
      if (string.IsNullOrWhiteSpace(request.TargetId)) {
        return new Response(request.Id, 2, "", "Clone requires a nonempty targetId.", null);
      }
      lock (gate) {
        if (!branches.TryAdd(request.TargetId, null)) {
          return new Response(request.Id, 2, "", "The clone target already exists.", null);
        }
      }
      Session? child = null;
      var published = false;
      try {
        var snapshot = await parent.Session.Clone(token);
        child = snapshot.Child;
        var receipt = new CloneReceipt(1, daemonEpoch, request.SessionId, parent.Session.Epoch,
          request.TargetId, child.Epoch, snapshot.ParsedEntries, snapshot.VerificationEntries);
        lock (gate) {
          token.ThrowIfCancellationRequested();
          if (disposed || parent.Closing) {
            throw new OperationCanceledException("The parent native session is closing.");
          }
          branches[request.TargetId] = new Branch(child);
          published = true;
        }
        return new Response(request.Id, 0, JsonSerializer.Serialize(receipt, JsonOptions), "", null);
      } catch (OperationCanceledException) {
        return new Response(request.Id, 130, "", "Native session clone cancelled.", null);
      } catch (NotSupportedException exception) {
        return new Response(request.Id, 7, "", "DAFNY_SESSION_UNSUPPORTED: " + exception.Message, null);
      } catch (Exception exception) {
        return new Response(request.Id, 6, "", exception.Message, null);
      }
      finally {
        if (!published) {
          child?.Dispose();
          lock (gate) {
            branches.Remove(request.TargetId);
          }
        }
      }
    }

    /// <summary>Serializes the branch's reusable caches at the clone boundary; the branch is left unchanged.</summary>
    private async Task<Response> Export(Request request, Branch source, CancellationToken token) {
      try {
        var toolchain = DefinitionAnalysis.ContextToolchainIdentity();
        if (toolchain == null) {
          return new Response(request.Id, 6, "", "The native toolchain identity is unavailable, so the session cannot be exported.", null);
        }
        var (resolverContexts, resultContexts) = await source.Session.ExportTransfer(token);
        var payload = NativeSessionTransfer.Serialize(new NativeSessionTransfer.TransferDocument(NativeSessionTransfer.SchemaVersion,
          daemonEpoch, request.SessionId, source.Session.Epoch, toolchain, resolverContexts, resultContexts));
        NativeSessionTransfer.CheckFrame(payload, transferFrameLimit);
        return new Response(request.Id, 0, payload, "", null);
      } catch (NativeSessionTransfer.TransferTooLargeException exception) {
        return new Response(request.Id, 6, "", "DAFNY_SESSION_TRANSFER_TOO_LARGE: " + exception.Message, null);
      } catch (OperationCanceledException) {
        return new Response(request.Id, 130, "", "Native session export cancelled.", null);
      } catch (NotSupportedException exception) {
        return new Response(request.Id, 7, "", "DAFNY_SESSION_UNSUPPORTED: " + exception.Message, null);
      } catch (Exception exception) {
        return new Response(request.Id, 6, "", exception.Message, null);
      }
    }

    /// <summary>Validates a transfer document and installs it into a fresh branch, or installs nothing.</summary>
    private async Task<Response> Import(Request request, Branch target, CancellationToken token) {
      try {
        var document = NativeSessionTransfer.Parse(request.Payload, DefinitionAnalysis.ContextToolchainIdentity(),
          Session.ResolverContextCapacity, Session.ResultContextCapacity);
        var (parsed, verification) = await target.Session.Import(document, token);
        var receipt = new NativeSessionTransfer.ImportReceipt(NativeSessionTransfer.SchemaVersion, daemonEpoch, request.SessionId,
          target.Session.Epoch, parsed, verification);
        return new Response(request.Id, 0, JsonSerializer.Serialize(receipt, JsonOptions), "", null);
      } catch (NativeSessionTransfer.TransferRejectedException exception) {
        return new Response(request.Id, 2, "", "DAFNY_SESSION_TRANSFER_REJECTED: " + exception.Message, null);
      } catch (OperationCanceledException) {
        return new Response(request.Id, 130, "", "Native session import cancelled.", null);
      } catch (Exception exception) {
        return new Response(request.Id, 6, "", exception.Message, null);
      }
    }

    private async Task<Response> Close(Request request, CancellationToken token) {
      Branch branch;
      lock (gate) {
        if (!branches.TryGetValue(request.SessionId, out var found) || found == null || found.Closing) {
          return new Response(request.Id, 2, "", "The requested native session is unavailable.", null);
        }
        branch = found;
        branch.Closing = true;
        if (branch.Active == 0) {
          branch.Drained.TrySetResult();
        }
      }
      var cleanup = FinishClose(request.SessionId, branch);
      lock (gate) {
        closures.RemoveAll(task => task.IsCompletedSuccessfully);
        closures.Add(cleanup);
      }
      try {
        await cleanup.WaitAsync(token);
        return new Response(request.Id, 0, "", "", null);
      } catch (OperationCanceledException) {
        // The caller can stop waiting, but this registry still owns the drain and disposes it at shutdown.
        return new Response(request.Id, 130, "", "Native session close cancelled; branch cleanup continues.", null);
      }
    }

    private async Task FinishClose(string id, Branch branch) {
      await branch.Lifetime.CancelAsync();
      await branch.Drained.Task;
      lock (gate) {
        branches.Remove(id);
      }
      branch.Session.Dispose();
      branch.Lifetime.Dispose();
    }

    public async ValueTask DisposeAsync() {
      string[] ids;
      lock (gate) {
        disposed = true;
        ids = branches.Where(entry => entry.Value is { Closing: false }).Select(entry => entry.Key).ToArray();
      }
      foreach (var id in ids) {
        await Close(new Request("dispose", Operation: "close-session", SessionId: id), CancellationToken.None);
      }
      Task[] pending;
      lock (gate) {
        pending = closures.ToArray();
      }
      await Task.WhenAll(pending);
    }
  }

  private static async Task<string?> ReadBoundedLine(TextReader reader, int limit) {
    var buffer = new StringBuilder();
    var character = new char[1];
    while (await reader.ReadAsync(character, 0, 1) != 0) {
      if (character[0] == '\n') {
        return buffer.ToString();
      }
      if (buffer.Length >= limit) {
        throw new InvalidDataException("Native session request exceeds the input limit.");
      }
      buffer.Append(character[0]);
    }
    return buffer.Length == 0 ? null : buffer.ToString();
  }

  /// <summary>
  /// A small most-recently-used map. Retained caches are keyed by option context, so alternating
  /// contexts stay warm while the number of resident contexts stays bounded.
  /// </summary>
  internal sealed class RetentionMap<T>(int capacity) where T : class {
    private readonly List<KeyValuePair<string, T>> entries = new();
    public int Evictions { get; private set; }
    public int Count => entries.Count;
    public IEnumerable<T> Values => entries.Select(entry => entry.Value);
    public IReadOnlyList<KeyValuePair<string, T>> Snapshot() => entries.ToArray();

    /// <summary>Mark an existing entry as most recently used.</summary>
    public bool Touch(string key, out T? value) {
      var index = entries.FindIndex(entry => entry.Key == key);
      if (index < 0) {
        value = null;
        return false;
      }
      value = entries[index].Value;
      entries.RemoveAt(index);
      entries.Add(new KeyValuePair<string, T>(key, value));
      return true;
    }

    /// <summary>
    /// Return the entry for the key or create it, evicting the least recently used entry at capacity.
    /// <paramref name="create"/> receives the evicted value, if any, so its owner can be released or reused.
    /// </summary>
    public T Acquire(string key, Func<T?, T> create) {
      if (Touch(key, out var existing)) {
        return existing!;
      }
      T? evicted = null;
      if (entries.Count >= capacity) {
        evicted = entries[0].Value;
        entries.RemoveAt(0);
        Evictions++;
      }
      var value = create(evicted);
      entries.Add(new KeyValuePair<string, T>(key, value));
      return value;
    }

    public void Clear() => entries.Clear();
  }

  /// <summary>The native parser, resolver and analysis facts that share one resolver identity.</summary>
  internal sealed record ResolverRetention(DafnyLangParser Parser, DafnyLangSymbolResolver Resolver,
    DefinitionAnalysis.SessionCache Facts, DafnyOptions Options);

  /// <summary>One option context's Boogie result cache and its own compilation count.</summary>
  internal sealed class ResultRetention(NativeVerificationCache cache) {
    public NativeVerificationCache Cache { get; } = cache;
    public int Compilations { get; set; }
  }

  internal sealed class Session : IDisposable {
    internal const int ResultContextCapacity = 4;
    internal const int ResolverContextCapacity = 2;
    // Resolver/translation internals include process-static state. Solvers run outside this gate.
    private static readonly SemaphoreSlim CompilerPreparation = new(1);
    private readonly SemaphoreSlim preparation = new(1);
    private readonly string epoch = Guid.NewGuid().ToString("N");
    private readonly SwitchingFileSystem fileSystem = new();
    private readonly CliTelemetryPublisher telemetry = new(NullLogger<TelemetryPublisherBase>.Instance);
    private readonly DafnyProgramVerifier translator = new(NullLogger<DafnyProgramVerifier>.Instance);
    private readonly ConcurrentQueue<DafnyDiagnostic> diagnostics = new();
    private readonly RetentionMap<ResolverRetention> resolvers = new(ResolverContextCapacity);
    private readonly RetentionMap<ResultRetention> results = new(ResultContextCapacity);
    private sealed record PendingResolver(string OptionsIdentity, IReadOnlyList<CachingParser.ParsedSeed> Seeds);
    // Imported parser sources wait here, keyed by resolver context, until a request can parse them.
    private readonly Dictionary<string, PendingResolver> pendingResolvers = new(StringComparer.Ordinal);
    private bool imported;
    private State? state;
    private string? configuration;
    private readonly SemaphoreSlim admission = new(1);
    private readonly System.CommandLine.Parsing.Parser requestParser;
    private readonly AsyncLocal<System.Action<DafnyOptions>?> optionsSink = new();
    private int generation;
    private int readers;
    private TaskCompletionSource drained = CompletedSource();

    internal int RetainedResultContexts => results.Count;
    internal int RetainedResolverContexts => resolvers.Count;
    internal string Epoch => epoch;
    /// <summary>Imported parser sources that seeded a resolver context's parser.</summary>
    internal int ImportedSeedsBound { get; private set; }
    /// <summary>Imported parser sources dropped because their resolver identity did not match the request.</summary>
    internal int ImportedSeedsDiscarded { get; private set; }
    /// <summary>Test seam: the solver content hash used by the context identity (default: the file's bytes).</summary>
    internal Func<string, string?>? ToolFileHash { get; init; }

    /// <summary>
    /// The session's identities hash the solver file that the engine starts, so every solver path must name the
    /// same file for both (<see cref="DafnyOptions.IsExactSolverPath"/>): absolute and normalized.
    /// <c>--solver-path</c> is absolutized against the request directory and qualifies.
    /// </summary>
    private static void RejectInexactSolverPaths(DafnyOptions options) {
      if (options.ProverOptions.Select(DafnyOptions.ProverPathValue)
          .Any(path => path != null && !DafnyOptions.IsExactSolverPath(path))) {
        throw new NotSupportedException("Session solver paths must be absolute and normalized; use --solver-path or such a PROVER_PATH.");
      }
    }

    public Session() {
      var root = new RootCommand();
      foreach (var command in new[] { ResolveCommand.Create(), VerifyCommand.Create(), DefinitionAnalysisCommand.Create() }) {
        DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, (options, _) => {
          optionsSink.Value!(options);
          return Task.FromResult(0);
        });
        root.AddCommand(command);
      }
      requestParser = DafnyNewCli.CreateParser(root);
    }

    private static TaskCompletionSource CompletedSource() {
      var source = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
      source.SetResult();
      return source;
    }

    private static DafnyOptions DetachedParserOptions(DafnyOptions options) {
      if (!options.TryCreateDetachedSnapshot(out var detached, out var failure)) {
        throw new NotSupportedException("The parser option context cannot be cloned: " + failure);
      }
      // Request writers, captured files, output delegates and projects belong to the current request.
      ((Bpl.CommandLineOptions)detached).OutputWriter = TextWriter.Null;
      detached.ErrorWriter = TextWriter.Null;
      detached.SnippetFileSystem = null;
      detached.PrintPathMapper = null;
      detached.DafnyProject = null;
      return detached;
    }

    /// <summary>
    /// Runs <paramref name="work"/> at a safe drained boundary: admitted, preparation held, no reader active.
    /// Clone, export and import share it. Only work that parses sources needs the process-wide compiler gate.
    /// </summary>
    private async Task<T> AtDrainedBoundary<T>(bool compilerGate, Func<T> work, CancellationToken token) {
      await admission.WaitAsync(token);
      var compilerAdmitted = false;
      var preparing = false;
      try {
        if (compilerGate) {
          await CompilerPreparation.WaitAsync(token);
          compilerAdmitted = true;
        }
        await preparation.WaitAsync(token);
        preparing = true;
        while (readers != 0) {
          var wait = drained.Task;
          preparation.Release();
          preparing = false;
          if (compilerAdmitted) {
            CompilerPreparation.Release();
            compilerAdmitted = false;
          }
          await wait.WaitAsync(token);
          if (compilerGate) {
            await CompilerPreparation.WaitAsync(token);
            compilerAdmitted = true;
          }
          await preparation.WaitAsync(token);
          preparing = true;
        }
        token.ThrowIfCancellationRequested();
        return work();
      }
      finally {
        if (preparing) {
          preparation.Release();
        }
        if (compilerAdmitted) {
          CompilerPreparation.Release();
        }
        admission.Release();
      }
    }

    internal Task<(Session Child, int ParsedEntries, int VerificationEntries)> Clone(CancellationToken token) =>
      AtDrainedBoundary(true, () => {
        var child = new Session();
        try {
          var parsedEntries = 0;
          foreach (var entry in resolvers.Snapshot()) {
            token.ThrowIfCancellationRequested();
            var options = DetachedParserOptions(entry.Value.Options);
            var parser = entry.Value.Parser.Clone(options, child.fileSystem, child.telemetry, token);
            parsedEntries += parser.CachedParseCount;
            child.resolvers.Acquire(entry.Key, _ => new ResolverRetention(parser,
              new DafnyLangSymbolResolver(NullLogger<DafnyLangSymbolResolver>.Instance,
                NullLogger<CachingResolver>.Instance, child.telemetry), new DefinitionAnalysis.SessionCache(), options));
          }
          // Seeds an imported session has not bound to a request yet are immutable text and carry over.
          foreach (var pending in pendingResolvers) {
            child.pendingResolvers[pending.Key] = pending.Value;
            parsedEntries += pending.Value.Seeds.Count;
          }
          var verificationEntries = 0;
          foreach (var entry in results.Snapshot()) {
            token.ThrowIfCancellationRequested();
            var cache = entry.Value.Cache.Clone(out var count, token);
            verificationEntries += count;
            child.results.Acquire(entry.Key, _ => new ResultRetention(cache) {
              Compilations = entry.Value.Compilations
            });
          }
          token.ThrowIfCancellationRequested();
          return (child, parsedEntries, verificationEntries);
        } catch {
          child.Dispose();
          throw;
        }
      }, token);

    /// <summary>
    /// The same data a clone copies, in detached transferable form. Reads the retained parser sources and
    /// native result journals at the drained boundary and changes nothing else. It needs no compiler gate
    /// because no source is parsed.
    /// </summary>
    internal Task<(NativeSessionTransfer.ResolverTransfer[] Resolvers, NativeSessionTransfer.ResultTransfer[] Results)>
      ExportTransfer(CancellationToken token) =>
      AtDrainedBoundary(false, () => {
        var exported = new List<NativeSessionTransfer.ResolverTransfer>();
        foreach (var pending in pendingResolvers) {
          exported.Add(new NativeSessionTransfer.ResolverTransfer(pending.Key, pending.Value.OptionsIdentity,
            pending.Value.Seeds.Select(NativeSessionTransfer.ToEntry).ToArray()));
        }
        foreach (var entry in resolvers.Snapshot()) {
          token.ThrowIfCancellationRequested();
          exported.Add(new NativeSessionTransfer.ResolverTransfer(entry.Key,
            DefinitionAnalysis.ResolutionOptionsIdentity(entry.Value.Options),
            entry.Value.Parser.ExportSeeds(token).Select(NativeSessionTransfer.ToEntry).ToArray()));
        }
        // The receiver retains at most this many contexts; the oldest ones would be evicted there first.
        var resolverContexts = exported.Skip(Math.Max(0, exported.Count - ResolverContextCapacity)).ToArray();
        var resultContexts = results.Snapshot().Select(entry => {
          token.ThrowIfCancellationRequested();
          return new NativeSessionTransfer.ResultTransfer(entry.Key, entry.Value.Compilations,
            entry.Value.Cache.ExportSnapshots(token).ToArray());
        }).ToArray();
        return (resolverContexts, resultContexts);
      }, token);

    /// <summary>
    /// Installs a validated document into this fresh session: result caches now, parser sources parked until
    /// the first request that creates the matching resolver context (a fresh process has no options to parse
    /// them with). All or nothing; a session that already served a request or imported is rejected.
    /// </summary>
    internal Task<(int ParsedEntries, int VerificationEntries)> Import(NativeSessionTransfer.TransferDocument document,
      CancellationToken token) =>
      AtDrainedBoundary(false, () => {
        if (state != null || imported || resolvers.Count != 0 || results.Count != 0 || pendingResolvers.Count != 0) {
          throw new NativeSessionTransfer.TransferRejectedException("An import needs a fresh session that has served no request.");
        }
        var built = new List<(string Key, ResultRetention Retention)>();
        try {
          var verificationEntries = 0;
          foreach (var result in document.Results) {
            token.ThrowIfCancellationRequested();
            var cache = NativeVerificationCache.Restore(result.Entries, out var count, token);
            verificationEntries += count;
            built.Add((result.Key, new ResultRetention(cache) { Compilations = result.Compilations }));
          }
          token.ThrowIfCancellationRequested();
          var parsedEntries = 0;
          foreach (var (key, retention) in built) {
            results.Acquire(key, _ => retention);
          }
          built.Clear();
          foreach (var resolver in document.Resolvers) {
            pendingResolvers[resolver.Key] = new PendingResolver(resolver.OptionsIdentity,
              resolver.Entries.Select(NativeSessionTransfer.ToSeed).ToArray());
            parsedEntries += resolver.Entries.Length;
          }
          imported = true;
          return (parsedEntries, verificationEntries);
        }
        finally {
          foreach (var (_, retention) in built) {
            retention.Cache.Dispose();
          }
        }
      }, token);

    /// <summary>
    /// Creates a resolver context's parser, from parked imported sources when they were exported for exactly
    /// this resolver identity. A mismatch or an option set that cannot be detached parses cold.
    /// </summary>
    private DafnyLangParser CreateParser(DafnyOptions options, string resolverContext, string resolutionIdentity,
      CancellationToken token) {
      if (pendingResolvers.TryGetValue(resolverContext, out var pending)) {
        if (pending.OptionsIdentity == resolutionIdentity && pending.Seeds.Count != 0) {
          try {
            var parser = DafnyLangParser.FromSeeds(options, DetachedParserOptions(options), fileSystem, telemetry,
              NullLogger<DafnyLangParser>.Instance, NullLogger<CachingParser>.Instance, pending.Seeds, token);
            pendingResolvers.Remove(resolverContext);
            ImportedSeedsBound += pending.Seeds.Count;
            return parser;
          } catch (NotSupportedException) {
            // Parse cold below; the seeds stay parked for a request whose options can be detached.
            return ColdParser(options);
          }
        }
        pendingResolvers.Remove(resolverContext);
        ImportedSeedsDiscarded += pending.Seeds.Count;
      }
      return ColdParser(options);
    }

    private DafnyLangParser ColdParser(DafnyOptions options) => new(options, fileSystem, telemetry,
      NullLogger<DafnyLangParser>.Instance, NullLogger<CachingParser>.Instance);

    public async Task<Response> Execute(Request request, CancellationToken cancellationToken) {
      var stdout = new StringWriter();
      var stderr = new StringWriter();
      State? selected = null;
      CapturedFileSystem? responseFiles = null;
      CliCompilation? cli = null;
      var taskCount = 0;
      var cacheHits = 0;
      var solverRuns = 0;
      var moduleHits = 0;
      var moduleMisses = 0;
      IReadOnlyList<ICanVerify>? verificationTargets = null;
      CliCompilation.LineRange? verificationRange = null;
      var preparedTargets = new Dictionary<ICanVerify, IReadOnlyList<IVerificationTask>>();
      var admitted = false;
      var selectionRejected = false;
      var completed = false;
      var compilerAdmitted = false;
      var admissionHeld = false;
      var preparing = false;
      var outcome = "error";
      var code = 6;
      void ReleasePreparation() {
        if (preparing) {
          preparation.Release();
          preparing = false;
        }
        if (compilerAdmitted) {
          CompilerPreparation.Release();
          compilerAdmitted = false;
        }
        if (admissionHeld) {
          admission.Release();
          admissionHeld = false;
        }
      }
      try {
        await admission.WaitAsync(cancellationToken);
        admissionHeld = true;
        await CompilerPreparation.WaitAsync(cancellationToken);
        compilerAdmitted = true;
        if (request.Arguments is not { Length: > 0 } arguments || arguments[0] is not ("resolve" or "definition-analysis" or "verify")) {
          throw new NotSupportedException("Only resolve, definition-analysis and verify are supported.");
        }
        var parsedCommand = await ParseOptions(arguments, request, stdout, stderr);
        if (parsedCommand == null) {
          code = 2;
          return new Response(request.Id, code, stdout.ToString(), stderr.ToString(), Evidence());
        }
        var options = parsedCommand.Options;
        RouteAnalysisDiagnostics(options, arguments[0]);
        if (options.UseStdin || options.GetOrOptionDefault(CommonOptionBag.InputType) != CommonOptionBag.InputTypeEnum.Source ||
            options.Get(CommonOptionBag.AnalyzeProofs) || options.Get(CommonOptionBag.WarnContradictoryAssumptions) ||
            options.Get(CommonOptionBag.WarnRedundantAssumptions) || options.Get(CommonOptionBag.SuggestProofRefactoring) ||
            options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
          throw new NotSupportedException("Standard input, proof-dependency reports and alternate input formats require the one-shot CLI.");
        }
        if (!options.GetOrOptionDefault(CommonOptionBag.UnicodeCharacters) ||
            options.Get(DeveloperOptionBag.PrintOption) != null || options.Get(DeveloperOptionBag.ResolvedPrint) != null ||
            options.Get(DeveloperOptionBag.BoogiePrint) != null || options.Get(DeveloperOptionBag.PassivePrint) != null ||
            options.Get(DeveloperOptionBag.SplitPrint) != null) {
          throw new NotSupportedException("Legacy character and compiler dump modes require the one-shot CLI.");
        }
        if (!DefinitionAnalysis.SupportsDiagnosticContext(options, allowSourceLibraries: true) || options.CliRootSourceUris.Any(uri => !uri.LocalPath.EndsWith(".dfy", StringComparison.OrdinalIgnoreCase))) {
          throw new NotSupportedException("The session supports explicit Dafny source roots and the default native transformation/library context.");
        }
        options.VerifySnapshots = 1;
        options.VcsCores = 1;
        options.Set(BoogieOptionBag.Cores, 1U);
        // CLI command parsing does not materialize this server-only option default.
        // The resident parser and resolver must explicitly enable native caching.
        options.Set(DafnyLangSymbolResolver.UseCaching, true);
        RejectInexactSolverPaths(options);
        if (arguments[0] == "verify" || options.Get(DefinitionAnalysisCommand.IncludeProofInputs)) {
          var solverReporter = new BatchErrorReporter(options);
          options.ProcessSolverOptions(solverReporter, Token.Cli);
          foreach (var diagnostic in solverReporter.AllMessages) {
            new ConsoleErrorReporter(options).MessageCore(RemapDiagnostic(diagnostic, request));
          }
          if (solverReporter.ErrorCount != 0) {
            throw new IOException("Native solver configuration failed.");
          }
          RejectInexactSolverPaths(options);
        }
        var parseOnly = arguments[0] == "definition-analysis" && options.Get(DefinitionAnalysisCommand.SpansOnly);
        // The context names each solver by path and content, so a state (and its engine, which starts that path)
        // is never reused for a request that names another solver path.
        var optionsIdentity = ToolFileHash == null ? DefinitionAnalysis.ContextOptionsIdentity(options)
          : DefinitionAnalysis.ContextOptionsIdentity(options, ToolFileHash);
        var capture = new CapturedFileSystem(request);
        // Native checksum dependencies do not cover every Dafny source-library axiom.
        // Bind the declared library closure conservatively before reusing native results.
        var libraryIdentity = string.Join("\0", options.Get(CommonOptionBag.Libraries)
          .Select(file => file.FullName + "\0" + capture.Fingerprint(new Uri(file.FullName))));
        var context = Hash(request.ContextId + "\0" + optionsIdentity + "\0" + libraryIdentity + parseOnly);
        var resolutionIdentity = DefinitionAnalysis.ResolutionOptionsIdentity(options);
        var resolverContext = Hash(request.ContextId + "\0" + resolutionIdentity + "\0" + libraryIdentity);
        var roots = options.CliRootSourceUris.ToList();
        await preparation.WaitAsync(cancellationToken);
        preparing = true;
        try {
          cancellationToken.ThrowIfCancellationRequested();
          var same = state != null && !state.Retired && configuration == context && roots.SequenceEqual(state.Roots) &&
            state.Files.Inputs.All(input => capture.Fingerprint(input.Key) == input.Value.Hash);
          while (!same && readers != 0) {
            var waitForDrain = drained.Task;
            preparation.Release();
            preparing = false;
            CompilerPreparation.Release();
            compilerAdmitted = false;
            await waitForDrain.WaitAsync(cancellationToken);
            await CompilerPreparation.WaitAsync(cancellationToken);
            compilerAdmitted = true;
            await preparation.WaitAsync(cancellationToken);
            preparing = true;
            same = state != null && !state.Retired && configuration == context && roots.SequenceEqual(state.Roots) &&
              state.Files.Inputs.All(input => capture.Fingerprint(input.Key) == input.Value.Hash);
          }
          if (same) {
            resolvers.Touch(resolverContext, out _);
            results.Touch(context, out _);
          } else {
            state?.Dispose();
            state = null;
            // Parser, resolver and facts are keyed by resolver identity, so alternating option
            // contexts keep their resolved modules. Only an evicted context's facts are dropped.
            var retained = resolvers.Acquire(resolverContext, evicted => {
              evicted?.Facts.Reset();
              return new ResolverRetention(CreateParser(options, resolverContext, resolutionIdentity, cancellationToken),
                new DafnyLangSymbolResolver(NullLogger<DafnyLangSymbolResolver>.Instance,
                  NullLogger<CachingResolver>.Instance, telemetry),
                new DefinitionAnalysis.SessionCache(), options);
            });
            // Native results are retained per option context and are never cleared by another context.
            // A context's cache is cleared when the context is evicted and at shutdown. Memory is bounded by
            // the cache's own entry bound (least recently used first), never by a count of compilations.
            var retainedResults = results.Acquire(context, evicted => {
              if (evicted == null) {
                return new ResultRetention(new NativeVerificationCache());
              }
              evicted.Cache.Clear();
              evicted.Compilations = 0;
              return evicted;
            });
            retainedResults.Compilations++;
            configuration = context;
            fileSystem.Current = capture;
            diagnostics.Clear();
            // Match the resident language-server engine, including its native result-cache policy.
            options.RunningBoogieFromCommandLine = false;
            options.DafnyProject ??= new DafnyProject(null, roots.First(), null,
              new HashSet<string> { roots.First().LocalPath }, new HashSet<string>(), new Dictionary<string, object>()) {
              ImplicitFromCli = true
            };
            generation++;
            var compilerOptions = new DafnyOptions(options, useNullWriters: true);
            var engineDiagnostics = new BoundedWriter();
            ((Bpl.CommandLineOptions)compilerOptions).OutputWriter = engineDiagnostics;
            compilerOptions.ErrorWriter = engineDiagnostics;
            var engine = new ExecutionEngine(compilerOptions, retainedResults.Cache, DafnyMain.LargeThreadScheduler);
            var shared = new SharedVerifier(translator, engine);
            var compilation = new Compilation(NullLogger<Compilation>.Instance, fileSystem,
              new TextDocumentLoader(NullLogger<ITextDocumentLoader>.Instance, retained.Parser, retained.Resolver), shared, engine,
              new CompilationInput(compilerOptions, generation, compilerOptions.DafnyProject)) {
              ShouldProcessSolverOptions = false,
              ShouldResolve = !parseOnly
            };
            var recorded = compilation.Updates.OfType<NewDiagnostic>().Subscribe(diagnostic => {
              if (diagnostic.Diagnostic.Source != MessageSource.Verifier) {
                diagnostics.Enqueue(diagnostic.Diagnostic);
              }
            });
            state = new State(compilation, engine, shared, capture, roots, generation,
              optionsIdentity, diagnostics, recorded, engineDiagnostics, retained.Facts, retainedResults.Cache);
            compilation.Start();
            await compilation.Resolution;
          }
          selected = state!;
          responseFiles = new CapturedFileSystem(request);
          responseFiles.CopyInputsFrom(selected.Files);
          // Excerpts under diagnostics show the bytes this request compiled, never the file at the logical path.
          options.SnippetFileSystem = new ExcerptFileSystem(responseFiles);
          options.PrintPathMapper = path => RemapOutputPath(path, request);
          cli = new CliCompilation(selected.Compilation, options);
          var reportedDiagnostics = selected.Diagnostics.Count;
          foreach (var diagnostic in selected.Diagnostics.Where(diagnostic => !parseOnly ||
                     diagnostic.Source is MessageSource.Parser or MessageSource.Project)) {
            cli.ReportDiagnostic(RemapDiagnostic(diagnostic, request));
          }
          if (arguments[0] == "verify" || options.Get(DefinitionAnalysisCommand.IncludeProofInputs)) {
            await selected.PrepareProofInputs(cancellationToken);
            foreach (var diagnostic in selected.Diagnostics.Skip(reportedDiagnostics)) {
              cli.ReportDiagnostic(RemapDiagnostic(diagnostic, request));
            }
          }
          if (arguments[0] == "verify" && await selected.Compilation.Resolution is {
            HasErrors: false, CanVerifies: not null
          } preparedResolution) {
            verificationTargets = cli.FilterCanVerifies(preparedResolution.CanVerifies, out verificationRange);
            // Prepare the whole native module roster before admitting concurrent readers.
            // A queued caller must not join another request's cancellable preparation.
            foreach (var target in verificationTargets) {
              preparedTargets[target] = await selected.VerificationTasks(preparedResolution, target, cancellationToken);
            }
          }
          if (readers++ == 0) {
            drained = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
          }
          admitted = true;
          if (arguments[0] == "definition-analysis") {
            var resolution = await selected.Compilation.Resolution;
            var uris = await selected.SourceUris();
            object? document = null;
            if (options.Get(DefinitionAnalysisCommand.SpansOnly) && options.Get(DefinitionAnalysisCommand.AnalysisSources)?.Any() == true) {
              await stderr.WriteLineAsync("definition-analysis does not support --analysis-source with --spans-only.");
              selectionRejected = true;
            } else if (options.Get(DefinitionAnalysisCommand.SpansOnly)) {
              var parsed = await selected.Compilation.ParsedProgram;
              if (parsed != null && !parsed.HasParseErrors) {
                document = DefinitionAnalysis.AnalyzeSpans(parsed, uris);
              }
            } else if (resolution is { HasErrors: false }) {
              // The reported scope is a query on this immutable compilation; it never
              // replaces the compilation, widens its roots or changes its proof inputs.
              var reported = DefinitionAnalysisCommand.SelectAnalysisSources(options, uris, resolution.ResolvedProgram,
                out var selectionError);
              if (reported == null) {
                await stderr.WriteLineAsync(RemapOutputText(selectionError!, request));
                selectionRejected = true;
              }
              var analyzed = reported == null ? null : DefinitionAnalysis.AnalyzeDocument(resolution.ResolvedProgram, reported,
                options.Get(DefinitionAnalysisCommand.IncludeStatements),
                options.Get(DefinitionAnalysisCommand.IncludeSemanticFacts),
                options.Get(DefinitionAnalysisCommand.IncludeProofInputs),
                options.Get(DefinitionAnalysisCommand.IncludeVerificationFacts)
                  ? resolution.CanVerifies!.Values.SelectMany(tree => tree.Values) : null,
                selected.Files.TextSnapshots, selected.Facts, () => selected.ProofInputs);
              if (analyzed != null) {
                moduleHits = selected.Facts.ModuleHits;
                moduleMisses = selected.Facts.ModuleMisses;
                document = options.Get(DefinitionAnalysisCommand.IncludeSourceFacts) ||
                  options.Get(DefinitionAnalysisCommand.IncludeSemanticFacts) ||
                  options.Get(DefinitionAnalysisCommand.IncludeProofInputs) ||
                  options.Get(DefinitionAnalysisCommand.IncludeVerificationFacts) ? analyzed : analyzed.Definitions;
              }
            }
            if (document != null) {
              await stdout.WriteLineAsync(JsonSerializer.Serialize(document, JsonOptions));
            }
          }
        }
        finally {
          ReleasePreparation();
        }

        cancellationToken.ThrowIfCancellationRequested();
        if (arguments[0] == "verify") {
          var resolution = await selected.Compilation.Resolution;
          code = await cli.GetAndReportExitCode();
          if (code == 0 && resolution is { HasErrors: false, CanVerifies: not null }) {
            var targets = verificationTargets!;
            var range = verificationRange!;
            if (targets.Count == 0) {
              await stderr.WriteLineAsync("The requested verification scope contains no native targets.");
              code = (int)ExitValue.DAFNY_ERROR;
            } else {
              var logger = new VerificationResultLogger(options, resolution.ResolvedProgram.ProofDependencyManager,
                path => RemapOutputPath(path, request));
              try {
                foreach (var target in targets) {
                  var prepared = preparedTargets[target];
                  var selectedTasks = prepared.Where(task => !range.Filters || cli.KeepVerificationTask(task, range)).ToList();
                  var verified = new List<VerificationTaskResult>();
                  foreach (var task in selectedTasks) {
                    var entry = selected.TaskEntry(task);
                    taskCount++;
                    var observation = await entry.Wait(cancellationToken, () => selected.Retired = true,
                      (reused, started) => {
                        if (reused) { cacheHits++; }
                        if (started) { solverRuns++; }
                      });
                    selected.Complete(task, observation.Result);
                    verified.Add(new VerificationTaskResult(task, observation.Result));
                  }
                  lock (selected.ReportingGate) {
                    foreach (var result in verified) {
                      foreach (var diagnostic in Compilation.GetDiagnosticsFromResult(options, target.Origin.Uri,
                                 target, result.Task, result.Result)) {
                        cli.ReportDiagnostic(RemapDiagnostic(diagnostic, request));
                      }
                    }
                    logger.Report(new CanVerifyResult(target, verified));
                  }
                }
              }
              finally {
                await logger.Finish();
              }
              code = await cli.GetAndReportExitCode();
              await stdout.WriteLineAsync($"Dafny program verifier finished with {taskCount} assertion batches");
            }
          }
        } else {
          code = await cli.GetAndReportExitCode();
          if (selectionRejected && code == 0) {
            code = (int)ExitValue.PREPROCESSING_ERROR;
          }
        }
        cancellationToken.ThrowIfCancellationRequested();
        if (!responseFiles!.IsFresh() || parsedCommand.LibraryDirectories.Any(directory => !directory.IsFresh())) {
          throw new IOException("A consumed input changed during the native request; its result is incomplete.");
        }
        completed = true;
        outcome = "completed";
      } catch (NotSupportedException exception) {
        code = 7;
        await stderr.WriteLineAsync("DAFNY_SESSION_UNSUPPORTED: " + exception.Message);
      } catch (OperationCanceledException) {
        if (selected != null) { selected.Retired = true; }
        code = 130;
        outcome = "cancelled";
        await stderr.WriteLineAsync("Native session request cancelled.");
      } catch (Exception exception) {
        if (selected != null) { selected.Retired = true; } else if (state != null) { state.Retired = true; }
        code = 6;
        await stderr.WriteLineAsync(exception.Message);
      }
      finally {
        ReleasePreparation();
        if (admitted) {
          await preparation.WaitAsync();
          try {
            if (--readers == 0) {
              drained.TrySetResult();
            }
          }
          finally {
            preparation.Release();
          }
        }
      }
      return new Response(request.Id, code, stdout.ToString(), stderr.ToString(), Evidence());

      object Evidence() => new {
        SchemaVersion = 1,
        SessionEpoch = epoch,
        request.SessionId,
        Generation = request.Generation ?? selected?.Generation ?? generation,
        SourceIdentity = responseFiles?.Identity ?? Hash("unresolved"),
        request.ContextId,
        OptionsIdentity = selected?.OptionsIdentity ?? Hash("unresolved"),
        ToolchainIdentity = DefinitionAnalysis.ContextToolchainIdentity(),
        ConsumedInputs = responseFiles?.ActualFingerprints ?? new Dictionary<string, string>(),
        Completed = completed,
        Outcome = outcome,
        TaskCount = taskCount,
        CacheHitCount = cacheHits,
        SolverRunCount = solverRuns,
        AnalysisModuleHits = moduleHits,
        AnalysisModuleMisses = moduleMisses,
        ResultCacheEvictions = results.Evictions,
        ResolverEvictions = resolvers.Evictions
      };
    }

    private sealed record LibraryDirectory(string Path, IReadOnlySet<string> Members) {
      public bool IsFresh() => Directory.Exists(Path) && Members.SetEquals(CommonOptionBag.SplitOptionValueIntoFiles(new[] { Path }));
    }
    private sealed record ParsedCommand(DafnyOptions Options, IReadOnlyList<LibraryDirectory> LibraryDirectories);

    private async Task<ParsedCommand?> ParseOptions(string[] arguments, Request request, StringWriter stdout, StringWriter stderr) {
      DafnyOptions? parsed = null;
      var syntax = requestParser.Parse(arguments);
      var sources = syntax.GetValueForArgument(DafnyCommands.FilesArgument)?.ToList() ?? new List<FileInfo>();
      if (sources.Any(file => file.Extension.Equals(".toml", StringComparison.OrdinalIgnoreCase)) ||
          syntax.GetValueForOption(DafnyProject.FindProjectOption)) {
        throw new NotSupportedException("Explicit project-file discovery requires the one-shot CLI.");
      }
      int code;
      optionsSink.Value = options => parsed = options;
      try {
        code = await requestParser.InvokeAsync(arguments, new WritersConsole(TextReader.Null, stdout, stderr));
      }
      finally {
        optionsSink.Value = null;
      }
      if (code != 0 || parsed == null) { return null; }
      string Absolute(string value) => Path.GetFullPath(value, request.Cwd ?? Directory.GetCurrentDirectory());
      string Logical(string value) => RemapPrefix(Absolute(value), request.SourceRoot, request.LogicalRoot);
      parsed.CliRootSourceUris.Clear();
      parsed.CliRootSourceUris.AddRange(sources.Select(file => new Uri(Logical(file.ToString()))));
      var libraries = new List<FileInfo>();
      var directories = new List<LibraryDirectory>();
      foreach (var input in parsed.Get(CommonOptionBag.Libraries)) {
        // Directory enumeration is the existing native library policy, on the physical snapshot.
        foreach (var inputPath in input.ToString().Split(',').Select(Absolute)) {
          var expanded = CommonOptionBag.SplitOptionValueIntoFiles(new[] { inputPath }).ToList();
          if (Directory.Exists(inputPath)) {
            directories.Add(new LibraryDirectory(inputPath, expanded.ToHashSet(StringComparer.Ordinal)));
          }
          libraries.AddRange(expanded.Select(path => new FileInfo(Logical(path))));
        }
      }
      if (libraries.Any(file => !file.Extension.Equals(".dfy", StringComparison.OrdinalIgnoreCase))) {
        throw new NotSupportedException("Session libraries must be native Dafny source files or source directories.");
      }
      parsed.Set(CommonOptionBag.Libraries, libraries);
      // Reported sources name logical files like roots; they never become roots.
      // Only definition-analysis declares the option; other commands report it as null.
      if (parsed.Get(DefinitionAnalysisCommand.AnalysisSources) is { Count: > 0 } reportedSources) {
        parsed.Set(DefinitionAnalysisCommand.AnalysisSources, reportedSources
          .Select(file => new FileInfo(Logical(file.ToString()))).ToList());
      }
      parsed.LibraryFiles = libraries.Select(file => file.FullName).ToHashSet();
      var solver = parsed.Get(BoogieOptionBag.SolverPath);
      if (solver != null) {
        parsed.Set(BoogieOptionBag.SolverPath, new FileInfo(Absolute(solver.ToString())));
        parsed.ApplyBinding(BoogieOptionBag.SolverPath);
      }
      var position = parsed.Get(VerifyCommand.FilterPosition);
      if (position != null && request.SourceRoot != null && request.LogicalRoot != null) {
        parsed.Set(VerifyCommand.FilterPosition, RemapPrefix(position, request.SourceRoot, request.LogicalRoot));
      }
      var loggers = parsed.Get(CommonOptionBag.VerificationLogFormat);
      if (loggers != null) {
        parsed.Set(CommonOptionBag.VerificationLogFormat, loggers.Select(configuration => {
          var marker = "LogFileName=";
          var start = configuration.IndexOf(marker, StringComparison.OrdinalIgnoreCase);
          if (start < 0) { return configuration; }
          start += marker.Length;
          var end = configuration.IndexOf(',', start);
          if (end < 0) { end = configuration.Length; }
          return configuration[..start] + Absolute(configuration[start..end]) + configuration[end..];
        }).ToList());
      }
      return new ParsedCommand(parsed, directories);
    }

    public void Dispose() {
      state?.Dispose();
      foreach (var retained in results.Values) {
        retained.Cache.Dispose();
      }
      results.Clear();
      foreach (var retained in resolvers.Values) {
        retained.Facts.Reset();
      }
      resolvers.Clear();
      pendingResolvers.Clear();
      translator.Dispose();
      preparation.Dispose();
      admission.Dispose();
    }
  }

  private sealed class State : IDisposable {
    public Compilation Compilation { get; }
    private readonly ExecutionEngine engine;
    private readonly SharedVerifier verifier;
    public CapturedFileSystem Files { get; }
    public List<Uri> Roots { get; }
    public int Generation { get; }
    public string OptionsIdentity { get; }
    public ConcurrentQueue<DafnyDiagnostic> Diagnostics { get; }
    public DefinitionAnalysis.SessionCache Facts { get; }
    private readonly IDisposable diagnosticsSubscription;
    private readonly BoundedWriter engineDiagnostics;
    public DafnyProofInputs? ProofInputs { get; private set; }
    private bool proofInputsPrepared;
    private volatile bool retired;
    public bool Retired {
      get => retired || verifier.Failed || Compilation.HasErrors ||
        Compilation.Resolution.IsFaulted || Compilation.Resolution.IsCanceled;
      set => retired = value;
    }
    public object ReportingGate { get; } = new();
    private readonly ConcurrentDictionary<IVerificationTask, NativeTaskEntry> taskEntries = new();
    private readonly NativeImplementationCompletion completions;
    public State(Compilation compilation, ExecutionEngine engine, SharedVerifier verifier, CapturedFileSystem files,
      List<Uri> roots, int generation, string optionsIdentity, ConcurrentQueue<DafnyDiagnostic> diagnostics,
      IDisposable diagnosticsSubscription, BoundedWriter engineDiagnostics, DefinitionAnalysis.SessionCache facts,
      NativeVerificationCache cache) {
      Compilation = compilation;
      Facts = facts;
      this.engine = engine;
      this.verifier = verifier;
      Files = files;
      Roots = roots;
      Generation = generation;
      OptionsIdentity = optionsIdentity;
      Diagnostics = diagnostics;
      this.diagnosticsSubscription = diagnosticsSubscription;
      this.engineDiagnostics = engineDiagnostics;
      completions = new NativeImplementationCompletion(cache.PublishSuccessful);
    }
    public async Task<HashSet<Uri>> SourceUris() => (await Compilation.RootFiles)
      .Where(file => !file.ShouldNotVerify && file.Uri.IsFile && file.Extension == DafnyFile.DafnyFileExtension)
      .Select(file => file.Uri).ToHashSet();
    public async Task PrepareProofInputs(CancellationToken token) {
      if (proofInputsPrepared) {
        return;
      }
      var resolution = await Compilation.Resolution;
      if (resolution is { HasErrors: false }) {
        var translations = new List<Tuple<string, Bpl.Program>>();
        foreach (var module in BoogieGenerator.VerifiableModules(resolution.ResolvedProgram)) {
          translations.Add(Tuple.Create(module.SanitizedName, await verifier.Translation(resolution, module, token)));
        }
        if (resolution.ResolvedProgram.Reporter.ErrorCount != 0) {
          throw new InvalidOperationException("The native translation emitted errors.");
        }
        var uris = await SourceUris();
        ProofInputs = await DafnyMain.LargeStackFactory.StartNew(() =>
          DefinitionAnalysis.ProofInputsFromTranslations(resolution.ResolvedProgram, uris, translations), token);
        DefinitionAnalysis.BindNativeVerificationChecksums(translations, ProofInputs);
      }
      proofInputsPrepared = true;
    }
    public NativeTaskEntry TaskEntry(IVerificationTask task) => taskEntries.GetOrAdd(task, key => new NativeTaskEntry(key));
    public async Task<IReadOnlyList<IVerificationTask>> VerificationTasks(ResolutionResult resolution,
      ICanVerify target, CancellationToken token) {
      var prepared = await verifier.Tasks(resolution, target.ContainingModule, token);
      foreach (var implementation in prepared.GroupBy(task => task.Split.Run.Implementation)) {
        completions.Register(implementation.Key, implementation.ToDictionary(task => task, task => task.Split.SplitIndex));
      }
      var selected = prepared.Where(task => ReferenceEquals(Compilation.GetTaskOwner(task), target)).ToList();
      if (prepared.Any(task => Compilation.GetTaskOwner(task) == null)) {
        throw new InvalidOperationException("The native verification task lost its resolved declaration identity. " + engineDiagnostics);
      }
      return selected;
    }
    public void Complete(IVerificationTask task, VC.VerificationRunResult result) =>
      completions.Complete(task.Split.Run.Implementation, task, result);
    public void Dispose() {
      Compilation.Dispose();
      engine.Dispose();
      diagnosticsSubscription.Dispose();
    }
  }

  /// <summary>Completeness bookkeeping for native cache insertion, never a reuse decision.</summary>
  internal sealed class NativeImplementationCompletion {
    private sealed class Parts(Dictionary<IVerificationTask, int> expected) {
      public Dictionary<IVerificationTask, int> Expected { get; } = expected;
      public Dictionary<int, VC.VerificationRunResult> Results { get; } = new();
      public bool Published { get; set; }
    }
    private readonly object gate = new();
    private readonly Dictionary<Bpl.Implementation, Parts> implementations = new();
    private readonly System.Action<Bpl.Implementation, Bpl.ImplementationRunResult> publish;
    public NativeImplementationCompletion(System.Action<Bpl.Implementation, Bpl.ImplementationRunResult> publish) {
      this.publish = publish;
    }
    public void Register(Bpl.Implementation implementation, IReadOnlyDictionary<IVerificationTask, int> expected) {
      var indices = expected.Values.ToHashSet();
      if (indices.Count != expected.Count || !indices.SetEquals(Enumerable.Range(0, expected.Count))) {
        throw new InvalidOperationException("Native split indices do not form a complete implementation roster.");
      }
      lock (gate) {
        if (implementations.TryGetValue(implementation, out var existing)) {
          if (existing.Expected.Count != expected.Count || expected.Any(part =>
                !existing.Expected.TryGetValue(part.Key, out var index) || index != part.Value)) {
            throw new InvalidOperationException("Native implementation roster changed within one immutable state.");
          }
        } else {
          implementations.Add(implementation, new Parts(expected.ToDictionary(part => part.Key, part => part.Value)));
        }
      }
    }
    public void Complete(Bpl.Implementation implementation, IVerificationTask task, VC.VerificationRunResult result) {
      Bpl.ImplementationRunResult? aggregate = null;
      lock (gate) {
        var parts = implementations[implementation];
        if (!parts.Expected.TryGetValue(task, out var index)) {
          throw new InvalidOperationException("Completion does not belong to the native implementation roster.");
        }
        parts.Results[index] = result;
        if (!parts.Published && parts.Expected.Count > 0 && parts.Expected.Values.ToHashSet().SetEquals(parts.Results.Keys) &&
            parts.Results.Values.All(value => value.Outcome == Bpl.SolverOutcome.Valid)) {
          parts.Published = true;
          var results = parts.Results.OrderBy(part => part.Key).Select(part => part.Value).ToList();
          var resources = results.Sum(value => (long)value.ResourceCount);
          var obligations = results.Sum(value => (long)value.Asserts.Count);
          if (resources <= int.MaxValue && obligations <= int.MaxValue) {
            aggregate = new Bpl.ImplementationRunResult(implementation, null) {
              VcOutcome = VC.VcOutcome.Correct,
              Start = results.Min(value => value.StartTime),
              End = results.Max(value => value.StartTime + value.RunTime),
              Elapsed = TimeSpan.FromTicks(results.Sum(value => value.RunTime.Ticks)),
              ResourceCount = (int)resources,
              ProofObligationCountBefore = 0,
              ProofObligationCountAfter = (int)obligations,
              RunResults = results
            };
          }
        }
      }
      if (aggregate != null && !string.IsNullOrEmpty(implementation.Checksum) && implementation.DependencyChecksum != null) {
        publish(implementation, aggregate);
      }
    }
  }

  /// <summary>
  /// Lifts lambdas the way the one-shot CLI (VerifySnapshots 0) does, before the engine sees the program.
  /// With VerifySnapshots &gt; 0, Boogie's lifter attaches a fresh {:checksum} attribute to every lambda, and its
  /// alpha-equality compares attribute parameter lists by reference, so equal lambdas (for example the same set
  /// comprehension in a definition and in a proof) would each get their own lifted function and the solver would
  /// need extensionality to relate them. The lifted functions then get the constant checksum Boogie would have
  /// given them, so implementation dependency checksums stay defined. The lift happens once per program: proof-input
  /// preparation already lifts the same translation to compute its modular keys, and the engine's own lifting
  /// finds no lambda left.
  /// </summary>
  internal static void LiftLambdasAsOneShot(ExecutionEngineOptions engineOptions, Bpl.Program program) {
    if (!engineOptions.ExpandLambdas || engineOptions.VerifySnapshots <= 0 || engineOptions is not DafnyOptions options) {
      return;
    }
    DefinitionAnalysis.LiftLambdasOnce(options, program);
  }

  private sealed class SharedVerifier : IProgramVerifier {
    private readonly DafnyProgramVerifier translator;
    private readonly ExecutionEngine engine;
    private readonly ConcurrentDictionary<ModuleDefinition, Task<Bpl.Program>> translations = new();
    private readonly LazyConcurrentDictionary<ModuleDefinition, Task<IReadOnlyList<IVerificationTask>>> tasks = new();
    private volatile bool failed;
    public bool Failed => failed;
    public SharedVerifier(DafnyProgramVerifier translator, ExecutionEngine engine) {
      this.translator = translator;
      this.engine = engine;
    }
    public async Task<Bpl.Program> Translation(ResolutionResult resolution, ModuleDefinition module, CancellationToken token) {
      var translation = translations.GetOrAdd(module, _ => translator.TranslateModuleAsync(engine, resolution, module, token));
      try {
        return await translation;
      } catch {
        failed = true;
        translations.TryRemove(new KeyValuePair<ModuleDefinition, Task<Bpl.Program>>(module, translation));
        throw;
      }
    }
    public async Task<IReadOnlyList<IVerificationTask>> Tasks(ResolutionResult resolution, ModuleDefinition module, CancellationToken token) {
      if (Failed) {
        throw new InvalidOperationException("The native preparation was retired after a failed producer.");
      }
      var prepared = tasks.GetOrAdd(module, () => GetVerificationTasksAsync(engine, resolution, module, token));
      try {
        return await prepared;
      } catch {
        failed = true;
        tasks.Remove(module);
        translations.TryRemove(module, out _);
        throw;
      }
    }
    public async Task<IReadOnlyList<IVerificationTask>> GetVerificationTasksAsync(ExecutionEngine executionEngine,
      ResolutionResult resolution, ModuleDefinition moduleDefinition, CancellationToken cancellationToken) {
      var program = await Translation(resolution, moduleDefinition, cancellationToken);
      await DafnyMain.LargeStackFactory.StartNew(() => LiftLambdasAsOneShot(executionEngine.Options, program), cancellationToken);
      return await translator.GetVerificationTasksFromTranslationAsync(executionEngine, resolution, moduleDefinition,
        program, cancellationToken);
    }
  }

  internal sealed class NativeTaskEntry {
    private readonly IVerificationTask task;
    private readonly object gate = new();
    private Task<VC.VerificationRunResult>? result;
    private int subscribers;
    private bool cancelling;
    public bool Cached { get; }
    private readonly Func<IReadOnlyList<Bpl.AssertCmd>> currentAssertions;
    /// <param name="currentAssertions">The current split's assertions; a seam for tests, normally the task's split.</param>
    public NativeTaskEntry(IVerificationTask task, Func<IReadOnlyList<Bpl.AssertCmd>>? currentAssertions = null) {
      this.task = task;
      this.currentAssertions = currentAssertions ?? (() => task.Split.Asserts);
      Cached = task.CacheStatus is Completed;
    }
    public async Task<(VC.VerificationRunResult Result, bool Reused, bool Started)> Wait(CancellationToken token, Action retire,
      System.Action<bool, bool>? observed = null) {
      Task<VC.VerificationRunResult> producer;
      bool reused;
      bool started;
      lock (gate) {
        if (cancelling) {
          throw new OperationCanceledException("The native task is draining cancellation.");
        }
        subscribers++;
        reused = Cached || result?.IsCompletedSuccessfully == true;
        started = result == null && !Cached;
        producer = result ??= Run();
      }
      observed?.Invoke(reused, started);
      try {
        return (await producer.WaitAsync(token), reused, started);
      }
      finally {
        var drain = false;
        lock (gate) {
          subscribers--;
          if (subscribers == 0 && !producer.IsCompleted) {
            cancelling = true;
            drain = true;
          }
        }
        if (drain) {
          retire();
          task.Cancel();
          try {
            await producer;
          } catch (OperationCanceledException) {
          }
        }
      }
    }
    /// <summary>
    /// Replace the assertions of a reused result by the current split's assertions, matched by ordinal.
    /// The result key already binds the ordered assertion kinds and descriptions, so a disagreement means
    /// the key is unsound; fail the task rather than report a location from another compilation.
    /// </summary>
    internal static VC.VerificationRunResult RebaseCachedResult(VC.VerificationRunResult cached,
      IReadOnlyList<Bpl.AssertCmd> current) {
      var old = NativeVerificationCache.Shapes(cached);
      if (old.Count != current.Count) {
        throw new InvalidOperationException(
          $"A reused native result has {old.Count} assertions but the current split has {current.Count}.");
      }
      for (var index = 0; index < old.Count; index++) {
        if (old[index].Type != current[index].GetType().FullName ||
            old[index].Success != current[index].Description?.SuccessDescription ||
            old[index].Failure != current[index].Description?.FailureDescription) {
          throw new InvalidOperationException(
            $"A reused native result disagrees with the current split at assertion {index}.");
        }
      }
      return cached with { Asserts = current.ToList() };
    }

    private async Task<VC.VerificationRunResult> Run() {
      var result = await Produce();
      // The cache key carries no positions, so a reused result still points at the assertion objects
      // of the compilation that produced it. Report the current split's assertions instead.
      return Cached ? RebaseCachedResult(result, currentAssertions()) : result;
    }

    private async Task<VC.VerificationRunResult> Produce() {
      var updates = task.TryRun();
      if (updates == null) {
        if (task.CacheStatus is Completed cached) {
          return cached.Result;
        }
        throw new InvalidOperationException("A native task has another unowned producer.");
      }
      var finished = new TaskCompletionSource<VC.VerificationRunResult>(TaskCreationOptions.RunContinuationsAsynchronously);
      VC.VerificationRunResult? completed = null;
      using var subscription = updates.Subscribe(status => {
        if (status is Completed result) {
          completed = result.Result;
        }
      }, error => finished.TrySetException(error), () => {
        if (completed != null) {
          finished.TrySetResult(completed);
        } else {
          finished.TrySetException(new OperationCanceledException("Native task completed without a verification result."));
        }
      });
      return await finished.Task;
    }
  }

  private sealed class SwitchingFileSystem : IFileSystem {
    public CapturedFileSystem Current { get; set; } = null!;
    public FileSnapshot ReadFile(Uri uri) => Current.ReadFile(uri);
    public bool Exists(Uri path) => Current.Exists(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => Current.GetDirectoryInfoBase(root);
  }

  /// <summary>
  /// A read-only view of one request's captured source bytes for diagnostic excerpts. It never records a read, so the
  /// consumed-input identity and freshness checks are unaffected.
  /// </summary>
  private sealed class ExcerptFileSystem(CapturedFileSystem files) : IFileSystem {
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(files.ReadForExcerpt(uri)), null);
    public bool Exists(Uri path) => files.ExcerptExists(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => files.GetDirectoryInfoBase(root);
  }

  private sealed record CapturedInput(string Text, string Hash, bool Supplied);

  private sealed class BoundedWriter : TextWriter {
    private readonly StringBuilder text = new();
    private readonly object gate = new();
    public override Encoding Encoding => Encoding.UTF8;
    public override void Write(char value) {
      lock (gate) {
        if (text.Length < 32768) { text.Append(value); }
      }
    }
    public override void Write(string? value) {
      if (value == null) { return; }
      lock (gate) {
        var remaining = 32768 - text.Length;
        text.Append(value.AsSpan(0, Math.Min(value.Length, remaining)));
      }
    }
    public override string ToString() {
      lock (gate) { return text.ToString(); }
    }
  }

  private sealed class CapturedFileSystem : IFileSystem {
    private Request request;
    public Dictionary<Uri, CapturedInput> Inputs { get; } = new();
    public CapturedFileSystem(Request request) { this.request = request; }
    public void CopyInputsFrom(CapturedFileSystem source) {
      foreach (var input in source.Inputs) {
        Inputs.Add(input.Key, input.Value);
      }
    }
    private string ActualPath(Uri uri) {
      var path = uri.LocalPath;
      if (request.LogicalRoot != null && request.SourceRoot != null &&
          (path == request.LogicalRoot || path.StartsWith(request.LogicalRoot.TrimEnd('/') + "/", StringComparison.Ordinal))) {
        return request.SourceRoot.TrimEnd('/') + path[request.LogicalRoot.TrimEnd('/').Length..];
      }
      return path;
    }
    private CapturedInput Capture(Uri uri) {
      var path = ActualPath(uri);
      if (request.SourceSnapshots != null &&
          (request.SourceSnapshots.TryGetValue(uri.LocalPath, out var supplied) || request.SourceSnapshots.TryGetValue(path, out supplied))) {
        return new CapturedInput(supplied, Hash(supplied), true);
      }
      var bytes = File.ReadAllBytes(path);
      if (bytes.Length > RequestLimit) {
        throw new IOException("A source input exceeds the session file limit.");
      }
      var text = new UTF8Encoding(false, true).GetString(bytes);
      if (text.StartsWith('\uFEFF')) {
        text = text[1..];
      }
      return new CapturedInput(text, Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant(), false);
    }
    /// <summary>The captured text, else the supplied or physical text without capturing it.</summary>
    public string ReadForExcerpt(Uri uri) => Inputs.TryGetValue(uri, out var captured) ? captured.Text : Capture(uri).Text;
    public bool ExcerptExists(Uri uri) => Inputs.ContainsKey(uri) || Exists(uri);
    public string? Fingerprint(Uri uri) {
      try {
        return Capture(uri).Hash;
      } catch (FileNotFoundException) {
        return null;
      } catch (DirectoryNotFoundException) {
        return null;
      }
    }
    public FileSnapshot ReadFile(Uri uri) {
      if (!Inputs.TryGetValue(uri, out var captured)) {
        if (Inputs.Count >= 1024) {
          throw new IOException("Native session consumed-input limit reached.");
        }
        captured = Capture(uri);
        if (Inputs.Values.Sum(input => input.Text.Length) + captured.Text.Length > 64 * 1024 * 1024) {
          throw new IOException("Native session source-memory limit reached.");
        }
        Inputs.Add(uri, captured);
      }
      return new FileSnapshot(new StringReader(captured.Text), null);
    }
    public bool Exists(Uri uri) => request.SourceSnapshots?.ContainsKey(uri.LocalPath) == true ||
      request.SourceSnapshots?.ContainsKey(ActualPath(uri)) == true || File.Exists(ActualPath(uri));
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => OnDiskFileSystem.Instance.GetDirectoryInfoBase(root);
    public IReadOnlyDictionary<string, string> TextSnapshots => Inputs.ToDictionary(input => input.Key.LocalPath, input => input.Value.Text);
    public Dictionary<string, string> ActualFingerprints => Inputs.ToDictionary(input => ActualPath(input.Key), input => input.Value.Hash);
    public string Identity => Hash(JsonSerializer.Serialize(Inputs.OrderBy(input => input.Key.AbsoluteUri)
      .Select(input => new[] { input.Key.AbsoluteUri, input.Value.Hash })));
    public bool IsFresh() => Inputs.All(input => Fingerprint(input.Key) == input.Value.Hash);
  }

  private static string RemapPrefix(string value, string? from, string? to) {
    if (from != null && to != null && (value == from || value.StartsWith(from.TrimEnd('/') + "/", StringComparison.Ordinal))) {
      return to.TrimEnd('/') + value[from.TrimEnd('/').Length..];
    }
    return value;
  }
  internal static string RemapOutputPath(string path, Request request) => RemapPrefix(path, request.LogicalRoot, request.SourceRoot);

  private static bool IsPathCharacter(char value) => char.IsLetterOrDigit(value) || value is '_' or '-' or '.' or '/' or '\\';

  /// <summary>
  /// Maps a logical root that appears inside message text to the request's physical root. This is
  /// <see cref="RemapPrefix"/> for a path embedded in a message: the root must start a path (the text
  /// start or a character that cannot belong to a path precedes it) and end at a path boundary (a
  /// separator, the end of the text or a character that cannot belong to a path), so a sibling such as
  /// "/root2" is never rewritten.
  /// </summary>
  internal static string RemapOutputText(string text, Request request, bool escapeBraces = false) {
    if (request.LogicalRoot == null || request.SourceRoot == null || request.LogicalRoot == request.SourceRoot) {
      return text;
    }
    var from = request.LogicalRoot.Length > 1 ? request.LogicalRoot.TrimEnd('/') : request.LogicalRoot;
    var to = request.SourceRoot.Length > 1 ? request.SourceRoot.TrimEnd('/') : request.SourceRoot;
    if (from.Length == 0 || !text.Contains(from, StringComparison.Ordinal)) {
      return text;
    }
    if (escapeBraces) {
      to = to.Replace("{", "{{").Replace("}", "}}");
    }
    var result = new StringBuilder();
    var index = 0;
    while (index < text.Length) {
      var found = text.IndexOf(from, index, StringComparison.Ordinal);
      if (found < 0) {
        break;
      }
      var end = found + from.Length;
      var startsPath = found == 0 || !IsPathCharacter(text[found - 1]);
      // A root that already ends in a separator (the file system root) continues into its children.
      var endsPath = end == text.Length || from.EndsWith('/') || text[end] == '/' || !IsPathCharacter(text[end]) ||
        (text[end] == '.' && (end + 1 == text.Length || !IsPathCharacter(text[end + 1])));
      result.Append(text, index, found - index);
      result.Append(startsPath && endsPath ? to : from);
      index = end;
    }
    result.Append(text, index, text.Length - index);
    return result.ToString();
  }

  /// <summary>
  /// Maps logical-root paths in a queued diagnostic to the request's physical root. Diagnostics are built when
  /// a compilation is created and replayed to every request that reuses it, and snapshot directories can differ
  /// between those requests, so the mapping is applied at replay, to message parts rather than rendered text.
  /// Error id, range, level and source stay unchanged; request options map paths when locations are printed.
  /// </summary>
  internal static DafnyDiagnostic RemapDiagnostic(DafnyDiagnostic diagnostic, Request request) {
    if (request.LogicalRoot == null || request.SourceRoot == null || request.LogicalRoot == request.SourceRoot) {
      return diagnostic;
    }
    IReadOnlyList<string> Parts(string errorId, IReadOnlyList<string> parts) {
      // Without a catalogued message the first part is the format string, which string.Format will parse.
      IReadOnlyList<object> remaining = parts;
      DafnyDiagnostic.GetFormatMsgAndRemainingParts(errorId, ref remaining);
      var hasFormat = remaining.Count < parts.Count;
      return parts.Select((part, index) => RemapOutputText(part, request, hasFormat && index == 0)).ToList();
    }
    return diagnostic with {
      MessageParts = Parts(diagnostic.ErrorId, diagnostic.MessageParts),
      RelatedInformation = diagnostic.RelatedInformation
        .Select(related => related with { MessageParts = Parts(related.ErrorId, related.MessageParts) }).ToList()
    };
  }

  private static string Hash(string text) => Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(text))).ToLowerInvariant();
}
