using DafnyDriver.Commands;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Program = Microsoft.Dafny.Program;

namespace DafnyDriver.Test;

public class ParserCacheCloneTests {
  private static readonly Uri Root = new("file:///parser-clone/root.dfy");
  private static readonly Uri Helper = new("file:///parser-clone/helper.dfy");
  private const string Source = """
    include "helper.dfy"
    module Main {
      function F(x: (int, int), a: array2<int>): (int, int) { (x.0 + 1, x.1) }
    }
    module Prefix.Child { function Value(): int { 3 } }
    """;

  // Forking retains warm entries but reconstructs token/options/include/delegate owners from immutable text.
  [Fact]
  public async Task ParserClonesOwnTheirTemplatesAndHitInheritedEntries() {
    var parentFiles = Files();
    var childFiles = Files();
    var siblingFiles = Files();
    var logger = new CacheLogger();
    var parent = new CachingParser(logger, parentFiles, Telemetry());
    var parentOptions = Options();
    var parentProgram = await Parse(parent, parentFiles, parentOptions);
    Assert.Equal(2, parent.CachedParseCount);

    // These references currently reach mutable parts of the branch-local cached template.
    MainModule(parentProgram).NameNode.StartToken.val = "ChangedParentToken";
    parentProgram.Files[0].Includes.Clear();
    var parentReads = parentFiles.ReadCount;
    var childOptions = Options();
    var siblingOptions = Options();
    var child = parent.Clone(childOptions, childFiles, Telemetry());
    var sibling = parent.Clone(siblingOptions, siblingFiles, Telemetry());
    Assert.Equal(parentReads, parentFiles.ReadCount);
    Assert.Equal(0, childFiles.ReadCount);
    Assert.Equal(0, siblingFiles.ReadCount);
    Assert.Equal(2, child.CachedParseCount);
    Assert.Equal(2, sibling.CachedParseCount);

    var childProgram = await Parse(child, childFiles, childOptions);
    var siblingProgram = await Parse(sibling, siblingFiles, siblingOptions);
    Assert.Equal(2, logger.Misses);
    Assert.Equal(4, logger.Hits);
    Assert.NotSame(MainModule(childProgram).NameNode.StartToken, MainModule(siblingProgram).NameNode.StartToken);
    Assert.NotSame(MainModule(childProgram).Options, MainModule(siblingProgram).Options);
    Assert.NotSame(parentOptions, MainModule(childProgram).Options);
    Assert.NotSame(childProgram.Files[0].Includes, siblingProgram.Files[0].Includes);
    Assert.NotSame(childProgram.Files[0].Includes[0].ParseOptions, siblingProgram.Files[0].Includes[0].ParseOptions);
    Assert.NotSame(childProgram.SystemModuleManager.SystemModule, siblingProgram.SystemModuleManager.SystemModule);
    var childFunction = childProgram.DefaultModuleDef.Descendants().OfType<Function>().Single(f => f.Name == "F");
    var siblingFunction = siblingProgram.DefaultModuleDef.Descendants().OfType<Function>().Single(f => f.Name == "F");
    Assert.NotSame(childFunction.Body, siblingFunction.Body);
    Assert.NotSame(childFunction.Body!.StartToken, siblingFunction.Body!.StartToken);
    MainModule(childProgram).NameNode.StartToken.val = "ChangedChildToken";
    MainModule(childProgram).Options.Set(MethodOrFunction.AllowExternalContracts, false);
    childProgram.Files[0].Includes.Clear();
    Assert.Equal("Main", MainModule(siblingProgram).NameNode.Value);
    Assert.Equal("Main", MainModule(siblingProgram).NameNode.StartToken.val);
    Assert.True(MainModule(siblingProgram).Options.Get(MethodOrFunction.AllowExternalContracts));
    Assert.Single(siblingProgram.Files[0].Includes);
    Assert.Contains(siblingProgram.DefaultModuleDef.Descendants().OfType<ModuleDecl>(), m => m.Name == "Helper");
  }

  // A child's changed filesystem and pruning leave the parent and a second child warm and usable.
  [Fact]
  public async Task ChildEditsAndPruningAreIndependent() {
    var parentFiles = Files();
    var childFiles = Files();
    var siblingFiles = Files();
    var parentOptions = Options();
    var childOptions = Options();
    var siblingOptions = Options();
    var parent = new CachingParser(NullLogger<ProgramParser>.Instance, parentFiles, Telemetry());
    await Parse(parent, parentFiles, parentOptions);
    var child = parent.Clone(childOptions, childFiles, Telemetry());
    var sibling = parent.Clone(siblingOptions, siblingFiles, Telemetry());
    childFiles.Values[Root] = "module Changed { function F(): int { 8 } }";
    var changed = await Parse(child, childFiles, childOptions);
    Assert.Contains(changed.DefaultModuleDef.Descendants().OfType<ModuleDecl>(), m => m.Name == "Changed");
    Assert.Equal(1, child.CachedParseCount);
    Assert.Equal(2, parent.CachedParseCount);
    Assert.Equal(2, sibling.CachedParseCount);
    Assert.Equal("Main", MainModule(await Parse(parent, parentFiles, parentOptions)).NameNode.Value);
    Assert.Equal("Main", MainModule(await Parse(sibling, siblingFiles, siblingOptions)).NameNode.Value);
  }

  // Copied access markers and mutable keys/values belong to separate caches.
  [Fact]
  public async Task CacheCloneCopiesMembershipKeysValuesAndPruningState() {
    var parent = new PruneIfNotUsedSinceLastPruneCache<byte[], Box>(new HashEquality());
    var key = new byte[] { 1, 2, 3, 4 };
    parent.Set(key, new Box(7));
    await parent.UseAndPrune(() => Task.FromResult(0), CancellationToken.None);
    byte[]? copiedKey = null;
    var child = parent.Clone(k => copiedKey = (byte[])k.Clone(), value => new Box(value.Value));
    var sibling = parent.Clone(k => (byte[])k.Clone(), value => new Box(value.Value));
    Assert.NotSame(key, copiedKey);
    Assert.True(child.TryGet([1, 2, 3, 4], out var childValue));
    childValue!.Value = 99;
    Assert.True(parent.TryGet([1, 2, 3, 4], out var parentValue));
    Assert.Equal(7, parentValue!.Value);
    await child.UseAndPrune(() => Task.FromResult(0), CancellationToken.None);
    await sibling.UseAndPrune(() => Task.FromResult(0), CancellationToken.None);
    Assert.Equal(1, parent.Count);
    Assert.Equal(1, child.Count);
    Assert.Equal(0, sibling.Count);
    child.Set([3, 4, 5, 6], new Box(3));
    Assert.Equal(1, parent.Count);
    Assert.Equal(2, child.Count);
  }

  // Active use is rejected immediately, and an idle copy does not inherit the source lock.
  [Fact]
  public async Task CacheCloneRequiresDrainedSourceAndOwnsItsGate() {
    var parent = new PruneIfNotUsedSinceLastPruneCache<int, Box>(EqualityComparer<int>.Default);
    var child = parent.Clone(k => k, value => new Box(value.Value));
    var release = new TaskCompletionSource();
    var running = parent.UseAndPrune(async () => { await release.Task; return 0; }, CancellationToken.None);
    try {
      Assert.Throws<InvalidOperationException>(() => parent.Clone(k => k, value => value));
      await child.UseAndPrune(() => Task.FromResult(0), CancellationToken.None);
    }
    finally {
      release.SetResult();
      await running;
    }
  }

  // Cancelling the first copied entry stops before the next and releases the source gate.
  [Fact]
  public void CancelledCloneStopsCopyingAndLeavesParentUsable() {
    var parent = new PruneIfNotUsedSinceLastPruneCache<int, Box>(EqualityComparer<int>.Default);
    parent.Set(1, new Box(1));
    parent.Set(2, new Box(2));
    using var cancellation = new CancellationTokenSource();
    var copiedEntries = 0;
    var error = Assert.Throws<OperationCanceledException>(() => parent.Clone(key => key, value => {
      copiedEntries++;
      cancellation.Cancel();
      return new Box(value.Value);
    }, cancellation.Token));
    Assert.Equal(cancellation.Token, error.CancellationToken);
    Assert.Equal(1, copiedEntries);
    Assert.Equal(2, parent.Count);
    var child = parent.Clone(key => key, value => new Box(value.Value));
    Assert.Equal(2, child.Count);
  }

  private static ModuleDecl MainModule(Program program) => program.DefaultModuleDef.SourceDecls.OfType<ModuleDecl>()
    .Single(module => module.NameNode.Value == "Main");

  private static DafnyOptions Options() {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(MethodOrFunction.AllowExternalContracts, true);
    return options;
  }

  private static CliTelemetryPublisher Telemetry() => new(NullLogger<TelemetryPublisherBase>.Instance);

  private static MemoryFiles Files() => new(new Dictionary<Uri, string> {
    [Root] = Source,
    [Helper] = "module Helper { function One(): int { 1 } }"
  });

  private static async Task<Program> Parse(CachingParser parser, MemoryFiles files, DafnyOptions options) {
    var reporter = new BatchErrorReporter(options);
    var file = DafnyFile.HandleDafnyFile(files, reporter, options, Root, Token.NoToken)!;
    var result = await parser.ParseFiles(Root.ToString(), [file], reporter, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(m => m.Message)));
    return result.Program;
  }

  private sealed class Box(int value) {
    public int Value { get; set; } = value;
  }

  private sealed class MemoryFiles(Dictionary<Uri, string> values) : IFileSystem {
    public Dictionary<Uri, string> Values { get; } = values;
    public int ReadCount { get; private set; }
    public FileSnapshot ReadFile(Uri uri) { ReadCount++; return new(new StringReader(Values[uri]), null); }
    public bool Exists(Uri path) => Values.ContainsKey(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }

  private sealed class CacheLogger : ILogger<ProgramParser> {
    public int Hits { get; private set; }
    public int Misses { get; private set; }
    public IDisposable BeginScope<TState>(TState state) => NullScope.Instance;
    public bool IsEnabled(LogLevel logLevel) => true;
    public void Log<TState>(LogLevel level, EventId eventId, TState state, Exception? exception, Func<TState, Exception?, string> formatter) {
      var message = formatter(state, exception);
      if (message.StartsWith("Parse cache hit for", StringComparison.Ordinal)) { Hits++; }
      if (message.StartsWith("Parse cache miss for", StringComparison.Ordinal)) { Misses++; }
    }
  }

  private sealed class NullScope : IDisposable {
    public static readonly NullScope Instance = new();
    public void Dispose() { }
  }
}
