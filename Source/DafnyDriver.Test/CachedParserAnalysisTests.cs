using System.Text.Json;
using DafnyDriver.Commands;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Xunit;
using Program = Microsoft.Dafny.Program;

namespace DafnyDriver.Test;

public class CachedParserAnalysisTests {
  private static readonly Uri Root = new("file:///workspace/clone-cache/root.dfy");
  private static readonly Uri Include = new("file:///workspace/clone-cache/helper.dfy");
  private const string Source = """
    include "helper.dfy"
    module Main {
      import Helper
      function Render(x: int): int
        requires x >= 0
        ensures Render(x) >= x
      { x + Helper.One() }
      function Next(x: int): int { x + 1 } by method { return x + 1; }
      lemma Valid(x: int) { assert x + 1 > x; }
      module Nested { function Value(): int { 2 } }
    }
    module Prefix.Child { function Value(): int { 3 } }
    """;

  // The real cached parser must preserve complete analysis on misses, hits and changed included input.
  [Fact]
  public async Task CachedParserFullAnalysisMatchesOrdinaryParserAcrossEdits() {
    var files = new MemoryFiles(new Dictionary<Uri, string> {
      [Root] = Source,
      [Include] = "module Helper { function One(): int { 1 } }\n"
    });
    var logger = new CacheLogger();
    var cached = new CachingParser(logger, files, new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance));
    var resolutionCache = new ResolutionCache();
    var facts = new DefinitionAnalysis.SessionCache();
    var expected = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    var cold = await Analyze(cached, files, resolutionCache, facts);
    var warm = await Analyze(cached, files, resolutionCache, facts);
    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(cold));
    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(warm));
    Assert.Equal(2, logger.Misses);
    Assert.Equal(2, logger.Hits);
    Assert.True(facts.ModuleHits > 0);
    Assert.True(cold.Document.SourceFacts.Modules.Count >= 4);
    var render = Assert.Single(cold.Document.Definitions.Where(definition => definition.Name == "Render"));
    Assert.NotNull(render.BodyStart);
    Assert.NotEmpty(render.SourceModules);
    Assert.NotEmpty(render.LocalIncludedModules);
    var semantic = Assert.Single(cold.Document.SourceFacts.SemanticFacts!.Definitions.Where(definition => definition.FullName == "Main.Render"));
    Assert.NotEqual(semantic.ContractSha256, semantic.BodySha256);

    files.Values[Include] = "module Helper { function One(): int { 2 } }\n";
    var edited = await Analyze(cached, files, resolutionCache, facts);
    var expectedEdit = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    Assert.Equal(JsonSerializer.Serialize(expectedEdit), JsonSerializer.Serialize(edited));
    Assert.Equal(3, logger.Misses);
    Assert.Equal(3, logger.Hits);
    Assert.True(facts.ModuleHits > 0);

    files.Values[Root] = Source.Replace("{ x + Helper.One() }", "\n{ x + Helper.One() + 1 }");
    var moved = await Analyze(cached, files, resolutionCache, facts);
    var expectedMoved = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    Assert.Equal(JsonSerializer.Serialize(expectedMoved), JsonSerializer.Serialize(moved));
    Assert.NotEqual(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(moved));
    Assert.NotEqual(render.BodyStart,
      Assert.Single(moved.Document.Definitions.Where(definition => definition.Name == "Render")).BodyStart);
    Assert.Equal(4, logger.Misses);
    Assert.Equal(4, logger.Hits);
  }

  // Reused exports keep their resolved owners and complete facts across root sets and source edits.
  [Fact]
  public async Task CachedExportsPreserveResolvedOwnersAndFullAnalysisAcrossEdits() {
    const string importer = """
      include "helper.dfy"
      module Main {
        import Helper`Public
        export reveals *
        function Render(): int { Helper.One() + 1 }
      }
      module Empty { export Empty }
      """;
    const string dependency = """
      module Helper {
        export reveals *
        export Public extends Helper
        opaque function Hidden(): int { 1 }
        function One(): int { Hidden() }
        lemma RevealHidden() { reveal Hidden; }
      }
      """;
    var files = new MemoryFiles(new Dictionary<Uri, string> { [Root] = importer, [Include] = dependency });
    var cached = new CachingParser(new CacheLogger(), files,
      new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance));
    var resolutionCache = new ResolutionCache();
    var facts = new DefinitionAnalysis.SessionCache();
    IReadOnlyList<Uri> roots = [Root];

    // A resolve-only request warms native module objects without memoized analysis hiding a bad owner.
    var (resolved, reporter) = await Parse(cached, files, roots);
    await Resolve(resolved, reporter, resolutionCache);
    var original = await AssertParity();
    roots = [Root, Include];
    await AssertParity();
    Assert.True(facts.ModuleHits > 0);

    files.Values[Include] = dependency.Replace("Hidden(): int { 1 }", "Hidden(): int { 2 }");
    var changedDependency = await AssertParity();
    Assert.NotEqual(JsonSerializer.Serialize(original), JsonSerializer.Serialize(changedDependency));

    files.Values[Root] = importer.Replace("Helper.One() + 1", "Helper.One() + 2");
    var changedImporter = await AssertParity();
    Assert.NotEqual(JsonSerializer.Serialize(changedDependency), JsonSerializer.Serialize(changedImporter));
    Assert.True(facts.ModuleHits > 0);

    async Task<Snapshot> AssertParity() {
      var expected = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files, roots: roots);
      var fresh = await Analyze(cached, files, resolutionCache, new DefinitionAnalysis.SessionCache(), roots);
      var reused = await Analyze(cached, files, resolutionCache, facts, roots);
      var warm = await Analyze(cached, files, resolutionCache, facts, roots);
      Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(fresh));
      Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(reused));
      Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(warm));
      var exports = warm.Document.Definitions.Where(definition => definition.Kind == "export").ToList();
      Assert.Equal(4, exports.Count);
      Assert.All(exports, definition => Assert.NotNull(definition.BodyVisibility));
      var publicExport = Assert.Single(exports.Where(definition => definition.FullName == "Helper.Public"));
      Assert.Contains("Helper.Hidden", publicExport.BodyVisibility!.RevealedFunctions);
      Assert.Contains("Helper.RevealHidden", publicExport.BodyVisibility.ReferencedDeclarations);
      var emptyExport = Assert.Single(exports.Where(definition => definition.FullName == "Empty.Empty"));
      Assert.Empty(emptyExport.BodyVisibility!.RevealedFunctions);
      Assert.Empty(emptyExport.BodyVisibility.ReferencedDeclarations);
      Assert.False(emptyExport.BodyVisibility.RevealsAllFunctions);
      return warm;
    }
  }

  // Failed exports remain unresolved on cache hits, and repairing their source restores complete analysis.
  [Fact]
  public async Task CachedFailedExportStaysUnresolvedUntilDependencyIsRepaired() {
    const string dependency = "module Helper { export provides Missing function One(): int { 1 } }\n";
    var files = new MemoryFiles(new Dictionary<Uri, string> {
      [Root] = "include \"helper.dfy\"\nmodule Main { import Helper function Render(): int { Helper.One() } }\n",
      [Include] = dependency
    });
    var cached = new CachingParser(new CacheLogger(), files,
      new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance));
    var resolutionCache = new ResolutionCache();
    var cold = await FailedResolution();
    var warm = await FailedResolution();
    Assert.Equal(cold.Errors, warm.Errors);
    Assert.Same(cold.Export, warm.Export);

    files.Values[Include] = dependency.Replace("provides Missing", "provides One");
    var (repaired, reporter) = await Parse(cached, files);
    await Resolve(repaired, reporter, resolutionCache);
    var repairedExport = Assert.Single(repaired.DefaultModuleDef.Descendants().OfType<ModuleExportDecl>());
    Assert.NotSame(cold.Export, repairedExport);
    var expected = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    var facts = new DefinitionAnalysis.SessionCache();
    var fresh = await Analyze(cached, files, resolutionCache, facts);
    var reused = await Analyze(cached, files, resolutionCache, facts);
    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(fresh));
    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(reused));
    Assert.NotNull(Assert.Single(reused.Document.Definitions.Where(definition => definition.Kind == "export")).BodyVisibility);

    async Task<(int Errors, ModuleExportDecl Export)> FailedResolution() {
      var (program, failedReporter) = await Parse(cached, files);
      Microsoft.Dafny.Type.ResetScopes();
      await new CachingResolver(program, NullLogger<CachingResolver>.Instance,
        new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance), resolutionCache).Resolve(CancellationToken.None);
      Assert.True(failedReporter.ErrorCount > 0);
      var export = Assert.Single(program.DefaultModuleDef.Descendants().OfType<ModuleExportDecl>());
      Assert.Same(export.Signature.ModuleDef, export.EnclosingModuleDefinition);
      Assert.False(export.EnclosingModuleDefinition.SuccessfullyResolved);
      return (failedReporter.ErrorCount, export);
    }
  }

  // Refining function ellipses survive parser-cache cloning and resolve like the ordinary source.
  [Fact]
  public async Task CachedParserPreservesAuthoredRefiningFunctionSignature() {
    const string source = "abstract module Base { function F(x:int):int }\n" +
      "module Refined refines Base { function F... { x + 1 } }\n";
    var files = new MemoryFiles(new Dictionary<Uri, string> { [Root] = source });
    var cached = new CachingParser(new CacheLogger(), files, new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance));
    // The baseline full-analysis exporter cannot handle the replaced source-roster member's null owner.
    // Compare authored shape and actual resolution here; complete documents are covered above.
    var expected = await RefiningShape(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    Assert.Equal(expected, await RefiningShape(cached, files));
    Assert.Equal(expected, await RefiningShape(cached, files));
  }

  // Resolving @Options on a returned module cannot mutate the parser's cached attribute graph.
  [Fact]
  public async Task CachedModuleAttributesRemainUnresolvedAndIndependentlyOwned() {
    var files = new MemoryFiles(new Dictionary<Uri, string> {
      [Root] = "@Options(\"--function-syntax:3\") module Configured { function F():int { 1 } }\n"
    });
    var logger = new CacheLogger();
    var cached = new CachingParser(logger, files, new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance));
    var (first, firstReporter) = await Parse(cached, files);
    var firstModule = Assert.Single(first.DefaultModuleDef.Descendants().OfType<ModuleDefinition>().Where(module => module.Name == "Configured"));
    var firstAttribute = Assert.IsType<UserSuppliedAtAttribute>(firstModule.Attributes);
    Assert.False(firstAttribute.Builtin);
    Microsoft.Dafny.Type.ResetScopes();
    await new ProgramResolver(first).Resolve(CancellationToken.None);
    Assert.True(firstReporter.ErrorCount == 0, string.Join("\n", firstReporter.AllMessages.Select(message => message.Message)));
    Assert.True(firstAttribute.Builtin);
    var (second, _) = await Parse(cached, files);
    var secondModule = Assert.Single(second.DefaultModuleDef.Descendants().OfType<ModuleDefinition>().Where(module => module.Name == "Configured"));
    var secondAttribute = Assert.IsType<UserSuppliedAtAttribute>(secondModule.Attributes);
    Assert.NotSame(firstModule.NameNode, secondModule.NameNode);
    Assert.NotSame(firstAttribute, secondAttribute);
    Assert.NotSame(firstAttribute.Arg, secondAttribute.Arg);
    Assert.False(secondAttribute.Builtin);
    Assert.Null(secondAttribute.Arg.PreType);
    Assert.Equal(1, logger.Misses);
    Assert.Equal(1, logger.Hits);
    var expected = await Analyze(new ProgramParser(NullLogger<ProgramParser>.Instance, files), files);
    Assert.Equal(JsonSerializer.Serialize(expected), JsonSerializer.Serialize(await Analyze(cached, files)));
  }

  private sealed record Snapshot(string Parsed, DefinitionAnalysisDocument Document);

  private static async Task<string> RefiningShape(ProgramParser parser, MemoryFiles files) {
    var (program, reporter) = await Parse(parser, files);
    var sources = files.Values.Keys.ToHashSet();
    var parsedShape = new {
      Spans = DefinitionAnalysis.AnalyzeSpans(program, sources),
      Functions = program.DefaultModuleDef.Descendants().OfType<Function>()
        .Select(function => new {
          function.Name,
          function.SignatureIsOmitted,
          BodyStart = function.BodyStartTok.pos
        }).ToList()
    };
    Assert.Contains(parsedShape.Functions, function => function.SignatureIsOmitted);
    Microsoft.Dafny.Type.ResetScopes();
    await new ProgramResolver(program).Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    var resolvedFunctions = SymbolExtensions.GetSymbolDescendants(program.DefaultModule).OfType<Function>()
      .Select(function => new {
        function.Name,
        function.SignatureIsOmitted,
        Parameters = function.Ins.Select(formal => new { formal.Name, Type = formal.Type.ToString() }).ToList(),
        ResultType = function.ResultType.ToString(),
        BodyStart = function.BodyStartTok.pos,
        Body = function.Body?.Origin.pos
      }).ToList();
    Assert.Contains(resolvedFunctions, function => function.Name == "F" && function.Body != null &&
      function.Parameters.Any(parameter => parameter.Name == "x"));
    return JsonSerializer.Serialize(new { Parsed = parsedShape, Resolved = resolvedFunctions });
  }

  private static async Task<Snapshot> Analyze(ProgramParser parser, MemoryFiles files,
    ResolutionCache? resolutionCache = null, DefinitionAnalysis.SessionCache? facts = null,
    IReadOnlyList<Uri>? roots = null) {
    var (program, reporter) = await Parse(parser, files, roots);
    var sources = files.Values.Keys.ToHashSet();
    var parsedShape = JsonSerializer.Serialize(new {
      Spans = DefinitionAnalysis.AnalyzeSpans(program, sources),
      Functions = program.DefaultModuleDef.Descendants().OfType<Function>()
        .Select(function => new {
          function.Name,
          function.SignatureIsOmitted,
          BodyStart = function.BodyStartTok.pos,
          ByMethod = function.ByMethodTok?.pos
        }).ToList()
    });
    await Resolve(program, reporter, resolutionCache);
    var targets = SymbolExtensions.GetSymbolDescendants(program.DefaultModule).OfType<ICanVerify>()
      .Where(target => sources.Contains(target.Origin.Uri) && !target.Origin.IsCopy && target.ShouldVerify).ToList();
    var document = DefinitionAnalysis.AnalyzeDocument(program, sources, includeStatements: true,
      includeSemanticFacts: true, verificationTargets: targets, sessionCache: facts,
      sourceSnapshots: files.Values.ToDictionary(file => file.Key.LocalPath, file => file.Value));
    return new Snapshot(parsedShape, document);
  }

  private static async Task Resolve(Program program, BatchErrorReporter reporter, ResolutionCache? resolutionCache) {
    Microsoft.Dafny.Type.ResetScopes();
    ProgramResolver resolver = resolutionCache == null ? new ProgramResolver(program) :
      new CachingResolver(program, NullLogger<CachingResolver>.Instance,
        new CliTelemetryPublisher(NullLogger<TelemetryPublisherBase>.Instance), resolutionCache);
    await resolver.Resolve(CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    foreach (var export in program.DefaultModuleDef.Descendants().OfType<ModuleExportDecl>()) {
      var owner = export.EnclosingModuleDefinition;
      Assert.Same(export.Signature.ModuleDef, owner);
      Assert.True(owner.SuccessfullyResolved);
      Assert.Contains(owner.TopLevelDecls, declaration => ReferenceEquals(declaration, export));
    }
  }

  private static async Task<(Program Program, BatchErrorReporter Reporter)> Parse(ProgramParser parser, MemoryFiles files,
    IReadOnlyList<Uri>? roots = null) {
    var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.Set(MethodOrFunction.AllowExternalContracts, true);
    var reporter = new BatchErrorReporter(options);
    var rootFiles = (roots ?? [Root]).Select(uri =>
      DafnyFile.HandleDafnyFile(files, reporter, options, uri, Token.NoToken)!).ToList();
    var parsed = await parser.ParseFiles(Root.ToString(), rootFiles, reporter, CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    return (parsed.Program, reporter);
  }

  private sealed class MemoryFiles(Dictionary<Uri, string> values) : IFileSystem {
    public Dictionary<Uri, string> Values { get; } = values;
    public FileSnapshot ReadFile(Uri uri) => new(new StringReader(Values[uri]), null);
    public bool Exists(Uri path) => Values.ContainsKey(path);
    public DirectoryInfoBase GetDirectoryInfoBase(string root) => throw new InvalidOperationException("Unexpected directory lookup.");
  }
  private sealed class CacheLogger : ILogger<ProgramParser> {
    public int Hits { get; private set; }
    public int Misses { get; private set; }
    public IDisposable BeginScope<TState>(TState state) => NullScope.Instance;
    public bool IsEnabled(LogLevel level) => true;
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
