using System;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class InferModifiesCachingTest {
  private static readonly Uri First = new("file:///cache-test/first.dfy");
  private static readonly Uri Second = new("file:///cache-test/second.dfy");
  private static readonly Guid DefaultModuleId = Guid.NewGuid();

  // Changing one source's eligibility invalidates its importers but retains an independent module.
  [Fact]
  public async Task MembershipChangesInvalidateOnlyRelevantModules() {
    var sources = ImmutableDictionary<Uri, string>.Empty
      .Add(First, "module A { class Cell { var x: int method Write() { x := 1; } } }")
      .Add(Second, "module Dep { import A } module Stable { method M() {} }");
    var fixture = new Fixture(sources);
    var first = await fixture.Resolve(false);
    var library = await fixture.Resolve(true);
    var restored = await fixture.Resolve(false);

    Assert.NotSame(Module(first, "A"), Module(library, "A"));
    Assert.NotSame(Module(library, "A"), Module(restored, "A"));
    Assert.NotSame(Module(first, "Dep"), Module(library, "Dep"));
    Assert.NotSame(Module(library, "Dep"), Module(restored, "Dep"));
    Assert.Same(Module(first, "Stable"), Module(library, "Stable"));
    Assert.Same(Module(library, "Stable"), Module(restored, "Stable"));
    Assert.Single(Method(first, "A", "Write").Mod.Expressions!);
    Assert.Empty(Method(library, "A", "Write").Mod.Expressions!);
    Assert.Single(Method(restored, "A", "Write").Mod.Expressions!);
  }

  // The shared default module uses each method's own source URI when eligibility changes.
  [Fact]
  public async Task SharedDefaultModuleTracksAllMethodOrigins() {
    var sources = ImmutableDictionary<Uri, string>.Empty
      .Add(First, "class FirstCell { var x: int method WriteFirst() { x := 1; } }")
      .Add(Second, "class SecondCell { var x: int method WriteSecond() { x := 1; } }");
    var fixture = new Fixture(sources);
    var first = await fixture.Resolve(false);
    var warm = await fixture.Resolve(false);
    var library = await fixture.Resolve(true);
    var restored = await fixture.Resolve(false);

    Assert.Same(first.DefaultModuleDef, warm.DefaultModuleDef);
    Assert.NotSame(first.DefaultModuleDef, library.DefaultModuleDef);
    Assert.NotSame(library.DefaultModuleDef, restored.DefaultModuleDef);
    Assert.Single(Method(first, "_module", "WriteFirst").Mod.Expressions!);
    Assert.Empty(Method(library, "_module", "WriteFirst").Mod.Expressions!);
    Assert.Single(Method(library, "_module", "WriteSecond").Mod.Expressions!);
    Assert.Single(Method(restored, "_module", "WriteFirst").Mod.Expressions!);
  }

  private static ModuleDefinition Module(Program program, string name) =>
    program.ModuleSigs.Keys.Single(module => module.Name == name);

  private static Method Method(Program program, string moduleName, string name) =>
    Module(program, moduleName).TopLevelDecls.OfType<TopLevelDeclWithMembers>()
      .SelectMany(decl => decl.Members).OfType<Method>().Single(method => method.Name == name);

  private sealed class Fixture {
    private readonly DafnyOptions options = new(DafnyOptions.Default);
    private readonly IFileSystem fileSystem;
    private readonly CachingParser parser;
    private readonly ResolutionCache cache = new();
    private readonly Telemetry telemetry = new();

    public Fixture(ImmutableDictionary<Uri, string> sources) {
      options.ApplyDefaultOptionsWithoutSettingsDefault();
      options.Set(CommonOptionBag.InferModifiesOption, true);
      fileSystem = new InMemoryFileSystem(sources);
      parser = new CachingParser(NullLogger<ProgramParser>.Instance, fileSystem, telemetry);
    }

    public async Task<Program> Resolve(bool firstIsLibrary) {
      var reporter = new BatchErrorReporter(options);
      var files = new[] {
        DafnyFile.HandleDafnyFile(fileSystem, reporter, options, First, Token.NoToken, firstIsLibrary, false)!,
        DafnyFile.HandleDafnyFile(fileSystem, reporter, options, Second, Token.NoToken, false)!
      };
      var program = (await parser.ParseFiles("cache-test", files, reporter, CancellationToken.None)).Program;
      // Parsing allocates a new default declaration each time. Give this test a stable
      // identity so that a cache hit would be possible for the shared default module.
      program.DefaultModule = new LiteralModuleDecl(options, program.DefaultModuleDef, null, DefaultModuleId);
      await new CachingResolver(program, NullLogger<CachingResolver>.Instance, telemetry, cache)
        .Resolve(CancellationToken.None);
      Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
      return program;
    }
  }

  private sealed class Telemetry() : TelemetryPublisherBase(NullLogger<TelemetryPublisherBase>.Instance) {
    public override void PublishTelemetry(ImmutableDictionary<string, object> data) { }
  }
}
