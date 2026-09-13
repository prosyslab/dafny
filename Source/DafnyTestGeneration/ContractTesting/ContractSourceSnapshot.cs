using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Dafny;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Microsoft.Extensions.Logging.Abstractions;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Native source parsing against an immutable, closed collection of supplied files.</summary>
public static class ContractSourceSnapshot {
  public static Uri UriFor(string path) => new(Path.GetFullPath(path));

  public static ContractSource Find(IReadOnlyList<ContractSource> sources, Uri uri) =>
    sources.Single(source => UriFor(source.Path) == uri);

  public static IReadOnlyList<ContractSource> Replace(IReadOnlyList<ContractSource> sources, string path, string content) {
    Validate(sources);
    var uri = UriFor(path);
    if (sources.Count(source => UriFor(source.Path) == uri) != 1) {
      throw new ArgumentException("A diagnostic replacement must identify exactly one supplied source snapshot.");
    }
    return sources.Select(source => UriFor(source.Path) == uri
      ? source with { Content = content, Sha256 = ContractHarnessBuilder.Hash(content) } : source).ToList();
  }

  // As with the native parser, errors leave a parsed AST; callers must check the
  // reporter before accessing resolver-populated members such as RawModules().
  public static async Task<Program> ParseAsync(ErrorReporter reporter, IReadOnlyList<ContractSource> sources,
    CancellationToken cancellationToken, bool resolve = true) {
    Validate(sources);
    var files = sources.ToDictionary(source => UriFor(source.Path), source => source.Content);
    var fileSystem = new SnapshotFileSystem(files);
    // Includes remain native parser operations, but every file operation is closed
    // over the authorized snapshot dictionary rather than the process filesystem.
    reporter.Options.DisallowIncludes = false;
    var roots = sources.Select(source => DafnyFile.HandleDafnyFile(fileSystem, reporter, reporter.Options,
      UriFor(source.Path), Token.NoToken, false)).ToList();
    var parsed = await new ProgramParser(NullLogger<ProgramParser>.Instance, fileSystem)
      .ParseFiles(sources[0].Path, roots, reporter, cancellationToken);
    if (resolve && reporter.ErrorCount == 0) {
      await new ProgramResolver(parsed.Program).Resolve(cancellationToken);
    }
    return parsed.Program;
  }

  private static void Validate(IReadOnlyList<ContractSource> sources) {
    if (sources.Count == 0 || sources.Any(source => source == null || string.IsNullOrWhiteSpace(source.Path) ||
          source.Content == null || ContractHarnessBuilder.Hash(source.Content) != source.Sha256)) {
      throw new ArgumentException("Source snapshots require paths, content and matching hashes.");
    }
    if (sources.Select(source => UriFor(source.Path)).Distinct().Count() != sources.Count) {
      throw new ArgumentException("Source snapshot paths must have distinct canonical identities.");
    }
  }

  private sealed class SnapshotFileSystem(IReadOnlyDictionary<Uri, string> files) : IFileSystem {
    public FileSnapshot ReadFile(Uri uri) => files.TryGetValue(uri, out var content)
      ? new FileSnapshot(new StringReader(content), null)
      : throw new FileNotFoundException("The include is outside the supplied source snapshots.", uri.LocalPath);

    public bool Exists(Uri path) => files.ContainsKey(path);

    public DirectoryInfoBase GetDirectoryInfoBase(string root) =>
      new InMemoryDirectoryInfoFromDotNet8(root, files.Keys.Select(uri => uri.LocalPath));
  }
}
