#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public static partial class DefinitionAnalysis {
  /// <summary>Execution-local facts keyed by the resolver's reused module objects.</summary>
  /// <remarks>
  /// Declaration nodes depend on which sources are reported, so each analysis profile
  /// (reported sources and statement facts) owns separate node objects. A request only
  /// reads its own profile; profiles share nothing but the resolved modules they key on.
  /// </remarks>
  public sealed class SessionCache {
    private const int ProfileLimit = 4;

    private sealed class Profile {
      public Dictionary<ModuleDefinition, List<DefinitionNode>> Modules { get; } = new();
      public Dictionary<DefinitionNode, CallFacts> Calls { get; } = new();
      public Dictionary<DefinitionNode, DefinitionAnalysisResult> Results { get; } = new();
      public long LastUse { get; set; }

      public void PruneModules(Func<ModuleDefinition, bool> live) {
        foreach (var key in Modules.Keys.Where(key => !live(key)).ToList()) {
          Modules.Remove(key);
        }
        var nodes = Modules.Values.SelectMany(declarations => declarations).ToHashSet();
        foreach (var key in Calls.Keys.Where(key => !nodes.Contains(key)).ToList()) {
          Calls.Remove(key);
        }
        foreach (var key in Results.Keys.Where(key => !nodes.Contains(key)).ToList()) {
          Results.Remove(key);
        }
      }
    }

    private readonly Dictionary<string, Profile> profiles = new();
    private readonly HashSet<ModuleDefinition> usedModules = new();
    private Profile current = new();
    private long uses;
    public int ModuleHits { get; private set; }
    public int ModuleMisses { get; private set; }
    public int ProfileCount => profiles.Count;
    public int CachedModuleCount => profiles.Values.Sum(profile => profile.Modules.Count);

    public void Reset() {
      profiles.Clear();
      usedModules.Clear();
      current = new Profile();
    }

    internal void Begin(IReadOnlySet<Uri> sources, bool statements) {
      var requested = string.Join("\0", sources.Select(uri => uri.AbsoluteUri).OrderBy(uri => uri, StringComparer.Ordinal)) + statements;
      if (!profiles.TryGetValue(requested, out var profile)) {
        if (profiles.Count >= ProfileLimit) {
          profiles.Remove(profiles.MinBy(entry => entry.Value.LastUse).Key);
        }
        profiles[requested] = profile = new Profile();
      }
      profile.LastUse = ++uses;
      current = profile;
      ModuleHits = 0;
      ModuleMisses = 0;
      usedModules.Clear();
    }

    internal bool TryModule(ModuleDefinition module, out List<DefinitionNode>? declarations) {
      usedModules.Add(module);
      if (current.Modules.TryGetValue(module, out declarations)) {
        ModuleHits++;
        return true;
      }
      ModuleMisses++;
      return false;
    }

    internal void StoreModule(ModuleDefinition module, List<DefinitionNode> declarations) => current.Modules[module] = declarations;
    internal CallFacts Calls(DefinitionNode node, Func<CallFacts> create) {
      if (!current.Calls.TryGetValue(node, out var value)) {
        current.Calls[node] = value = create();
      }
      return value;
    }
    internal bool HasResult(DefinitionNode node) => current.Results.ContainsKey(node);
    internal DefinitionAnalysisResult Result(DefinitionNode node, Func<DefinitionAnalysisResult> create) {
      if (!current.Results.TryGetValue(node, out var value)) {
        current.Results[node] = value = create();
      }
      return value;
    }
    internal void Prune(IReadOnlyList<DefinitionNode> current) {
      var live = current.ToHashSet();
      foreach (var key in this.current.Calls.Keys.Where(key => !live.Contains(key)).ToList()) {
        this.current.Calls.Remove(key);
        this.current.Results.Remove(key);
      }
      // Every module of the analyzed program passed through TryModule. Modules the
      // resolver replaced are dead in every profile; unchanged ones stay reusable.
      foreach (var profile in profiles.Values) {
        profile.PruneModules(usedModules.Contains);
      }
    }
  }
}
