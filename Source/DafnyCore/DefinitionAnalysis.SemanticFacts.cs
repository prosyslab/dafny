#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public static partial class DefinitionAnalysis {
  private static DafnySemanticFacts SemanticFactsFor(
    DafnyOptions options,
    IReadOnlySet<Uri> analysisSourceUris,
    IReadOnlyList<DefinitionAnalysisResult> definitions,
    DefinitionSourceFacts sourceFacts) {
    var sources = analysisSourceUris
      .Where(uri => uri.IsFile)
      .Select(uri => Path.GetFullPath(uri.LocalPath))
      .Distinct(StringComparer.Ordinal)
      .OrderBy(path => path, StringComparer.Ordinal)
      .ToList();
    if (sources.Count == 0) {
      throw new InvalidOperationException(
        "definition-analysis semantic facts require at least one file source");
    }

    var sourceSet = sources.ToHashSet(StringComparer.Ordinal);
    var definitionsBySource = definitions
      .Where(definition => sourceSet.Contains(Path.GetFullPath(definition.SourcePath)))
      .GroupBy(definition => Path.GetFullPath(definition.SourcePath), StringComparer.Ordinal)
      .ToDictionary(group => group.Key, group => group.ToList(), StringComparer.Ordinal);
    var wiringBySource = sourceFacts.Imports
      .Select(import => (Source: import.SourcePath, Start: import.Start, End: import.End))
      .Concat(sourceFacts.Includes
        .Select(include => (Source: include.SourcePath, Start: include.Start, End: include.End)))
      .Where(item => sourceSet.Contains(Path.GetFullPath(item.Source)))
      .GroupBy(item => Path.GetFullPath(item.Source), StringComparer.Ordinal)
      .ToDictionary(group => group.Key, group => group.ToList(), StringComparer.Ordinal);

    var regions = new List<SourceFingerprintRegion>();
    var sourceRegionIds = new Dictionary<string, (string Full, string Declaration, string Scaffold)>(StringComparer.Ordinal);
    foreach (var source in sources) {
      var declarationSpans = definitionsBySource.TryGetValue(source, out var sourceDefinitions)
        ? sourceDefinitions.Select(definition => (definition.Start, definition.End)).ToList()
        : [];
      var wiringSpans = wiringBySource.TryGetValue(source, out var sourceWiring)
        ? sourceWiring.Select(item => (item.Start, item.End)).ToList()
        : [];
      sourceRegionIds[source] = (
        AddRegion(source),
        AddRegion(source, excludedSpans: declarationSpans),
        AddRegion(source, excludedSpans: declarationSpans.Concat(wiringSpans)));
    }

    var definitionRegionIds = new List<(DefinitionAnalysisResult Definition, string Declaration, string Contract, string Body)>();
    foreach (var definition in definitions) {
      var source = Path.GetFullPath(definition.SourcePath);
      if (!sourceSet.Contains(source)) {
        continue;
      }
      var contractEnd = definition.BodyStart ?? definition.End;
      var removableAttributes = definition.Attributes
        .Where(attribute => attribute.Name == "isolate_assertions" &&
                           attribute.Arguments.Count == 0 &&
                           definition.Start <= attribute.Start &&
                           attribute.Start < attribute.End &&
                           attribute.End <= contractEnd)
        .Select(attribute => (attribute.Start, attribute.End))
        .ToList();
      var bodyStart = definition.BodyStart ?? definition.Start;
      definitionRegionIds.Add((
        definition,
        AddRegion(source, includedSpan: (definition.Start, definition.End)),
        AddRegion(source, includedSpan: (definition.Start, contractEnd), excludedSpans: removableAttributes),
        AddRegion(source, includedSpan: (bodyStart, definition.End))));
    }

    var request = new SourceFingerprintRequest(regions);
    var fingerprintDocument = SourceFingerprint.Compute(options, request, out var error);
    if (fingerprintDocument == null) {
      throw new InvalidOperationException(
        error ?? "definition-analysis semantic fingerprinting failed");
    }
    var fingerprints = fingerprintDocument.Fingerprints.ToDictionary(
      result => result.Id,
      result => result.Sha256,
      StringComparer.Ordinal);

    return new DafnySemanticFacts(
      sources.Select(source => {
        var ids = sourceRegionIds[source];
        return new DafnySourceSemanticFingerprint(
          source,
          fingerprints[ids.Full],
          fingerprints[ids.Declaration],
          fingerprints[ids.Scaffold]);
      }).ToList(),
      definitionRegionIds.Select(item => new DafnyDefinitionSemanticFingerprint(
        item.Definition.SourcePath,
        item.Definition.FullName,
        item.Definition.Kind,
        fingerprints[item.Declaration],
        fingerprints[item.Contract],
        fingerprints[item.Body])).ToList());

    string AddRegion(
      string source,
      (int Start, int End)? includedSpan = null,
      IEnumerable<(int Start, int End)>? excludedSpans = null) {
      var id = $"region-{regions.Count}";
      regions.Add(new SourceFingerprintRegion(
        id,
        source,
        includedSpan == null ? null : new SourceFingerprintSpan(includedSpan.Value.Start, includedSpan.Value.End),
        (excludedSpans ?? []).Select(span => new SourceFingerprintSpan(span.Start, span.End)).ToList()));
      return id;
    }
  }
}
