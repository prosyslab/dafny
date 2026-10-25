#nullable enable
using System.Collections.Generic;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Selects source-view preparation or packet extraction.</summary>
public enum ContractRuntimeAuthoringAction { Prepare, Extract }

/// <summary>Reports the bounded source-authoring operation without changing campaign status.</summary>
public enum ContractRuntimeAuthoringStatus { Ready, Extracted, Unsupported, Error, Cancelled, Timeout }

/// <summary>Binds a private authoring view to exact original and prepared source snapshots.</summary>
public sealed record ContractRuntimeAuthoringManifest(
  [property: JsonRequired] IReadOnlyList<ContractDependency> OriginalSources,
  [property: JsonRequired] IReadOnlyList<ContractDependency> PreparedSources,
  [property: JsonRequired] IReadOnlyList<string> DraftSymbols,
  string? GeneratorSymbol = null,
  ContractDependency? RuntimeSource = null);

/// <summary>One additive native request for preparing or extracting a runtime source view.</summary>
public sealed record ContractRuntimeAuthoringRequest(
  [property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] ContractRuntimeAuthoringAction Action,
  [property: JsonRequired] IReadOnlyList<ContractSource> Sources,
  [property: JsonRequired] ContractEntry Entry,
  IReadOnlyList<ContractRuntimeDraft>? Drafts = null,
  ContractSource? Generator = null,
  IReadOnlyList<string>? RequestedDraftSymbols = null,
  IReadOnlyList<ContractSource>? AuthoredSources = null,
  ContractRuntimeAuthoringManifest? Manifest = null,
  int TimeoutMilliseconds = 30000,
  IReadOnlyList<ContractDependency>? TrustedSources = null);

/// <summary>Returns exact view snapshots or extracted legacy campaign packets.</summary>
public sealed record ContractRuntimeAuthoringResult(
  int SchemaVersion,
  ContractRuntimeAuthoringAction Action,
  ContractRuntimeAuthoringStatus Status,
  string Reason,
  IReadOnlyList<ContractSource>? Sources = null,
  ContractRuntimeAuthoringManifest? Manifest = null,
  IReadOnlyList<ContractRuntimeDraft>? Drafts = null,
  ContractSource? Generator = null);
