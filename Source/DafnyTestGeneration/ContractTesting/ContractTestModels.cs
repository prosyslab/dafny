using System;
using System.Collections.Generic;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractJson {
  public const int SchemaVersion = 1;
  public static readonly JsonSerializerOptions Options = new() {
    PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
    UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
    Converters = { new JsonStringEnumConverter(JsonNamingPolicy.SnakeCaseLower, allowIntegerValues: false) }
  };
}

public enum ContractValueKind { Integer, Bitvector, Boolean, Character, Sequence, Set, Multiset, Map, Datatype, Reference, Null }
public enum ContractTestStatus { Passed, Counterexample, InvalidInput, Unsupported, Inconclusive, Timeout, Cancelled, Error }
public enum ContractQueryOutcome { Sat, Unsat, Unknown, Timeout, Error }
public enum ContractQueryKind { PremiseConsistency, EntryPrecondition, ObservedPostcondition, CallPrecondition, ContractRealization, ClosedClause }

public sealed record ContractMapEntry([property: JsonRequired] ContractValue Key,
  [property: JsonRequired] ContractValue Value);
public sealed record ContractValue([property: JsonRequired] ContractValueKind Kind, string? Value = null,
  IReadOnlyList<ContractValue>? Items = null, string? Constructor = null,
  IReadOnlyDictionary<string, ContractValue>? Fields = null,
  IReadOnlyList<ContractMapEntry>? Entries = null, int? Width = null);
public sealed record ContractHeapObject(string Id, string Type, IReadOnlyDictionary<string, ContractValue> Fields,
  IReadOnlyList<int>? Dimensions = null, IReadOnlyList<ContractValue>? Elements = null);
public sealed record ContractSource(string Path, string Content, string Sha256);
public sealed record ContractDependency(string Path, string Sha256);
public enum ContractInputMode { Unit, EntryReachable }
public sealed record ContractEntry(string Symbol, IReadOnlyList<string>? TypeArguments = null,
  ContractValue? Receiver = null, ContractInputMode InputMode = ContractInputMode.Unit,
  string? ReachableFrom = null, ContractValue? ReachableReceiver = null, int ReachableInvocation = 0);
public sealed record ContractTestRequest(int SchemaVersion, IReadOnlyList<ContractSource> Sources,
  ContractEntry Entry, IReadOnlyDictionary<string, ContractValue> Inputs,
  IReadOnlyList<ContractHeapObject>? Heap = null, IReadOnlyList<ContractDependency>? Dependencies = null,
  int TimeoutMilliseconds = 30000);
public sealed record ContractSourceLocation(string Path, int Line, int Column, string Symbol, string Sha256);
public sealed record ContractQueryResult(ContractQueryKind Kind, ContractQueryOutcome Outcome, string Diagnostics);
// Process results contain only serializable evidence; resolved compiler objects never cross the boundary.
public sealed record ContractCompileResult(int SchemaVersion, ContractTestStatus Status, string Reason,
  string? AssemblyPath = null, string? AssemblySha256 = null, string? ObservationPath = null,
  ContractSourceLocation? Entry = null);
