#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using System.Threading;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Candidate pure-value membership observations; original native WD certification is still required.</summary>
public sealed class ContractRuntimeTypeEvidence {
  private sealed record Observation(Type Type, ContractValue Value, string Obligation, bool Passed);
  private readonly List<Observation> observations = [];
  private readonly Program original;
  private readonly string sourceSetHash;

  private ContractRuntimeTypeEvidence(Program original, string sourceSetHash) {
    this.original = original;
    this.sourceSetHash = sourceSetHash;
  }

  /// <summary>Fingerprints every original path and its actual contents, including imported declarations.</summary>
  public static string SourceSetHash(IReadOnlyList<ContractSource> sources) => ContractHarnessBuilder.Hash(
    JsonSerializer.Serialize(sources.OrderBy(source => source.Path, StringComparer.Ordinal)
      .Select(source => new { source.Path, ContentHash = ContractHarnessBuilder.Hash(source.Content) })));

  internal bool IsBoundTo(Program program, IReadOnlyList<ContractSource> sources) =>
    ReferenceEquals(original, program) && sourceSetHash == SourceSetHash(sources);

  /// <summary>Collects actual compiled type checks and binds their formal types to the original source declarations.</summary>
  public static ContractRuntimeTypeEvidence Collect(Program original, IReadOnlyList<ContractSource> originalSources,
    IReadOnlyDictionary<string, ContractRuntimeClause> clauses, IReadOnlyList<JsonElement> records,
    IReadOnlySet<string> compiledChecks, IReadOnlySet<string> draftedSymbols,
    CancellationToken cancellationToken = default, long? deadlineTimestamp = null,
    Action<string, string>? phaseObserver = null) {
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    var result = new ContractRuntimeTypeEvidence(original, SourceSetHash(originalSources));
    var owners = ContractRuntimeObligationTransformer.Members(original).ToDictionary(member => member.FullDafnyName);
    string? syntheticResultName = null;
    var bindings = new Dictionary<string, (string Name, Type Type)?>();
    var eligibleTypes = new Dictionary<string, bool>();
    foreach (var record in records) {
      ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
      if (record.ValueKind != JsonValueKind.Object || record.EnumerateObject().GroupBy(item => item.Name).Any(group => group.Count() != 1) ||
          !record.TryGetProperty("kind", out var kind) || kind.ValueKind != JsonValueKind.String || kind.GetString() != "check" ||
          !record.TryGetProperty("id", out var idNode) || idNode.ValueKind != JsonValueKind.String ||
          !record.TryGetProperty("passed", out var passed) || passed.ValueKind is not (JsonValueKind.True or JsonValueKind.False) ||
          !record.TryGetProperty("values", out var values) || values.ValueKind != JsonValueKind.Object) { continue; }
      var id = idNode.GetString()!;
      if (!bindings.TryGetValue(id, out var binding)) {
        binding = ContractPhaseRecorder.Measure(phaseObserver, "binding:" + id, cancellationToken, () => Bind(id));
        bindings.Add(id, binding);
      }
      if (binding is not { } formal || values.EnumerateObject().Count() != 1 || !values.TryGetProperty(formal.Name, out var serialized)) { continue; }
      ContractValue value;
      try {
        value = JsonSerializer.Deserialize<ContractValue>(serialized.GetRawText(), ContractJson.Options)!;
        if (value == null) { continue; }
        ContractModelCodec.Validate(value);
      } catch (Exception error) when (error is JsonException or ArgumentException) { continue; }
      var prior = result.observations.FindIndex(item => SameType(item.Type, formal.Type) && ContractModelCodec.ValuesEqual(item.Value, value));
      if (prior < 0) {
        result.observations.Add(new(formal.Type, value, id, passed.GetBoolean()));
      } else if (!passed.GetBoolean()) {
        // Repeated identical executions are expected; a contradiction can never authorize reuse.
        result.observations[prior] = result.observations[prior] with { Passed = false };
      }
    }
    ContractQueryDeadline.Check(deadlineTimestamp, cancellationToken);
    return result;

    (string Name, Type Type)? Bind(string id) {
      if (!clauses.TryGetValue(id, out var clause) || !clause.TypeConstraint || clause.Variables.Count != 1 ||
          clause.Variables[0] is not Formal diagnosticFormal ||
          clause.Obligation.DecisionMethod != ContractRuntimeDecisionMethod.Runtime ||
          !ContractRuntimeObligationTransformer.IsCompiled(compiledChecks, id) ||
          draftedSymbols.Contains(clause.Owner.FullDafnyName)) { return null; }
      if (!owners.TryGetValue(clause.Owner.FullDafnyName, out var owner) || owner is not MethodOrFunction callable ||
          clause.Owner.Origin.Uri != owner.Origin.Uri) { return null; }
      var source = originalSources.SingleOrDefault(candidate => candidate.Path == clause.Obligation.Path &&
        ContractSourceSnapshot.UriFor(candidate.Path) == owner.Origin.Uri);
      if (source == null || source.Sha256 != clause.OriginalSourceHash || clause.OriginalSourceSetHash != result.sourceSetHash) { return null; }
      // Membership binding needs the authoritative signature only. DescribeFunction
      // would clone the entire body and repeat whole-program fresh-name traversal.
      var formals = diagnosticFormal.InParam ? callable.Ins : callable switch {
        Method method => method.Outs,
        Function function => [function.Result ?? new Formal(function.Origin,
          syntheticResultName ??= ContractCallableSelector.FunctionResultName(original, function),
          function.ResultType, false, false, null)],
        _ => []
      };
      var formal = formals.SingleOrDefault(candidate => candidate.Name == diagnosticFormal.Name);
      if (formal == null || !SameType(formal.Type, diagnosticFormal.Type)) { return null; }
      var typeKey = TypeIdentity(formal.Type);
      if (!eligibleTypes.TryGetValue(typeKey, out var eligible)) {
        eligible = ContractInitialTypeProof.IsPure(formal.Type, []) &&
          !ContractRuntimeObligationTransformer.ExecutionReachable(original, [], [formal.Type])
            .Any(callable => draftedSymbols.Contains(callable.FullDafnyName));
        eligibleTypes.Add(typeKey, eligible);
      }
      if (!eligible) { return null; }
      return (formal.Name, formal.Type);
    }
  }

  /// <summary>Returns a matching successful runtime check; this alone does not certify the type's definitions.</summary>
  public string? Match(ContractValue value, Type type) => observations.FirstOrDefault(item => item.Passed &&
    SameType(item.Type, type) && ContractModelCodec.ValuesEqual(item.Value, value))?.Obligation;

  private static bool SameType(Type left, Type right) => TypeIdentity(left) == TypeIdentity(right);

  private static string TypeIdentity(Type type) {
    type = type.NormalizeExpandKeepConstraints();
    var kind = type switch {
      SetType set => set.Finite ? "set" : "iset",
      MapType map => map.Finite ? "map" : "imap",
      _ => type.GetType().Name
    };
    return type is UserDefinedType { ResolvedClass: { } declaration }
      ? declaration.GetType().Name + ":" + declaration.FullDafnyName + ":" + declaration.Origin.Uri +
        "<" + string.Join(",", type.TypeArgs.Select(TypeIdentity)) + ">"
      : kind + ":" + (type.TypeArgs.Count == 0 ? type.ToString() : string.Join(",", type.TypeArgs.Select(TypeIdentity)));
  }
}
