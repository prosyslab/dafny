#nullable enable
using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractScreenAction { Inspect, Screen }
public enum ContractScreenQuestion { InputDomain, MethodRealizability, LemmaImplication, CallerSufficiency }
public enum ContractScreenStatus { Completed, Partial, Unsupported, InvalidInput, Timeout, Cancelled, Error }
public enum ContractScreenDomain { Admissible, PreconditionRejected, InvalidInput, PremiseInconsistent, Unsupported, Unknown, Timeout, Cancelled, Error }
public enum ContractScreenProperty { NotChecked, Realizable, Unrealizable, ImplicationHolds, ImplicationViolated, Unsupported, Unknown, Timeout, Cancelled, Error }

/// <summary>Bounds one serial, diagnostic-only attempt.</summary>
public sealed record ContractScreenBudgets(int AttemptMilliseconds = 30000, int QueryMilliseconds = 5000);
/// <summary>One concrete typed input, with no proposed outputs or user assertions.</summary>
public sealed record ContractScreenCase([property: JsonRequired] string Id,
  [property: JsonRequired] IReadOnlyDictionary<string, ContractValue> Inputs);
/// <summary>Binds inspection to complete original source and native diagnostic preparation.</summary>
public sealed record ContractScreenBinding(string SourceSetHash, string TargetIdentity,
  string DeclarationFingerprint, string ContractFingerprint, string ContextIdentity,
  string PreparationPolicyVersion, string ProducerIdentity, string OptionsIdentity);
/// <summary>The standalone inspect/screen protocol, independent of runtime campaigns.</summary>
public sealed record ContractScreenRequest([property: JsonRequired] int SchemaVersion,
  [property: JsonRequired] ContractScreenAction Action,
  [property: JsonRequired] IReadOnlyList<ContractSource> Sources,
  [property: JsonRequired] ContractEntry Target,
  [property: JsonRequired] IReadOnlyList<ContractDependency> Dependencies,
  [property: JsonRequired] ContractScreenQuestion Question,
  ContractScreenBinding? Binding = null, IReadOnlyList<ContractScreenCase>? Cases = null,
  ContractScreenBudgets? Budgets = null);
public sealed record ContractScreenFormal(string Name, string Type, bool Ghost);
public sealed record ContractScreenTargetDescriptor(string Symbol, string Kind,
  IReadOnlyList<ContractScreenFormal> Inputs, IReadOnlyList<ContractScreenFormal> Outputs,
  IReadOnlyList<string> Requires, IReadOnlyList<string> Ensures);
/// <summary>Syntax support is distinct from completed logical dependency certification.</summary>
public sealed record ContractScreenCapability(bool Supported, IReadOnlyList<string> ReasonCodes,
  IReadOnlyList<string> SupportedFeatures, bool CertificationPending,
  ContractScreenTargetDescriptor? Target = null);
/// <summary>Retains the independent domain and property decisions for one requested case.</summary>
public sealed record ContractScreenCaseResult(string Id, ContractScreenDomain Domain,
  ContractScreenProperty Property, IReadOnlyList<string> ReasonCodes,
  IReadOnlyList<string> EffectiveOptionsIdentities, IReadOnlyDictionary<string, ContractValue> Inputs,
  [property: JsonRequired] IReadOnlyList<string> QueryIdentities);
public sealed record ContractScreenCounts(int Requested, int Admissible, int PreconditionRejected,
  int Decided, int Undecided);
/// <summary>Finite diagnostic evidence; completed never means a universal contract proof.</summary>
public sealed record ContractScreenResult(int SchemaVersion, ContractScreenAction Action,
  ContractScreenQuestion Question, ContractScreenStatus Status, ContractScreenBinding? Binding,
  ContractScreenCapability Capability, IReadOnlyList<ContractScreenCaseResult> Cases,
  ContractScreenCounts Counts, IReadOnlyList<string> Diagnostics,
  [property: JsonRequired] IReadOnlyList<string> DependencyOptionsIdentities);

/// <summary>Checks protocol bounds without parsing Dafny, reading files or invoking a solver.</summary>
public static class ContractScreenValidation {
  public const int MaximumRequestBytes = 1024 * 1024;
  public const int MaximumCases = 32;
  public const int MaximumDiagnosticCharacters = 16384;

  /// <summary>Validates lexical values and duplicate numeric collection keys by their actual Dafny values.</summary>
  public static void ValidateConcreteValue(ContractValue value) {
    ContractModelCodec.Validate(value);
    _ = ContractModelCodec.ToDafny(value);
    // Preserve the caller's payload for identity/echo; canonicalization is local to duplicate validation.
    ContractModelCodec.Validate(Canonical(value));

    static ContractValue Canonical(ContractValue item) => item with {
      Value = item.Kind is ContractValueKind.Integer or ContractValueKind.Bitvector
        ? BigInteger.Parse(item.Value!, CultureInfo.InvariantCulture).ToString(CultureInfo.InvariantCulture) : item.Value,
      Items = item.Items?.Select(Canonical).ToList(),
      Fields = item.Fields?.ToDictionary(pair => pair.Key, pair => Canonical(pair.Value)),
      Entries = item.Entries?.Select(entry => new ContractMapEntry(Canonical(entry.Key), Canonical(entry.Value))).ToList()
    };
  }

  public static void Validate(ContractScreenRequest request) {
    if (request == null || request.SchemaVersion != 1 || !Enum.IsDefined(request.Action) ||
        !Enum.IsDefined(request.Question) || request.Sources == null || request.Sources.Count == 0 ||
        request.Target == null || string.IsNullOrWhiteSpace(request.Target.Symbol) || request.Dependencies == null) {
      throw new ArgumentException("invalid_request");
    }
    var budgets = request.Budgets ?? new();
    if (budgets.AttemptMilliseconds is <= 0 or > 30000 || budgets.QueryMilliseconds is <= 0 or > 5000 ||
        budgets.QueryMilliseconds > budgets.AttemptMilliseconds) {
      throw new ArgumentException("invalid_budgets");
    }
    var cases = request.Cases ?? [];
    if (request.Action == ContractScreenAction.Inspect && (request.Binding != null || cases.Count != 0) ||
        request.Action == ContractScreenAction.Screen && (request.Binding == null || cases.Count is 0 or > MaximumCases) ||
        cases.Any(item => item == null || string.IsNullOrWhiteSpace(item.Id) || item.Inputs == null) ||
        cases.Select(item => item.Id).Distinct(StringComparer.Ordinal).Count() != cases.Count) {
      throw new ArgumentException("invalid_cases_or_binding");
    }
    if (JsonSerializer.SerializeToUtf8Bytes(request, ContractJson.Options).Length > MaximumRequestBytes) {
      throw new ArgumentException("request_too_large");
    }
    ContractSourceSnapshot.ValidateTrustedSources(request.Sources, request.Dependencies);
    if (request.Target.InputMode != ContractInputMode.Unit || request.Target.Receiver != null ||
        request.Target.TypeArguments?.Count > 0 || request.Target.ReachableFrom != null ||
        request.Target.ReachableReceiver != null || request.Target.ReachableInvocation != 0) {
      throw new NotSupportedException("unsupported_target_mode");
    }
  }
}
