#nullable enable
using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Source-only, bounded support checks shared by authoring and runtime preparation.</summary>
public static class ContractRuntimeFeasibility {
  public const string PolicyVersion = "runtime-feasibility-v1";
  public const int MaximumRequestBytes = ContractRuntimeSourceAuthoring.MaximumRequestBytes;
  public const int MaximumDiagnosticCharacters = 16384;
  private const int MaximumSourceCount = 4096;
  private static readonly IComparer<string> CanonicalTextOrder = Comparer<string>.Create((left, right) => {
    var leftRunes = left.EnumerateRunes().GetEnumerator();
    var rightRunes = right.EnumerateRunes().GetEnumerator();
    while (leftRunes.MoveNext()) {
      if (!rightRunes.MoveNext()) { return 1; }
      var comparison = leftRunes.Current.Value.CompareTo(rightRunes.Current.Value);
      if (comparison != 0) { return comparison; }
    }
    return rightRunes.MoveNext() ? -1 : 0;
  });

  /// <summary>Resolves only supplied snapshots; never prepares a generator or starts a prover/compiler.</summary>
  public static async Task<ContractRuntimeFeasibilityResult> RunAsync(ContractRuntimeFeasibilityRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    cancellationToken.ThrowIfCancellationRequested();
    Validate(request);
    var deadlineTimestamp = ContractQueryDeadline.AfterMilliseconds(request.TimeoutMilliseconds);
    using var deadline = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
    deadline.CancelAfter(request.TimeoutMilliseconds);
    var token = deadline.Token;
    var nativeOptions = new DafnyOptions(options) { DisableScopes = true };
    nativeOptions.Set(CommonOptionBag.UnicodeCharacters, true);
    var reporter = new BatchErrorReporter(nativeOptions);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, token);
    ContractQueryDeadline.Check(deadlineTimestamp, token);
    if (reporter.ErrorCount != 0) {
      throw new ArgumentException(Bound(string.Join("\n", reporter.AllMessages
        .Where(message => message.Level == ErrorLevel.Error).Select(message => message.Message))));
    }
    Method goal;
    try {
      goal = ContractCallableSelector.SelectMethod(program, request.Entry,
        requireConcreteReceiver: false, allowLemmaContract: true);
    } catch (NotSupportedException error) {
      return Result([new("unsupported_target", error.Message)], []);
    }
    var modelPolicy = ParseModelPolicy(request.ContractModelPolicy);
    var blockers = AnalyzeResolved(program, request.Sources, goal, request.ExternExecution, modelPolicy, token);
    if (blockers.Count != 0) { return Result(blockers, []); }
    var modeled = modelPolicy == null ? null :
      ContractRuntimeContractModels.CreateForAuthoring(program, goal, modelPolicy)?.ExternSymbols;
    var root = ContractCallableSelector.NativeCallable(program, goal);
    var drafts = goal is Lemma ? Array.Empty<string>() : ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, [root],
        cancellationToken: token)
      .Where(callable => (!callable.IsGhost || callable is Function) &&
        (callable != root || root is Method { Body: null }) &&
        callable != (root as Function)?.ByMethodDecl &&
        request.Sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == callable.Origin.Uri) &&
        ContractRuntimeSourcePreparation.NeedsDraft(callable, nativeOptions, request.ExternExecution) &&
        modeled?.Contains(callable.FullDafnyName) != true)
      .Select(callable => callable.FullDafnyName).Distinct(StringComparer.Ordinal)
      .Order(CanonicalTextOrder).ToArray();
    return Result(blockers, drafts);

    ContractRuntimeFeasibilityResult Result(IReadOnlyList<ContractRuntimeFeasibilityBlocker> failures,
      IReadOnlyList<string> requiredDrafts) {
      ContractQueryDeadline.Check(deadlineTimestamp, token);
      var binding = new ContractRuntimeFeasibilityBinding(
        SourceSetHash(request.Sources), CanonicalIdentity(JsonSerializer.SerializeToElement(request.Entry, ContractJson.Options)),
        RequestIdentity(request), PolicyVersion,
        ContractHarnessBuilder.Hash(typeof(ContractRuntimeFeasibility).Module.ModuleVersionId + ":" +
          typeof(Program).Module.ModuleVersionId),
        ContractHarnessBuilder.Hash(DefinitionAnalysis.ContextOptionsIdentity(nativeOptions) + ":" +
          nativeOptions.DisableScopes), request.ExternExecution);
      ContractQueryDeadline.Check(deadlineTimestamp, token);
      var diagnostics = new List<string>();
      var remaining = MaximumDiagnosticCharacters;
      foreach (var failure in failures) {
        if (remaining == 0 || diagnostics.Count == 32) { break; }
        var limit = Math.Min(remaining, 2048);
        var diagnostic = failure.Diagnostic.Length <= limit ? failure.Diagnostic : failure.Diagnostic[..limit];
        diagnostics.Add(diagnostic);
        remaining -= diagnostic.Length;
      }
      return new(1, failures.Count == 0, failures.Select(failure => failure.Code).Distinct().ToArray(),
        diagnostics, binding, requiredDrafts);
    }
  }

  /// <summary>Checks known source restrictions while leaving missing bodies available for authoring.</summary>
  public static IReadOnlyList<ContractRuntimeFeasibilityBlocker> AnalyzeResolved(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, ContractRuntimeExternExecution externExecution,
    ContractRuntimeContractModelPolicy? modelPolicy = null, CancellationToken cancellationToken = default) {
    cancellationToken.ThrowIfCancellationRequested();
    var blockers = new List<ContractRuntimeFeasibilityBlocker>();
    if (goal is not Lemma && goal.FunctionFromWhichThisIsByMethodDecl is { ByMethodBody: null }) {
      blockers.Add(new("unsupported_goal_execution", "Runtime goals require a method or function-by-method."));
    }
    if (ContractRuntimeObligationTransformer.UnsupportedRuntimeIterator(program, goal,
          cancellationToken: cancellationToken) is { } iterator) {
      blockers.Add(new("unsupported_iterator", iterator));
    }
    if (goal is Lemma && !ContractCallableSelector.SupportsLemmaContract(goal)) {
      blockers.Add(new("unsupported_lemma", "Unsupported contract-only lemma signature."));
    }
    foreach (var formal in goal.Ins) {
      cancellationToken.ThrowIfCancellationRequested();
      if (!ContractRuntimeObligationTransformer.CompilableType(formal.Type)) {
        blockers.Add(new("non_compilable_input_type", goal.FullDafnyName + "." + formal.Name + ": " + formal.Type));
      }
    }
    var nativeGoal = ContractCallableSelector.NativeCallable(program, goal);
    var roots = goal is Lemma ? Array.Empty<MethodOrFunction>() : new[] { nativeGoal };
    var reached = ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, roots,
      goal is Lemma ? goal.Ins.Select(formal => formal.Type) : null, cancellationToken: cancellationToken);
    if (ContractRuntimeObligationTransformer.UnsupportedDiagnosticNames(reached, sources) is { } names) {
      blockers.Add(new("reserved_diagnostic_name", names));
    }
    if (ContractRuntimeObligationTransformer.UnsupportedGenericReferences(reached.Where(callable => !callable.IsGhost)) is { } generics) {
      blockers.Add(new("unsupported_generic_reference", generics));
    }
    foreach (var failure in ContractHeapFactory.UnsupportedRequiredGhostFields(program, goal, cancellationToken)) {
      blockers.Add(new("unsupported_required_ghost_field", failure));
    }
    if (modelPolicy != null) {
      cancellationToken.ThrowIfCancellationRequested();
      try {
        _ = ContractRuntimeContractModels.CreateForAuthoring(program, goal, modelPolicy);
      } catch (NotSupportedException error) {
        blockers.Add(new("contract_models_unsupported", error.Message));
      }
    }
    cancellationToken.ThrowIfCancellationRequested();
    return blockers;
  }

  /// <summary>Authenticates the semantic request independently of its execution deadline.</summary>
  public static string RequestIdentity(ContractRuntimeFeasibilityRequest request) {
    var value = JsonSerializer.SerializeToElement(new {
      request.SchemaVersion,
      request.Entry,
      TrustedSources = request.TrustedSources?.OrderBy(source => source.Path, CanonicalTextOrder)
        .ThenBy(source => source.Sha256, CanonicalTextOrder).ToArray(),
      Dependencies = request.Dependencies.OrderBy(source => source.Path, CanonicalTextOrder)
        .ThenBy(source => source.Sha256, CanonicalTextOrder).ToArray(),
      request.ExternExecution,
      request.ContractModelPolicy
    }, ContractJson.Options);
    return CanonicalIdentity(value);
  }

  /// <summary>Canonical content identity shared with clients independently validating native replies.</summary>
  public static string SourceSetHash(IReadOnlyList<ContractSource> sources) => CanonicalIdentity(
    JsonSerializer.SerializeToElement(sources.OrderBy(source => source.Path, CanonicalTextOrder)
      .Select(source => new { source.Path, Sha256 = ContractHarnessBuilder.Hash(source.Content) }), ContractJson.Options));

  private static string CanonicalIdentity(JsonElement value) {
    var output = new StringBuilder();
    Write(value);
    return ContractHarnessBuilder.Hash(output.ToString());

    void Write(JsonElement element) {
      if (element.ValueKind == JsonValueKind.Object) {
        output.Append('{');
        var separator = "";
        foreach (var property in element.EnumerateObject().OrderBy(property => property.Name, CanonicalTextOrder)) {
          output.Append(separator);
          Text(property.Name);
          output.Append(':');
          Write(property.Value);
          separator = ",";
        }
        output.Append('}');
      } else if (element.ValueKind == JsonValueKind.Array) {
        output.Append('[');
        var separator = "";
        foreach (var item in element.EnumerateArray()) { output.Append(separator); Write(item); separator = ","; }
        output.Append(']');
      } else if (element.ValueKind == JsonValueKind.String) {
        Text(element.GetString()!);
      } else { output.Append(element.GetRawText()); }
    }

    // Match the wire's compact ensure_ascii=false JSON without platform-specific Unicode escaping.
    void Text(string text) {
      output.Append('"');
      foreach (var character in text) {
        output.Append(character switch {
          '"' => "\\\"",
          '\\' => "\\\\",
          '\b' => "\\b",
          '\f' => "\\f",
          '\n' => "\\n",
          '\r' => "\\r",
          '\t' => "\\t",
          < ' ' => "\\u" + ((int)character).ToString("x4", CultureInfo.InvariantCulture),
          _ => character.ToString()
        });
      }
      output.Append('"');
    }
  }

  private static ContractRuntimeContractModelPolicy? ParseModelPolicy(ContractRuntimeFeasibilityModelPolicy? policy) {
    if (policy == null) { return null; }
    if (string.IsNullOrWhiteSpace(policy.Goal) || policy.Lower is not { Length: > 0 and <= 100 } ||
        policy.Upper is not { Length: > 0 and <= 100 } ||
        !BigInteger.TryParse(policy.Lower, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var lower) ||
        !BigInteger.TryParse(policy.Upper, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var upper) ||
        policy.Lower != lower.ToString(CultureInfo.InvariantCulture) && policy.Lower != "-0" ||
        policy.Upper != upper.ToString(CultureInfo.InvariantCulture) && policy.Upper != "-0" ||
        lower > upper || policy.MaxCandidates is < 1 or > ContractRuntimeContractModels.MaximumCandidates) {
      throw new ArgumentException("Invalid bounded model policy.");
    }
    return new(policy.Goal, lower, upper, policy.MaxCandidates);
  }

  private static void Validate(ContractRuntimeFeasibilityRequest request) {
    if (request == null || request.SchemaVersion != 1 || request.Sources == null ||
        request.Sources.Count is < 1 or > MaximumSourceCount || request.Entry == null ||
        string.IsNullOrWhiteSpace(request.Entry.Symbol) || request.TimeoutMilliseconds is <= 0 or > 30000 ||
        !Enum.IsDefined(request.ExternExecution) || request.TrustedSources?.Count > MaximumSourceCount ||
        request.Dependencies == null || request.Dependencies.Count > MaximumSourceCount) {
      throw new ArgumentException("Invalid runtime feasibility schema, sources, entry, policy or budget.");
    }
    long bytes = 0;
    foreach (var source in request.Sources) {
      if (source == null || source.Content == null || string.IsNullOrWhiteSpace(source.Path) ||
          Path.IsPathRooted(source.Path) || source.Path.Replace('\\', '/').Split('/').Any(part => part is "." or "..")) {
        throw new ArgumentException("Feasibility requires relative source snapshots.");
      }
      bytes += Encoding.UTF8.GetByteCount(source.Content);
      if (bytes > MaximumRequestBytes) { throw new ArgumentException("Runtime feasibility source budget exceeded."); }
    }
    ContractSourceSnapshot.ValidateTrustedSources(request.Sources, request.TrustedSources);
    if (request.Dependencies.Any(dependency => dependency == null || string.IsNullOrWhiteSpace(dependency.Path) ||
          dependency.Sha256 == null || dependency.Sha256.Length != 64 ||
          dependency.Sha256.Any(character => character is not (>= '0' and <= '9' or >= 'a' and <= 'f'))) ||
        request.Dependencies.Select(dependency => dependency.Path).Distinct(StringComparer.Ordinal).Count() != request.Dependencies.Count) {
      throw new ArgumentException("Runtime dependency identities require unique paths and SHA-256 digests.");
    }
    _ = ParseModelPolicy(request.ContractModelPolicy);
  }

  internal static string Bound(string text) => text.Length <= MaximumDiagnosticCharacters
    ? text : text[..MaximumDiagnosticCharacters];
}
