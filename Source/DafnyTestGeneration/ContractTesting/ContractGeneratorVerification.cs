#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VC;
using Program = Microsoft.Dafny.Program;
using Declaration = Microsoft.Dafny.Declaration;

namespace DafnyTestGeneration.ContractTesting;

internal sealed record ContractGeneratorVerificationPart(string Check, int Index);
internal sealed record ContractGeneratorVerificationResult(ContractGeneratorProofCoverage Coverage, string Diagnostics,
  bool TimedOut = false);

/// <summary>Runs complete ordinary Dafny verification tasks for an audited direct generator scope.</summary>
internal static class ContractGeneratorVerification {
  internal static async Task<ContractGeneratorVerificationResult> VerifyAsync(Program program, IProgramVerifier verifier,
    IReadOnlyList<ContractSpecificationScope> scopes, Method generator, long deadline,
    CancellationToken cancellationToken) {
    var checks = scopes.SelectMany(scope => scope.Checks).ToHashSet();
    var required = checks.Select(check => check.VerboseName).ToHashSet(StringComparer.Ordinal);
    var generatorCheck = new ContractSpecificationCheck(generator, ContractNativeProofRole.Correctness).VerboseName;
    var expected = new List<ContractGeneratorVerificationPart>();
    var completed = new Dictionary<ContractGeneratorVerificationPart, SolverOutcome>();
    var diagnostics = new List<string>();
    var accepted = scopes.All(scope => scope.Failure == null);
    var declarations = checks.Select(check => check.Declaration).Distinct().ToList();
    if (declarations.Any(declaration => declaration is not ICanVerify target || !target.ShouldVerify ||
          !target.ShouldVerify(program.Compilation) || !target.ContainingModule.ShouldVerify(program.Compilation))) {
      accepted = false;
      diagnostics.Add("A required declaration is not an ordinary native verification target.");
    }
    using var engine = ExecutionEngine.CreateWithoutSharedCache(program.Options);
    if (accepted) {
      var resolution = new ResolutionResult(false, program, null);
      foreach (var module in declarations.Cast<ICanVerify>().Select(target => target.ContainingModule).Distinct()) {
        ContractQueryDeadline.Check(deadline, cancellationToken);
        var tasks = await verifier.GetVerificationTasksAsync(engine, resolution, module, cancellationToken);
        var selected = new List<(IVerificationTask Task, ContractGeneratorVerificationPart Part)>();
        foreach (var task in tasks) {
          var check = task.Split.Implementation.VerboseName;
          var selectedCheck = SelectCheck(checks, module, task.ScopeToken as IOrigin, check, out var supported);
          if (!supported) {
            accepted = false;
            diagnostics.Add("An ordinary verification part has no unique audited obligation: " + check);
            break;
          }
          if (selectedCheck == null) { continue; }
          var part = new ContractGeneratorVerificationPart(check, expected.Count);
          expected.Add(part);
          selected.Add((task, part));
        }
        if (!accepted) { break; }
        foreach (var (task, part) in selected) {
          ContractQueryDeadline.Check(deadline, cancellationToken);
          var outcome = await RunTaskAsync(task, diagnostics.Add, cancellationToken);
          ContractQueryDeadline.Check(deadline, cancellationToken);
          if (outcome is { } result) { completed.Add(part, result); }
          if (outcome != SolverOutcome.Valid) { diagnostics.Add(part.Check + ": " + (outcome?.ToString() ?? "missing completion")); }
        }
      }
    }
    return new(Account(required, expected, completed, generatorCheck, accepted),
      string.Join("\n", diagnostics), completed.Values.Contains(SolverOutcome.TimeOut));
  }

  private static IOrigin? UnwrappedOrigin(IOrigin? origin) {
    while (origin is OriginWrapper wrapper) { origin = wrapper.WrappedOrigin; }
    return origin;
  }

  internal static ContractSpecificationCheck? SelectCheck(IReadOnlyCollection<ContractSpecificationCheck> checks,
    ModuleDefinition module, IOrigin? origin, string nativeCheck, out bool supported) {
    var unwrapped = UnwrappedOrigin(origin);
    var owners = unwrapped == null ? [] : checks.Where(check => check.Declaration is ICanVerify target &&
      ReferenceEquals(target.ContainingModule, module) &&
      ReferenceEquals(unwrapped, UnwrappedOrigin(check.Declaration.Origin))).ToList();
    var matches = owners.Where(check => check.VerboseName == nativeCheck).ToList();
    // Required descriptors with missing owners cannot be mistaken for assertion-free obligations.
    supported = matches.Count == 1 || owners.Count == 0 && checks.All(check => check.VerboseName != nativeCheck);
    return matches.Count == 1 ? matches[0] : null;
  }

  // A complete trusted task enumeration can have assertion-free roles. A missing result for an enumerated
  // part is never assertion-free, and the generator root requires a positive native correctness result.
  internal static ContractGeneratorProofCoverage Account(IReadOnlySet<string> required,
    IReadOnlyList<ContractGeneratorVerificationPart> expected,
    IReadOnlyDictionary<ContractGeneratorVerificationPart, SolverOutcome> completed,
    string generatorCheck, bool completeEnumeration = true) {
    var covered = new HashSet<string>(StringComparer.Ordinal);
    var positive = new HashSet<string>(StringComparer.Ordinal);
    var validEnumeration = completeEnumeration && expected.Distinct().Count() == expected.Count &&
      expected.All(part => required.Contains(part.Check)) && completed.Keys.All(expected.Contains);
    if (validEnumeration) {
      foreach (var check in required) {
        var parts = expected.Where(part => part.Check == check).ToList();
        if (parts.All(part => completed.TryGetValue(part, out var outcome) && outcome == SolverOutcome.Valid)) {
          covered.Add(check);
          if (parts.Count != 0) { positive.Add(check); }
        }
      }
    }
    return new(required, covered, validEnumeration, generatorCheck, positive,
      !validEnumeration || completed.Values.Any(outcome => outcome != SolverOutcome.Valid));
  }

  private static async Task<SolverOutcome?> RunTaskAsync(IVerificationTask task, Action<string> diagnostic,
    CancellationToken cancellationToken) {
    using var cancellation = cancellationToken.Register(task.Cancel);
    var updates = task.TryRun();
    if (updates == null) {
      return task.CacheStatus is Completed cached ? cached.Result.Outcome : null;
    }
    var completion = new TaskCompletionSource<SolverOutcome?>(TaskCreationOptions.RunContinuationsAsynchronously);
    using var subscription = updates.Subscribe(status => {
      if (status is Completed completed) { completion.TrySetResult(completed.Result.Outcome); }
    }, error => {
      diagnostic("Ordinary verifier task failed: " + error.Message);
      completion.TrySetResult(null);
    }, () => completion.TrySetResult(null));
    return await completion.Task.WaitAsync(cancellationToken);
  }
}
