# Native failure kinds and unseeded Boogie validation

Status: draft (plan only; implementation needs approval)
Date: 2026-11-13
Parent: [Cosyn deterministic native failure recovery](../../cosyn/plan/2026-11-13-deterministic-native-and-late-warning-recovery.md) (D1)
Previous work: [native verification OOM](2026-11-12-native-verification-oom.md), delivered as `70cc9c08`

## Authorization and scope

On 2026-11-13 the user chose to write a plan for both native follow-ups and to
implement them only after approval. This is maintenance. No commit, pin change,
image build or paid run is authorized by this plan.

## Problems and evidence

1. Unseeded one-shot verification still crashes on Boogie validation errors.
   Network-disabled checks in the rebuilt agent image (`sha256:d164baed…`) and
   evaluator image (`sha256:1707e83e…`) used the input
   `lemma L(n: nat) { assert forall k: nat {:trigger k} | k < n :: k < n; }`.
   - With `--boogie=/randomSeed:42` it exits 2 with
     `<stdin>(1,49): Error: a matching pattern must be more than just a variable by itself`.
   - Without a seed it prints `Encountered internal compilation exception: Boogie
     program had 1 resolution errors` and the container exits 139.
   - Log (temporary): `/workspace/tmp/weekly-ea5d937c-delivery/image-check.log`.
   - Cause: in `DafnyProgramVerifier.GetVerificationTasksFromTranslationAsync`,
     only the `StableRandomSeed` branch runs `DefinitionAnalysis.ApplyStableSeededOrder`,
     which validates through `ModularProofKeys.LiftLambdas` and raises
     `BoogieValidationException`. The unseeded branch calls
     `engine.GetVerificationTasks` directly. Boogie throws there, and
     `CliCompilation` reports it as an internal compilation exception.
   - Current grading and Cosyn verify paths always pass the seed, so this path is
     not used today. It fails closed.

2. Every unhandled session exception is code 6.
   `AnalysisSessionCommand` ends its request handling with `catch (Exception)`,
   sets code 6 and writes only `exception.Message` to stderr. Cosyn infers "out of
   memory" from a stderr substring. Before `70cc9c08`, invalid Boogie input, and
   in a diagnostic host a missing `DafnyPrelude.bpl`, both produced the same
   code 6. The caller cannot tell a candidate fault from an environment fault.

## Goals and pass criteria

N1. Unseeded one-shot `verify` reports Boogie validation errors exactly like the
seeded path: exit 2, located Dafny diagnostics, no internal exception, no solver
start.

- Proposed approach: run the same validation (`ModularProofKeys.LiftLambdas`)
  before `engine.GetVerificationTasks` in the unseeded branch. Then the existing
  `BoogieValidationException` handling in `GetVerificationTasksAsync` reports it.
- Risk to check: lifting before the engine may change unseeded solver input.
  Controls must show that unseeded verification results and checksums for valid
  programs are unchanged. If they change, validate on a copy or validate without
  lifting instead.

N2. Session responses carry a structured failure kind for operational failures.

- Add a `failureKind` response field. Keep code 6 for compatibility.
- Proposed kinds:
  - `resource`: `OutOfMemoryException` and `InsufficientExecutionStackException`.
  - `solver`: prover process death (`ProverDiedException`).
  - `environment`: missing toolchain inputs such as the prelude, and file access
    failures outside candidate sources.
  - `internal`: everything else.
- Candidate errors keep their ordinary codes below 6.
- Pass criteria: in-memory session tests produce each kind from a controlled
  trigger without real resource exhaustion. Existing responses are unchanged
  except for the new field.
- Cosyn adoption (classification by kind) belongs to the parent plan and needs a
  protocol version check there.

## Non-goals

- No change to proof obligations, solver options, cache identity of valid
  programs, or seeded behavior.
- No change to Cosyn or root in this plan.

## Planned changes

| Files and symbols | Change | Why | Validation |
| --- | --- | --- | --- |
| `Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs`: `GetVerificationTasksFromTranslationAsync` | Validate before `engine.GetVerificationTasks` in the unseeded branch | Unseeded one-shot crashes on invalid Boogie input | Unseeded stdin invalid/valid controls; valid-program result and checksum parity |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: request catch blocks and response fields | Classify operational exceptions into `failureKind` | Code 6 hides the cause | In-memory session tests per kind |
| `Source/DafnyDriver.Test/` session tests, `Source/DafnyCore.Test/` if validation helpers change | Focused regressions | Coverage | `dotnet test --no-build --no-restore --filter …`, serial |
| `wiki/native-analysis-session.md` | Record the behavior and limits | Keep records current | Cross-check |

## Validation commands

From `/workspace/dafny`:

- Build the touched projects separately with `-m:1`. Run the affected test classes
  with `dotnet test … --no-build --no-restore --filter …` and
  `RunConfiguration.MaxCpuCount=1`.
- Format check: `dotnet format whitespace /workspace/dafny --folder
  --verify-no-changes --include <changed files>`; `git diff --check`.
- After delivery: rerun `/workspace/tmp/weekly-ea5d937c-delivery/image-check.sh`
  on the rebuilt images. Expect exit 2 for the invalid input with and without the
  seed, and exit 0 for the valid control.
- Independent review: `gpt-6.1-sol` is not available in this harness; report this
  at implementation time.

## Delivery (needs separate approval)

Commit on `expecto`, push, move both pins, rebuild images, as was done for
`70cc9c08`.

## Execution log

- 2026-11-13: plan written. No code changes.
