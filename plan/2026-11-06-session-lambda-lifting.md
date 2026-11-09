# Lift lambdas in sessions exactly as the one-shot verifier does

Status: in-progress (user approved on 2026-11-06)
Date: 2026-11-06
Parent: [single-proof Cat run](../../plan/2026-11-06-cat-topdown-single-proof.md).

## Problem and evidence

The native session rejected a valid reference proof, `CatCore.ExtendNumberTrace`,
that one-shot `verify` accepts with identical argv and bytes. Evidence:
`/workspace/tmp/experiment/cat-topdown-single-proof/blocker-session-verify-discrepancy.json`
and `/workspace/tmp/session-verify-mismatch/` (temporary).

The cause is in Boogie 3.5.5:
- The session sets `VerifySnapshots=1` (`AnalysisSessionCommand.cs`, present since
  the first session commit).
- With that setting, Boogie's lambda lifters attach a fresh `{:checksum}` attribute
  to every lambda (`MaxHolesLambdaLifter.cs:350-362`, `LambdaHelper.cs:225-237`).
- `AlphaEquality` compares attributes, and `QKeyValue.Equals` compares `Params` by
  reference (`QKeyValue.cs:256`). Identical lambdas therefore stop being shared.
- Proofs that relate the same set comprehension in several places then need set
  extensionality, which Z3 does not find.
- A 12-line reproducer passes one-shot and fails in the session.

Soundness: the bug only rejects valid proofs. Unshared lambda functions keep
correct defining axioms, so the error cannot produce a false success.

## Change

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs` `LiftLambdasAsOneShot`, called in `SharedVerifier.GetVerificationTasksAsync` | Before the engine sees the program, resolve and type-check it, then lift lambdas with an options copy using `VerifySnapshots=0`. Give the lifted functions the constant checksum Boogie would have added, so caching and dependency checksums keep working. Proof-input fingerprints still come from the unlifted translation. | New `AnalysisSessionLambdaLiftingTests` (4): Boogie behaviour pin, single lifted function with checksum, unchanged behaviour with `VerifySnapshots=0`, real-solver session reproducer |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Document the snapshot-mode lambda-sharing pitfall and the fix | Link review |

The patch is `/workspace/tmp/session-verify-mismatch/lambda-lifting-fix.patch`. It
was produced by the investigation and is applied unchanged.

## Validation

- `dotnet test Source/DafnyDriver.Test` with the filter
  `AnalysisSession|NativeVerificationCache|ParserCacheClone|CachedParser|NativeTaskEntry|LambdaLifting`.
- Python client tests.
- `dotnet format whitespace --verify-no-changes` on the touched files.
- Rebuild into `/workspace/tmp/session-cache-retention/bin`.
- Real check: reference Cat `ExtendNumberTrace` passes in a session, and the
  solver input matches one-shot.
- A fresh independent verifier follows.
- Long-term option: an upstream Boogie fix that compares `Params` by sequence.

## Progress

- 2026-11-06: Plan written and patch applied.
- 2026-11-06: Patch applied.
  - Driver filter: 163 passed. Python: 151 passed. Format: clean.
  - Real session on the reference Cat `ExtendNumberTrace`: rc 0, 39 verified.
- 2026-11-06: The fresh independent review (Sonnet) returned accept with fixes.
  - Solver input was identical to one-shot for all 39 Cat checks.
  - Adversarial lambda-body edits always missed the cache and gave the one-shot
    verdict.
  - Finding: the pre-lift path swallowed Boogie resolution and type errors. A
    type error was silently accepted where the engine would have thrown.
  - Fixed: `LiftLambdasAsOneShot` now throws the engine's `ArgumentException` on
    resolution or type errors. New test `IllFormedProgramsAreRejectedBeforeLifting`
    (2 cases).
  - Process note: this edit was made before this Progress entry was written.
  - Driver filter after the fix: 165 passed. Format: clean.
