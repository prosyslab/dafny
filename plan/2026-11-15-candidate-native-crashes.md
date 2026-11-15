# Candidate inputs that crash the native session

Status: done
Date: 2026-11-15
Parent: [weekly FAIL:F classification](../../plan/2026-11-15-weekly-fail-f-native-classification.md)
Sibling: [Cosyn proof-input rejection and cleanup exit](../../cosyn/plan/2026-11-15-proof-input-rejection-and-cleanup-exit.md)

## Authorization and scope

On 2026-11-15 the user asked to fix every cause found in the FAIL:F analysis of weekly run
`weekly-20261114t015031z-a6d430c1b660`, and to commit each fix as it is done. This plan covers
the native Dafny fork and its Python client. This is maintenance. Commits are authorized.
Push, pin changes, image builds and paid runs are not.

## Problems and evidence

Analysis (temporary): `/workspace/tmp/weekly-a6d430c1-fail-f-analysis/summary.md`. Minimal
inputs and scripts are in `repro/` next to it.

N1. touch-r04. A duplicate module (`Duplicate module name`) makes a remapped session request
fail with exit 6 and `Object reference not set to an instance of an object.`
`LiteralModuleDecl.cs:196` reports with `new NestedOrigin(Origin, otherModule.Origin)` and no
message. `ErrorReporterExtensions.cs:65` turns it into related information with
`MessageParts = [null]`. `AnalysisSessionCommand.RemapDiagnostic` passes that null to
`RemapOutputText`, which calls `text.Contains`. The same input with equal source and logical
roots, or through the CLI, prints the normal diagnostic. `ModuleDefinition.cs:755` (duplicate
top-level name) has the same shape.

N2. tr-r02. `hide P(x + y);` inside a `match` case aborts the process with
`Process terminated. Assertion failed.` at `BinaryExpr.get_ResolvedOp`. `HideRevealStmt.GenResolve`
resolves only the callee name (`applySuffix.Lhs`); the arguments stay unresolved. `MatchFlattener`
clones the case body with resolved fields, and the `BinaryExpr` clone constructor reads
`ResolvedOp`, whose getter has `Debug.Assert(_theResolvedOp != YetUndetermined)`. Native Dafny is
built with `dotnet build` and no configuration (Debug), so the assert ends the process. Reproduced
locally and in the weekly agent image `sha256:039755a5…`.

N3. tr-r02. After the worker dies, `_SessionTransport.close` stops and reaps it, then closes
stdin. The buffered request bytes cannot be flushed, `close` raises `BrokenPipeError`, and the
transport records `could not stop and reap native worker`. Every later `close` re-raises that
cached error. Reproduced 3 of 3 times with the N2 input; the worker returncode is -6.

## Goals and pass criteria

1. N1: `RemapDiagnostic` keeps a null message part as null. A remapped duplicate-module request
   returns the normal resolution diagnostic with the related location on the physical path.
2. N2: `hide`/`reveal` with argument expressions inside a `match` case resolves like the same
   statement outside a match, with no assert or internal exception. Existing reveal tests keep
   their results. (Revised after review 1: the first criterion, a `BinaryExpr` clone that keeps an
   unresolved operator, named one symptom; the fix moved to the hide/reveal clone, see the log.)
3. N3: when the worker has been reaped, a `BrokenPipeError` from closing its stdin does not make
   `close` fail. A worker that cannot be stopped still fails as today.

## Non-goals

- Changing the build configuration to Release (affects every Debug assert and all build
  receipts). Other Debug asserts reachable from candidate input stay possible; N3 and the
  Cosyn sibling plan keep such a crash from wedging the run.
- Rejecting or resolving `hide`/`reveal` argument expressions. Upstream accepts and ignores them.
- Making a genuine stop failure retryable.
- Changing the D1 native failure-kind plan.

## Existing code reviewed

- `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: `RemapOutputText`, `RemapDiagnostic`,
  `RemapOutputPath`.
- `Source/DafnyCore/Generic/ErrorReporterExtensions.cs`, `Reporting.cs` (`DafnyRelatedInformation`),
  `AST/NestedOrigin.cs`.
- `Source/DafnyCore/AST/Expressions/Operators/BinaryExpr.cs`,
  `AST/Statements/Verification/HideRevealStmt.cs`.
- `python/dafny_analysis/session.py`: `_SessionTransport.close`, `_stop_worker`, `_read_loop`.
- Tests: `Source/DafnyDriver.Test/AnalysisSessionDiagnosticLocationTests.cs`,
  `IntegrationTests/.../LitTest/ast/reveal/`, `python/tests/test_session.py` fakes.

## Planned changes

| Files and symbols | Change | Why, and what is missing without it | Validation |
| --- | --- | --- | --- |
| `AnalysisSessionCommand.RemapDiagnostic` | Map a part only when it is not null | N1: a message-less related location fails the whole request | New `AnalysisSessionDiagnosticLocationTests` case with `[null]` related parts; repro script |
| `BinaryExpr(Cloner, BinaryExpr)` (dropped after review) | Copy `_theResolvedOp` instead of reading `ResolvedOp` | Covered only operators; made redundant by `CloneTarget`, untested, reverted | Not applicable |
| `HideRevealStmt(Cloner, HideRevealStmt)`, new `CloneTarget` (replaces the `BinaryExpr` change after review) | With resolved fields, clone the arguments of a hidden or revealed call as unresolved syntax and keep the resolved callee | N2: cloning never-resolved arguments aborts on `BinaryExpr.ResolvedOp` (Debug assert) or fails with `Value cannot be null` in `UserDefinedType(Cloner, ...)` | New LIT test `ast/reveal/hideArgumentsInMatch.dfy`; existing `ast/reveal` and `autoRevealDependencies` tests; argument-form sweep, match against if/else; repro input |
| `python/dafny_analysis/session.py`: `_SessionTransport.close` | Ignore `BrokenPipeError` from closing stdin after the worker is reaped | N3: a crashed worker leaves a permanent close error | New `test_session.py` case with a fake stdin that raises on close after exit; repro script |
| `python/tests/test_session.py` (added after review) | Case for a worker that survives every stop stage with a broken stdin | N3 pass criterion "a worker that cannot be stopped still fails" had no test | Runs with `-m integration` |
| Wiki: `native-analysis-session.md`, `python-analysis-client.md`, `wiki/INDEX.md` | Record the three causes, the fixes and the hide/reveal observations | Keep the session record current | Cross-check against source |

## Risks and compatibility

- N2 (final form) changes only resolved clones of hide/reveal call arguments, which resolution
  never resolves. The callee, `OffsetMembers` and `ResolvedStatements` are cloned as before.
- N3 still raises when `_stop_worker` cannot reap the worker. Closing stdin after `BrokenPipeError`
  leaves the raw stream closed (CPython closes the raw stream even when flush fails).

## Validation

From `/workspace/dafny`, local only:

- `dotnet build Source/Dafny.sln` before and after the change.
- `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~AnalysisSessionDiagnosticLocationTests"`.
- LIT: `make test name=ast/reveal` (the new test and existing reveal tests).
- `make format` (check only touched files in the diff).
- From `/workspace/dafny/python`: `python3 -m pytest -q tests/test_session.py` and the same file
  with `-m integration`, before and after; `ruff check` and `ruff format --check` on touched files.
- Repro scripts against `Binaries/Dafny` from this checkout.
- Independent verification by a fresh agent (see the parent plan for the model note).

## Execution log

- 2026-11-15: plan written.
- Environment: base `87dcbe557` (branch `expecto`), .NET SDK 8.0.133, Python 3.12.3. Commands from
  `/workspace/dafny` unless noted; logs in `/workspace/tmp/weekly-fail-f-fixes/` (temporary).
- Baseline `dotnet build Source/Dafny.sln`: 0 errors (`dafny-build-baseline.log`).
- N1: guard in `RemapDiagnostic`; new Driver test `MessagelessRelatedLocationIsRemapped`.
  `AnalysisSessionDiagnosticLocationTests` 19/19. Without the guard the new test fails with a
  NullReferenceException in `RemapOutputText`.
- N2 first step: `BinaryExpr` clone copies `_theResolvedOp`. First LIT design failed because a
  `reveal` in one branch of a method cancels a `hide` in its other branches (upstream, same on the
  pinned build); the reveals moved to their own method. A missing third error came from reporting
  without isolation; the RUN line uses `--isolate-assertions`.
- N3: `close` ignores `BrokenPipeError` from closing stdin after `_stop_worker`; new test
  `test_reaped_worker_broken_stdin_does_not_fail_close`. Live repro (`live_repro.py`): pinned
  build plus fixed client gives the expected rc 6 and EOF failures, then two clean closes.
- Independent review 1: a fresh Claude Opus 5.5 agent (disclosed substitute for `gpt-6.1-sol`,
  unavailable here), given only the plan, the analysis and the repository state. N1 and N3 met.
  N2 partly met: arguments that name a user-defined type still failed inside a match (exit 6,
  `Value cannot be null`, from `UserDefinedType(Cloner, ...)`), on both builds. Low findings: no
  test for an unstoppable worker; the N3 tests run only with `-m integration`, like their
  neighbours; the LIT comment about reveals overstated the isolated case.
- Review fixes: `HideRevealStmt.CloneTarget` clones hide/reveal call arguments as unresolved syntax
  and keeps the resolved callee. The LIT test gained a `Typed` method and an opaque `reveal G(n as
  Small)` case, and its comment was corrected. Before the rebuild the extended test failed with
  `Value cannot be null`; after it, 6 errors on the 6 annotated asserts, and the same 6 with the
  `Typed` match rewritten as if/else. Removing `reveal G` adds the expected seventh error. New test
  `test_unreaped_worker_with_broken_stdin_still_fails_close`.
- Local checks after review fixes 1 (with the `BinaryExpr` change still in place): build 0 errors (`dafny-build-hide-clone.log`);
  `make test name=ast/reveal build=false` 9/9; `make test name=autoRevealDependencies build=false`
  9/9; `dotnet test Source/DafnyCore.Test --no-build --filter
  "FullyQualifiedName~DefinitionBodyVisibility|FullyQualifiedName~Reveal"` 23/23; `dotnet test
  Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSession"` 132/132;
  `dotnet format whitespace --verify-no-changes` on the four touched C# files exit 0. Sweep of 59
  hide/reveal argument forms from the review (212 files, match and if/else): all exit 0, no
  mismatch. Original repro inputs: hide-in-match exit 0, duplicate module exit 2; live session:
  exit 2 with `Duplicate module name` and the related location on the physical path, exit 0 for
  the hide input, every close clean.
- Python, from `/workspace/dafny/python`: `python3 -m pytest -q -p no:cacheprovider tests` 165
  passed; `-m integration tests/test_session.py` 22 passed. `ruff check` reports 4 E501 and
  `ruff format --check` two hunks, all present at HEAD and outside the changed lines.
- Independent review 2 of the `HideRevealStmt` change: a fresh Claude Opus 5.5 agent, same
  substitute note, given goal 2, the upstream semantics and the repository state. Met for argument
  expressions: 379 match/if-else pairs (70 argument forms, dotted, static, instance and constant
  callees, wildcards, auto-reveal, the old resolver, unrolling and partial evaluation) give equal
  output on the new build except one column offset; the pinned build crashes in 166 match cases;
  the if/else outputs are byte-identical between builds. The LIT test fails with only the
  `BinaryExpr` change (exit 6) and passes with only the `HideRevealStmt` change. Findings: the
  `BinaryExpr` change was untested and its comment no longer true, so it was reverted; `CloneTarget`
  clones `Lhs` twice (harmless, kept). Remaining older bug, out of scope: revealing a labeled assert
  or requires label inside a match aborts (exit 134) on both builds, because the clone builds new
  `AssertLabel` objects whose `E` is never set (`HideRevealStmt.cs`, `AssertStmt.cs`); fixing it
  needs a label map in the cloner.
- After the `BinaryExpr` revert: build 0 errors (`dafny-build-final.log`); `ast/reveal` 9/9 and
  `autoRevealDependencies` 9/9 (LIT, `build=false`); Core filter 23/23; Driver `AnalysisSession`
  132/132; format check on the three touched C# files exit 0; sweep 212/212 exit 0; repro and live
  session results unchanged.
- Shared tree: another session (`Definition analysis module 버그`) changed
  `DefinitionAnalysis.cs`, `DefinitionAnalysis.ProofInputs.cs` and added
  `DefinitionReferenceTests.cs` at 20:41 while this work ran. The builds after that include those
  uncommitted changes; they are not on the `resolve`/`verify` path checked here and are not part of
  this commit.
- Not run: the full `DafnyDriver.Test` and `IntegrationTests` suites (too long for this scope;
  the reviewer's full Driver run hit a 590 s timeout); JavaScript-backend LIT steps in wider
  filters fail on a missing `bignumber.js` in node, also on the unfixed build.
