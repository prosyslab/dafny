# Keep session caches across option changes and make result reuse position-insensitive

Status: done (local source scope; independent review accepted 2026-11-04; no image, artifact or paid-run claim)
Date: 2026-11-04
Parent: [goal-owned native sessions](../../cosyn/plan/2026-11-04-goal-owned-native-sessions.md).
Related: [native analysis session](2026-11-02-native-analysis-session.md),
[analysis scope reuse](2026-11-04-analysis-scope-reuse.md),
[wiki](../wiki/native-analysis-session.md).

## Problem and evidence

The native-on Cat Topdown trial had 0 result-cache hits over 1,141 solver runs.
Analyses of identical workspace bytes reported 0/22 module hits. A free local
reproduction (Dafny 4.11.1+0776df27, built from the dirty tree, at
`/workspace/tmp/incremental-analysis-scope/bin`; tmux `native-cache-miss-diagnosis`;
outputs in `/workspace/tmp/native-cache-miss-diagnosis/`, temporary) found three causes.

1. Root-set alternation (fixed in the source, not in the live image). The live image
   passed expanded roots for one analysis and `[Cat.dfy]` for the others.
   `roots.SequenceEqual(state.Roots)` then failed on every request.
   The current Cosyn tree uses `--analysis-source`; the real-flow second prove takes
   1.1 s instead of 69 s.
2. Option alternation clears everything. `AnalysisSessionCommand.Session.Execute`
   (`AnalysisSessionCommand.cs:296-345`) keeps one `configuration` and one
   `resolutionConfiguration`. Any request with different identity options
   calls `resultCache.Clear()`. If the resolver identity differs too, it also
   recreates the parser and resolver and calls `facts.Reset()`. Cosyn's
   `SharedProofs.certificates` (`shared_proofs.py:152-171`) omits
   `--allow-external-contracts`, which is part of `ResolverOptions`.
   The sequence S,A,S,A is cold every time (about 21 s each). With the option
   aligned, each request after the first takes 0.05-0.07 s with 22/22 hits.
   The sequence S,V,S,V reproduces the live signature: 0 hits and the same
   solver runs every time. Isolated-mode verify paths in Cosyn also differ
   (`--allow-external-contracts` absent, `--extract-counterexample` in merge
   checks). Host alignment would change the verification policy, so retention
   must hold under mixed contexts. That the live S requests interleaved this way is an
   inference from the call sites; the live telemetry has no argv.
3. Position-sensitive result keys. `DefinitionAnalysis.BindNativeVerificationChecksums`
   (`DefinitionAnalysis.ProofInputs.cs:99-139`) folds `NativeSourceLocations`
   into the Boogie checksum. That value is the absolute (line, col, pos) of every
   token in the declaration. So any edit above a declaration, or a whitespace
   change inside it, invalidates its result.
   - The Dafny base checksum (`BoogieGenerator.InsertChecksum`) is an MD5 of the
     printed declaration and is already position-free.
   - The location binding exists only because cached `VerificationRunResult.Asserts`
     keep old `AssertCmd` tokens, and `JsonVerificationLogger` and
     `TextVerificationLogger` would otherwise report stale lines.

## Goals and pass criteria

- Alternating option contexts (S/A/V) no longer drop results or resolver caches:
  - S,A,S,A after the first request is warm, even without the Cosyn alignment.
  - S,V,S,V reaches cache hits on the second V.
- A blank-line or comment shift above a verified declaration, and a whitespace-only
  change inside it, gives cache hits.
- After such a hit, the JSON, text and TRX logs report the current assertion lines,
  byte-equal to a cold one-shot run of the same source after timestamp normalization.
- A changed assertion, contract, body, dependency, option, seed or library still
  misses. Reordered assertions with the same text miss.
- Memory stays bounded: retained contexts are capped and evicted LRU.

## Non-goals

- Serializing caches to disk or between processes. `BinaryFormatter` is obsolete in
  .NET 8, removed in .NET 9, and no AST type is `[Serializable]` (0 of 419
  classes). Resolver caches are keyed by object identity. Only the
  verification-result cache is a separate, possible future store.
- Changing which outcomes are cached (only complete Valid rosters, as now).
- Proof-dependency, coverage or counterexample reports (unsupported in sessions).

## Design

A. Per-context retention (cause 2)
- Replace the single `resultCache` with a small LRU map from context to
  `VerificationResultCache` (capacity 4). Remove `resultCache.Clear()` on a
  context change; keep `Clear` only on eviction and shutdown.
- Do the same for (parser, resolver, `DefinitionAnalysis.SessionCache`), keyed by
  `resolverContext` (capacity 2).
- The `ExecutionEngine` for a new `State` takes the cache of its context.
- Keep the `generation % 32` bound, but count it per context. It is a memory bound,
  not a correctness rule. Record it in evidence as `resultCacheClears`.

B. Position-free key with an assertion-shape guard (cause 3)
- In `BindNativeVerificationChecksums`, replace `NativeSourceLocations` with
  `AssertionShape(implementation)`. This is a hash of the ordered list of each
  `AssertCmd`'s command kind, `Description.SuccessDescription`/`FailureDescription`
  text, and its ordinal in the implementation. It contains no tokens.
- Keep the proof-input fingerprint and the base checksum unchanged.
- Same checksum therefore means the same declaration text, dependencies, options
  and assertion sequence.

C. Rebase cached results to current tokens (cause 3)
- In the cached branch of `TaskEntry.Run` (`task.CacheStatus is Completed cached`),
  return `cached.Result with { Asserts = current }`. `VerificationRunResult` is a
  record (`<Clone>$` is present in Boogie.VCGeneration 3.5.5).
- `current` is the current task's split assertions, matched by ordinal and
  description text. The split's assertion list is taken from the Boogie split API.
  If that API is not exposed in 3.5.5, map through the current implementation's
  ordered assertion list instead, using the shape ordinals from B.
- If the counts or descriptions differ, report a native protocol error for that
  task and retire the state. Never report old tokens. By construction of B this
  cannot happen unless the shape logic is wrong; a test covers it.
- `Start`/`RunTime`/`ResourceCount` stay as cached. Evidence marks the task as
  reused, as today.

## Planned changes

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: `Session` fields, `Execute` (296-370), shutdown (630) | Context-keyed LRU result caches and resolver caches; per-context generation bound; `resultCacheClears` evidence | Driver memory tests: S,A,S,A warm; S,V,S,V hit; eviction bound |
| Same file: `TaskEntry.Run` cached branch | Rebase `Asserts` to current split assertions; error on mismatch | Driver test with a shifted source: reused task reports current lines |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`: `BindNativeVerificationChecksums`, remove `NativeSourceLocations`, add `AssertionShape` | Position-free key with shape guard | Core tests: shift above / whitespace inside give equal checksums; text or order changes differ |
| `python/dafny_analysis/session.py` `NativeEvidence` | Optional `resultCacheClears` count | Python client fake tests |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Replace "location change forces native verification" and the "cleared on verifier context changes" statements | Link review |

## Validation

Free, local:
- `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~DefinitionAnalysis"`
- Affected Driver tests (`dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~AnalysisSession"`)
- Python client tests
- `make format`

Then rebuild into a new `/workspace/tmp/session-cache-retention/bin` and rerun
the `controlled.py` / `cosyn_flow.py` sequences from
`/workspace/tmp/native-cache-miss-diagnosis/scripts/` under tmux. Add shift and
whitespace cases and a one-shot log comparison. Expected:
- S,A,S,A and S,V,S,V are warm after the first request.
- Shift cases hit with current lines.
- Changed-assertion cases miss.

Independent review must check soundness. Boogie validity must not depend on token
positions; `captureState` labels carry positions but do not affect VC validity.
The reviewer must confirm this from source, not from this plan.

Paid runs are not part of this plan. A new artifact and image identity is needed
before any live use.

## Risks

- A cached result reported against the wrong assertion would be a false location,
  not a false verdict. The shape guard plus the mismatch error prevent it.
- More retained contexts use more memory. Capacities are fixed, and evidence
  reports clears and evictions.
- The Boogie split API surface is unknown until compiled against 3.5.5. The
  fallback mapping is planned in C.

## Progress and validation log (implementation, 2026-11-04)

Tool versions: dotnet 8.0.133, Python 3.12, Dafny 4.11.1+0776df27 (dirty tree, other
uncommitted work preserved), Boogie 3.5.5, Z3 from the existing test assets. Working
directory `/workspace/dafny-optimization` unless stated. Scratch and outputs
(temporary) are under `/workspace/tmp/session-cache-retention/`.

Implemented changes versus the table:

| File / symbol | Done |
| --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: new `RetentionMap<T>` (LRU), `ResolverRetention`, `ResultRetention`; `Session` fields and `Execute` | Result caches per verifier context (capacity 4), parser/resolver/facts per resolver context (capacity 2); `resultCache.Clear()` on context change and `facts.Reset()` removed; clear on eviction (instance recycled), per-context 32-compilation window and shutdown. `State` now carries its `Facts`. `Session`, `Request`, `Response` became internal and `Session` takes an optional window size, so memory tests can drive it. Evidence adds `ResultCacheClears`, `ResultCacheEvictions`, `ResolverEvictions`. |
| Same file: `NativeTaskEntry.Run`, `RebaseCachedResult` | Every result of a task that was `Completed` in the cache is rebased with `with { Asserts = task.Split.Asserts }` after verifying count, type and success/failure text per ordinal; a mismatch throws (request fails with native error code 6, state retired by the existing catch). An optional constructor argument supplies the current assertions to tests. |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`: `BindNativeVerificationChecksums`, `AssertionShape` | `NativeSourceLocations` removed. The shape also lists non-free call `requires` and the implementation's non-free `ensures`, found by name in the translated program, because a fresh translation is unresolved (`CallCmd.Proc` and `Implementation.Proc` are null) and Boogie only desugars these into assertions later. Called procedures also contribute their name. Fresh-GUID behaviour without a fingerprint is unchanged. |
| `python/dafny_analysis/session.py` `NativeEvidence` | Optional `result_cache_clears`, `result_cache_evictions`, `resolver_evictions`. |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Two invalidated statements replaced; new section "Session cache retention"; index lines updated. |

Boogie API for C: `VC.ManualSplit.Asserts` (inherited `Split.Asserts`, `List<AssertCmd>`),
read as `task.Split.Asserts`; `VC.VerificationRunResult` is a record, so `with` works.
Compiled against 3.5.5; the by-ordinal fallback was not needed.

Findings during implementation:
- The first Driver run showed a reused result still carried old lines: for a cached
  task Boogie can return the result through the stream rather than through a null
  `TryRun`, so rebasing was moved to the `Run` wrapper and covers both paths.
- A shape taken only from `AssertCmd`s in the translation does not see call
  preconditions or postconditions (a reordered call and assert gave equal shapes),
  hence the contract-based entries above.
- The stdout of the JSON logger contains the log document twice; not investigated,
  not caused by this change as far as observed (the test reads the first line).
- Reused verifies are still slow (15-18 s) because the whole compilation is rebuilt
  when the context changes. Out of scope; recorded as follow-up (one `State` per
  context).

Commands and results (all serial, free, local):
- `dotnet build Source/DafnyDriver/DafnyDriver.csproj -m:1 -v:q`, `dotnet build
  Source/DafnyCore.Test/DafnyCore.Test.csproj -m:1 -v:q`, `dotnet build
  Source/DafnyDriver.Test/DafnyDriver.Test.csproj -m:1 -v:q`: 0 errors.
- `dotnet test Source/DafnyCore.Test --no-build --filter
  "FullyQualifiedName~DefinitionAnalysis|FullyQualifiedName~ProofInput|FullyQualifiedName~DeclarationClone"`:
  63 passed, 0 failed, 0 skipped. New cases: positions ignored (5: shift above,
  comment above, whitespace in contract, whitespace in body, indentation), semantic
  changes miss (4: assertion text, order, contract, dropped assertion), shape guard
  (1). The old test asserting that a location change changes the key was replaced.
- `dotnet test Source/DafnyDriver.Test --no-build --filter
  "FullyQualifiedName~AnalysisSession|FullyQualifiedName~NativeTaskEntry|FullyQualifiedName~CachedParser|FullyQualifiedName~AnalysisSourceSelection|FullyQualifiedName~JsonVerificationLogger|FullyQualifiedName~InternalErrorExit"`:
  52 passed, 0 failed, 0 skipped (log `driver-tests.log`). New: 10 in
  `AnalysisSessionRetentionTests` (S,A,S,A warm; analysis between two verifies keeps
  results; two verify contexts keep separate results; LRU bounds and evictions;
  per-context window; shift above and whitespace inside report current lines and
  equal a cold session's JSON; assertion, contract and invariant changes miss) and 5
  in `NativeTaskEntryTests` (rebase through both Boogie paths; count, description and
  order mismatch fail the task and later subscribers). They run in memory with
  supplied source snapshots and the real solver on a tiny program; no files.
- Skipped: the whole `Source/DafnyDriver.Test` project. One attempt ran about nine
  minutes without finishing (it includes language-server process tests) and was
  stopped; this is not a pass.
- Python: `cd python && python3 -m pytest -q`: 105 passed, 12 deselected (opt-in);
  `ruff check .`, `ruff format --check .` (after formatting one test file) and
  `pyright .` clean.
- `dotnet format whitespace Source/Dafny.sln --verify-no-changes --include <the five
  touched C# files>`: no changes. The repository-wide `make format` was not run to
  avoid reformatting other uncommitted work.
- Native binary: `dotnet build Source/Dafny/Dafny.csproj -o
  /workspace/tmp/session-cache-retention/bin -m:1 -v:q` (0 errors); `Dafny --version`
  4.11.1+0776df27.

Free reproduction (tmux sessions `session-cache-retention-controlled` for
`controlled.py` and `cosyn_flow.py`, `session-cache-retention-shift2` for the new
`shift.py`; scripts copied and adapted under `scripts/`, originals untouched;
outputs `out/controlled.log`, `out/flow-*.log`, `out/shift.json`; private copy of the
public Cat sources, no provider calls):

| Case | Before (diagnosis outputs) | After |
| --- | --- | --- |
| i A,A / ii V,V / iii A,V,A,V / iv selection | warm second request | unchanged (0.03-0.08 s; V hits 3/3) |
| iii ledger roots (expanded vs one root) | 17 s per request | unchanged (17 s); root alternation is the already-fixed cause 1 |
| v S,A,S,A | 22/22 module misses each, 20.7-23.6 s | 21/22 hits on requests 3 and 4, 16.6 and 15.5 s |
| vi S+ext,A | warm | warm |
| vii S,V,S,V | V 0 hits and 3 solver runs both times | second V 3/3 hits, 0 solver runs, 16.9 s |
| Cosyn flow (old image roots) | second prove 69.1 s | 62.6 s, verify 3/3 hits |
| Cosyn flow (current tree) | second prove 1.1 s | 1.7 s |
| shift: blank lines above | verification forced | 3/3 hits, 0 solver runs; JSON, text, TRX equal a cold one-shot after normalization; lines 24,27 become 29,32 |
| shift: whitespace inside body | verification forced | 3/3 hits, equal to cold, lines current |
| changed assertion (`assert name == "cot"`) | miss | 0/3 hits, 3 solver runs, logs equal cold |

The "before" shift behaviour was not re-measured: an attempt with
`/workspace/tmp/incremental-analysis-scope/bin/Dafny` returned a null-reference error
for verify (rc 6) in the shift script, so the before column is taken from the
diagnosis and from the replaced unit test. The one-shot `vcResults` order is
completion order; logs were compared by `vcNum` and with times, GUIDs and the
TRX deployment directory normalized.

Not done: independent review (to follow), image or artifact identity, paid runs,
whole-project Driver test run, `make format` over the full solution.

Open risks:
- Shape coverage rests on the base checksum, the proof-input fingerprint and the shape
  together; the mismatch error is the backstop. Reviewer to confirm from Boogie
  source that VC validity does not depend on token positions (`captureState` labels).
- Several resolver contexts of a large program use more memory (2 resolver and 4
  result contexts); no memory measurement was made.
- Time per context-alternating request is not reduced (see findings).

## Independent review and close (2026-11-04)

A fresh verifier (Sonnet, high effort) re-read only the requirements and the
current tree. Its verdict was ACCEPT, with no soundness defect found. It reran:
- Core filter: 63 passed.
- Driver filters (AnalysisSession, NativeTaskEntry, CachedParser,
  AnalysisSourceSelection, JsonVerificationLogger): 49 passed.
- Python client: 105 passed, 12 deselected.

It also ran its own adversarial session cases (scripts and output in
`/workspace/tmp/session-cache-retention-review/adv/`, temporary):
- Callee contract, function body, opaque/reveal, constant, datatype, library
  contract and library function changes all missed and reported failure.
- A callee body-only change still hit for the caller, which is correct.
- A shift and whitespace inside a body gave hits with current lines.
- Option and seed changes missed.
- A genuinely failing assertion never turned into a success.
- Cross-file and cross-module cases behaved correctly.

It confirmed from Boogie 3.5.5 source that `captureState` is read only when a
model is expected and never enters the VC. Other uses of token positions affect
names and ordering descriptors only.

Remaining findings:
- `dotnet format whitespace` reports 2 errors at `DefinitionAnalysis.ProofInputs.cs:45`
  (`ResolutionOptionsIdentity`). That block was already in the uncommitted diff
  before this task, so it is not fixed here.
- Any text change in a module translation makes every definition in that module
  miss (coarse but safe).

Not run: the whole DafnyDriver.Test project, `make format` over the full solution,
and a memory measurement. Wall time for context-alternating requests is not
reduced, because only one `State` is kept. Keeping a `State` per context is a
possible follow-up.

## Second independent verification (parent-requested, 2026-11-04)

The parent session separately started another fresh verifier (Sonnet, high
effort), given only the requirements and the repository state. It reported: accept with one formatting fix and no soundness
defect.
- It read Boogie 3.5.5 source, shallow-cloned to
  `/workspace/tmp/session-cache-retention-review/boogie` (temporary).
- Key: `VerificationResultCache.Lookup` uses `impl.Id` + `Checksum` + `DependencyChecksum`.
- `captureState` is read only for model extraction, and split and description
  logic do not use positions.
- Every cached-return path goes through `NativeTaskEntry.Run`'s rebasing.

Its checks, in tmux `scr-review-tests` and `scr-review-adv*`:
- Core: 63 passed.
- Driver filters: 52 passed.
- Python: 105 passed.
- Adversarial native session cases (scripts in
  `/workspace/tmp/session-cache-retention-review/scripts`):
  - Weakened callee `ensures`, function/opaque/const/datatype/decreases edits,
    refinement and extern contract edits and context alternation all miss and
    fail like a cold run.
  - Shifts and whitespace hit, with current assertion lines.
  - Swapping declarations misses (conservative).

Fix applied after review (supersedes "not fixed here" above; whitespace only,
in a block that already predated this task in the uncommitted diff):
- `dotnet format whitespace Source/DafnyCore/DafnyCore.csproj --include Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`
  split the `options.TimeLimit, options.ResourceLimit, options.AutoTriggers`
  initializer (line 45) onto three lines. No other change.

Observation, not caused by this change: a fresh session returns rc 0 for an
`{:extern}` method with `ensures` that the cold CLI rejects with rc 2, when run
without `--allow-external-contracts`/`--allow-warnings`. This is a pre-existing
session/CLI warning-policy difference and needs its own task.

Limits:
- The full `DafnyDriver.Test` project and the repo-wide `make format` were not run.
- Memory for the larger retention was not measured. Capacities are fixed.
- Wall time for context-alternating requests stays at 15-18 s, because the
  native session still keeps one `State`; retaining one `State` per context
  would be a follow-up.
- A function-body edit anywhere in a module invalidates every result in that
  module (fingerprint scope).
- No image or paid-run claim.
