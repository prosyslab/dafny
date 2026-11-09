# Transfer clonable session caches to a new native process

Status: in-progress (user approved on 2026-11-05)
Date: 2026-11-05
Parent host plan: [cross-process child sessions](../../cosyn/plan/2026-11-05-cross-process-child-sessions.md).
Builds on: [native cache cloning](2026-11-05-native-cache-cloning.md).

## Problem and evidence

In-process cloning puts sibling branches in one daemon. `CompilerPreparation` is a
process-static gate (`AnalysisSessionCommand.cs:413`): resolver and translation
internals hold process-static state, so branches in one process prepare
compilations one at a time.

The in-image smoke (`/workspace/tmp/experiment/cat-topdown-goal-leases/`, r3) showed:
- two cloned siblings: check sequences 52.6 s and 52.8 s, against 36.5 s cold;
- one sibling resolve hit the host's 10 s timeout.

Forking a live .NET process is unsafe: fork copies only the calling thread while the
runtime has GC, JIT and thread-pool threads. OS checkpoint/restore (CRIU) needs
privileges and a new dependency.

The data that `Session.Clone` copies is already detached:
- Parser seeds are rebuilt from retained source text and URI.
- `NativeVerificationCache.Snapshot` and `Split` are scalar records.

The same data can therefore cross a process boundary.

## Contract (shared with the host plan)

`operation=export-session`, with `sessionId`:
- Runs at the same safe drained boundary as `clone`: admission, preparation, readers
  drained. It takes `CompilerPreparation` only if the parser snapshot requires it.
- Response: returncode 0, `nativeEvidence` null, stdout one strict JSON document,
  `schemaVersion: 1`:
  - `daemonEpoch`, `sessionId`, `sessionEpoch`;
  - `toolchain`: the existing native toolchain identity used by result checksums and
    proof inputs;
  - `resolvers`: per retained resolver context, its key, the options identity used
    by the parser clone, and parsed entries `{uri, text}` in the parser's retained
    form;
  - `results`: per retained result context, its key, `compilations`, and entries
    (`Snapshot`/`Split` records, with base64 dependency bytes).
- No command is replayed and nothing is read from disk.
- The document must fit the existing frame limit. If it does not, fail with a clear
  native error; never truncate.

`operation=import-session`, sent to a fresh process before any other request on
`sessionId`, with the export document as an exact payload:
- Validate: schema, `toolchain` equal to this process's identity, well-formed keys,
  and checksum/dependency shapes.
- Build parser seeds and result caches exactly the way `Session.Clone` builds a
  child, using this process's options and file system.
- Response: a receipt like the clone receipt (`sessionId`, `sessionEpoch`,
  `parsedEntries`, `verificationEntries`).
- A mismatch or malformed payload fails the request and imports nothing.
- Native freshness and checksum lookup stay authoritative. Imported results can
  only hit when the current checksum matches, as with clone.

The Python client (`python/dafny_analysis/session.py`) gets
`export_session(...) -> bytes` and `import_session(payload, ...) -> receipt`,
with the same cancellation, deadline and error mapping as `clone`. In-process
`clone` stays available and unchanged.

## Pass criteria

- An imported child reaches the same cache hits as an in-process clone for the
  same parent: verify hits with 0 solver runs, and parser reuse counts.
- A toolchain or option mismatch rejects the import.
- Malformed payloads reject.
- Parent state is unchanged after export.
- Two children in separate processes prepare compilations concurrently, with no
  shared gate.
- One-shot CLI and existing session behaviour are unchanged.

## Planned changes (refined by the implementer before coding)

Wire details the contract leaves open, fixed here (recorded as additions, not changes):
- `import-session` carries the exact export stdout in a new optional request field
  `payload` (string). No other request field is added.
- Import receipt: `{schemaVersion:1, daemonEpoch, sessionId, sessionEpoch, parsedEntries,
  verificationEntries}`, stdout JSON, `nativeEvidence` null.
- Failure codes: 2 with `DAFNY_SESSION_TRANSFER_REJECTED:` for malformed, mismatched or
  not-fresh imports; 6 with `DAFNY_SESSION_TRANSFER_TOO_LARGE:` for an oversized export;
  7 `DAFNY_SESSION_UNSUPPORTED:` from an older daemon; 130 for cancellation.
- Frame bound: the export is refused unless the payload, JSON-escaped into a request frame
  plus a 4096-byte reserve, fits the 8 MiB request limit (the binding side; the response
  frame carries the same string and has a 16 MiB limit). Nothing is truncated.
- Document entry shapes (all camelCase): resolver entry `{uri, text}`; result entry =
  `NativeVerificationCache.Snapshot` fields `id, name, checksum, dependencies (base64),
  programId, start, end, elapsed, resources, obligationsBefore, obligationsAfter, splits[]`
  with split fields `vcNum, iteration, startTime, runTime, maxCounterExamples,
  resourceCount, solverUsed, assertions[{type, success, failure}]`.

Feasibility finding (recorded, deviation from "Build parser seeds ... using this
process's options"): a fresh process has no `DafnyOptions` for a retained resolver
context, and the options identity cannot be turned back into options. Parser seeds are
therefore parked at import, keyed by the resolver key and its options identity, and
parsed with the first matching request's detached options (the same
`DetachedParserOptions` call `Clone` uses) when that request creates the resolver
context. A request whose key matches but whose `ResolutionOptionsIdentity` differs
discards the seeds and parses cold. The wire format is unchanged; the receipt's
`parsedEntries` counts accepted seeds, and the syntax parse moves to the first request.
Result caches need no options and are built at import time.

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyLanguageServer/Caching/PruneIfNotUsedSinceLastPruneCache.cs`: new `Export<TResult>(select, ct)`, `Seed(key, value)` | Read a drained cache under its semaphore (reject when in use, as `Clone` does); add an entry with `Accessed=false`, which is the parent's post-prune state | `ParserCacheCloneTests` additions |
| `Source/DafnyLanguageServer/Language/CachingParser.cs`: new `ParsedSeed(Uri, Source)`, `ExportSeeds(ct)`, static `FromSeeds(logger, fs, telemetry, seeds, options, ct)`; private `ParseTemplate` extracted from `Clone` and shared; `ComputeKey` | Export retained `{uri, text}`; rebuild the cache key (SHA-256 of uri, NUL, text) and a branch-private template from text, as `Clone` does | `ParserCacheCloneTests`: seeds equal clone's hits, uri round trip |
| `Source/DafnyLanguageServer/Language/DafnyLangParser.cs`: `ExportSeeds`, static `FromSeeds` | Same under the parser mutex | covered through parser tests |
| `Source/DafnyDriver/NativeVerificationCache.cs`: `Snapshot`, `Split`, `AssertionShape` become `internal`; new `ExportSnapshots(ct)` and static `Restore(snapshots, utcNow, out count, ct)`; `Clone` becomes `Restore(ExportSnapshots())`; `Snapshot.Validate()` | One snapshot copy path and one child-building path for clone, export and import; strict shape checks | `NativeVerificationCacheTests`: round trip equals clone, validation rejects |
| New `Source/DafnyDriver/Commands/NativeSessionTransfer.cs`: `TransferDocument`, `ResolverTransfer`, `ResultTransfer`, `TransferEntry`, `ImportReceipt`, `Serialize`, `Parse`, `FrameBytes`, `TransferRejectedException` | Strict (unmapped members, required fields, enum names, base64) document model, schema/toolchain/key/shape validation, frame accounting | `AnalysisSessionTransferTests` |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: `Request.Payload`; `SessionRegistry.Execute` dispatch for `export-session`/`import-session`; `SessionRegistry.Export`, `SessionRegistry.Import`; `Session.ExportTransfer(ct)`, `Session.Import(doc, ct)`, pending-seed map and its use in `Execute` where the resolver context is created; drained-boundary code of `Clone` extracted to `Session.AtDrainedBoundary` (optional compiler gate) and shared; `Clone` also carries pending seeds | Operations, shared boundary, parked seeds | `AnalysisSessionTransferTests`: round trip, mismatches, malformed, frame limit, parent unchanged, imported hits equal clone |
| `python/dafny_analysis/session.py`: `ImportReceipt`, `_SessionTransport.export_session/import_session` (shared `_transfer`), `_receive_control` branches, `NativeDafnySession.export_session/import_session` | Client methods with clone's admission, deadline, cancellation drain and error mapping | `python/tests/test_session.py` fake transport |
| wiki `native-analysis-session.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Document the protocol and limits | Link review |

## Validation

- Focused `dotnet test` filters: AnalysisSession*, NativeVerificationCache,
  ParserCacheClone, CachedParser, NativeTaskEntry.
- Python client tests and `dotnet format whitespace --verify-no-changes`.
- Rebuild into `/workspace/tmp/session-cache-retention/bin`.
- Real check: a parent daemon verifies public Cat, exports, two fresh processes
  import, and both children verify concurrently with cache hits.
- A fresh independent verifier follows. No LLM calls and no Docker.

## Progress

- 2026-11-05: Contract written; implementation delegated.
- 2026-11-05: Implemented on branch `native-session-optimization` (base 650e6db3, tree
  left uncommitted). Native owner root `/workspace/dafny-optimization`; scratch, logs and
  the real-check output are in `/workspace/tmp/cross-process-transfer/` (temporary).

- 2026-11-05 (review fix, in progress): the independent review found that
  `_SessionTransport._control` registers the control before `_frame` can raise for an
  oversized payload, so each refused import leaks a control that counts in `_normal_count`
  and eight of them wedge the transport. Plan: change `python/dafny_analysis/session.py`
  `_control` to build the frame first and unregister the control if `_enqueue` raises;
  audit `transfer`, `clone`, `_request_cancel` for the same ordering (`_request_cancel`
  registers before `_frame` too, but its frame is fixed-size); add to
  `python/tests/test_session.py` a fake-transport test of repeated oversized imports
  (`max_pending=2`) followed by a successful run, export and import. Optional C# item:
  make the `built` cleanup in `Session.Import` skip retentions already installed in
  `results` if `results.Acquire` throws midway, with a unit test. Checks: Python tests,
  ruff, pyright; dotnet filters, format and a binary rebuild only if C# changes.

- 2026-11-05 (review fix, done): `_control` and `_request_cancel` now build the frame
  before registering the control and unregister it if `_enqueue` raises. Audit: `transfer`
  and `clone` only register through `_control` after their open and deadline checks;
  `_request_cancel` was reordered for consistency; the shutdown control in `close` has a
  fixed-size frame and the transport is already stopping. New test
  `test_repeated_oversized_imports_do_not_wedge_the_transport` (`max_pending=2`, five
  refused imports, then a run, an import and an export, with `_controls` empty); with the
  old ordering restored it fails, with the fix it passes (restored file kept at
  `/workspace/tmp/cross-process-transfer/session.py.fixed`). Results: 82 unit and 20
  fake-integration tests in `test_session.py`, 149 in the non-integration `python/tests`;
  ruff check and format and pyright clean.
- Skipped, with reason: the optional `Session.Import` cleanup change. `results.Acquire`
  runs on a fresh map holding at most four validated contexts at capacity four with a
  lambda that only returns the prepared retention, so it cannot evict or throw there;
  a test would need a new seam. No C# changed, but `AnalysisSessionCommand.cs` had an
  mtime of 19:12 (not edited by this task), so `final.sh` was rerun: 158 passed, format
  verify exit 0 for all three projects, binary rebuilt at 19:17:56 JST, and no `.cs`,
  `.csproj`, `.props` or `.targets` file under `Source` is newer than `DafnyDriver.dll`.

## Implementation notes and deviations

Implemented as the contract is written, with these recorded points:

- Open details fixed in the table section: request field `payload`, receipt fields, failure
  codes, frame accounting, entry field names.
- Deviation, parser seeds (see the feasibility finding above): seeds are parked and parsed
  with the first matching request's detached options. `parsedEntries` counts accepted
  seeds. Verified: after import, the fresh process exports the same contexts as the parent
  (test `ImportedChildReachesTheCacheHitsOfAnInProcessClone`); a request with another
  option set never uses them (`ImportedSeedsBound` 0); a tampered identity discards them
  (`ImportedSeedsDiscarded`). Result caches are built at import time.
- Export takes no `CompilerPreparation` (nothing is parsed); it takes admission and
  preparation and waits for readers, like `clone`. Import takes the same two gates.
- Frame accounting uses two measures: the import request frame as the Python client writes
  it (unescaped non-ASCII, `\"` quotes, 8 MiB limit) and the export response frame as this
  process escapes it (`\u0022` quotes, 16 MiB limit). The export fails with code 6
  `DAFNY_SESSION_TRANSFER_TOO_LARGE` if either is exceeded, with a 4096-byte reserve.
- `Request` gained `Payload`; `SessionRegistry` gained an internal `transferFrameLimit`
  (default 8 MiB) used only by tests to exercise the limit.
- Import requires a fresh branch: no request served, no earlier import, no retained
  context. The target branch must already exist (the process's `default` branch).
- Parent after export: only expired journal entries are dropped, as `clone` already does;
  `Lookup` on the native cache refreshes the sliding expiration of entries it exports.
- Python: `NativeDafnySession.export_session(timeout_seconds, cancel_event) -> bytes`,
  `import_session(payload, timeout_seconds, cancel_event) -> ImportReceipt` (also stored
  as `import_receipt`). Transfers count in the normal request lane with jobs and clones
  and use clone's deadline, cancellation drain and error mapping (code 7 with the marker
  maps to `SessionUnsupportedError`, other failures to `NativeSessionError`).
- Process note: restoring the mutated file with `cp -p` kept an old mtime, so the first
  rebuild reused the mutated assembly and two tests failed. Touching the file and
  rebuilding fixed it; the logs `dotnet-focused-final.log` are from the rebuilt tree.

## Commands, results and skips (2026-11-05)

Working directory `/workspace/dafny-optimization`, SDK 8.0.133, offline, serial, tmux
sessions `xproc-*`.

| Check | Result |
| --- | --- |
| `/workspace/tmp/cross-process-transfer/build-test.sh` (LanguageServer, Driver, Test builds with `--no-restore -m:1 -p:BuildProjectReferences=false`, then `dotnet test --no-build` with filters `AnalysisSession`, `NativeVerificationCache`, `ParserCacheClone`, `CachedParser`, `NativeTaskEntry`) | 0 build errors; 158 passed, 0 failed, 0 skipped (log `dotnet-focused-final.log`). New: 46 in `AnalysisSessionTransferTests` (round trip, hits equal clone with 0 solver runs, option and toolchain mismatch, 32 malformed shapes, frame limit, parent unchanged, fresh-only, cancel, fake-solver wire round trip) and 3 in `ParserCacheCloneTests` |
| `dotnet format whitespace <project> --verify-no-changes --no-restore` for DafnyLanguageServer, DafnyDriver, DafnyDriver.Test | all three exit 0 (`format-verify.log`) |
| `PYTHONPATH=python python3 -m pytest -q -n 0 -p no:cacheprovider -m 'not integration' python/tests/test_session.py` and `-m integration` | 82 unit passed (was 59), 20 fake integrations passed (was 17); whole `python/tests` non-integration 149 passed; ruff check and format, pyright (`/workspace/tmp/verifier-optimization-cosyn/pyrightconfig.json`) clean |
| Mutation: in `NativeSessionTransfer.Validate` the toolchain comparison replaced by `false` | `RejectedImportsInstallNothing` and `ToolchainMismatchRejectsTheDocument` failed (44/46 passed); file restored from `/workspace/tmp/cross-process-transfer/NativeSessionTransfer.cs.orig`, sha256 `d39fd8f8...ab458b` identical before and after, then touched and rebuilt |
| `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q` (2026-11-05T07:19:18Z to 07:19:30Z) | 0 errors. `DafnyDriver.dll` 16:19:30 JST; `find Source -name '*.cs' -o -name '*.csproj'` (excluding obj, bin) newer than it prints nothing. The launcher `Dafny.dll` is older (16:17:08, not rewritten by an incremental build) |
| Real check, tmux `xproc-real2`, `/workspace/tmp/cross-process-transfer/real_check.py`, output `real-check/out/result.json` and `real-check/run.log` | below |

Real check (public Cat copy at `real-check/ws`, resolve and verify argv from the r3 smoke,
`--filter-symbol=Cat.CatBenchmarkItem.Name.`, three Dafny processes plus a clone baseline):

| Step | Result |
| --- | --- |
| Parent resolve, verify | 7.7 s, 43.5 s; 3 tasks, 0 hits, 3 solver runs |
| Export | 0.149 s; payload 1,408,268 bytes (sha256 `11b56d01...3060e3`); 2 resolver contexts with 15 entries each, 2 result contexts with 0 and 2 entries |
| Parent verify after export | 0.021 s, 3 of 3 hits, 0 solver runs (parent unchanged) |
| Import into two fresh processes | 0.7 s each; receipts parsed 30, verification 2 |
| Children resolve and verify concurrently | resolve 7.78 s and 7.90 s, overlapping 7.78 s (both started at the same instant); verify 41.0 s and 43.0 s, overlapping 40.9 s; each 3 tasks, 3 hits, 0 solver runs; wall 50.9 s |
| Baseline, two in-process clones of the same parent | resolve 5.3 s and 10.7 s; verify 47.3 s and 80.9 s; each 3 of 3 hits, 0 solver runs; wall 91.7 s |

Reading: the transferred results removed all solver runs in the children, and separate
processes removed the serialization (81 s against 43 s for the slower sibling). A child
still spends about 41 s in verify with 0 solver runs: its compilation (resolution and
translation of the included files) must be prepared in the fresh process; the cache
saves solver time only. No claim is made beyond this one workload and one run.

Not run: the root integration tests, the Cosyn host and its tests, Docker or image
builds, the in-image smoke, any LLM or paid run, the opt-in native process pytest tests
(`test_native_integration.py`), the fresh independent verifier, whole-solution `dotnet
test`. Exact parent state after export was compared through exported documents and cache
hits, not by memory inspection.

Durable findings: [wiki](../wiki/native-analysis-session.md#cross-process-session-transfer-2026-11-05).
Status stays in-progress until the independent verifier and the host plan finish.
- 2026-11-09: committed as "[Session] transfer clonable caches to a new native process" on branch `native-session-optimization`.
