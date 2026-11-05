# Render session diagnostic excerpts from the request's source bytes

Status: done (local source scope; independent review accepted 2026-11-05)
Date: 2026-11-05
Parent: [goal-owned native sessions](../../cosyn/plan/2026-11-04-goal-owned-native-sessions.md).
Related: [warning path remap](2026-11-05-session-warning-path-remap.md),
[native analysis session](2026-11-02-native-analysis-session.md),
[wiki](../wiki/native-analysis-session.md).
Evidence: lab note `/workspace/lab-notebook/2026-11-05/goal-owned-native-smoke.md`
(section "Rerun after F1/F2 fixes (r2)", finding F6); outputs
`/workspace/tmp/experiment/goal-owned-native-smoke-20261105-r2/out/s3/`
(`assertfail/raw_calls.json` call index 4, `analysis.json` `snippets`), temporary.
Independent review of the warning remap plan also recorded this as a follow-up.

## Goal

In `analysis-session`, a request that binds `source_root != logical_root` must print the
source excerpt under a diagnostic (`NN | code` and the caret line) from the bytes the
compilation used, not from the logical-root file on disk. One-shot output and equal-root
or root-less sessions stay as they are.

## Evidence

Smoke r2, case assertfail, verify: header `bench/utils/cat/Impl/Cat.dfy(27,6): Error:
assertion could not be proved` is right, but the excerpt is `27 |     }` with caret `^`. The
candidate line 27 is `      assert name == "cot";`; the logical-root file's line 27 is `    }`.
Same for resolvefail (`26 |       name := "cat";` instead of `var bogus: int := "text";`).
5 of 5 lease excerpts matched the logical-root line, 0 of 5 the candidate.

## Root cause (confirmed in source)

- `Source/DafnyCore/HumanReadableOutputWriter.cs:62` and `:77` call
  `Snippets.WriteSourceCodeSnippet(options, range, tw)` for the main range and for each
  related location, while writing a diagnostic through `ConsoleErrorReporter` (the
  `cli.ReportDiagnostic` path of the session; the same call is used by the one-shot CLI).
  The older `DafnyConsolePrinter.cs:106` calls it for Boogie errors.
- `Source/DafnyCore/Snippets.cs:24` obtains the line with `GetFileLine`, and
  `Snippets.cs:51` reads the file with
  `DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance, ..., uri, ...)`. `OnDiskFileSystem`
  (`Source/DafnyCore/AST/Grammar/IFileSystem.cs:52`) opens `uri.LocalPath`. The URI of a
  diagnostic range is the parsed (logical) URI, so under `source_root != logical_root` the
  read goes to the logical-root path on disk, which is stale or absent, and never to the
  request's supplied snapshot or physical file. The source comment at `Snippets.cs:49-50`
  already says "This is not guaranteed to be the same file that Dafny parsed".
- The session parses through its own `IFileSystem` (`SwitchingFileSystem` ->
  `CapturedFileSystem`, `AnalysisSessionCommand.cs:1018` and `:1048`), which holds the
  physical or supplied bytes keyed by logical URI. Snippet rendering does not use it.
- With equal roots the logical file and the physical file are the same, so the on-disk read
  is right by accident; a snapshot supplied in `source_snapshots` that differs from the disk
  file would also be misreported.
- Per-request cache: `FsCaches` is a `ConditionalWeakTable<DafnyOptions, ...>`; each session
  request parses its own `DafnyOptions`, so a request does not see another request's lines.

Not a replay-time problem by itself: queued and verification-result diagnostics are
rendered when the request writes them (`Execute` replay loops and
`Compilation.GetDiagnosticsFromResult` loop), with the request's options. The reader just
needs the request's bytes there.

## Approach

Approach 1 from the request: render excerpts from the same bytes the compilation used. No
text is remapped after rendering.

Add an optional per-options file system for source excerpts:
`DafnyOptions.SnippetFileSystem` (`IFileSystem?`, default null). `Snippets.GetFileLine`
uses `options.SnippetFileSystem ?? OnDiskFileSystem.Instance`. Everything else in
`Snippets` stays (one-shot path unchanged because the property is null).

The session sets it on the request's own options object (the one used by
`CliCompilation`, whose `ConsoleErrorReporter`/`HumanReadableOutputWriter` render the
text), after `responseFiles` exists. The excerpt file system is a read-only view of that
request's `CapturedFileSystem`:

- URI in `Inputs` (the consumed closure, copied from the reused `State`): its captured text.
  A reused State is only selected when every captured input's fingerprint equals the new
  request's, so these bytes are the new request's bytes; a request whose bytes differ builds
  a new compilation with new captures.
- URI not captured: `Capture(uri)` without registering it (supplied snapshot, else the
  physical file via `ActualPath`). It never adds to `Inputs`, so consumed-input identity,
  freshness checks and limits are unaffected.

Global state: none shared across requests. The hook lives on the request's `DafnyOptions`
instance and its per-instance line cache, so concurrent requests with different roots do
not interact. No process-global hook is needed.

Alternatives rejected: remapping the rendered text (not allowed; the stale line would
still be wrong); a `Snippets` static override (process-global, unsafe under concurrency);
retaining text in each token (large change in the parser, unnecessary because
`CapturedFileSystem` already keeps the text).

## Planned changes

| File / symbol | Change | Why | Test |
| --- | --- | --- | --- |
| `Source/DafnyCore/DafnyOptions.cs`: new property `SnippetFileSystem` | optional `IFileSystem` for excerpt text; copied with other fields by `CopyTo` | no way to give the excerpt reader the compilation's file system | covered by Driver tests |
| `Source/DafnyCore/Snippets.cs`: `GetFileLine` | read via `options.SnippetFileSystem ?? OnDiskFileSystem.Instance`; update the stale comment | root cause | Driver tests, one-shot equality |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: new `SnippetFiles` view over `CapturedFileSystem`, `CapturedFileSystem.ReadForExcerpt`; `Session.Execute` sets `options.SnippetFileSystem` once `responseFiles` is created | route the session's excerpt reads through the request's captured bytes | root cause | Driver tests |
| `Source/DafnyDriver.Test/AnalysisSessionSnippetSourceTests.cs` (new) | see below | missing coverage | `dotnet test --filter AnalysisSession` |
| `wiki/native-analysis-session.md` | new section, update the warning-path limits note | records | link review |
| `plan/INDEX.md` | register at top | | |

Layers: native evaluator/session code only. No spec, proof, dataset, scoring or reporting
layer changes. No Cosyn edits. Python client unchanged (native text passes through).

## Tests (Driver memory tests, no Docker, no provider)

New `AnalysisSessionSnippetSourceTests` (collection "Proof input translation") with a
real temporary logical directory holding stale files (every line `// stale logical line N`,
same line count), a different physical directory, `source_root != logical_root`, and
supplied snapshots keyed by logical path (a theory also covers the case without supplied
snapshots, where the physical file is read):

- resolution error (`var bogus: int := "text";`): resolve, definition-analysis and verify
  excerpts equal the candidate line, contain no `stale`, and equal the one-shot excerpt of
  the same file in the physical directory;
- failing assertion and failing postcondition with related location (excerpt of the main
  range and of the `Related location`): verify;
- reused State with another `source_root` (second request has solver runs 0 and task
  count > 0, so it replays from the same State; its excerpt still is the candidate);
- verification result replayed from a different compilation (the candidate moved by a
  comment line, cache hits > 0): the excerpt shows the moved candidate line;
- equal-root and no-root requests: excerpt unchanged, equal to one-shot.

Excerpt lines are compared, not headers: headers use the process-cwd-relative path, a
known and unchanged difference (see the warning-path-remap plan's non-goals).

## Validation commands

Free, local, serial (no LLM or provider calls, no Docker); long runs in tmux; scratch in
`/workspace/tmp/session-snippet-source/`. Working directory `/workspace/dafny-optimization`.

- `dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj -m:1 -v:q`
- `dotnet test Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSession"`
  and `FullyQualifiedName~AnalysisSourceSelection|CachedParser|NativeTaskEntry`
- Core tests (DafnyCore is touched): `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~Snippet|DefinitionAnalysis|DeclarationClone"` plus any existing reporter/snippet tests found.
- `cd python && python3 -m pytest -q`
- `dotnet format whitespace Source/DafnyCore/DafnyCore.csproj --verify-no-changes --include <touched files>` and the same for DafnyDriver and DafnyDriver.Test.
- Mutation: bypass the new hook (temporary env switch or restored edit), expect the new
  tests to fail, restore byte-identically (sha256 before and after).
- Rebuild `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q`;
  record time and `Dafny --version`; confirm no source file is newer than `Dafny.dll`.
- Real session check: copies of the r2 smoke scripts under
  `/workspace/tmp/session-snippet-source/real/` (originals untouched), reproducing the
  assert-fail and resolution-error cases with `source_root != logical_root`.

## Risks

- A diagnostic in a file the session never captured (for example a doo or non-file URI) had no
  excerpt before (the read failed and was ignored) and keeps none. The fallback never throws
  to the caller; `GetFileLine` still catches exceptions.
- `DafnyOptions.CopyTo` copies the new field to option copies; copies used for compilation
  have null writers and render nothing, so sharing the view is harmless.
- Excerpt text of an uncaptured physical read can be newer than the compiled bytes; the
  completion freshness check already covers consumed inputs and an uncaptured file is not one.

## Progress and validation log

Implemented 2026-11-05 as planned (files and symbols as in the table; no scope change).
Tool versions: dotnet 8.0.133, Python 3.12, Dafny 4.11.1+0776df27 (dirty tree; other
uncommitted work preserved, nothing reset, stashed or committed). Scratch and logs:
`/workspace/tmp/session-snippet-source/` (temporary). tmux sessions: `snip-build-pre`,
`snip-test-pre`, `snip-build`, `snip-test1`, `snip-t2`, `snip-mut`, `snip-driver`,
`snip-core`, `snip-base`, `snip-bin`, `snip-real`.

Root cause confirmation. Before the fix, the 12 new tests failed (`test-pre.log`); the
failures that matter show `stale logical line N` under the diagnostic header for resolve,
definition-analysis and verify, which is the F6 symptom reproduced in memory. (Some
failures in that first run were test-side: verify blocks were compared in one-shot order,
and the postcondition excerpt expected line was wrong; fixed afterwards, see below.)
The source reading is at `Snippets.cs:51` (`OnDiskFileSystem.Instance`) as in Root cause.

| Command (cwd `/workspace/dafny-optimization`) | Result |
| --- | --- |
| `dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj -m:1 -v:q` | 0 errors (1 existing VSTHRD103 warning) |
| `dotnet test Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSessionSnippetSource"` | 12 passed, 0 failed, 0 skipped (`test2.log`) |
| Mutation: hook line in `Session.Execute` replaced by a comment, rebuilt, same filter (`mutation.log`) | 10 failed, 2 passed (the two equal-root/no-root cases, which do not depend on the hook); file restored from a copy, sha256 `c3e82bea...fb6ab5d` before and after, `cmp` identical |
| `dotnet test Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSession\|FullyQualifiedName~AnalysisSourceSelection\|FullyQualifiedName~CachedParser\|FullyQualifiedName~NativeTaskEntry"` (tmux `snip-driver`, `driver-focused.log`) | 71 passed, 0 failed, 0 skipped (59 earlier + 12 new; includes `AnalysisSessionPathRemapTests`) |
| `dotnet test Source/DafnyCore.Test -m:1` (`core.log`) | 541 passed, 90 failed, 0 skipped. All 90 failures are `HelperFunctionInterpreterTest` (`Assert.NotNull` in `TryInterpret`). Baseline check: with `Snippets.cs` and `DafnyOptions.cs` temporarily reset to HEAD content (backup and sha256 in `core-backup/`, restored byte-identically, `sha256sum -c` OK) the same class fails 90 of 97 (`core-baseline.log`), so the failures are pre-existing and unrelated to this change. No existing Core reporter/snippet tests exist |
| `cd python && python3 -m pytest -q` | 105 passed, 12 deselected (opt-in native) |
| `dotnet format whitespace <csproj> --verify-no-changes --include <files>` for `DafnyOptions.cs` + `Snippets.cs` (Core), `AnalysisSessionCommand.cs` (Driver), `AnalysisSessionSnippetSourceTests.cs` (Driver.Test) | exit 0 on all three |
| `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q` (tmux `snip-bin`, `binary-build.log`) | 0 errors, 25 s (2026-11-05T01:58:44Z to 01:59:09Z); `Dafny --version` 4.11.1+0776df27c2449bad68e9a28e687bb6c70bf4b401 (dirty tree). `Dafny.dll` mtime 10:59:09 JST; newest touched source 10:58:00 (`Snippets.cs`, `DafnyOptions.cs`); `find Source -name '*.cs' -newer Dafny.dll` (excluding obj/bin) and the same for `*.csproj` print nothing |
| Real check: copies of the r2 scripts in `/workspace/tmp/session-snippet-source/real/scripts/` (only `EXP`/`ORIG`/`OUT` paths changed in `lib.py`, script paths in `s3.py` and `run_scn.sh`; originals untouched), `bash run_scn.sh s3` in tmux `snip-real`, exit 0, 10:59:37 to 11:06:08 JST; real Cosyn pool/service/one-shot with the rebuilt binary, `source_root` = attempt workspace, `logical_root` = run workspace | `out/s3/result.json`: excerpts of all 5 lease Cat.dfy diagnostics match the candidate line and 0 match the logical-root line (before: 0 and 5). assertfail verify calls 4 and 5: `27 |       assert name == "cot";`; resolvefail resolve, definition-analysis, verify: `26 |       var bogus: int := "text";`; run-level service and one-shot also match the candidate; `prove_diag` of the lease in assertfail now reads `...(27,6): Error: assertion could not be proved / 27 | assert name == "cot"; / ^^^^^^`. None of the remaining lease vs one-shot differences (6 shown per case) contains an excerpt line; they are the known earlier differences (JSON compaction, verify summary, optionsSha256, resolve warnings) |

Test-side corrections made while the new tests were being written: caret padding literal,
the postcondition's main excerpt is line 4 (`{`) in this Dafny version, and verify excerpts
are compared as sorted blocks because verification order differs from one-shot.

Skips and limits: no Cosyn edits or tests (not requested), no Docker, no LLM or provider
calls, no verifier agent yet (independent verification follows). The real check ran the
`good`, `assertfail` and `resolvefail` cases of s3 only; s1, s2 and s4 were not rerun. A
reused State is exercised by the in-memory test only (the real check has no repeated
identical request with another `source_root`). A failing result replayed across
compilations is not possible (only `Valid` results are cached), so that path has no test.
Durable findings: recorded in the wiki section "Diagnostic excerpt source (2026-11-05)".

## Independent review and close (2026-11-05)

A fresh verifier (Sonnet, high effort) accepted the change. It found no correctness,
concurrency or one-shot issue.
- Every excerpt goes through `Snippets.GetFileLine`, with the request's own
  `DafnyOptions` (a new instance per request). Reused States hold a copy made
  before the hook is set, and they never render text.
- `ReadForExcerpt` does not touch `Inputs`, fingerprints or cache identity.
- Tests:
  - Driver filters: 71 passed, including the 12 new tests.
  - Core focused: 23 passed.
  - Python: 105 passed.
  - Format: clean.
- Real binary, stale logical root: 6 of 6 cases passed, including a reused State
  under a second root and a supplied snapshot.
- Mutations (hook ignored; a static file system leaked across requests) each made
  10 of 12 new tests fail. Both were restored byte-identically. The verifier's
  `--no-incremental` rebuild after restoring wrote only to the repository build
  output. The smoke binary in `/workspace/tmp/session-cache-retention/bin` keeps
  its 10:59 timestamps.
- The 90 `HelperFunctionInterpreterTest` failures predate this change. The
  test's reflection looks for an older `PartialEvalState` constructor signature
  (`HelperFunctionInterpreterTest.cs:332` versus `PartialEvaluatorVisitor.cs:16`),
  and these tests never touch Snippets or `DafnyOptions`.
- Not covered by tests: a diagnostic in an uncaptured file, and two truly
  concurrent requests with different roots (covered only by reasoning).
