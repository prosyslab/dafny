# Native execution phase timing observations

Status: done
Date: 2026-11-12
Parent: [integration plan](../../plan/2026-11-12-cosyn-profiling.md)

## Objective and acceptance

The user authorized profiling CoSyn agents and explicitly allowed a native-verifier communication DTO. Add optional versioned timing observations to existing native session evidence so parse, resolve, compiler/admission wait, translation and actual solver work can be distinguished without changing verification semantics, caches, diagnostics or stdout. This is maintenance, not a benchmark run. No commits, pin changes, dependencies or live experiments are in scope.

Measure parse/resolve at the actual pipeline methods rather than sequential awaits of concurrent tasks. Cached verification results must not contribute old solver runtimes as new work. Return observations on failures/cancellation when possible and make absent observations explicit. Bound phase rosters and names; record no source contents, requests, credentials or model data.

## Existing code and change table

Existing `AnalysisSessionCommand.Response.NativeEvidence`, Python `NativeEvidence` and `NativeSessionCompletedProcess` carry optional run observations independent of diagnostic/output parsing. `Compilation` owns actual parse/resolve boundaries. `SharedVerifier` owns uncached translation and `NativeTaskEntry` owns solver producers versus shared subscribers. Preserve the current evidence schema with optional nested timing DTO and its own version.

| Exact files / symbols | Change, reason and currently missing behavior | Validation |
| --- | --- | --- |
| `Source/DafnyCore/Pipeline/Compilation.cs::{ParseAsync,ResolveAsync}` | Capture actual parse/resolve duration and expose immutable measured snapshot; awaited tasks currently overlap | Focused memory-native checks and build |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs::{Evidence,Session.Execute,SharedVerifier,NativeTaskEntry}` | Add optional bounded phase DTO, accurate wait/preparation/translation/analysis/solver measurements and copy to native response evidence | Focused driver memory tests; cached-hit/new-solver behavior |
| `python/dafny_analysis/session.py::{NativeEvidence,NativeSessionCompletedProcess}` | Strict additive typed DTO, aliases, finite nonnegative duration/version validation, preserve observations through CompletedProcess | `python/tests/test_session.py` memory controls and new DTO test module if needed |
| `Source/DafnyDriver.Test/NativeTaskEntryTests.cs`, `python/tests/test_session.py` | Observable native-phase coverage without a provider or bulk outputs | Targeted `dotnet test --no-build` filter after build; audit I/O before tests |
| `wiki/execution-profiling.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Native timing semantics, compatibility, limits and verified evidence | Links/diff review |

Update exact paths in this plan before coding if native ownership differs from the inspected map. One-shot CLI calls that do not expose native evidence retain outer operation timings; do not inject unstructured stderr sentinels or mislabel whole verification wall time as solver-only time.

## Validation

Workdir `/workspace/dafny`. Inspect local `AGENTS.md`, `CLAUDE.md`, `.editorconfig` and test helpers first. Run Python memory tests serially with `python3 -m pytest -q -n 0 python/tests/<affected memory modules>`. Build production code outside a test with `dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore` (existing dependencies required). Run focused native unit tests only after auditing complete helper and native file paths; never put compilation generation inside Python development tests. Format touched C# with repository conventions and `dotnet format whitespace ... --no-restore --include <changed files>` if available; avoid broad unrelated formatting. Record the exact final commands/filters before execution. A build pass does not establish Dafny proof correctness or deployed image adoption.

If a compatible local analysis client is needed, use an isolated process `PYTHONPATH=/workspace/dafny/python:/workspace/cosyn/src:/workspace/src` for checks rather than changing global installations. Do not move compiler checkouts into `bench/`. Non-sensitive temporary evidence belongs in `/workspace/tmp/cosyn-profiling/`. Initial native checkout on `expecto` is clean. No hidden task/reference data are authorized test inputs.

## Progress and closure

Implementation, focused native tests, independent verification and durable documentation are complete; see final acceptance below. Native runtime/image pins remain unchanged; release integration is separate from local source and DTO verification.

Implementation detail: `Request.ProfileTimings` negotiates the optional field; the Python client requests it and older servers may ignore it. Durations are seconds in a bounded fixed-name dictionary; translation and VC preparation measure producer work and may overlap proof-input preparation. Native task runtimes count only freshly started producers. Initial commit `9f281d50a7befa662350be47dd73ff0b2e0bb8d9`; initial tracked source clean, plan/index already modified. SDK 8.0.133.

## Implementation and validation, 2026-11-12

Implemented the agreed opt-in DTO and client request. The compilation measures parsing and resolution after prerequisites. The session includes all admission and compiler gate waits, including interrupted waits; fresh translation and VC preparation are accumulated while holding the preparation gates. Proof-input preparation includes translation. Analysis is a request duration. Solver runtime sums only newly started producers whose `TryRun` created work; cached result durations are not counted. Its sum can exceed wall time because batches run concurrently. Incomplete phases may be absent. Added the timing semantics to [the wiki](../wiki/execution-profiling.md). These were the initial owner observations before independent review; final acceptance is recorded below.

Commands below ran from `/workspace/dafny`; SDK 8.0.133. Initial source commit and dirty state are recorded above; the final worktree contains the listed changes and records. Temporary logs and marker are in `/workspace/tmp/cosyn-profiling/` and are not durable.

- `dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore` failed with no diagnostic, and diagnostic output is in `dafny-build.log`.
- A serial attempt with `-m:1` regenerated the parser identically (no tracked generated diff), then Gradle failed on read-only `/home/vscode/.gradle` and the stalled attempt was interrupted. No Gradle cache or installation was changed.
- `DOTNET_CLI_TELEMETRY_OPTOUT=1 dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -m:1 -p:DafnyRuntimeJar=/workspace/tmp/cosyn-profiling/existing-java-runtime.marker` passed with eight unrelated warnings. The timestamp marker bypassed rebuilding the already-present Java runtime jar; it does not validate Java runtime generation. `dafny-serial-build.log` records output.
- `DOTNET_CLI_TELEMETRY_OPTOUT=1 dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore -m:1 -p:SkipFocusedTestAssets=true -p:DafnyRuntimeJar=/workspace/tmp/cosyn-profiling/existing-java-runtime.marker` passed after final edits; incremental output is in `dafny-test-build-final2.log`. The explicit asset flag avoids copying Z3 assets.
- `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~NativeTaskEntryTests' -p:SkipFocusedTestAssets=true` passed 16 tests, zero skipped. Default sandbox denied the local loopback socket used by VSTest; the successful rerun used approved sandbox escalation. Test setup, fake task and target tests were inspected for I/O; they do not stage files or launch native solvers.
- `PYTHONPATH=/workspace/dafny/python:/workspace/cosyn/src:/workspace/src python3 -m pytest -q -n 0 python/tests/test_session.py -k 'native_timing or retention_counters or typed_evidence'` passed seven tests, 102 deselected. The test inputs and fake process transport are in memory; no generated compilation or fsync is involved.
- Scoped `dotnet format whitespace Source/DafnyDriver/DafnyDriver.csproj --no-restore --include Source/DafnyDriver/Commands/AnalysisSessionCommand.cs` stalled without output and was interrupted. Touched blocks were formatted manually; `git diff --check` passed.
- `find plan wiki -type f ! -name '*.md' -print` returned no violations.

Limits: the tests cover DTO negotiation and rejection, fresh/reused fake producer semantics, and the error path; at that point they did not exercise actual parse/resolve, translation or solver timings end to end. No paid run, Dafny proof suite, image build or deployment was performed. These owner results preceded independent review; final acceptance is recorded below.

### Additional native in-memory coverage

Extend `Source/DafnyDriver.Test/NativeTaskEntryTests.cs` with a `Session.Execute` resolve request against one synthetic source snapshot and a repeated identical request. Assert successful actual parse and resolve durations on the first request and omission of both stale durations on the reused compilation. The snapshot filesystem resolves supplied source roots without creating a file or directory; no solver is invoked. Build the test project with the existing serial asset flags above and run only this new test with `--no-build`.

The focused snapshot test passed (1 passed, 0 skipped) using `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~SnapshotResolutionTimingsDoNotReplayOnReuse' -p:SkipFocusedTestAssets=true` with the previously approved loopback escalation. The preceding serial test-project build passed with eight pre-existing warnings; temporary output is `/workspace/tmp/cosyn-profiling/dafny-snapshot-test-build.log`. The test checks actual parse and resolve timings and same-state reuse. It does not establish translation, solver timing, or deployed-runtime behavior. No solver, source files or source directories were created.

Independent review found that `math.isfinite` raises `OverflowError` for an oversized JSON integer before Pydantic can reject it. The Python DTO now checks against the largest finite float before calling `math.isfinite`; a transport regression supplies `10**1000` and confirms `SessionProtocolError`. `PYTHONPATH=/workspace/dafny/python:/workspace/cosyn/src:/workspace/src python3 -m pytest -q -n 0 python/tests/test_session.py -k 'native_timing'` passed 6 tests, 104 deselected. No native source changed for this correction.

## Final independent acceptance

The fresh verification agent reviewed current source and found no blocking findings on 2026-11-12. Focused owner checks and independent checks passed; see the parent integration plan for the consolidated evidence. Implementation and documentation are complete. Existing images, installed client, pins and services remain unchanged; no live provider, benchmark, real SMT campaign or deployment was run. Source release/rollout is separate from this completed implementation scope.

## Commit authorization, 2026-11-12

After the completed implementation and independent review, the user explicitly requested commits. Commit the native/client timing DTO, pipeline observations, focused tests and owner records together. Publishing and consumer pin updates remain separate. No source behavior changed for this commit handoff. Existing verification remains applicable; inspect staged diffs and run configured commit hooks. No push is included.
