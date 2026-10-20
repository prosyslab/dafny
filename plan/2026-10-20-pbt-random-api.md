# PBT random API bounds and Unicode scalar draws

Status: done

## Objective and acceptance

Repository maintenance in the native Dafny repository at base `10dca3ba4a2909c11299176440401fc31413b53d`. Make the generator-facing random API expose its actual collection-size bounds and ensure inclusive character draws always return valid Unicode scalar values. `Size()` must declare and return `2 <= s <= 32`; character intervals spanning the UTF-16 surrogate gap must sample only valid characters, including both boundary endpoints. Existing streams for intervals not spanning that gap must remain unchanged. Deterministic, pure-memory unit cases must exercise those behaviors, constructor ordinal validation, reproducibility, and non-consuming size queries.

Non-goals: proof-engine changes, evaluator/scoring changes, new dependencies, command-line redesign, randomness-distribution changes outside the invalid surrogate interval, paid runs, broad native suites, commits or Git index changes (parent integration owns commits).

## Evidence, compatibility, and ownership

Read `/workspace/AGENTS.md`, `/workspace/cosyn/AGENTS.md`, native `AGENTS.md`, `CLAUDE.md`, `.editorconfig`, `Makefile`, plan/wiki indexes and current RNG/runtime/test sources. No descendant instructions exist under affected `Source/`, `plan/`, or `wiki/` trees. `PbtRandom.cs` currently builds `Dafny.Rune` directly from integer draws, but `Rune` rejects surrogate code points. `Size()` uses `min(2 + ordinal / 4, 32)`, while Dafny exposes only `nat`. The existing test project already links the exact runtime C# library files and references the native runtime; no package changes are needed. Existing source-hash pin in `ContractRuntimeLibraryTests.cs` must be updated by the parent integration owner after these edits; it is outside this agent's authorized test-file scope.

All changes belong to this native repository's RNG specification/runtime and pure unit-test layers. No proof engine, evaluator, dataset, scoring, or experiment-reporting layer changes. Preserve pre-existing `plan/INDEX.md` and resource-overflow plan changes. A public explicit-seed/ordinal constructor permits direct deterministic tests without subprocesses or filesystem setup; the existing CLI constructor delegates through it, rejecting negative ordinals so the size lower bound holds. Character rank compression removes only the surrogate gap, with one draw per call and the old path retained for unaffected intervals. Required approval: none beyond the parent task authorization; no dependencies added.

## Change table

| Exact file/symbol | Change and reason | Unmet without it | Validation |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/Library/PbtRuntime.dfy`, `PbtRandom.Source.Size`, `Char` comment | Add known size bounds and clarify Unicode scalar range | Generator proofs cannot use actual bounds; character domain unclear | Focused declaration resolution/contract inspection and formatting |
| `Source/DafnyTestGeneration/ContractTesting/Library/PbtRandom.cs`, `Source` constructors and `Char` | Explicit seed/nonnegative ordinal seam, reject negative CLI ordinals through delegation; compress surrogate gap for crossing intervals | Direct runtime tests require process state; valid char ranges can throw | Dedicated pure-memory unit cases and cached targeted build |
| `Source/DafnyTestGeneration.Test/PbtRandomSourceTests.cs` | Dedicated deterministic behavioral tests without subprocesses, tempdirs, builds, or files | No local regression of runtime promises | Filtered `dotnet test --no-build --no-restore` |
| `plan/2026-10-20-pbt-random-api.md`, `plan/INDEX.md` | Record scope, commands, outcomes, handoff | No durable maintenance audit | Diff review |
| `wiki/pbt-random-api.md`, `wiki/INDEX.md` | Record RNG scalar-domain and stream compatibility contract with evidence | Future changes may repeat surrogate bug | Source references and plan backlinks |

## Validation plan

Working directory for all commands: `/workspace/cosyn/dafny`. Cached .NET 8 SDK, restored assets, and referenced binaries are prerequisites. Builds are manual preparation, never invoked by a test. Inspect cached prerequisites first. Run:

1. `dotnet --version` and inspect Git state/revision.
2. `dotnet build Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore -p:BuildProjectReferences=false -m:1 -nr:false` and analogous test project build; expect compile success, using cached references, no restore/network.
3. `dotnet format whitespace Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --include Source/DafnyTestGeneration/ContractTesting/Library/PbtRandom.cs Source/DafnyTestGeneration.Test/PbtRandomSourceTests.cs --verify-no-changes`; expect no whitespace changes. `make format` is inspected but repository-wide rewriting is outside this narrow change.
4. `dotnet Binaries/Dafny.dll format Source/DafnyTestGeneration/ContractTesting/Library/PbtRuntime.dfy --check`; `make format-dfy` only formats Core/standard-library trees and does not cover this file.
5. `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~PbtRandomSourceTests`; expect all deterministic pure-memory cases pass. Tests call only RNG/BigInteger/Rune, SHA-256, and assertions; no fixture, subprocess, filesystem, or temp directory paths.
6. Parent/fresh verifier owns existing runtime declaration source-hash test and independent review, including API postcondition inspection or in-memory resolution. No full suite, live experiment, downstream proof claim, image build, or paid call.

Before handoff inspect `git diff --check`, exact diff and plan/wiki trees recursively for non-Markdown files. Record failures and skipped checks explicitly. Scratch, if needed, belongs in `/workspace/tmp/pbt-random-api/`, never plan/wiki.

## Execution and handoff

Implemented the planned RNG source/API changes and dedicated pure-memory tests. [Reusable findings](../wiki/pbt-random-api.md) record the scalar-gap mapping and stream compatibility. No new package, unrelated source change, Git index write, or commit. No scratch artifacts were needed.

Validation on 2026-10-20 from the native root, `.NET SDK 8.0.131`, base `10dca3ba4a2909c11299176440401fc31413b53d` plus this task's exact source changes:

- Both planned cached manual `dotnet build ... --no-restore -p:BuildProjectReferences=false -m:1 -nr:false` commands passed. Production resource build: zero warnings/errors. Test-project build: four warnings in untouched `ContractRuntimeProfile.cs` (two unreachable-code warnings), `PbtObservation.cs` (obsolete `Elements`) and `ContractPhaseTimingTests.cs` (synchronous cancellation). The test project was rebuilt once after replacing a set-equality assertion with explicit `SetEquals` before final execution.
- Planned scoped `dotnet format whitespace ... --verify-no-changes` passed, exit 0; it reported workspace-load warnings without diagnostics. `dotnet Binaries/Dafny.dll format Source/DafnyTestGeneration/ContractTesting/Library/PbtRuntime.dfy --check` passed: all files correctly formatted. Broad make-format wrappers do not provide additional necessary scoped coverage here.
- Planned filtered `dotnet test ... --no-build --no-restore --filter FullyQualifiedName~PbtRandomSourceTests` initially aborted because the sandbox prohibited VSTest's local TCP listener (`SocketException (13)`). The exact command reran with approved escalation and passed **19/19**, zero failures/skips, 43 ms reported test duration. The test bodies and their RNG callees have no filesystem/process/build/tempdir boundary; VSTest's runner transport is external to them.
- A manual Python SHA-256 computation over the original source's seed/ordinal/counter serialization supplied the preserved-stream vector: `66`, `746`, `true`, `3`, U+0023 for seed `0x0123456789ABCDEF`, ordinal 7, sequential Int/Nat/Bool/Index/Char draws. The test validates the unchanged public behavior with those exact known outputs.
- `sha256sum Source/DafnyTestGeneration/ContractTesting/Library/PbtRuntime.dfy`: `bc629d6e9ad3d5f20e64759dde905196ed5122c2404c20969f9d8ba7da7803df`. Parent integration has been notified to update the existing `ContractRuntimeLibraryTests.DafnySourceSha256` outside this agent's scope. Existing hash-pin test is not claimed passing before that update.
- Final `git diff --check` passed; source/test diff review matched the change table. Recursive `find plan wiki -type f ! -name '*.md'` returned no files. Pre-existing resource-overflow plan/index changes remain untouched.

Remaining: parent-owned exact source-hash pin update, fresh independent verification, status closeout, separate commit and main integration. The plan remains `in-progress` until those scoped acceptance prerequisites complete. No full suite, live/paid experiment, generated proof program, benchmark suite, or image build ran; none is required to establish the bounded local RNG behavior. No live process remains. Next concrete action: parent integrates the hash pin and requests a fresh independent RNG review against this plan and current source.

## Parent integration and independent acceptance

Parent updated the existing exact-resource test pin after independently checking `ReadWithoutTerminator`: raw-file SHA-256 `bc629d6e...` is not the normalized resource SHA-256. The final pin is `adcd11f333a7086255e3736b212dbd613737f7b6af084f64f86545cf76d5425e`. The initial stale/raw pin failed and was corrected; no passing claim is made for that attempt. Fresh independent source review, cached resource/test builds, scoped formatting and 23 selected pure-memory cases (19 RNG plus four library cases) passed. Evidence and exact commands: `/workspace/tmp/pbt-main-hardening-20261020/verify-rng.md`. The parent owns the user-authorized item-1 commit and main integration.
