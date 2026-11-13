# Native verification OOM investigation and repair

Status: done
Date: 2026-11-12
Parent: [weekly R4 root cause and repair](../../plan/2026-11-12-native-verification-oom.md)

## Objective and acceptance

Identify and repair the native allocation/retention defect behind repeated
verification OOMs, preserving proof results, options, cache authority, selected
scope, cancellation and complete diagnostics. The user approved planning and
implementation. This is maintenance; private benchmark inputs must remain in
their isolated location and must not enter documentation or future prompts.

The root plan records actual R4 evidence and authorization. Distinguish a
confirmed memory mechanism from risks discovered during inspection. A bounded
diagnostic and behavioral regression must demonstrate the repaired mechanism.
No live provider experiments, commits, pin changes or running-cohort mutation.

## Existing code reviewed

`AnalysisSessionCommand.Session.Execute`, `State.VerificationTasks`,
`SharedVerifier`, `NativeTaskEntry`, `NativeImplementationCompletion`,
`NativeVerificationCache`, `DafnyProgramVerifier`, and in-memory session/cache
tests. Initial HEAD is `466072769`, clean native worktree; .NET SDK is 8.0.133.
Whole-module task preparation, sixteen checker concurrency, and full result
retention require investigation; none is yet asserted to be the sole cause.

## Change table

| Files/symbols | Intended change | Why/current gap | Check |
| --- | --- | --- | --- |
| This plan and `plan/INDEX.md` | Record diagnosis and exact repair before edits | No verified native OOM diagnosis | Review changes against actual commands |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: `Session.Execute`, `State`, `SharedVerifier`, native completion/task lifecycle | Diagnose peak allocation and retention; refine exact repair here before code edits | Selected checks exhaust the managed heap, including replacement contexts | Bounded in-memory diagnostic; affected session regression |
| `Source/DafnyDriver/NativeVerificationCache.cs`: publication/retention | Diagnose retained native result ownership; change only if causal evidence supports it | Count limits do not establish retained object lifetime | Synthetic cache/ownership regression and reuse parity |
| `Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs`: task preparation boundary | Investigate preparation allocation; change only if confirmed | Current API prepares whole native module | Scope and checksum parity controls |
| `Source/DafnyDriver.Test/` affected native session/cache tests | Focused in-memory regressions, exact files recorded before edits | Missing behavioral check for confirmed mechanism | Serial filtered test runs without temp directories or native builds inside tests |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md` | Add confirmed findings and operational limits | Native memory ownership needs durable evidence | Source/record links and independent review |

## Validation commands and boundaries

Run from `/workspace/dafny`; no package additions. Inspect test helper call paths
before running them. Use already-cached dependencies and existing build outputs.
Build affected projects separately using `dotnet build ... --no-restore -m:1` with
project-reference/runtime-generation controls as necessary; document exact final
commands before use. Run tests with `dotnet test ... --no-build --no-restore
--filter ...`; finalize filters before code edits. Use bounded in-memory source
snapshots and tiny positive/negative solver programs, no repository copies,
temporary directories, durable sync calls, or native compilation inside tests.

Format only touched C# files using local `dotnet format` with `--no-restore` and
run `git diff --check`. Independent verification must start with requirements and
current repository files in a new `gpt-6.1-sol` / `high` context.

Non-sensitive diagnostic output goes to
`/workspace/tmp/native-verification-oom/`, never records directories. Private
benchmark diagnostics stay with their authorized run. Excluded: paid runs,
benchmark sweeps, changing proof policy or heap/concurrency settings as an
unproven workaround, restarting the weekly cohort, commits and pin/image updates.

## Risks

Do not remove unselected native implementations if that changes modular keys,
checksums, solver declarations or later queries. Dropping retained graph objects
must preserve current-request diagnostics and completed cache evidence. Any
scope/approach expansion must be recorded here before implementation.

## Execution and closure

Planning approved; investigation in progress. Record exact commands, outcomes,
failed controls, versions, limits, independent review, and remaining delivery
work here. Status remains open until acceptance checks are satisfied.

The initial bounded diagnostic examines `NativeVerificationCache.PublishSuccessful`
using a synthetic in-memory successful result and weak references to its original
implementation graph, alongside its existing reuse behavior. Any repair will be
specified here before editing code. Candidate regression file:
`Source/DafnyDriver.Test/NativeVerificationCacheTests.cs`. Run the focused tests
serially with `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter
FullyQualifiedName~NativeVerificationCacheTests` after building the affected test
project separately. Intra-request allocations need an independent bounded probe;
the parent is examining the original run and will coordinate any reproduction.
Add an in-memory weak-reference regression to that test file before the repair,
using a no-inline helper to release the original identity, result, and assertion;
test both their collection while the cache stays live and reuse of the published
entry. Build only the test project against existing references with `dotnet build
Source/DafnyDriver.Test --no-restore -m:1 -p:BuildProjectReferences=false
-p:SkipFocusedTestAssets=true`, then run the single test with the no-build command
and a matching fully qualified filter. The expected initial failure documents
whether the publication path owns the original graph.

The test-project build above passed on .NET SDK 8.0.133 with one existing
VSTHRD103 warning. The first test invocation could not open the test runner's
loopback socket in the sandbox; the same focused command with loopback access
failed as expected at `references.Identity.IsAlive`. This confirms the published
entry retains the original graph while the cache lives, but does not establish
the cause of the first cold R4 failure.

A temporary diagnostic host in `/workspace/tmp/native-verification-oom/host/`
uses existing test-output assemblies, receives one in-memory request on stdin,
and reports redacted counters and first-chance OOM stacks. `dotnet restore
/workspace/tmp/native-verification-oom/host/Probe.csproj --ignore-failed-sources`
completed with a vulnerability-feed network warning; `dotnet build
/workspace/tmp/native-verification-oom/host/Probe.csproj --no-restore -m:1`
passed. A one-method in-memory verification completed with one solver run.
This scratch host is temporary and is not a source deliverable.

The archived cold replay and a tiny independent reproduction identify a prover
failure, not a managed heap exhaustion. For a bare-variable quantifier trigger,
the initial Boogie resolution reports an invalid pattern; `ModularProofKeys.Compute`
then suppresses that failure and reuses the mutated program. A later preparation
misses the original validation error and starts the solver. The tiny session
reproduces `ProverDiedException` with one solver run; the one-shot pipeline rejects
the same input in Boogie preparation. Treat these as invalid program diagnostics,
with original locations/messages, before any solver task starts.

Before implementation, add focused in-memory integration cases to
`Source/DafnyDriver.Test/AnalysisSessionRetentionTests.cs`: seed 42 invalid trigger,
repeated request, proof-input analysis, corrected valid trigger with warm reuse,
and ordinary false assertion. In `Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs`,
collect Boogie resolution/typecheck errors through `IErrorSink`, propagate a
distinct validation exception rather than treating it as unsupported proof keys,
and retain the failure for repeated attempts on the same translated program. In
`Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`, require valid cached
translations for the session entry point while preserving unsupported-key behavior
for ordinary analysis callers. `Source/DafnyCore.Test/ModularProofKeyTests.cs`
will check repeated validation on the same Boogie object.
`Source/DafnyDriver.Test/AnalysisSessionLambdaLiftingTests.cs` must also assert
the new structured validation diagnostics for its existing resolution and type
error cases; run that class with the affected driver tests.
Independent review found seeded one-shot verification also calls the stable-order
lift before Boogie's engine, and the new typed failure otherwise escapes as an
internal exception. In `Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs`,
convert this failure to source diagnostics and an empty task roster in its normal
`GetVerificationTasksAsync` entry point for CLI and LSP. Its direct translation
entry point still propagates failure to the native session's request-local
reporting path. Add a seeded one-shot in-memory stdin regression in
`Source/DafnyDriver.Test/AnalysisSessionLambdaLiftingTests.cs`. Rebuild language
server, driver, and driver tests separately with `--no-restore -m:1
-p:BuildProjectReferences=false`, then run the focused test and repeat the
affected classes serially. Independent verification must review this follow-up.
`Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`, report those diagnostics
with native source locations as completed candidate failures, preserving freshness
checks and preventing solver starts. Preserve unsupported-key fallback for other
cases. Separately, `NativeVerificationCache.PublishSuccessful` will store its
existing detached snapshot restoration rather than the original successful result,
using the proven weak-reference regression; ordinary native insert stays unchanged.

Build separately from `/workspace/dafny` with `dotnet build Source/DafnyCore
--no-restore -m:1 -p:BuildProjectReferences=false`, then `dotnet build
Source/DafnyDriver --no-restore -m:1 -p:BuildProjectReferences=false`, then the
test-project build above. Run the affected regression classes using `dotnet test
Source/DafnyDriver.Test --no-build --no-restore --filter
'FullyQualifiedName~AnalysisSessionRetentionTests|FullyQualifiedName~NativeVerificationCacheTests'`.
These session cases use tiny solver subprocesses; test runner loopback access is
required. Run relevant core proof-key tests after building their project separately.
The two-solver-path fixture requires `z3/bin/z3-4.16.0` and `z3/bin/z3-4.12.1`
adjacent to the test-output assemblies. Since asset copying was disabled, stage
two symlinks there to the existing read-only binaries under
`/workspace/_build/dafny/Binaries/z3/bin/` before rerunning; no solver binaries
are copied and no fixture setup is added to tests.

The red session regression produced one solver failure and an incomplete result.
A separate archived replay observed 18 solver launches including version checks,
13 exit-code-1 processes, no signalled process and maximum 37.03 MiB peak solver
RSS; the host process exited zero while the native response was code 6. Together
with the low managed heap and tiny reproduction, this is evidence of malformed
solver input, not host memory exhaustion. Temporary redacted observations are in
`/workspace/tmp/native-verification-oom/r4-solver-exits.jsonl` and
`/workspace/tmp/native-verification-oom/r4-solver-probe.log`.

After the source repair, the same archived request and heap cap returned native
code 2 with `completed=true`, zero selected tasks and zero solver runs; host exit
was zero. This is a bounded maintenance replay, not a provider experiment or a
claim that the candidate proof succeeds. Its redacted temporary output is
`/workspace/tmp/native-verification-oom/r4-fixed.log`.

With .NET SDK 8.0.133, the core, driver, driver test and core test projects built
separately using the commands above and `GeneratePackageOnBuild=false` for the
final core and driver builds. Core build had no warnings; driver had seven
pre-existing CS8632 nullable-context warnings; driver tests had one existing
VSTHRD103 warning and core tests one existing CS8604 warning. Test runs used
`--no-build --no-restore` and `RunConfiguration.MaxCpuCount=1`,
`xUnit.ParallelizeTestCollections=false`, `xUnit.MaxParallelThreads=1`.
Three new focused driver cases passed; the initial affected driver classes had
41 passes and one failure due to the absent two-solver test-output fixture. The
two existing binaries were subsequently linked as described above for the
independent rerun. The selected proof-key cases passed 20 of 20 with no skips.
The full-solution scoped `dotnet format whitespace --no-restore
--verify-no-changes --include ...` and a core-project attempt were interrupted
after not finishing; a driver-project attempt hit a 20-second timeout. Folder
mode rejected `--no-restore`, then `timeout 45s dotnet format whitespace
/workspace/dafny --folder --verify-no-changes --include` with the nine changed
C# paths exited zero. Folder mode does not load or restore a project. Native
`git diff --check` passed; no non-Markdown files were found in native `plan/`
and `wiki/`.

The initially failing two-solver test passed after its two existing solver binaries
were linked into the test output. The three affected driver classes then passed
49 of 49 with no skips. Independent review's earlier driver and core runs passed
83 and 75 cases respectively, but review found the seeded one-shot boundary
described above. The language server rebuilt without warnings; driver and driver
test builds retained the pre-existing warnings listed above. The new seeded
one-shot test passed twice, the last time under `timeout 45s` with standard
libraries disabled and stdin supplied from a `StringReader`. `DafnyFile` wraps
stdin directly in a `FileSnapshot`; the test does not create a source file,
temporary directory, compiled output, or durable sync call. Final independent
verification subsequently accepted the repair as recorded below.

## Final independent verification and closure

Fresh `gpt-6.1-sol` / `high` review started from requirements and current source,
without the development conversation. It accepted the final owner boundary with
no remaining actionable finding after its seeded CLI finding was repaired.
Commands ran serially from `/workspace/dafny` with Debug/net8.0 outputs,
`--no-build --no-restore`, and `-- RunConfiguration.MaxCpuCount=1`. Driver assembly
and affected core collections disable xUnit parallelization. Approved loopback
access was needed for vstest; sandbox-denied attempts executed no tests.

| Project and fully qualified name filter | Result |
| --- | --- |
| `Source/DafnyDriver.Test`: `NativeVerificationCacheTests`, `NativeTaskEntryTests`, `AnalysisSessionRetentionTests`, `AnalysisSessionLambdaLiftingTests`, `AnalysisSessionDiagnosticLocationTests` | 83 passed, no skips; before final CLI follow-up |
| `Source/DafnyCore.Test`: `ModularProofKeyTests` | 75 passed, no skips |
| `Source/DafnyDriver.Test`: `AnalysisSessionLambdaLiftingTests`, `AnalysisSessionRetentionTests` | 26 passed, no skips; final source |
| `Source/DafnyCore.Test`: `StableSeedTests` | 14 passed, no skips; final source |

For each row, the exact `--filter` joins the names with `|`, prefixing every name
with `FullyQualifiedName~`. External seeded stdin verification now returns 2
with the original pattern diagnostic at `<stdin>(1,49)` and terminates normally;
its valid control returns 0 with one verified proof. The reviewer corrected its
initial expected-column assertion before both final controls passed. These are
bounded native controls, not benchmark or provider runs.

`timeout 45s dotnet format whitespace /workspace/dafny --folder
--verify-no-changes --include <all nine changed C# paths>` passed. Folder mode
does not load a project and rejects `--no-restore`, so that flag was omitted.
Earlier graph-loading formatter attempts timed out/interrupted and are not
passes. Native `git diff --check` passed; recursive plan/wiki inspection found
no non-Markdown artifacts.

The parent rebuilt the diagnostic host from final local DLLs, then replayed the
archived R4 input in tmux session `r4-final`, socket
`native-verification-oom-r4`, with the same snapshots, real solver, 10 GiB cap,
seed and verification timeouts. Temporary `r4-final.log` and `r4-final.exit`
under `/workspace/tmp/native-verification-oom/` record host exit 0, native code 2,
completed rejection, zero tasks and zero solver runs. No proof success or repaired
historical result is claimed.

Changes and indexes match this plan; durable findings are in
[native session knowledge](../wiki/native-analysis-session.md#boogie-validation-before-verification-2026-11-12).
Native base is `466072769` with uncommitted changes. No commit, pin update, image
build, paid experiment, active-container mutation or official downstream grading
was performed. The local source repair is complete; future pinned runtime/image
adoption is outside this scope. Private source remains in the original isolated
run; maintenance scratch contains redacted operational evidence only.

Delivery (2026-11-13): the user approved committing this repair, publishing it
on `expecto` and adopting it as the root and Cosyn pin after weekly run
`weekly-20261112t164226z-ea5d937c1c94` lost two more trials to the same
invalid-trigger failure. Pin adoption and image evidence are recorded in the
[parent plan](../../plan/2026-11-12-native-verification-oom.md).
