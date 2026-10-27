# Repair PBT preparation and compilation bottlenecks

Status: done (scoped preparation/compiler repair; end-to-end PBT remains incomplete)
Date: 2026-10-26
Parent: [counterexample loop](../../plan/2026-10-26-pbt-counterexample-loop.md)

## Objective and evidence

The user prioritizes the demonstrated PBT bottleneck before further experiments.
Defer the prepared budget-only image/operator replay and any fresh model trial.
Keep R13 and its evidence immutable. The sampling-budget repair has independent
source/local acceptance and actual CLI publication, but no campaign efficacy claim.

Retained R13 call4 phase evidence measures about29.9s before transformation,
73.1s for two transformation/resolution rounds and51.38s in the compiler worker.
Native total154.37s is not a C#-only duration. Generated-project/DLL timestamps
give an approximate18.24s C# interval, not an instrumented timer. The first
transformed diagnostic has ghost-context errors; the second has no diagnostics.
Those retries and source-closure work remain separate investigations.

Current runner resolves the final transformed sources and computes compiled
check literals, then ContractCompilerWorker resolves those same sources again.
Its second resolve uses compiler-specific options, so direct AST reuse without
moving configuration before the accepted resolve is unsafe. Tuple wrapper
representation and resolver/plugin behavior can depend on those settings.

Read-only independent inspection establishes the required option lifetime:
resolve every attempt with a fully copied, compilation-configured options object;
leave shared options unchanged through retries. At the old compile boundary,
apply the exact existing settings to shared options as before, while compiling
the retained program with its original configured clone/backend. Preserve shared
options identity for later classification/query construction, including the
generator-proof replacement case. Do not assign shared options to the clone.

## Acceptance and non-goals

- Every transformed attempt receives its compiler settings before parse/resolve.
- Compile only the final accepted, zero-error program from that exact
  transformation; the compiler path must perform no further parse/resolve.
- Keep compiled-check discovery and code generation on the same Program object.
- Keep existing main selection, post-verification rewriters, dependencies/hash
  checks, executable assembly checks, aggregate deadline and cancellation.
- Preserve original/transformed/query source sets, authority, obligations,
  exclusions, classification and runtime-observation semantics. No new fallback.
- Add pure in-memory regression cases with no directory/file creation, native
  compilation, solver process or synchronization. Delete the existing sole direct
  caller test with a prohibited directory/native-build fixture rather than retain
  a compatibility parse path for it.
- Record phase observations for staging and actual target compilation separately
  using the existing optional observer; do not claim those are pure C# timers.

No benchmark contract change, coverage reduction, paid provider dispatch, package,
global cache, compiler-server reuse, new result schema or live-image mutation.
Do not modify the transformation retry policy until a separate demonstrated cause,
exact repair and validation are added to this plan. The current task does not claim
that all preprocessing can disappear or that a counterexample has been found.

Read-only source investigation additionally confirms repeated whole-source UTF-8
encoding in `Text`/`Index` and repeated immutable-string Remove/Insert copying in
`Apply`. Optimize these exact operations within this plan: cache source bytes for
text extraction and render accepted edits in one forward pass. Retain existing
containment and overlap rejection semantics, including equal-position insertion
order, replacement boundaries and Unicode byte offsets. Keep the existing
containment/overlap selection algorithm initially; removing its quadratic scans
is not required for this repair. Do not remove resolution retries or obligation
work. The final selected-draft closure resolve is also repeated by the runner,
but reusing that separate result is deferred until these changes are measured.

## Change table

| Exact file/symbol | Change, necessity and unmet behavior | Validation |
| --- | --- | --- |
| `Source/DafnyDriver/ContractTesting/ContractCompilerWorker.cs` | Factor current compilation option assignments; create an internal in-memory resolve entry and retain its Program/transformation/options/reporter together; compile the accepted value without reparsing. Keep staging, main, dependency, codegen and assembly checks. Use existing phase observation for staging/compile boundaries. | Option-copy isolation, ghost tuple representation, same Program/backend identity, error/main/cancellation rejection before I/O; source review of sole parse path and compiler behavior. |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Resolve transformed attempts via configured compiler entry, use that Program for diagnostics/lowering/check literals, retain only the final accepted attempt and pass it to compilation. Apply shared option mutations at the existing compile boundary. Preserve accepted sampling-budget repair. | Pure seam tests and independent control-flow review, including lowered/rejected attempts and generator-proof option identity. |
| `Source/DafnyDriver.Test/ContractRuntime/CompilationResolutionTests.cs` | Meaningful small memory-only regression cases using existing SnapshotFileSystem/NoProverFactory patterns. Stop before disk/code generation; no native-build fake that accidentally reaches I/O. | Full fixture/helper call-path audit; focused no-build/no-restore test invocation after a separate bounded assembly build. |
| `Source/DafnyDriver.Test/ContractRuntimeRecordingTests.cs` | Delete the sole old-signature direct caller and its exclusive fixture/source. Every case reaches RuntimeFixture, which creates a directory and compiles generated code; repository rules prohibit retaining this workload. | Search for exclusive references; build consistency; do not execute the removed workload or recreate it elsewhere. |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs`: `Text`, `Index`, `Apply`, source-byte lookup | Cache immutable source bytes for slicing; replace repeated whole-source string edits with a single forward renderer after unchanged containment/overlap selection. This removes repeated encoding/copying without changing which checks or edits survive. | Existing pure transform regressions and new bounded ASCII/Unicode, equal-offset insertion, replacement-boundary, nested-removal and invalid-overlap cases. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs` | Add only small in-memory renderer/transform regressions; reuse audited MemoryOptions/NoProverFactory. | Exact output/AST/hash behavior, including prior swallowed-interior-insertion regression; no source substring-only prompt tests or native execution. |
| This plan/index; `wiki/pbt-trusted-sources.md`/index; linked Cosyn PBT plans/index/wiki | Record measured bottleneck, accepted source behavior and remaining actual performance/sampling limits. | Independent evidence/diff/Markdown-only audit; no candidate source or witness in shared docs. |
| `/workspace/tmp/pbt-preparation-bottleneck-20261026/native-test-build.py` | Derive the existing bounded standalone Driver test build worker with the prior14 production pins plus compiler worker and new test, settled only after source freeze. | AST/Ruff review, exact16 before/after hashes,600s/256KiB bound, named tmux, fresh product/test assembly binding. |
| `/workspace/tmp/pbt-preparation-bottleneck-20261026/transform-test-build.py` | Derive the same bounded assembly-build worker for DafnyTestGeneration.Test; bind the edited transformer/test and exact production inputs. | Separate serial build in tmux; no native build reachable from selected tests. |

## Validation

Working directory `/workspace/cosyn/dafny`; read AGENTS.md, CLAUDE.md, Makefile and
explicit parent instructions. No additional directory instructions exist for the
listed source/test paths. Separate implementation and independent verification.

Scoped `dotnet format whitespace Source/Dafny.sln --no-restore --include` for the
three edited C# files, followed by `--verify-no-changes`. `git diff --check` for
the scope and recursive Markdown-only plan/wiki inspection.

Separate operator assembly build in tmux, bounded600s/256KiB:
`dotnet msbuild Source/DafnyDriver.Test/DafnyDriver.Test.csproj -nologo -t:Build -verbosity:minimal -maxCpuCount:1 -nodeReuse:false -p:SkipFocusedTestAssets=true`.
After auditing the complete selected call paths:
`dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~CompilationResolutionTests|FullyQualifiedName~SamplingBudgetTests' -v:minimal`.
No broad native campaign suite, native compiler or solver inside development tests.
For the source-edit change, separately build
`Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj` with the same
bounded msbuild flags, then run the fully audited pure `ContractRuntimeObligationTests`
filter with `--no-build --no-restore`. Format the transformer and its test file
with the same scoped formatter. Record accepted fixture/output equivalence;
source-operation improvements alone do not establish measured speedup.
The test build can update host dependency outputs; it is not CLI publication or
image acceptance. Record actual tested source/assembly identity, versions/results
and all unrun checks.

Only after source acceptance will the parent plan update pins for a separately
bounded same-request operator measurement. No fresh model dispatch while fixing
this bottleneck. Existing R13 outcome and all old artifacts are preserved.

## Risks and approval

Configuring shared options before retry resolution would alter the original AST's
subsequent transformations. Reusing a program resolved with different options would
change tuple/codegen behavior. Replacing shared options outright would alter
classification's observable settings. Preserve all three boundaries explicitly.
Compilation mutates its accepted AST; it must not consume an earlier failed/lowered
attempt. Preserve cancellation checks before any staging/compiler activity.

The user's latest instruction authorizes this root-cause performance repair.
No additional permission, package or benchmark policy change is required.

## Source verification and Driver fixture correction

The two separate assembly builds completed0 with all16 exact inputs matched.
Independent transformer verification passed35/failed0/skipped0 using the audited
memory-only owner filter. Its artifacts are under
`/workspace/tmp/pbt-preparation-bottleneck-20261026/independent-transform-tests*`.
Driver verification passed14/failed1: the test incorrectly assumed a true default
for OptimizeErasableDatatypeWrapper instead of setting the intended non-compilation
caller value. The test now explicitly sets true; production code is unchanged.
Preserve `driver-memory-tests-initial.log` and the original assembly result.

Add `/workspace/tmp/pbt-preparation-bottleneck-20261026/native-test-build-r02.py`,
derived only by the corrected test pin and distinct r02 log/result filenames.
The existing bounded600s/256KiB,16-source before/after and fresh assembly checks
apply. Dispatch this separate rebuild in named tmux, then independently rerun the
same15 selected cases with fresh identities. This is necessary for acceptance;
the stale pre-correction assembly must not be reported as passing.

The user now explicitly authorizes all three stated workstreams: remove sample
execution blockers; reduce agent preparation round trips with fast checks/actionable
feedback; reduce repeated preprocessing and optimize compilation. Further exact
file/change scope is being designed before edits. No fresh model trial is needed
to inspect or verify the tool repairs, and no benchmark contract is relaxed.

## Authorized expansion: preparation reuse and diagnostic compilation

Ready: 2026-10-26. This expansion supersedes the earlier deferral of selected-draft
closure reuse. Structured feedback will have its own explicit wire plan before
edits; old wire behavior remains required. The corrected Driver baseline passed
15/0/0 with test assembly `d18ddbd925e566babe664c793e313534a61710709971f4acff091cd7f328e765`.

Additional acceptance: retain the final resolved runtime preparation as a single
source/program/options/diagnostics bundle, remove only the runner's duplicate
resolve, and preserve source closure iterations and authoritative proof checks.
A negative-only early check may reject known unsupported receiver/heap proof cases;
passing that check never grants proof authority or removes runtime entry checks.

For PBT diagnostic assemblies only, avoid serializing the complete Dafny source,
embedding the existing runtime source, redundant package references on net8, and
duplicate generated-source writes. Use the compiler's installed DafnyRuntime.dll
through the existing backend reference mechanism. Do not change ordinary Dafny
compilation, callable reachability, declaration retention, obligations, trust,
extern source binding, or compiler-server isolation. No new package or library.
Measure distinct code generation, rendering, writes, and dotnet-build phases.

| Exact additional file/symbol | Change, necessity and unmet behavior | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSelectedDraftPreparation.cs` | Return a cohesive final runtime bundle; keep whole fallback/candidate bundles during proof dependency expansion; apply existing SupportsRequiredPostconditions only as an early negative gate. Without this, the runner resolves the same final source closure again and unsupported proof cases do unnecessary preparation. | Memory-only source/hash/options/program identity, closure extension and proof fallback, visible negative and hidden proof-only heap cases. |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Consume that exact runtime bundle, preserve deferred diagnostic artifact and all later selection/audit/missing/proof replacement checks. | Independent control-flow and identity review plus existing pure cases. Coordinate this file with later feedback work sequentially. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSelectedDraftPreparationTests.cs` | Add small in-memory preparation reuse and negative-gate regressions using SnapshotFileSystem/NoProverFactory. | Audited selected no-build/no-restore owner filter. |
| `Source/DafnyDriver/ContractTesting/ContractCsharpBackend.cs` (new), `ContractCompilerWorker.cs` | PBT-only C# backend chooses trusted runtime reference, omitted source attribute/translation record, net8 built-in framework references and exact phase observation. Validate compiler settings before I/O as before. | Pure option/backend identity and XML/rendered-code tests; actual bounded offline Csplit replay must establish assembly/runtime/extern execution. |
| `Source/DafnyCore/Backends/CSharp/CsharpBackend.cs` | Factor protected project-generation/build-process hooks without changing the ordinary backend's project or behavior. PBT subclass removes only obsolete framework package references. | Pure project XML checks for retained runtime/user references and normal backend defaults. |
| `Source/DafnyCore/Backends/CSharp/CsharpCodeGenerator.cs` | Narrow default-enabled source-attribute emission hook for PBT specialization. | In-memory rendered diagnostic contains executable code but no serialized Dafny source; ordinary backend retains source import support. |
| `Source/DafnyCore/Backends/ExecutableBackend.cs` | Default-enabled translation-record emission hook, disabled only by PBT diagnostic backend. Preserve input record merging. | Source and pure backend checks; no output-file tests. |
| `Source/DafnyDriver/Legacy/SynchronousCliCompilation.cs` | Optional internal diagnostic compilation settings skip preliminary spill already owned by C# backend and observe codegen/render/write phases. Preserve defaults for all other callers/backends. | Pure spill predicate/phase seam checks plus independent call-site audit. |
| `Source/DafnyDriver.Test/ContractRuntime/CompilationResolutionTests.cs` | Extend memory-only checks for PBT settings, rendered code/project and ordinary backend defaults. | No real process, filesystem creation, native compile or solver in test paths. |

Scoped formatting and separate bounded sequential assembly builds remain required.
After source freeze, update exact build-worker input pins before dispatch; do not
reuse old assemblies or report operator speedup from memory-only tests. Publish
the CLI and its matching runtime dependency before a dedicated PBT image replay.
The replay must retain exact original request bytes, report actual phases and
sample population, and preserve the latest image identity. Keep all prior evidence.

## Authorized expansion: preserve default arguments at runtime call boundaries

R13 call3 failed because the transformed WriteFile wrapper required an argument
that the original declaration defaulted. This is a tool defect before sampling.
Ready: 2026-10-26. Add the following exact scope before implementation:

| Exact file/symbol | Change, necessity and unmet behavior | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs`: wrapper formals, default rendering, wrapper-to-original calls, `InstrumentTypeShapes` | Preserve default expressions and nameonly on call-boundary wrappers, retain original lexical binding and authored nested ActualBindings, instrument contracted calls inside defaults, pass evaluated formals once with named actuals and explicit generic parameters. Count written bindings when inserting shape commas. Keep detached helpers unchanged and capture outer clause range only after rendering defaults. Without this, valid authored calls fail or may duplicate default evaluation. | Independent transformed AST inspection/reparse for method/function/receiver/import-alias/earlier-formal defaults, nested checked defaults, explicit and omitted named bindings and phantom generics. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs` | Small memory-only cases exercising the above observed defect and semantic edge cases; preserve the accepted renderer regressions. | Audited existing Transform/ParseMemory only, no solver/native compiler/process/directory. |

Default preservation must not suppress nested runtime obligations, evaluate a
written actual twice, or redirect ordinary default evaluation to detached goal
definitions. No source contract or benchmark behavior change is authorized.

## Authorized expansion: structured terminal feedback

Ready: 2026-10-26. Supersede the original no-new-schema non-goal only for this
compatible opt-in. Python integration is governed by the linked
[Cosyn feedback plan](../../plan/2026-10-26-pbt-preparation-feedback.md).
Request7 requires explicit draft/native extern policy and either proof setting;
it returns result4. Preserve exact old2/5→1 and4/6→3 pairings and field omission.

V4 requires `terminalStage`: input, source_preparation, transformation, compilation,
sampling, classification or supervision. It also requires `noValidSampleReasons`,
empty iff valid>0, otherwise a deterministic nonempty list drawn from
pipeline_not_reached, sampling_budget_expired, requires_rejected,
requires_unchecked, callee_contract_rejected, callee_contract_unchecked,
runtime_error, sample_timeout, worker_result_unavailable, campaign_deadline,
cancelled. Do not infer a detailed closed-query timeout from free-form strings.
Unavailable worker evidence is explicit; zero reported counters on supervisor
failure do not establish zero execution. Proof metadata presence matches request.

| Exact additional owner | Change, necessity and validation |
| --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs` | Request7/result4 constants, typed enums, nullable omitted legacy fields, request-aware version/metadata helpers. Pure JSON old/new shape and proof/version pairings. |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Request-aware failure overload preserves old helper; assign stage at known boundaries, report exact population causes and sampling-budget exit. Validate7 without changing old policies. Coordinate after closure edit freeze. |
| `Source/DafnyDriver/Commands/TestContractsCommand.cs` | Once decoded, preserve request-aware version on input/supervision/cancellation/no-result failures and validate worker pairing. Undecodable request retains legacy error. |
| `Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs` | Pure matrix, serialization/omission, deterministic mixed-population reasons and unavailable worker evidence cases. No process, solver, filesystem or campaign execution. |

Independent reviews and separate bounded builds follow source freeze. All
structured diagnostic fields describe observations and confer no proof authority.

## Consolidated build and operator measurement

After all owners freeze, prepare
`/workspace/tmp/pbt-preparation-bottleneck-20261026/native-final-build-r01.py`
from the existing bounded standalone build worker. Pin the20 scoped production
files (prior14, worker, new diagnostic backend, three Core backend files and legacy
compilation) and five selected test owners (CompilationResolutionTests,
SamplingBudgetTests, GeneratorProofResultTests, selected-draft preparation and
obligation tests). Build Driver.Test, TestGeneration.Test and CLI sequentially,
each with600s/256KiB bounds, `-maxCpuCount:1 -nodeReuse:false`, under named tmux.
No builds inside development tests. Keep an exclusive log per command and one
result manifest, exact before/after source hashes, two test assembly identities,
and published Dafny/apphost, Driver, TestGeneration, Core and DafnyRuntime products.
Do not dispatch before pins settle; later corrections use new attempt filenames.

The integration operator replay will derive a fresh helper/delta Dockerfile under
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r01/`, preserving
the old unlaunched budget-only draft. Pin the immutable R13 base, five published
products and exact retained call4 request/public extern dependency. Execute call4
once in one owned offline bounded container; call6 is deferred until call4 outcome
warrants it and scope is recorded. Preserve exact old schema/request/source bytes
for comparable timing; pure tests separately establish new7/4 behavior. New Python
code is not required inside this old-request operator replay. Dedicated PBT tag
only, latest identities before/after, no network/provider/evaluator operation.
Record phases, generated code size and population; if compilation or sampling
still fails, use that actual evidence for the next minimal repair. Parent integration
plan must record exact preparation/dispatch scope before helper mutation.

## Fresh build attempt and correction

Independent source reviews accepted the final default-binding/constructor closure,
preparation bundle/cancellation, backend and terminal metadata changes. The exact
25-input consolidated worker launched in tmux/socket
`pbt-preparation-final-build-20261026-r01` at2026-10-26T06:34:11Z. Its first project
compiled production assemblies, then failed compiling CompilationResolutionTests:
`ReadOnlyCollection<>` needed `using System.Collections.ObjectModel`. No tests ran;
no publication or operator performance result was accepted. Source25 stayed pinned.
Keep `native-final-build-r01-result.json` and its3610-byte Driver log unchanged.

Correct that test import in its existing scope. Add
`/workspace/tmp/pbt-preparation-bottleneck-20261026/native-final-build-r02.py`,
derived only by the corrected test pin and new attempt/output filenames, with the
same serial three builds, exact25 inputs and600s/256KiB per-command bounds. Verify
the tiny correction and settle r02 before dispatch in a fresh named tmux session.
The unexecuted operator helper must bind r02's accepted manifest after publication;
its20 production pins remain unchanged. Record nullable annotation warnings as
warnings, not test or publication success.

R02 launched in `pbt-preparation-final-build-20261026-r02` at06:38:52Z and failed
only the same test owner's `Render` call: options exposes `IExecutableBackend`,
while the helper requires `CsharpBackend`. Preserve its1104-byte log/result.
The test now retains and passes the typed ordinary backend local; production is
unchanged and all other signatures were checked against current definitions.
Authorize `native-final-build-r03.py` with only this test pin and attempt ID
updated, same25 inputs and bounded sequential commands. Dispatch in fresh named
tmux only after exact hash/AST checks. Bind the operator to the successfully
published final attempt's manifest; no failed attempt is publication evidence.

R03 launched at06:42:06Z in `pbt-preparation-final-build-20261026-r03` and completed
all three builds (8.150s/13.029s/4.459s), source25 unchanged. Its result manifest
SHA256 is `9f5798f2e636e2b367c93d821c58fccef05cee98f7ea48ba7be6a80e65e34639`.
Independent fresh Driver filters passed38/0/0; obligation filters passed41/0/0.
Selected-preparation filters passed31/failed1: one fixture declared an explicit
constructor but used `new C` rather than `new C()`, failing before its intended
capability gate. Preserve all final-r03 logs/results, including this failure.

Fix only that test allocation. Add a separate
`/workspace/tmp/pbt-preparation-bottleneck-20261026/selected-preparation-test-build-r04.py`
for one bounded TG.Test build, with the same exact production20/current tests5
pins and600s/256KiB limit in fresh named tmux. Record fresh test identity and verify
the five r03 published products are unchanged before/after. This is test assembly
repair, not another CLI publication; replay continues to bind r03's production
manifest. Independently rerun the corrected32-case owner only; the accepted Driver
and obligation suites need not repeat if their source/dependency products remain
identical. Do not dispatch the offline replay until this final test gate passes.

Operator capture refinement before dispatch: keep the1MiB aggregate/256KiB-per-file
trace retention bounds, but record omitted trace filenames/sizes/reasons when
successful sampling exceeds them. Retain complete in-bound files in ordinal order;
never truncate a trace and label it complete. Native result, phases, generated C#
and runtime-copy metadata remain available independently of optional trace capture.
This prevents increased sampling from turning an otherwise measurable campaign
into an artifact-capture failure. Population/result data remain complete, and any
counterexample still needs exact ordinal replay; omission is explicit evidence
limitation, never an excluded sample or passing check.

## Final local verification and operator handoff

The corrected selected-preparation fixture passed32/0failed/0skipped in4.37s
with no build/restore; r04 receipt and assembly identities match its exact test
source, and published r03 production products are unchanged. Together with the
independent Driver38 and obligation41 filters, all111 selected memory cases pass.
The production CLI publication is complete; no further source changes were needed.
Evidence is in `/workspace/tmp/pbt-preparation-bottleneck-20261026/`, including
`selected-preparation-memory-tests-final-r04-result.json`. These tests do not
establish runtime sampling or a benchmark counterexample.

The approved call4 operator helper first ran `--build` in named tmux
`pbt-csplit-performance-build-20261026-r01`. BuildKit interpreted the Dockerfile's
`FROM sha256:<local-image-id>` as a remote repository/tag and failed at metadata
lookup, before any PBT execution. Preserve the r01 helper and bounded failed-build
evidence; the parent operator plan owns the local dedicated-base-tag correction
and fresh r02 artifact names. No production repair or credential change follows
from that Dockerfile reference issue.

## Accepted same-input runtime measurement

The dedicated local-base-tag r02 build and operator replay completed. Independent
artifact review binds exact original call4/request4 bytes, source20/products5,
all64 trace files,304 phase records and unchanged latest/owned cleanup. Artifacts:
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r02/`. Native
request6/result3 compatibility was exercised; current7/4 is separately unit-tested.

| Recorded phase or size | Original R13 call4 | Repaired r02 |
| --- | ---: | ---: |
| Source preparation |17.094s|7.011s|
| Two transformation plus parse/resolve rounds |71.462s|46.001s|
| Compiler worker |51.380s|17.556s|
| Explicit dotnet build |not instrumented|15.813s|
| Generated C# |7,466,877bytes|5,184,348bytes|
| Campaign |154.369s|104.700s|

The first new sample started at76.697s;64 sample attempts consumed27.642s. Thus
the campaign totals include different accomplished work and are not a pure
compiler benchmark. Earlier approximate transformation totals are superseded by
this recomputation from exact phase events. This is a single observation, not
a repeated-run performance distribution.

All64 generated samples then failed before target execution: executed0/valid0/
runtimeErrors64/violations0. A separate generic instrumentation defect remained:
old-state capture declarations survived fixed-heap/unchecked decisions and ran
before input checks. The [capture admission follow-up](2026-10-26-pbt-old-capture-admission.md)
owns its minimal repair and new exact-input replay. It must preserve scalar
closed-query evidence and may not fabricate external ghost state. The original
performance/API changes are verified; end-to-end Csplit validation remains open.

## Final observed result and handoff, 2026-10-26

The exact-input r03 replay uses dedicated image
`cosyn-pbt-csplit-performance:20261026-r03` with immutable ID
`9012e786826d4afcd764f305c1cc108337aa413cbcde56127b915d64c9b70771`.
All shared latest IDs remain unchanged and the owned container was removed with
exact name/CID absence verified. No model/provider trial was launched.

The compiler worker measured21.339s versus original51.380s; actual dotnet build
was19.016s and generated C# was5,166,220bytes versus7,466,877. Earlier r02 measured
17.556s compiler worker, demonstrating run variability. These are separate phase
observations, not a pure C# speedup or completed campaign comparison.

All64 retained traces now reach three passed input checks, entry-heap capture and
the Executed marker, followed by a null-reference error. Thus the pre-entry capture
crash is removed. The draft first reads its context from the public external IO
singleton, whose ghost region fields have no executable initialization. The last
location marker is not an exception stack frame. No valid classified sample or
counterexample is established, and no contract or missing ghost state was invented.

Sampling finished by139.279s. Classification subsequently repeated45 failed initial
type checks (29.492s) and45 dependency-scope preparations (32.707s); the original
231782ms deadline expired before a worker result. Native supervisor zero counters
therefore mean unavailable classification, not zero observed execution. The final
campaign phase is unclosed. The complete-phase postprocessor rejected that state,
so there is no summary.json; the raw envelope and all65 artifacts are intact.

The exclusive offline `operator-observation.json` validates all artifact hashes,
64 ordinals and445 phase events, retaining native and observed counts separately
and explicitly recording the unclosed campaign. SHA256:
`aad419b510ebf33ffa5f37d6f14b12262260e39dde22110981b836708518735e`.
It is available under
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r03/`.
The remaining work is a sound external ghost-state execution model and avoiding
repeated classification work without bypassing admission. Neither is completed
by the current repair. No experiment is active; the continuing goal was cleared.

Independent final read-only audit accepted the offline observation hash, all65
artifacts, trace/phase counts, unavailable classification, cleanup and unchanged
latest identities. No discrepancy or overclaim was found.
