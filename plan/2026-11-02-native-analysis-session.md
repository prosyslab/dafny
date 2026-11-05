# Persistent native analysis session

Status: done for native source/local checks; parent owns artifact/image/runtime/experiment acceptance
Date: 2026-11-02
Parent: [integration implementation](../../plan/2026-11-02-verifier-optimization-implementation.md)

Implement an execution-owned JSONL session with existing native parser, resolver,
translation, verification tasks and Boogie result cache. Preserve one-shot CLI
behavior and explicit target coverage. Exclude predictors, persistent proof
storage, benchmark sources, dependencies, commits and managed `_build` edits.
This editable worktree starts at 0776df27c2449bad68e9a28e687bb6c70bf4b401.

Reviewed: CliCompilation, VerifyCommand, DefinitionAnalysis and its proof-input
and semantic-fact helpers, Compilation, DafnyProgramVerifier, CachingParser,
CachingResolver, native filesystem interfaces, Python runner/client/models and
focused memory tests. Native reused resolved module objects identify unchanged
facts. Existing proof-input injection is internal and translation is repeated.

| Files and symbols | Change and missing behavior | Verification |
| --- | --- | --- |
| Source/DafnyCore/DefinitionAnalysis.cs; Source/DafnyCore/DefinitionAnalysis.Session.cs | Cache module declaration extraction, calls and local facts by native resolved identity; assemble current graph and source metadata | In-memory unchanged/changed module parity and counters |
| Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs; Source/DafnyCore/Pipeline/Compilation.cs; Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs | Share fresh translated hashes and native task preparation, preserve existing consumers | Focused proof identity tests, native repeated verification |
| Source/DafnyDriver/CliCompilation.cs; Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs; Source/DafnyDriver/Commands/AnalysisSessionCommand.cs; Source/DafnyDriver/DafnyNewCli.cs | Resident native service, tracked snapshots, version/context checks, native cache evicted after 32 new compilations and on context changes, bounded jobs, existing logging | Native build and tiny positive/negative/cache/cancellation smoke |
| Source/DafnyDriver/VerificationResultLogger.cs; Source/DafnyDriver/JsonVerificationLogger.cs; Source/DafnyDriver/TextVerificationLogger.cs | Request-specific report paths and bounded logger/queue/stream ownership; direct request-owned task futures replace shared Compilation event observers | Actual JSON/TRX and concurrent native controls |
| python/dafny_analysis/session.py; python/tests/test_session.py | Host-owned process transport, bounded JSONL, request identity, cancellation and typed evidence | In-memory fake process/stream tests and Ruff |
| Source/DafnyCore.Test/DefinitionAnalysisSessionTests.cs | Module-fact extraction/invalidation controls using strict in-memory sources | Focused dotnet memory checks |
| Source/DafnyDriver.Test/NativeTaskEntryTests.cs | Controlled native-task completion, independent subscriber cancellation and drain ownership | Fake Boogie tasks and explicit in-memory barriers; no solver/process/files |
| Source/DafnyDriver/Commands/AnalysisSessionCommand.cs; Source/DafnyDriver.Test/AnalysisSessionOutputTests.cs | Route proof-input request diagnostics to stderr before JSON emission, preserving the existing one-shot behavior and warning policy | In-memory real diagnostic writer/output separation regression; public library-warning and exact recorded-source native controls in parent-owned isolated containers |
| Source/DafnyCore/Resolver/ProgramResolver.cs::ProcessDependenciesDefinition; Source/DafnyDriver.Test/CachedParserAnalysisTests.cs | Preserve validated ModuleExportDecl owner instead of captured parsed owner on cache hits | Real memory parser/resolver exports; owner/signature identity; complete document parity with fresh/reused facts, changed importer/dependency and root-set transitions; no filesystem/solver |
| AnalysisSessionCommand.NativeImplementationCompletion; NativeTaskEntryTests | Publish complete all-Valid native split results through existing Boogie Cache.Insert; strengthen native implementation checksum with existing proof-input fingerprint because native dependency collection omits arbitrary axioms; task API reads but does not populate that cache | Partial/invalid/cancelled split controls and actual cross-compilation native replay |
| Source/DafnyRuntime/DafnyRuntime.csproj | Optional DafnyGradleArguments property keeps default build unchanged while developer artifact build requests offline serial Gradle | Runtime-focused offline build |
| wiki/native-analysis-session.md; wiki/INDEX.md; this plan and plan/INDEX.md | Evidence, lifecycle and delivery limits | Diff/index/Markdown-only review |

Pass criteria: identical repeated inputs reuse actual resolved program and facts;
independent file/module edits reuse unaffected native module facts; proof inputs
and verification share one translation per compilation/module; native cache
replays across compilations; changes never import stale success; snapshot and
epoch provenance survive transport; native errors/cancellation remain terminal
failures; host CLI/report contracts stay compatible.

Compatibility risks: native mutable AST/static state requires serialized
preparation; task completion and solver teardown differ; context option changes
must partition caches; consumed input discovery must remain native. Python
transport does not parse Dafny includes. Native source and package delivery use
an explicit separately attested development artifact, preserving clean-pin
builders. No additional approval is required within the parent authorization.

Checks from this repository: `dotnet build Source/DafnyDriver/DafnyDriver.csproj
--no-restore`; focused `dotnet test Source/DafnyCore.Test --filter
FullyQualifiedName~DefinitionAnalysisSessionTests -p:SkipFocusedTestAssets=true`;
`python3 -m pytest -q python/tests/test_session.py`; scoped `ruff check` and
`ruff format --check`. Builds emit normal artifacts; memory tests stage no files
and invoke no solvers. Final native smoke is a tiny public synthetic maintenance
experiment under tmux, with artifacts under `/workspace/tmp/native-analysis-session`.
No paid run or benchmark proof belongs to this owner task.

## Proof-input diagnostic correction (2026-11-03)

Parent raw reproduction confirms session-only JSON contamination: nine library
warnings precede a valid proof-input document with rc0. Both one-shot modes parse
the exact recorded source and put the same warnings on stderr. Add only matching
request-local writer routing and focused regression before a new parent v4
artifact/image. Existing v3 model/measurement containers retain their frozen
binaries; current source now intentionally advances beyond native manifest
e81171fd… after this plan update. No warning suppression, permissive parsing,
proof-option change or one-shot behavior change is allowed. Record new source
identity and validate routing/caches using the explicit producer and parent
controls. Parent owns interruption and replacement model accounting.

Root implemented request-local routing plus six bounded real diagnostic-writer
cases. Serial checks from this worktree first flagged two adjacent pattern-indent
lines; only those spaces were corrected. Retry actual tmux session
`proof-input-output-checks-20261103-r2` passes whitespace, production Driver build,
focused Driver.Test build and19affected cases with0skips. Raw helper session
metadata retains the base name; actual suffix is recorded here. Evidence:
`/workspace/tmp/experiment/verifier-optimization-v4/output-check-results-2.json`.
No Core/LanguageServer semantics changed; no duplicate broad suite is needed.
Fresh independent review accepts this source/test boundary, while new-image
warning-policy and recorded-source controls remain pending. Freeze native source
after these record updates for the parent v4 producer.

## Resolved export ownership correction (2026-11-03)

V4warning-policy and16validator controls pass, but independent full typed
comparison finds export BenchItem.BenchItem has bodyVisibility only in uncached
output. ProgramResolver's pointer setter captures the parsed module and reassigns
the cached export owner after its literal owner was replaced. Export resolution
occurs inside its literal; the separate graph node is a no-op dependent on that
literal. Preserve its validated owner, with fresh-fact-cache regressions so memo
reuse cannot hide the error. Other declaration handling stays unchanged.
No forced resolved bool, unrelated policy rewrite, parser normalization or new
public API is needed. This reopens source beyond frozen v4; parent v5binds the
new source/control evidence before Topdown retry. V4is separate I/O evidence,
not full integration GO. Parent owns real native/container/model execution.

The export-only owner guard and two real in-memory regressions now pass serial
Core84/Driver21 with0skips. Fresh/reused facts, resolution-only warming, explicit
root sets, helper/importer edits, empty exports and cached invalid-export repair
are covered. Initial test compilation failed at three unsupported traversal API
calls; switching to existing Descendants() preserves every export assertion.
Production/test builds and scoped formatting pass. Evidence remains under
`/workspace/tmp/experiment/verifier-optimization-v5/check-results{,-2}.json`.
Fresh independent review verifies source hashes and raw gates and accepts v5
artifact construction. No remaining source/local check is open for this owner
phase. All real artifact/image/strict recorded metadata/warning/proof controls
and model trials remain mandatory in the parent plan; this ownership split
removes no acceptance check. The source record is frozen before those parent
gates, and their eventual results are recorded there rather than mutating this
build input solely to update status. A newly found source defect reopens this
owner plan normally. Historical pending-image notes below describe their times.

## Evidence and progress

Plan ready and implementation authorized by parent. Native source and client are
implemented; final native controls and independent review are accepted. Fresh artifact and image validation remain parent-owned.
The final approach uses request-owned native task futures. Sharing Compilation
verification events was rejected because subscribers cannot safely own cancellation
or results from another request. Each resolved module translation is shared with
proof-input extraction and native task preparation.

Toolchain and source: exact base 0776df27c2449bad68e9a28e687bb6c70bf4b401,
intentionally dirty editable developer worktree, .NET SDK 8.0.133. No commits,
benchmark solutions, paid runs or dependency changes. Scratch evidence is temporary
under [/workspace/tmp/native-analysis-session](/workspace/tmp/native-analysis-session).

Build recovery and evidence:

- Parent restored the seven wrapper projects strictly offline with
  `dotnet restore Source/Dafny/Dafny.csproj --source /home/vscode/.nuget/packages
  --disable-parallel -p:BuildInParallel=false -m:1` (exit 0). The earlier Driver
  six-project offline restore also passed. No credentials or root caches were read.
- Parent built the complete wrapper in the dedicated unprivileged, network-none
  container, with `dotnet build Source/Dafny/Dafny.csproj --no-restore
  --no-incremental -m:1 -p:BuildInParallel=false -p:UseSharedCompilation=false
  '-p:DafnyGradleArguments=--offline --no-daemon --max-workers=1'`. It passed in
  1:51.84 with 0 errors and 13 warnings; Java rebuilt successfully in 17 seconds.
  Task-local Gradle home is `/workspace/tmp/native-analysis-session/gradle-home`.
  This was compiler feedback before source freeze, not final artifact attestation.
- Earlier compile-only feedback borrowed four exact-pin reference/output assemblies
  from the managed checkout. The later full source build regenerated the closure;
  no borrowed Java artifact or generated source edit was used. The two explicitly
  authorized regular Z3 executables were copied from the exact-pin managed Binaries;
  public smoke producer metadata records both SHA256 digests.
- Current affected local builds use the restored assets and existing build closure:
  `dotnet build <Core|Driver|Dafny|Core.Test|Driver.Test.csproj> --no-restore -m:1
  -p:BuildProjectReferences=false -v:q`, with `-p:SkipFocusedTestAssets=true` on
  focused test projects. Logs are task-local. These checks do not replace the final
  fresh container artifact build.

Python client owner evidence (final alias-safe revision): `PYTHONPATH=python
python3 -m pytest -q python/tests/test_session.py -m ''` passed 45 memory cases in
0.55 seconds; Ruff format/check and scoped Pyright passed with 0 errors. Python
3.12.3, pytest 9.2.0, Ruff 0.15.12, Pydantic 2.14.2 and Pyright 1.1.414. The
Pyright environment config is task-local. Cases use fake process/filesystem/group
boundaries; no native process, provider, temporary directory or synchronization
operation is used. Independent reviewer repeated all 45 successfully.

Native controls use tiny public symbolic programs under approved tmux. The first
controls exposed a real shared-translation token mutation: Boogie's ordinary
TokenTextWriter assigns fresh tokens by default. Fingerprinting now calls its
existing five-argument constructor with setTokens=false. A memory regression
checks original declaration/assertion token object identities. Earlier failed
control artifacts are retained task-local. Cold and warm same-state verification
then showed one solver producer followed by one reuse and no producer, with
distinct real JSON/TRX report paths. Cross-compilation replay exposed that the
native VerificationTask API reads its cache but does not insert results. The
session now publishes only a complete native implementation roster whose every
split terminated Valid, through Boogie's own Cache.Insert. Native dependency
collection and Cache.Lookup retain ownership of reuse decisions; no proof cache
or body-only checksum decision is introduced. Partial, failing, cancelled or
unknown results are never inserted. Final cross-compilation controls pass; see the final table and independent acceptance below.

Pinned Boogie source review uses package commit
`d90c6c9ef7e0e244cef55ddd0557e28a1a1301d8` from the installed nuspec. Relevant
primary sources are ExecutionEngine.GetVerificationTasks/GetPrioritizedImplementations,
VerificationTask, VerificationResultCache, DependencyCollector and
ImplementationRunResult. Downloaded source snapshots are task-local review evidence,
not dependencies. The independent reviewer confirmed split-index ordering,
checksum/dependency checks and native terminal completion behavior.

A child escalation tool call twice stalled awaiting approval rather than running a
build. Parent interrupted both stalls. Subsequent controls use the already approved
standalone tmux command; no new approval or alternate network path was used. Host
unit testhost networking is sandbox-blocked, so focused native memory tests are
launched through that approved tmux socket, serially with bounded fake barriers.


## Final local verification, 2026-11-03

Native runtime/client source is frozen for independent review and artifact capture.
Final affected builds exit 0. Driver has seven existing nullable warnings and no
new warnings; Core, wrapper and focused test project builds have zero errors.
Protocol cancellation uses CancelAsync. The two VSTHRD003 suppressions cover only
this method's own Task.Run worker drain, with the absence of a UI context stated
at each suppression. The result cache reuses one instance and clears at context
changes, every 32 newly created compilations, and shutdown.

Actual incremental activation required an explicit
`options.Set(DafnyLangSymbolResolver.UseCaching, true)`: ordinary CLI parsing does
not materialize that server-only option's declared default, and Get<bool> returns
false when absent. The added real post-edit fact assertion exposed this omission;
its failed control is retained as `smoke/caching-default-failure-*`. After the fix,
an independent file/module edit reports two reused modules and two new modules.
The manually installed reused-module memory fixture alone did not establish this
runtime claim.

Commands below ran serially from `/workspace/dafny-optimization`, with .NET SDK
8.0.133 and test execution CLI 17.8.0. Unit testhost networking is permitted only
through the previously approved tmux socket. Every fake barrier has a five-second
failure deadline; no automatic worker count is used.

- `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore
  --filter 'FullyQualifiedName~DefinitionAnalysisSessionTests|FullyQualifiedName~DefinitionProofInputsTests|FullyQualifiedName~ProofInputRepeatabilityTests|FullyQualifiedName~DefinitionVerificationFactsTest|FullyQualifiedName~DefinitionBodyVisibilityTests'
  -v:minimal`: 82 passed, 0 skipped, 5 seconds. This includes twelve new session
  cases. These are affected memory checks; no solver or staged source directory.
- `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build
  --no-restore --filter FullyQualifiedName~NativeTaskEntryTests -v:minimal`:
  10 passed, 0 skipped. Results include per-subscriber cancellation, last-owner
  drain, terminal ordering, completed future counters, complete native split
  insertion and rejection of invalid/unknown/timeout/bounded outcomes.
- `dotnet format whitespace <Source/project-directory> --folder
  --verify-no-changes --include <exact changed C# paths> --verbosity normal`:
  all five affected directory groups pass, bounded by `timeout 45s`. The first
  project-mode Driver format also passed, but took several minutes to load the
  workspace; folder mode finishes in under one second. It does not restore or
  evaluate projects; --folder and --no-restore are mutually exclusive.
- `git diff --check`: pass. Root/source commits and dirty states, provider/auth
  mode none, no model, seed42, limits, tmux session and selected public inputs are
  recorded in `final-maintenance-context.json` under the task scratch directory.

The synthetic native experiment command is `PYTHONPATH=python python3
/workspace/tmp/native-analysis-session/smoke.py`, under tmux session
`native-session-final-20261103` at socket
`/workspace/tmp/devcontainer-isolated-validation/tmux.sock`. Final exit 0;
`final-exit-code`, `smoke/summary.json`, `smoke/run.log`, current report files and
`smoke/producer.json` retain evidence. The script uses one resident process,
maximum two simultaneous request callers, one solver core, seed42, native timeout
30 seconds and request deadline45 seconds. It uses tiny authored public sources
and no benchmark solutions. Its common options include standard-libraries:false,
allow-external-contracts, a relative bench/core source library, allow-warnings and
suppress-warnings. Verification adds verify-included-files, isolate-assertions,
verification-time-limit30 and fixed Boogie seed42. Distinct real JSON/TRX output
paths are used for warm requests. Parent/reviewer exact-host warning-policy parity
is an additional independent acceptance boundary.

Observed final native results:

| Control | Result |
| --- | --- |
| Repeated full analysis | Equal documents; warm four module hits, zero misses |
| Actual independent file edit then analysis | Two module hits and two misses |
| Cold symbolic proof | One solver producer, successful complete report |
| Same proof, different report path | One reuse, zero solver producers |
| Same implementation after unrelated file edit | One native cache hit, zero solver producers |
| Physical cwd/source-library switch Value1 to Value0 | Exit4, one producer; consumed bytes identify second snapshot |
| Weaken modular Callee ensures r==1 to r>=0 | Caller fails exit4, one producer |
| Ordinary source constant axiom1 to0 | Exit4, one producer |
| Verify one valid split, edit unrelated file, then full scope | Exit4, three tasks/producers; unchecked false split cannot inherit partial success |
| Mixed trivial and symbolic full scope | Success with two actual tasks; legitimate zero-task declaration accepted |
| Two concurrent target requests with JSON/TRX | Both succeed; protocol remains valid JSONL |
| Unresolved source in spans-only analysis | Parse-only analysis succeeds |
| Missing root followed by valid source | Error remains terminal; session recovers |
| Report origins with logical URI mapping | TRX points into physical snapshot, not logical cache root |
| One-shot invalid library snapshot | Exit4, matching resident negative result |

Z3 executables copied with explicit parent authorization from exact-pin managed
Binaries have SHA256 `be3e6fba449b54c8b30df410392d9f7161bf328fb8e1fdbd8b45250911eb221a`
(4.12.1) and `bf8484ec7c3c76ba5f221245e396748f9632cf6af05d219e10cd669a3913d373`
(4.16.0). The whole toolchain was not copied, no dependencies were added and
managed source/output was not changed. The parent fresh artifact build must bind
actual selected tool bytes; these local outputs are not the final attestation.

Durable findings are saved in [the owner wiki](../wiki/native-analysis-session.md).
Independent final review is accepted. Explicit unsupported contexts and
seed/options-sensitive translation reuse are documented there. No full upstream
integration suite, paid provider call, benchmark proof suite or statistical
experiment was run; those are outside this owner task. The parent owns final
artifact publication, full host image controls and authorized live trials.

### Final review follow-up: preparation ownership

Reopen source before artifact capture for the independently confirmed cancellation
ownership issue: a first caller's cancellable Lazy native task preparation could
be joined by another already admitted caller. Move full target-module preparation
under the existing serialized admission/preparation gate, before readers are
admitted. Outside the gate, share only completed task lists and the independently
owned NativeTaskEntry futures. This changes AnalysisSessionCommand.Execute only;
existing fake subscriber tests and native concurrent/filter controls remain the
affected checks. Do not capture an artifact until the follow-up freeze.

Independent review reproduced stale cached JSON assertion positions after a blank
line shift (cached line4 versus fresh line5). Strengthen only the native cache
checksum with complete native source-token coordinates for the authored owner
range, covering declaration, contract and internal body positions. Preserve the
existing position-insensitive portable proof-input hash. Add three strict-memory
position controls (before declaration, inside body and before ensures) in
DefinitionAnalysisSessionTests; rerun affected memory checks and independent
position JSON parity after the native build.

Final review-follow-up rebuild and affected tests pass: Core82/82, Driver10/10,
0 skipped. Full synthetic native controls exit0 again. A blank line before the
warmed method now forces one solver producer and JSON assertion line5, matching
current source; unchanged warm and unrelated-file cross-compilation still show
one native cache hit and zero producers. Preparation completes under the gate
before readers++, and only completed task lists/futures leave that gate. Final
source review and independent exact-host position parity rerun subsequently passed (below); no
artifact producer has run from this owner scope.

Final reviewer follow-up: mark states retired when native Compilation.HasErrors
or its Resolution task faults/cancels. A missing include may otherwise leave a
normal failed compilation whose partial captured closure does not identify the
newly created file. Add missing-include then create then identical-root immediate
recovery to the synthetic control. Only AnalysisSessionCommand.State.Retired and
the existing maintenance script change; rebuild Driver/wrapper and rerun the
affected native control before artifact GO.

The failed-state recovery control passes against the rebuilt Driver/wrapper:
missing include returns a terminal code6 error; creating that include and immediately
resolving the identical unchanged root succeeds. Explicit stdin is rejected with
SessionUnsupportedError so compiler input cannot consume protocol frames. Full
synthetic smoke remains exit0; all earlier cache, scope, position, library and
concurrency controls pass. Core82 and task-future10 checks are unaffected by the
last State retirement/stdin guards. Independent final follow-up subsequently passed (below).

## Independent acceptance and owner closure

The fresh verification agent accepted native/client source on 2026-11-03 with no
remaining blocking finding, conditional on the parent's fresh artifact/image
validation. Its independent follow-up exited0 with unchanged Core/Driver DLL
hashes before/after the controls. Temporary independent artifacts:

- [summary](/workspace/tmp/native-analysis-session-review/third/summary.json)
- [provenance](/workspace/tmp/native-analysis-session-review/third/provenance.json)
- [exit status](/workspace/tmp/native-analysis-session-review/third/exit.json)

The independent request flags exactly match root verification: standard libraries
false, fixed seed42, verify-included-files, isolate-assertions, time30 and
allow-external-contracts, without allow/suppress-warnings. It confirmed edited
source facts1hit/2misses, warm and cross-compilation native cache1hit/0solver,
constant-negative exit4, partial-scope then full cross-compilation failure4 with
two solver tasks, mixed trivial/full scope, concurrent real TRX, seed partition,
supplied real symlink overlay and identical-root include-creation recovery. The
position-shift result now has one producer/no hit and assertion line5,col20,
matching fresh one-shot verification. Source review accepts whole-token coordinate
binding and native task preparation before concurrent-reader admission.

Final C# whitespace verification and git diff checks pass; owner plan/wiki
Markdown-only audit passes with no non-Markdown artifacts. All source/client files
match the change table; no generated source, managed checkout, dependency or commit
was changed. Owner runtime/client code and records are frozen for fresh artifact
capture. The parent owns the conditional artifact/image gate and live trials; no
remaining native implementation work is held open for those separate results.

## Reopen: canonical clone source metadata, 2026-11-03

The parent withdrew old artifact/image acceptance after strict saved-input parity
found authored source-shape differences (75 Cat01 model differences). The old
cohort is interrupted; no paid retry is authorized. Earlier synthetic controls
remain historical observations and are insufficient for broad source-shape parity.
Caching must stay enabled. Use only compiler/public synthetic inputs and the
parent-supplied diagnostic metadata; do not inspect benchmark solutions or alter
the old artifact/manifest. Parent design extension is in the linked integration
plan. Native owner acceptance is reopened before source edits.

| Exact files/symbols | Planned correction and missing behavior | Verification |
| --- | --- | --- |
| Source/DafnyCore/AST/Modules/ModuleDefinition.cs: clone constructor | Copy authored BodyStartTok through cloner.Origin and independently clone NameNode/Attributes; literal/nested modules lose delimiters and shallow mutable attributes can contaminate cached parser input | Parsed module clone metadata plus full uncached/cached analysis equality |
| Source/DafnyCore/AST/Cloner.cs: CloneDeclaration, CloneFunction and their factory helpers | Preserve Declaration.BodyStartTok centrally for every factory result (classes, traits, datatypes, codatatypes, iterators, functions and predicate variants); preserve function SignatureEllipsis through canonical token mapping | Authored/bodyless/by-method/refining-function and declaration-kind breadth cases |
| Source/DafnyLanguageServer/Language/CachingParser.cs: parser-specific cloner | Preserve authored function SignatureEllipsis for parser-cache clones while retaining existing transformed-cloner semantics | Refinement source parse/resolution parity on cache miss/hit |
| Source/DafnyCore.Test/DeclarationCloneAnalysisTests.cs (new) | Strict-memory parsed canonical clone regressions for all affected declaration/function kinds, module nesting and source markers; methods/constructors remain covered controls | Focused Core memory tests, existing source/semantic/proof-input checks |
| Source/DafnyDriver.Test/CachedParserAnalysisTests.cs (new) | Instantiate actual CachingParser with dictionary IFileSystem and logger counters; compare complete serialized declaration/source/semantic/verification analysis against ProgramParser on misses, hits, replacements and includes | Strict-memory parser/resolver/document pipeline; no solver, provider, staging or new project reference |
| plan/2026-11-02-native-analysis-session.md; plan/INDEX.md; wiki/native-analysis-session.md; wiki/INDEX.md | Withdraw broad source-shape acceptance; record correction, failed diagnostic and fresh evidence | Markdown-only/index/diff audit |

Audit scope: Declaration copy constructors already copy BodyStartTok, but manual
CloneDeclaration factories bypass them; CloneFunction factories also pass null for
authored signature ellipsis. Preserve those authored fields without changing
generated parser/scanner code or normalizing emitted facts. Review module/default/
file/literal clone constructor paths and all factory declaration/function variants.
No new dependencies or Core-to-LanguageServer test cycle: actual CachingParser
coverage belongs to existing Driver.Test, which already references that assembly.

Free host commands from /workspace/dafny-optimization (restored assets required):
`dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore -m:1
-p:BuildProjectReferences=false -v:q`; then the equivalent focused Core.Test and
Driver.Test builds with `-p:SkipFocusedTestAssets=true`. Tests run serially under
approved tmux with --no-build --no-restore and exact new/affected class filters.
Use existing public NuGet cache offline only if a restore is actually missing.
Host referenced-project=false avoids Gradle/network work. Parent owns a fresh
dedicated full-build container, separately attested artifact/images, strict saved3
then30 model equality and full-validator latency checks. Local C# whitespace checks
use bounded folder mode. No source edits have occurred before this extension.

Status: ready; implementation follows this authorized correction scope.

Audit refinement: keep general transformed Cloner signature-ellipsis behavior unchanged; the real parser-cache cloner explicitly preserves authored function ellipsis. Module copies deep-clone mutable name/attributes, with @Options cache miss/resolve/hit ownership coverage. This adds the exact CachingParser.cs path before its edit.

Root continuation after the assigned model hit capacity twice: the first new
Core cases passed2/2 and main full cached-parser document parity passed. Two
Driver fixtures need correction, without changing production scope. Use the
existing supported @Options("--function-syntax:3") example, since warn-shadowing
is not allowed in module option attributes. Refinement's ordinary baseline
AnalyzeDocument throws at the existing null EnclosingClass lookup; two independent
reviewers traced the unchanged base0776 exporter/RefinementTransformer/source-
roster path. Keep the refinement regression at exact pre-resolve authored shape,
resolution success and resolved function metadata parity. Do not claim full
refinement-exporter support or fix that separate baseline bug here. Full document
equality remains strict in the actual cached-parser cold/warm/include/root-edit
test, including semantics and verifier targets. Record these failed fixtures and
the focused rerun rather than replacing their logs.

Correction source gate (root continuation): selected formatting fixed only the two
new tests. Fresh serial run under tmux clone-final-review-20261103-2 passed
whitespace, Core.Test and Driver.Test focused builds, Core84 and Driver13 with
zero failures/skips. The raw command/time/exit record is
/workspace/tmp/native-analysis-session/clone-final-results-2.json; its recorded
session field lacks the launch suffix, so the actual root launch session2 stated
here is authoritative. Initial failed fixture/format logs remain separate.
Driver has one preexisting VSTHRD103 warning; production Core/LanguageServer
focused builds have no new warning.

Independent clone/source reviews found no remaining code or regression-design
blocker and permit fresh artifact construction. Freeze compiler/client/source
records now through producer publication. This plan remains in-progress until
the parent corrected-image exact saved-model gate returns; source tests alone
do not close that required integration check. No current speed claim or new paid
result is accepted. Parent artifacts move to tmp/experiment/verifier-optimization-v2/.
