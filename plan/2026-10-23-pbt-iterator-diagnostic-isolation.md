# Isolate unrelated iterators and reject unsupported iterator execution

Status: done (independently accepted source/local scope; operational image checks remain parent work)
Date: 2026-10-23
Parent: [PBT stabilization](../../../plan/2026-10-21-pbt-stabilization-loop.md)
Related: [unrelated bodyless callables](2026-10-21-pbt-unreachable-bodyless.md)

## Objective and observable acceptance

Keep an unrelated incomplete iterator from preventing the selected method's
detached PBT diagnostic from compiling. This is public repository maintenance,
not a candidate turn. Do not alter original workspace declarations, contracts,
input semantics, selected goal/generator execution, proof admission, analyzer
fingerprints, benchmark inputs/evaluator/scoring or the running frozen cohort.

First reproduce the gap with a tiny public in-memory regression against unchanged
product source. Then extend diagnostic isolation conservatively to unrelated
iterators, with an existing unreachable trap rather than assumed behavior.
Preserve reachable iterator source and dependencies, and report actual iterator
execution as an explicit unsupported capability before preparation or source
rewrites; current runtime instrumentation cannot check its generated contracts.
Preserve any bodyless declaration whose existing native/abstract/disabled-compilation
semantics require preservation. Include
source/token boundaries, authored clauses and original snapshot invariants.
Use an actual in-memory code-generation boundary when feasible; a reparse-only
test must be described narrowly. An existing stale runtime-library command-test
pin must match the current unchanged normalized embedded library text.

Acceptance needs demonstrated isolation and generated-call red regressions, a
small isolation correction and structural early capability guard, meaningful
normal/preservation/rejection regressions, affected native builds/tests and
scoped formatting, plus a fresh independent verifier inspecting and running
checks from requirements/current source. Do not infer image or live efficacy
from source/local checks. The parent owns later separately tagged packaging and
registered-tool/native campaigns; no paid launch or commit is requested here.

## Inspected evidence and existing seams

Applicable root/Cosyn/native AGENTS.md and native CLAUDE.md were read. No deeper
plan/wiki or source/test instructions/templates were found in the named paths.
Native product source is initially clean; plan/INDEX.md has prior unrelated work.
Preserve existing dirty root/Cosyn/native records and every accepted frozen input.

Public source audit finds EraseUnreachableBody accepts only MemberDecl methods
and functions. IteratorDecl is a top-level ClassDecl with its own Body, so an
unrelated bodyless iterator can remain after transformation. Ordinary codegen
reports c_iterator_has_no_body. This is a source-level defect candidate, not a
demonstrated cause of any private experiment return. A separately accepted
bounded public projection classifies four initial unsupported returns only by
stage and cannot attribute this iterator mechanism to them.

Existing ContractRuntimeUnreachableBodyTests uses dictionary-only
ContractSourceSnapshot.ParseAsync, Transform and reparse for methods/functions,
constructors and exclusions; extend this seam rather than driver campaign tests.
Inspect transitive parsing/code-generation setup before running any test. The
driver CampaignHarness creates per-case directories/build outputs and is outside
routine validation. Existing public runtime-library memory/command tests have
different expected normalized resource hashes, a separate stale-test defect.

## Exact change table and ownership

| Owner / file or symbol | Change, necessity and preservation | Validation |
| --- | --- | --- |
| Native Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs::Transform, reachability capability query and diagnostic unreachable-body handling | Extend detached traps to unrelated iterators with parser-owned UTF-8 edits. Preserve actual goal/generator/type/dispatch dependencies. Add one shared structural reason query for reached iterator members and reject transformation before edits when their runtime contracts cannot be instrumented. Never trap executed code or silently omit checks. | Both red regressions; valid unrelated/type-only re-resolution and memory codegen; explicit executed-iterator rejection, unchanged snapshots/contracts and independent source review. |
| Native Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs::RunAsync | Use the shared structural capability query before initial missing-draft/generator discovery for the executable selected goal, and again for the exact goal/generator closure after generator resolution, before proof/draft discovery/transformation. Return normal Unsupported with an actionable fixed reason. Without this, models may be asked to implement generated MoveNext or prepare generators for an unsupported path. Preserve lemma-contract root semantics and all ordinary supported methods. | Pure in-memory query cases for goal/generator-only/unrelated iterator paths; independent call-order/source review. Actual wire/registered-tool rejection remains a later separately planned operational control, never a disk-writing campaign unit test. |
| Native Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs | Minimal in-memory bodyless/existing-body iterator isolation, type-only/abstract/disabled preservation, actual EOF/Unicode coverage, and explicit capability rejection for constructed/advanced goal and generator-only paths. Retain original dynamic/transitive closure assertions; each scenario has an intention comment. | Audit all setup/execution/cleanup; no directory, subprocess, solver, assembly build, durable write, runtime copying or installed-tree reads inside tests. |
| Native Source/DafnyDriver.Test/ContractRuntimeLibraryCommandTests.cs::DafnySourceSha256 | Update the stale expected normalized text digest only after independently deriving it from the unchanged public library and matching the existing pure memory pin. Preserve actual command output equality checks. | Bounded resource/constant comparison; run the command case only if its separate real-process execution scope is audited and classified appropriately. Do not run broad driver campaigns. |
| Native this plan and plan/INDEX.md; wiki/pbt-unreachable-bodyless.md and wiki/INDEX.md | Record exact supported cases, commands, red/green evidence and limitations, with parent links. | Scoped diffs and recursive Markdown-only audit. |
| Root parent plan/INDEX.md and wiki/architecture/pbt-runtime-image.md/index | Track this native iteration separately from the active immutable Q cohort; no live inputs change. | Accurate source/local versus operational evidence, reciprocal links and final audit. |
| /workspace/tmp/pbt-iterator-diagnostic-isolation-20261023-r01/ bounded build outputs/logs and verification/source-review.{json,md} | Isolate actual build artifacts and fresh independent evidence from shared Binaries/obj and frozen packages. No source/runtime tree copying inside tests. | Before any build, record and review the exact supported output/intermediate/reference/asset profile below; no external packages/restore or hidden references. |

## Validation profile and prerequisites

Working source root: /workspace/cosyn/dafny. Existing dotnet SDK, native reference
assemblies, project assets and package cache are prerequisites. Packages are not
being added. Inspect supported Makefile/dotnet wrappers and reuse the existing
cached no-dependencies configuration. Do not regenerate Coco, rebuild dependencies,
restore/install packages, mutate another build's output or rerun spent processors.
Read-only investigation establishes this normal per-project profile, with R set
to /workspace/tmp/pbt-iterator-diagnostic-isolation-20261023-r01 and P the exact
top-level project name. Use actual argv values, not unexpanded placeholders:

```text
-p:OutputPath=R/out/
-p:BaseIntermediateOutputPath=R/obj/P/
-p:IntermediateOutputPath=R/obj/P/Debug/
-p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/P/obj/
-p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/P/obj/project.assets.json
-p:AppendTargetFrameworkToOutputPath=false
-p:UseCommonOutputDirectory=true
-p:CompileUsingReferenceAssemblies=false
-p:DefaultItemExcludesInProjectFolder=obj/**
```

For the two test-project build/test invocations override common output copying
with these existing SDK/MSBuild scalar controls (the physical OutputPath remains
the same sole task-owned R/out):

```text
-p:UseCommonOutputDirectory=false
-p:_GetChildProjectCopyToOutputDirectoryItems=false
-p:CopyLocalLockFileAssemblies=true
```

The SDK's Common targets conditionally default _GetChildProjectCopyToOutputDirectoryItems
at line380 and UseCommonOutputDirectory at4676; command-line values remain
authoritative. Root885c60/2605c3 independently inspect reference/package Copy at
4920 and child content retrieval at5021: this pair permits locked package copies
while suppressing child content traversal entirely. MSBuildCopyContentTransitively=false
alone is insufficient because it still copies immediate child fixtures. The
first CopyLocal=true replacement build retained common=true and copied no package
leaves; its subsequent testhost again failed before discovery. Preserve that
failed profile attempt, do not call it a product regression, and allow one further
TG.Test replacement with this audited pair before actual red execution. Primary
project-reference DLL paths remain the already accepted R/out leaves; dependency
builds remain disabled. Do not stage a second runtime or source tree.

The default library-project setting leaves locked transitive runtime
assemblies out of the isolated test output; the first discovery attempt reported
missing Boogie.AbstractInterpretation before any test executed. Do not classify
that or the earlier sandbox testhost socket denial as an iterator red result.
Before enabling this copy, derive the exact runtime, native, resources and all
runtimeTargets leaves, plus copyToOutput contentFiles, from the existing two
test-project asset files (no directory walk/cache census),
inspect each named regular leaf's metadata and write a bounded public manifest
under R. Limit the union to512files/128MiB, plus the separately allowed two Z3
content files. Refuse missing/symlink/escaping leaves or excess bounds; do not
restore packages or copy directories. This is one ordinary build-time copy into
the same R/out, never test setup or per-test staging. Preserve unchanged sources
and asset files and reuse the normal SDK target, not a custom copy implementation.
Root6cf18b independently inspects SDK8.0.131 ResolveLockFileCopyLocalFiles at
Microsoft.PackageDependencyResolution.targets516-533: it includes native and
resource items as well as runtime items. A runtime-type-only manifest is a
partial preflight and must not be reported as the complete copy bound. Audit
each project's union before its next build; if the first replacement was already
launched with the narrower manifest, preserve that sequencing limitation and
bound actual named outputs without replaying the build.
Independent rootdf1034 corrects the earlier8056d0 audit's omitted singular
resource asset key: TG.Test243files/18613812B, Driver.Test299/34572548B,
union383/37242316B. This matches the expanded implementation metadata manifests
under R; all named leaves are regular, non-symlink cached package inputs within
512files/128MiB. These are metadata measurements, not package-content hashing.
Driver.Test's20own fixture leaves/69307B are separately bounded; no child tree is
copied. The original narrow runtime manifest is retained as incomplete evidence.

All generated output/intermediate/test-host TMPDIR/results stay under R; existing
project obj is read-only NuGet metadata. There is no restore or dependency build.
Root1bf2a9 observes SDK8.0.131, matching all three existing assets; repository
global.json8.0.111/latestFeature remains unchanged. Root11c89f measures six
named public reference leaves. Seed the common output once with these exact
ordinary DLLs, verifying size/hash while copying; this is actual build setup,
never development-test fixture setup or a whole runtime copy:

| Input (immutable app prefix unless stated) | Bytes | SHA-256 |
| --- | ---: | --- |
| DafnyCore.dll | 5359104 | a43f0c427d7c50bc880b9ee52548ed0a19b1ea2332fd7c5056e32c1e2caac5d2 |
| DafnyPipeline.dll | 1414144 | 4e919e907d1e041dfa6853b3f0ccd1e66998657844a7abe81dc464e09b701f29 |
| DafnyRuntime.dll | 178176 | f84079abf8fcf3a3f4d41f4b345a6d14e16901579337fd55194834d7bfa45013 |
| DafnyDriver.dll | 501248 | 2e82902c641185b936053dd47be4f44b83bd68f110573d7e29dcc9a7f5f3d950 |
| DafnyLanguageServer.dll | 355328 | 09bf943441cc1fee04097b95c5955c4cdcec49a9c0a4152f88b791d65093e4ed |
| /workspace/cosyn/dafny/Source/DafnyCore.Test/bin/Debug/net8.0/DafnyCore.Test.dll | 893952 | cb5a398784d37d0dfba09df330ad1f35b639b12a826df2f61f9ff3821f1ab511 |

Immutable app prefix is
/workspace/tmp/experiment/pbt-authored-generator-20261021-r03/context/app/.
Core.Test is an explicitly measured cached test utility, not a source-attested
new compiler/runtime. Audit that selected tests use no effectful helper from it;
record this inherited dependency limitation. Do not seed old TestGeneration.
Cached asset sizes are144208B(TG),372923B(TG.Test),398914B(Driver.Test), using
existing /home/vscode/.nuget/packages; cache completeness remains an actual-build
prerequisite, with no restore fallback if something is absent.

The top test projects' own Content items copy cached Z3 into R/out under either
copy profile. Root18b6ee bounds the exact source directory at2regular files/
58670216B, depth<=4; allow this one ordinary build-time copy to shared fresh out,
not per-test copies, reads or solver execution. PreserveNewest avoids repeated
copies across the two top projects. Do not build Core.Test, whose top-level
fixture copying would expand scope. Driver.Test's own small fixtures must be
bounded before its build; if that cannot be established, hold that build and
record the concrete prerequisite. No test body stages or compiles any files.

Concrete command forms (substitute each of the three named project profiles
above), serial, each initial build bounded120seconds, no automatic retry:

```text
dotnet build Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo <TG profile>
dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo <TG.Test profile>
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeUnreachableBodyTests --results-directory R/test-results <TG.Test profile>
dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo <Driver.Test profile>
dotnet format whitespace . --folder --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs Source/DafnyDriver.Test/ContractRuntimeLibraryCommandTests.cs --verify-no-changes
git diff --check
```

The first TG and TG.Test attempts consumed one call each but did not reach the
red regression. With a relocated BaseIntermediateOutputPath, the SDK default
Compile glob also admitted the pre-existing source-project obj tree, producing
duplicate generated assembly attributes (CS0579). Exclude that exact project-local
obj/** tree with the SDK-supported DefaultItemExcludesInProjectFolder property
on every build/test invocation. This retains the explicit read-only asset paths;
it does not suppress product source, change project files or admit stale TG.
Before retrying, inspect the installed SDK property's use and preserve both
failed logs under R. These are build-profile failures, not a red defect result.

After those two consumed calls, allow at most two further TG builds, two further
TG.Test builds and one Driver.Test build for the actual red/green cycle, with
the corrected profile. Two additional TG.Test builds are now allowed to populate
the asset-locked runtime dependencies before actual red execution, after the
bounded manifest check above; the first replacement was ineffective with the
original common=true property. Implementation limits are now three TG calls,
five TG.Test calls and one Driver.Test call, nine total including all failed
prerequisite/profile attempts. Update this plan
before any source-driven extra build
or longer timeout. Logs/tool output are bounded public maintenance evidence;
capture actual commands/chunks/exits without inventing downstream proof results.
After implementation freezes, the fresh independent verifier may sequentially
reuse this task-owned common output and run one cached TG, TG.Test and optional
Driver.Test build with the identical isolated properties, then its own audited
memory tests. Do not run implementation/verification builds concurrently, copy
another source tree or create a second solver-content output. This adds at most
three verification builds to the implementation build calls below. Source/
reference/output bindings must be inspected independently even if MSBuild reports
an up-to-date build. Further calls need an explicit relevant plan update first.
The fixed declared environment disables dotnet telemetry/workload notifications,
preserves HOME and uses R/tmp for TMPDIR. Do not change packages/toolchain flags.

1. Build only the test project against unchanged product plus one new in-memory
   reproducer; run its exact filter and require an assertion/codegen failure
   matching the iterator gap, not an environment failure.
2. After source settles, serial cached builds of TestGeneration and its test
   assembly; run only audited affected unreachable-body/preparation/signature
   and proof-integrity memory filters. Extend scope only for a relevant concern.
3. Use native dotnet format whitespace with exact changed files and
   --verify-no-changes; git diff --check. No whole benchmark suite or LIT run.
4. A fresh independent verifier starts with requirements/current source and runs
   its own affected checks, without implementation conversation/conclusions.
5. Inspect native/root plan/wiki trees for non-Markdown files, preserve unrelated
   work and record actual versions/revisions/commands/outcomes/skips.

Real compiler/image controls are distinct later operational experiments, not
development-test fixtures. A compiler emit check is permitted in memory only
after proving every helper/option/output stays in memory; otherwise keep the
regression at the parse/transform boundary and declare that limitation.

## Risks and current handoff

### Actual initial regression

After the profile prerequisites were corrected, the implementation agent reports
the exact AddsBodyToUnreachableConcreteIterator case executed against unchanged
product source: one failed/zero passed, exit1, log
/workspace/tmp/pbt-iterator-diagnostic-isolation-20261023-r01/logs/red-exact-test-final.log.
It failed transformed-source reparse with rbrace expected, before backend
c_iterator_has_no_body. This exposes generic generated-iterator-member insertion
at the iterator declaration boundary as well as the missing iterator-body
handling. The socket/dependency prerequisite aborts are retained separately and
are not red results. Independent source/result review is still pending; no
claim is made about the live cohort's private failure causes.

Source correction is now active; a fresh independent verifier is auditing
requirements/current public source in its own context and will execute only
after the implementation freezes and releases the single shared build output.

### Coverage extension before source freeze

The first green stage consumed TG3/TG.Test5/Driver.Test1 builds, including all
prerequisite/profile attempts. The implementation reports exact iterator1/1,
unreachable class11/11 and affected memory selection38/38 passing, plus the
Driver.Test compilation. These are implementation observations pending fresh
verification, not operational or live acceptance. The initial tests do not yet
meet every named preservation/boundary criterion: a type-only iterator reference
does not exercise _ctor/MoveNext or its transitive/dynamic-dispatch dependencies,
and a trailing comment inside a module is not an actual source EOF boundary.

Before SOURCE_READY, add bounded in-memory/source-emission regressions in the
same planned test file for a selected execution path that constructs/advances
an iterator and reaches its transitive callable/override, an unrelated bodyless
default-module iterator at actual EOF with Unicode/trailing-comment content,
and abstract-module bodyless preservation beside disabled compilation. Preserve
all original snapshots/clauses and positively check the reachable bodies and
callee/override remain intact. Native semantics must justify any extern
exemption; do not assume backend treatment from method behavior.

This relevant extension authorizes at most two additional TG.Test builds and
one additional TG build if a regression reveals a product correction, using
the same final isolated profile/output,120s each, with no new copy/restore.
Implementation caps are therefore TG4/TG.Test7/Driver.Test1, twelve calls total;
the fresh verifier retains its separate at-most-three-call budget after freeze.
Do not spend a new TG build if only tests change. Record each call and actual
source state; further changes/builds need a new relevant plan update first.

The two added test builds exposed fixture-only errors (a reserved local name,
then passing an unmarked legacy Generate as an explicit selected generator).
Preserve those failures without relaxing selected-generator validation. Allow
one further test-only replacement to use the existing valid legacy-constructor
seam: updated implementation caps TG4/TG.Test8/Driver.Test1, thirteen total.
The added EOF/abstract cases passed; true advancement has not yet traversed the
transformer. The next run must report that actual boundary before any further
behavior change. An independent source audit notes InstrumentCalls excludes
IteratorDecl.Body, while generated MoveNext shares the iterator source origin;
if the new case reveals a wrapper-placement or unreported-obligation gap, retain
the red result and amend the approach before implementing. Do not silently skip
checks or claim complete iterator/callee-contract support from source emission.

### Executed-iterator capability disposition

The valid advancement case did reach the transform and failed re-resolution with
member MoveNext__pbt_site_0 does not exist in iterator Needed, plus generated
wrapper errors. Log: R/logs/extension-dynamic-test-actual.log. Its original
_ctor/MoveNext, trait/override and transitive helper reachability assertions
passed. InstrumentCalls inserts a generated member wrapper at the iterator-wide
source origin and renames the call to a member that iterator syntax cannot
declare. In addition, IteratorDecl.Body and its nested calls/yield obligations
are not instrumented. Skipping the wrapper or adding only MoveNext pre/post
checks would leave that capability incomplete.

Disposition: retain full ordinary supported-method behavior, fix unrelated
iterator source isolation, and reject execution of reachable iterator members
with one explicit actionable Unsupported reason. This changes an already broken
runtime capability into early honest feedback, rather than claiming new iterator
support or silently dropping meaningful checks. The updated acceptance above
replaces the unachievable executed-iterator success criterion with structural
rejection before prep/edits and positive type-only preservation. No benchmark
specification, proof rule, task input, evaluator or score is changed.

Implement the shared query over actual ExecutionReachable/DiagnosticReachable
results, using IteratorDecl member ownership rather than names/message matching.
The initial runner check must precede MissingDrafts/generator discovery and omit
lemma-contract bodies as current runtime rooting does. The resolved-generator
check must use the exact selected generator and precede construction audit,
further missing drafts, proof and transformation. Transform itself must reject
the same unsupported closure before edits, using the existing externally handled
NotSupportedException boundary, without introducing broad catches or trust skips.
Keep the original dynamic closure/source assertions; test explicit rejection and
unchanged snapshots, plus generator-only rejection and ordinary/unrelated cases.
Actual native wire/MCP early-response checks belong to a later operational plan.

Add one ordinary cached product build for Source/DafnyDriver/DafnyDriver.csproj
with the same per-project output/intermediate/assets profile as TG, common=true,
--no-restore --no-dependencies -m:1 /nr:false -v:q --nologo,120s limit. Before
building, inspect its existing assets/SDK/normal output targets and bound named
embedded resources; it declares no top-level Content tree. Do not restore if a
cache prerequisite is missing. This overwrites only the task-owned old donor
Driver.dll in R/out after the new TG has built, preserving immutable donor bytes.
No apphost is executed. Add Driver to formatting as above. No campaign tests run.

This newly required guard/source disposition permits at most two additional
TG.Test builds and up to two TG builds beyond the currently consumed TG3/TT8,
only for the final correction or a relevant revealed failure. Current total
implementation caps: TG5/TG.Test10/Driver1/Driver.Test1, seventeen calls including
all prior failures. Expected sequence is TG4, Driver1, TG.Test9, then audited
memory checks; do not spend spare calls without a relevant changed source/failure.
After source freezes the fresh verifier may run one TG, one Driver, one TG.Test
and optional one Driver.Test build, sequentially in the SAME output/profile;
this is at most four independent build calls. No second solver or package copy,
extra runtime staging, dependency build or source-tree copy is authorized.

TG4/TG5 hit a new C# fixture-independent syntax error in conditional collection
expressions used by the structural guard; neither produced a changed product
assembly. Preserve both extension logs. Replace that conditional with ordinary
typed if/else assignments using existing Enumerable.Empty/new-array forms, and
review the exact source correction before retrying. Permit one replacement TG
build: updated caps TG6/TG.Test10/Driver1/Driver.Test1, eighteen implementation
calls. Driver and final TG.Test remain unconsumed and must follow a successful
new TG. No package/toolchain flag or runtime semantic change is authorized by
this syntax-only repair; no automatic further retry.

TG6 succeeded. Driver1 compiled the new501760B DLL into R/obj but its final
copy failed MSB3021 because the old task-owned donor copy R/out/DafnyDriver.dll
retained mode0444. The immutable donor path is untouched. Permit making only
that exact task-owned regular leaf owner-writable, then one replacement ordinary
Driver build with the same profile. Preserve the partial first output/log and
verify the final DLL/PDB pair against its intermediates before any source-ready
claim. Updated caps TG6/TG.Test10/Driver2/Driver.Test1, nineteen implementation
calls. This profile correction changes no source, package, reference, proof or
runtime requirement; no further automatic retry.

### Type-only guard regression and exact closure refinement

The first final class execution reports13/14passing: type-only iterator
preservation fails in the new capability guard, not diagnostic isolation.
Resolver AddTypeDependencyEdges adds a pseudo-call edge to IteratorDecl because
the declaration implements ICallable; the ordinary conservative execution closure
then scans its generated specs and reaches Needed.Valid. Thus owner membership
alone conflates a type dependency with actual iterator execution.

Keep every existing public ExecutionReachable/DiagnosticReachable caller and
its fingerprint/proof semantics unchanged. Extract or extend only a PRIVATE
closure core with an explicit include-iterator-type-declarations mode: all
existing callers use true, while UnsupportedRuntimeIterator alone uses false.
In that capability mode, suppress only native graph targets whose actual AST
object is IteratorDecl. Preserve direct edges to generated _ctor/MoveNext and
resolved function/value references, dynamic override expansion, type constraints
and ConstantField initializers. Do not add a public flag, name/message heuristic,
verification skip or independent duplicate traversal. The default conservative
closure remains the authority for proofs/isolation.

Add a bounded memory regression for a type-only UNUSED iterator whose body calls
a helper that constructs another iterator: unused iterator-body graph edges must
not contaminate the capability predicate. Preserve the existing true execution,
constructor/generator-only and type-only assertions and positive emission tests.
Record the exact previously audited affected-memory filters and rerun relevant
proof/reachability checks for this changed core after final source settles.

Authorize one further TG product build and one TG.Test build for this relevant
regression/refinement: updated implementation caps TG7/TG.Test11/Driver2/Driver.Test1,
twenty-one calls including all earlier failures. Same profile/output/120s limits;
do not rebuild Driver when its source and called public helper signature are
unchanged. Fresh verifier still waits SOURCE_READY with its own four-call cap.

TG7/TG.Test11 pass according to implementation; final execution is still pending.
The earlier38-pass log lacks its exact filter command and cannot stand as named
scope acceptance. Preserve it as historical implementation output with unknown
selection; do not reconstruct a favorable filter to match its count. Before any
new checks, record the exact argv/profile and audit each selected class's complete
setup/execution/cleanup. Use actual observed new counts as the evidence.

Extend the new unused-iterator-body constructor case through actual Transform,
reparse and memory code emission, positively checking the directly type-referenced
iterator body and immutable authored snapshots/contracts. Nested helpers/iterators
that cannot execute may receive the existing fail-fast diagnostic trap. Add the
corresponding selected-GOAL type-only scenario as a
separate case, since InstrumentCalls currently uses a goal-side conservative
closure and must not corrupt an actually unexecuted iterator/helper path. This
stays in the same test leaf and tests supported behavior, not an implementation
detail. Permit one replacement TG.Test build for these final evidence gaps:
updated caps TG7/TG.Test12/Driver2/Driver.Test1, twenty-two implementation calls.
If a new case exposes a product gap, preserve its red result and amend the exact
approach before another product build. No silent skipped checks or weakened proof
closure is authorized; image controls remain draft and unlaunched.

The new explicit54-case run reports53passing/1failing: the added assertion
requires authored YieldStmt in an unexecuted Nested iterator, although the normal
isolation correctly replaces that body with UnreachableBody. The selected-goal
type-only positive case passes. Requiring every nested unused helper/iterator
body to stay authored was an over-broad test requirement, corrected above: the
original immutable sources/contracts stay authored, while detached unreachable
bodies may be trapped. Do not expand diagnostic/default proof reachability to
satisfy that assertion; doing so could preserve an unrelated nested bodyless
iterator and reintroduce compilation failure.

Correct only the test expectations: require supported type-only capability,
directly referenced Unused body preservation, successful transformed reparse and
memory code emission, intact original snapshots/contracts and actual selected
bodies. Verify any nested/helper trap is genuinely outside the executable path;
do not demand all those detached bodies remain authored. An explicitly bodyless
Nested fixture may additionally demonstrate why no transitive preservation
expansion is needed. Permit one test-only replacement, no product rebuild:
caps TG7/TG.Test13/Driver2/Driver.Test1, twenty-three implementation calls.
Retain the54-case assertion failure and exact command as evidence; do not relabel
it as a product failure or a passing final selection. Independent review must
assess the corrected semantic requirement from current source and its own checks.

Iterator reachability includes generated constructor/MoveNext methods and may
include type or field references; a naive all-iterator rewrite could change
selected behavior. Prefer conservative preservation on uncertainty. New source
edits must not collide with generated member edits or lexical EOF/Unicode tokens.
No assumptions, extern/axiom attributes, proof skips or heuristic routing may be
introduced to obtain a pass. A stale test digest is independent of campaign
failure and must not be described as its cause.

### Final implementation handoff and independent execution

Implementation is SOURCE_READY; all its builders/testhosts ended and four source
leaves are frozen. Its final exact filter is:

```text
FullyQualifiedName~ContractRuntimeUnreachableBodyTests|FullyQualifiedName~ContractRuntimeGeneratorSignatureTests|FullyQualifiedName~ContractRuntimeGeneratorProofTests|FullyQualifiedName~ContractRuntimePreparationReuseTests
```

Final no-build/no-restore120s execution with the complete TT profile passes54/54,
exit0, chunk39fe8b, R/logs/green-relevant-memory-tests-final-corrected.log. The
prior53/54run and unknown-selection38log remain separate. Audited helpers use
snapshot dictionaries, parsing/resolution, string preparation, ConcreteSyntaxTree
emission and proof-report logic without verifier/solver, directories, processes,
staging, fsync or deferred effects inside tests. Scoped whitespace/diff pass.
Implementation consumed TG7/TG.Test13/Driver2/Driver.Test1=23calls including every
profile/syntax/fixture failure; Driver.Test is compile-only. Source hashes are
reported as transformer70c5d5c6..., tests182cb1ed..., runnercb915415... and
command testedba4066.... Reported final TG/Driver DLLs286d1879.../817bebbc...,
PDBs6dc643e7.../44ae27ac... match their intermediates, pending fresh measurement.

Fresh verifier independently built TG, Driver and TG.Test successfully in the
same isolated output; no acceptance report yet. Its first memory-test invocation
aborted before discovery because the sandbox denied vstest's localhost TCP
listener(SocketException13), not a test failure. Preserve
R/verification/logs/memory-tests.log. Permit ONE exact same audited no-build/
no-restore test argv/profile/filter outside that socket-restricting sandbox,
with loopback testhost control only, unchanged120s scope and bounded capture.
Use normal escalation review; do not add network/provider/native tests or change
permissions globally. If rejected, retain the refusal and report it; do not bypass.
This is an environment prerequisite replacement, not a failing-test retry.

### Independent acceptance and handoff

Fresh source/local review is accepted: its own TG/Driver/TG.Test/Driver.Test
builds pass with0warnings/errors, its exact authorized memory selection passes
71/71with0failed/skipped, and scoped whitespace/diff/binding audits pass. The
initial sandbox invocation remains a zero-test pre-discovery abort. Exact own
argv are in R/verification/logs/commands.md; the verifier audited every selected
helper independently, including fake/reject-before-verifier proof boundaries.
Rootf0ada8 reads and authenticates both exclusive0444 reports:

- source-review.json8494B, SHA256a54657d0040357f91f43398057207592698abba38dff3603b3c2aef70a675c38.
- source-review.md5825B, SHA2563be1d3e77edabbf41f8bedc90f136f380ea0026ad773b1fa1051c61792d80da9.

Root39558c independently measures the same four accepted source hashes.
Root5acf17 measures final output/intermediate DLL/PDB pairs after independent
Driver rebuilding: TG841216B/286d1879..., TG PDB213200B/6dc643e7...,
Driver501760B/2e5feffa..., Driver PDB135896B/0de5953f...; all pairs match.
These final Driver outputs supersede the implementation's earlier817bebbc.../
44ae27ac... pair. Root6df01c compares ordinary generated TG deps and Driver
deps/runtimeconfig byte-for-byte with accepted package metadata; all match.
No new runtime dependency/configuration payload is established as necessary.

Durable source/capability findings are in
[the updated iterator section](../wiki/pbt-unreachable-bodyless.md#iterator-declarations-and-execution-boundary-2026-10-23),
indexed from native wiki/INDEX.md. Later actual target compilation, solver proof,
new-image/registered-tool behavior and benchmark efficacy remain the separate
[root image/control plan](../../../plan/2026-10-23-pbt-iterator-isolation-image.md)
and active parent goal. Source tests do not claim those downstream results.

Current state: source/local acceptance is complete under the amended criteria.
Both genuine public red regressions and all failed prerequisites are retained;
no current blocker in this source scope. The parent goal remains active.
The final profile and expanded asset bounds above distinguish real regression
evidence from all earlier failed prerequisites. No image, paid call, frozen input
or commit is changed by this maintenance iteration.
Do not rebuild/mutate these outputs or copy them to a runtime without the next
plan's explicit input/source/output/preparation gates. No commit was created.
