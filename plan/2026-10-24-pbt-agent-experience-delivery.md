# Reconcile the reviewed PBT agent experience repairs for delivery

Status: done — superseded by [reviewed main delivery](2026-10-25-pbt-reviewed-main-delivery.md), which committed the reviewed scope in `6f24e6046`, `b531cdc0f` and `fff2a462c`; the frontend DTO was excluded and later removed
Date: 2026-10-24
Owner: native Dafny repository
Related: baseline (`2026-10-23-pbt-frontend-source-baseline.md`, removed 2026-10-25), [iterator isolation](2026-10-23-pbt-iterator-diagnostic-isolation.md), [candidate seed work](/workspace/tmp/pbt-agent-frontend-baseline-20261023-r01/native/plan/2026-10-24-pbt-runtime-verification-seed.md), [root image gate](/workspace/plan/2026-10-24-pbt-runtime-seed-image.md)


> 2026-10-25: the PBT agent frontend (`frontend_codec`, `frontend_policy`, native `ContractRuntimePreparationModels`) was removed; see [removal plan](../../plan/2026-10-25-remove-pbt-agent-frontend.md). Rows below naming those files no longer apply.

## Objective, evidence and acceptance

Add the isolated candidate's reviewed PBT changes to the canonical native
working tree while preserving every canonical iterator change and unrelated
dirty file. This is maintenance, not a benchmark run. It prepares the user's
requested single logical `[PBT] improve pbt tool usage agent experience` delivery;
no source-only handoff implies a commit, image acceptance or model benefit.

N is `/workspace/cosyn/dafny`, branch expecto. K is
`/workspace/tmp/pbt-agent-frontend-baseline-20261023-r01/native`, detached.
Both HEADs/shared comparison base are
`5fa47c6e949dad736db25e02b5edad95d0b0be1a`. Both trees contain pre-existing work.
Read-only classification found 23 production leaves: sixteen canonical files
equal the comparison base, two mixed files already contain canonical iterator
work retained by K, and five leaves are new. Do not use blanket copying or reset.
Recheck current contents before writing; a new overlap requires reassessment.

The current K CLI additionally contains the independently reviewed seed fix,
9,396 bytes/SHA256
`67c8e09d23c42a31a3ff926f8bdea678a1821c0c05db495f37a5e869714a3410`.
Its scoped build passed independently. Other retained source inventories predate
that repair, so reconcile from actual current K rather than an old buffer.

Independent inspection of twelve test/project leaves plus seventeen exact
helpers consumed 1,244,784/2MiB. No prohibited temporary-directory, durable-write,
bulk-file or on-disk compilation path was found in the new memory selections.
Managed `Compile` in unreachable-body tests creates a ConcreteSyntaxTree;
`NewFile` is an AST node, not a filesystem write. Real solver and CLI subprocess
tests remain separate final integration. This classification ran no tests.

Acceptance for this source phase: exact additive production/test changes,
preserved canonical work, unchanged HEAD/branch/gitlinks, independently reviewed
current diffs and test effects. Later gates require canonical builds, affected
memory checks, scoped formatting, bounded final integration, owner knowledge
and requested focused nested commits. K build/image results are historical
evidence and do not replace fresh canonical verification.

## Exact production changes

Each listed leaf receives only K's additive PBT delta. Existing contracts,
proof coverage, trusted-source/fingerprint authority, iterator support limits,
process ownership and meaningful refusal paths remain intact.

| Exact path | Change and why; validation |
| --- | --- |
| Source/DafnyCore/AST/Members/Method.cs | Preserve source analysis/PBT declaration support from K; independent semantic/diff review and affected native build. |
| Source/DafnyCore/DefinitionAnalysis.cs | Preserve analyzer proof/screen identities; no weakening of fingerprints or fixed specifications. |
| Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs | Preserve exact analyzer proof-input bindings used by proof promotion and screening. |
| Source/DafnyCore/DefinitionAnalysis.SemanticFacts.cs | Preserve sound semantic facts consumed by bounded screen queries. |
| Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs | Transfer checked bounded-witness reduction; memory witness/rollback checks. |
| Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs | Transfer associated scoped witness traversal without changing unrelated canonical behavior. |
| Source/DafnyCore/Rewriters/QuantifierBounds.cs | Transfer finite-domain/witness support with exact existing input bounds. |
| Source/DafnyDriver/Commands/TestContractsCommand.cs | Transfer actual current CLI bodyless-entry handling and effective verifier-seed forwarding; preserve supervision and defaults. |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs | Mixed file: retain both canonical iterator guards and RuntimeExecutionReachable discovery; add selected preparation, native-root identity and deferred bodyless-entry handling. |
| Source/DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs | Transfer selected declaration/dependency handling, including unresolved-call admission syntax fix. |
| Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs | Transfer exact selected-helper proof closure, original contracts and internal binding safeguards. |
| Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs | Preserve sound initial-type proof preparation and expected failure fallback. |
| Source/DafnyTestGeneration/ContractTesting/ContractQueryBuilder.cs | Transfer native logical screen query construction without spec weakening. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs | Preserve runtime checking behavior for retained objects/heap obligations. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs | Mixed file: retain canonical iterator dependency collection, pseudoedge exclusion, capability rejection and declaration erasure; add native-root adaptation and output captures. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs | Transfer selected source/draft closure and exact diagnostic preparation behavior. |
| Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs | Transfer retained query phase/cancellation/result handling at the solver boundary. |
| Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs | Transfer checked specification query/witness handling and honest unsupported outcomes. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimePreparationModels.cs | Add reviewed strict DTO foundation; do not claim unimplemented preparation dispatch. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSelectedDraftPreparation.cs | Add selected runtime/proof draft preparation and transitive closure. |
| Source/DafnyTestGeneration/ContractTesting/ContractScreenModels.cs | Add strict native inspect/screen wire models. |
| Source/DafnyTestGeneration/ContractTesting/ContractScreenService.cs | Add actual native logical inspect/screen service and honest diagnostics. |
| Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs | Add source preparation for native contract screening. |

## Exact test, project and knowledge changes

| Exact path | Additive treatment and validation |
| --- | --- |
| Source/DafnyCore.Test/ContractWitnessReductionTests.cs | Transfer bounded existential witnesses and rollback checks; managed memory workflow. |
| Source/DafnyCore.Test/DafnyCore.Test.csproj | Transfer only two SkipFocusedTestAssets conditions around recursive Z3/TestFiles asset copying; default behavior retained. |
| Source/DafnyDriver.Test/ContractRuntimeLibraryCommandTests.cs | Already identical in N/K; preserve canonical file. Real CLI final integration only. |
| Source/DafnyDriver.Test/ContractRuntimeDraftDiscoveryTests.cs | Already identical; preserve canonical file. Managed memory discovery selection. |
| Source/DafnyDriver.Test/DafnyDriver.Test.csproj | Add the same explicit SkipFocusedTestAssets opt-out to the existing Binaries/z3 recursive Content group. Current file has no guard; this is needed for bounded memory-test builds without the known recursive asset-copy risk. No dependency or fixture change. |
| Source/DafnyTestGeneration.Test/ContractQueryTests.cs | Remove only the two obsolete ContractRealization theory rows; real solver checks remain final integration. |
| Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs | Transfer output-capture scenarios and MemoryOptions/NoProverFactory helpers; managed memory. |
| Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs | Already identical; preserve canonical iterator tests and managed code generation. |
| Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj | Transfer only Z3-copy SkipFocusedTestAssets condition. |
| Source/DafnyTestGeneration.Test/ContractRuntimeFrontendModelsTests.cs | Add pure strict-schema/validation tests. |
| Source/DafnyTestGeneration.Test/ContractRuntimeSelectedDraftPreparationTests.cs | Add managed selected closure/identity/admission/rollback tests; no native proof invocation. |
| Source/DafnyTestGeneration.Test/ContractScreenModelTests.cs | Add pure schema/value validation tests. |
| Source/DafnyTestGeneration.Test/ContractScreenServiceTests.cs | Add fake-backend decision/cancellation/diagnostic tests; no real backend. |
| This plan and plan/INDEX.md | Record exact reconciliation/revisions/commands/results and remaining gates. |
| Existing wiki/pbt-generator-proof-helpers.md, pbt-installed-draft-evidence.md, pbt-runtime-output-capture.md, pbt-child-contract-screening.md and wiki/INDEX.md | LATER update only reusable canonical findings after actual review/verification; preserve unrelated current knowledge, no blanket wiki copy. If an exact topic is absent, amend before creating it. |

No benchmark source, tasks, oracle, scoring, evaluator, provider, security policy,
package or generated compiler source changes. Do not remove tests without an
actual prohibited effect; inspection supports no deletion recommendation.

## Source-only implementation and independent review

Author may modify only the listed source/test/project leaves, with three
identical tests left byte-exact, and create finite pre-change snapshots under
`/workspace/tmp/pbt-native-delivery-20261024-r01/` if needed. These are bounded
source-maintenance snapshots, not test fixtures. No plan/wiki artifact storage.
Before writing, record HEAD/branch and content identities of every touched N/K
leaf; preserve exact N prior bytes, verify additive diff and stop on unexpected
overlap. Never reset/stash/stage/commit or record gitlinks in this source phase.

Fresh named read/write allowance4MiB, each leaf<=256KiB, at most36 production/
test/project paths plus the two planning files and existing retained buffers.
Read applicable ancestor instructions and supported Makefile targets; new helper
reads require a precise bounded extension. No target imports, build/test/native,
formatter, Docker/provider/tmux or private benchmark access. Do not update docs
or run checks as implementation agent. Report exact changes, preserved iterator
hunks, current CLI identity, snapshots, pins, effects and unrun gates.

Fresh independent verifier starts from this plan and current N, without the
author's conversation or unverified conclusions. Inspect current diffs and
controlled helper effects before running checks. Preserve all canonical-only
changes; K equality alone is insufficient for mixed files. Explicitly verify
the third asset guard's default-on/opt-out semantics and absence of new packages.

## Later canonical validation

Execution is not released by source preparation. First prepare and independently
review bounded once-only tmux controls with exact finite output namespace,
project/dependency/source/SDK metadata, captures, process groups and teardown.
Reuse inspected native Makefile/scoped commands; never broad-copy runtime trees
or build the unguarded Driver.Test asset group. Restore/packages are out of scope.

Concrete command forms from N, with separately frozen exact stage environment,
OutputPath/IntermediateOutputPath and output policies before execution:

```text
dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:GeneratePackageOnBuild=false -p:UseSharedCompilation=false
dotnet build Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:GeneratePackageOnBuild=false -p:UseSharedCompilation=false
dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:GeneratePackageOnBuild=false -p:UseSharedCompilation=false
dotnet build Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:SkipFocusedTestAssets=true
dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:SkipFocusedTestAssets=true
dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false -p:SkipFocusedTestAssets=true
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeFrontendModelsTests
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractScreenModelTests
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractScreenServiceTests
```

After implementation settles, run each reviewed managed workflow separately:
Core `ContractWitnessReductionTests`; TG `ContractRuntimeObligationTests`,
`ContractRuntimeSelectedDraftPreparationTests`, `ContractRuntimeUnreachableBodyTests`;
Driver `ContractRuntimeDraftDiscoveryTests`. Use the corresponding concrete
`dotnet test <project> --no-build --no-restore --filter FullyQualifiedName~<class>`
form above, serially, one class per invocation. This is final integration of
managed components, not real solver execution. Release real `ContractQueryTests`
and `ContractRuntimeLibraryCommandTests` only through separately reviewed bounded
final controls after required prerequisites/effects are known. Scoped whitespace
checks cover exactly changed/new C# leaves with `dotnet format whitespace .
--folder --include <listed leaves> --exclude bin obj Binaries --verify-no-changes
--verbosity minimal`; freeze exact per-directory argv before execution. Review
project XML separately. No full suite, automatic workers or repeated checks
without a new relevant change.

## Risks, approvals and closure

The user already authorized all PBT fixes, a focused logical commit and main
integration. This source phase adds no paid call and makes no commit. The
Driver.Test asset-copy guard is a scoped validation-build support change;
default normal asset copying remains intact. Independent review must reject
unrelated edits, weakened proof/score contracts or inaccurate readiness claims.

Source reconciliation can proceed alongside the immutable root image and
cohort work because it changes neither K binaries nor V155 inputs. Final
delivery still requires actual canonical checks, focused owner documentation,
reviewed staged hunks and the requested native→Cosyn→root commit chain. Record
accurate co-authors when committing. Preserve all unrelated changes and record
unrun checks/blockers explicitly. Before handoff inspect plan/wiki recursively
for non-Markdown entries. Mark done only when delivery acceptance is achieved;
leave the broader stabilization goal active until its remaining work is done.

## Actual source handoff and independent refusal

The author completed33 changed leaves and left three shared tests without writes.
Current N/K match35/36 listed leaves; Driver.Test has the local asset guard.
Four prior-N snapshots remain under the authorized baseline. Author named R/W
was4,176,319/4MiB; no formatting/checks/staging/commit/gitlink change occurred.

Fresh independent review inspected actual N/K/base, snapshots and23 approved
helpers (5,206,193/5MiB). Iterator preservation, seeds, service/foundation scope,
project defaults and safe memory effects were checked. SOURCE was REFUSED:
screen preparation accepts assumed division/index well-formedness while later
verification preserves it. Fingerprinting cannot restore omitted obligations.
No actual build/test/format/native result was accepted.

The [focused K/N plan](/workspace/tmp/pbt-agent-frontend-baseline-20261023-r01/native/plan/2026-10-24-pbt-screen-option-soundness.md)
governs preparation policy and service-test fixes in both trees, reusing existing
internal verifier policy. After independent delta review, K needs scoped
TG/TG.Test checks; N still needs its complete canonical gates. Root image now
needs accepted seed Driver plus repaired TG, keeping V155 and eleven callbacks.


## Canonical validation controls: ready for source-only preparation

N is the canonical working tree; accepted K/T2 checks do not validate N. Prepare
only fresh `/workspace/tmp/experiment/pbt-canonical-native-checks-20261024-r01/`
controls: `run_checks.py`, `provenance.json`, and `output-policies.json`, each at
most128KiB. No execution, executable preflight, claim, freeze, provider, Docker,
Git mutation, product-source or test edit is released by this preparation.
Fresh named read/write budget4MiB covers this plan, retained T2/R06 mechanisms,
36 accepted leaves, six projects/assets, eight test-class definitions and named
metadata; no binary/toolchain content scan or repository/runtime copy.

The exact accepted36 paths comprise33 C# leaves in nine directories. Freeze one
whitespace argv per directory, including only the listed C# leaves, with:
`/usr/bin/dotnet format whitespace . --folder --include <exact names> --exclude
bin obj Binaries --verify-no-changes --verbosity minimal`, cwd the corresponding
N directory, timeout120s. Include identical listed tests for whitespace only;
this does not release their real solver/CLI test classes.

Then serially build Core, TestGeneration, Driver, Core.Test, TestGeneration.Test,
Driver.Test, each300s. Exact shared argv is `/usr/bin/dotnet build
Source/<project>/<project>.csproj --no-restore -m:1 -nr:false
-p:BuildProjectReferences=false -p:GeneratePackageOnBuild=false
-p:UseSharedCompilation=false -p:OutputPath=/workspace/cosyn/dafny/Binaries/
-p:AppendTargetFrameworkToOutputPath=false
-p:IntermediateOutputPath=obj/Debug/net8.0/ -p:ProduceReferenceAssembly=false
-p:_GetChildProjectCopyToOutputDirectoryItems=false`; append
`-p:SkipFocusedTestAssets=true` for each test project. Cwd is N. No reference
builds, package restore/generation or recursive Z3/TestFiles copy is authorized.

Finally run eight managed classes separately,120s each, using `/usr/bin/dotnet
test Source/<project>/<project>.csproj --no-build --no-restore -m:1 -nr:false
-p:BuildProjectReferences=false -p:OutputPath=/workspace/cosyn/dafny/Binaries/
-p:AppendTargetFrameworkToOutputPath=false
-p:IntermediateOutputPath=obj/Debug/net8.0/ -p:ProduceReferenceAssembly=false
-p:_GetChildProjectCopyToOutputDirectoryItems=false -p:SkipFocusedTestAssets=true
--filter FullyQualifiedName~<fully-qualified-class>. --logger
console;verbosity=minimal --results-directory <this stage>/results`:
Core.Test ContractWitnessReductionTests; TG.Test ContractRuntimeFrontendModelsTests,
ContractScreenModelTests, ContractScreenServiceTests, ContractRuntimeObligationTests,
ContractRuntimeSelectedDraftPreparationTests, ContractRuntimeUnreachableBodyTests;
Driver.Test ContractRuntimeDraftDiscoveryTests. Freeze observed source-derived
case counts and exact argv. ContractQueryTests and
ContractRuntimeLibraryCommandTests remain separately gated real final checks.

This profile has exactly23 stages:9 whitespace,6 builds,8 classes; maximum
stage deadlines3840s. Reuse accepted T2/R06 identity/read/metadata/census/capture/
observer/owned-group teardown helpers. Adapt only profile/namespace/control-file
bindings, initial absence and cumulative accounting. N's three test DLLs are
initially absent: pin absence, require it until their own authorized build,
then bind regular bounded output hashes. Do not invent before hashes or require
an absent assembly to change from a fictitious hash. Production outputs retain
actual baseline guards and must obtain new build identities. Do not copy K DLLs.

Require existing regular assets for all six projects and actual cached reference
metadata. Pin Core parser/Scanner outputs and Dafny.atg/Coco inputs; check metadata
and incremental timestamps before Core build and refuse stale/missing outputs
before any RunCoco tool restore. Pin .NET/project/format controls without broad
installed-toolchain reads. Driver.Test's active direct fixture group is20 files,
69,307B; Core direct prelude67,083B. Pin every exact leaf and admit only its
specific output destination. Guard default-on/explicit-skip project XML semantics.

Construct a finite output-policy record from six exact project/assets definitions,
known direct output names and finite content leaves; no recursive runtime or
Binaries discovery. Record initial named metadata census and absent prospective
leaves. Runtime membership must stay exact, at most512files/128MiB across the
six-project union; if the derived finite namespace does not fit, stop preparation
and report the concrete required scope adjustment. Native outputs remain under
N/Binaries and the six own obj/Debug/net8.0 directories only; assets stay immutable.

Each stream retains1MiB; each stage retains prior32MiB/64files/32dirs/128entries/
depth6 checked accounting ceilings, status8KiB and process-group2s grace. Add a
finite aggregate capsule bound128MiB plus3x128KiB control reservations+8KiB claim
+16KiB final =134635520B, at most261files and132directories including controls
and namespace parents. Aggregate retained stage entries<=512; include final
status reservations before acceptance. These are checked accounting limits, not
filesystem quotas. Native output128MiB is separate, so combined native/capsule
logical ceiling268853248B. Fail and retain evidence when a ceiling is exceeded.

Keep the maintained sanitized environment and stage-local TMP/TEMP/NUGET paths;
outer `/usr/bin/python3 -B -P` uses the reviewed capture import root. Prepare a
fresh tmux socket/session `pbt-canonical-native-r01-20261024`, cwd
`/workspace/tmp/experiment`, with exact env-i argv recorded. New controls must
state prepared-only and unapproved/unreleased. Fresh independent source/effects
review, actual approved-context executable binding, freezing and final exact
argv review precede one dispatch. Preserve all mixed/unrelated N/K changes.


### Preparation recovery budget and retained failure

The initial named extraction read only the authorized plan/source/project/assets/
controller leaves and constructed retained buffers. Its large JSON return was
truncated by the execution tool; orchestration JSON parsing then failed on the
truncation warning. No canonical controls existed or were written at that point;
no native build/check/import, dispatch or freeze occurred. Preserve this failed
preparation approach as process history; it establishes no validation result.

Prospectively authorize total8MiB named read/write for this exact three-control
preparation, accounting the initial reads once plus all recovery reads/writes.
The original4MiB allowance is not retroactively changed. Keep the same23 stages,
three <=128KiB controls, finite policies, source guards and cumulative caps.
Recovery constructs/writes the allowed controls in one process and emits only
compact counts/pins/summary <=40KiB; do not return full inherited manifests or
filelists through the tool. No new package/runtime copy, third-party helper,
executable preflight, freeze or dispatch is released. Independent source/effects
review and separately bound actual execution remain required.


### Canonical preparation blocked by existing multi-link package output

The compact recovery read the exact finite named inventory, then the initial
output census refused `N/Binaries/Boogie.AbstractInterpretation.dll`: it is a
regular36,352B file with link count2, mode0755, device2049/inode203302719.
The maintained regular-single-link guard correctly rejected that link count.
It is NOT a symlink. The first commentary diagnosis inferred a symlink from the
generic guard exception; a metadata-only follow-up corrected that inference.
An attempted failure-record script asserted that incorrect type before writing;
this is the first durable record of the concrete multi-link blocker.

No canonical control directory/files were created. No target import, native
check/build/test, executable preflight, freeze/claim, tmux, Docker/provider or
Git action ran. Product/test files and K binaries/results are unchanged. No DLL
or package/toolchain content was read. Other hard-link aliases were not searched.
Do not infer their locations or claim CopyLocal write safety without evidence.

Before retry, explicitly review a finite pre-existing multi-link output policy
and actual CopyLocal behavior, or authorize a distinct owned output/dependency
layout. Do not silently relax single-link helpers, modify linked package bytes,
copy runtime trees or substitute K results. Keep canonical validation pending.
Any further full extraction needs a prospective budget extension; retain both
preparation errors and the corrected diagnosis.

Reconstructed exact named extraction bytes, using unchanged leaf-size metadata:
first truncated extraction3378884B; compact recovery3446551B; shared non-plan
inventory3356400B. Earlier plan reads72,467B/writes46,197B are additional. The
asserted failure-note read23,713B without writing; this note reads23713B
and writes its final plan size. These are reconstructed inventory totals, not
a recovered instrumentation value from the truncated output. No validation
success is implied. The existing23-stage profiles and caps remain unchanged.
