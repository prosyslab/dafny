# Keep iterator type dependencies out of PBT implementation drafts

Status: done (independently accepted source/local scope; root owns actual registered controls)
Date: 2026-10-23
Parent: [PBT stabilization](../../../plan/2026-10-21-pbt-stabilization-loop.md)
Observed failure: [registered iterator controls](../../../plan/2026-10-23-pbt-iterator-isolation-image.md)
Predecessor: [iterator diagnostic isolation](2026-10-23-pbt-iterator-diagnostic-isolation.md)

## Objective and acceptance

Fix the actual public R07 false `Isolation.Typed.Valid` implementation-draft
request without changing authored sources, contracts, proof inputs, fingerprints,
trust, public reachability or conservative iterator support. This is tooling
maintenance under the ongoing stabilization instruction, not an evaluated turn.

1. Reproduce the exact R07 type-only source through real in-memory parsing,
   selection and the production missing-draft boundary. Retain the red assertion,
   exact source/test/assembly hashes, command and complete bounded log.
2. Reuse the existing closure mode that omits resolver type-only edges to
   IteratorDecl in implementation-draft discovery. Keep actual callable edges,
   selected goal/generator specification expressions, ordinary helpers, dispatch,
   constraints/witnesses/constants and existing by-method/lemma behavior.
3. Keep public ExecutionReachable/DiagnosticReachable and their callers' proof,
   fingerprint, source-preservation and certificate scopes unchanged. Reuse the
   same private mode for the existing iterator capability guard. No name filter.
4. Memory regressions cover the exact failing source; a type-only iterator's
   yield-only missing helper; real selected/spec helpers that must remain drafts;
   and the real prepared-generator/visibility/resolve/selection path. Preserve
   constructor/advancement Unsupported. Each test has an intention comment.
5. A fresh independent verifier inspects source and effects, builds affected
   projects and runs its own affected memory selection. Record all failures,
   source/output bindings, commands, versions and limits before source acceptance.

Actual native compilation of diagnostic targets, sampling, solver proof, image
adoption and csplit efficacy remain root-plan work. No paid call, new image or
container, package, commit or change to a completed cohort is authorized here.
The current owner-based Unsupported classification of direct generated validity
references remains conservative; finer support for ghost iterator validity is a
non-goal. Do not refine that boundary or add a redundant generated-Valid filter
while fixing the demonstrated type-only false dependency.

## Evidence and existing implementation

Root/cosyn/native AGENTS.md and native CLAUDE.md govern this work. No deeper
instructions/templates were found in the named plan/wiki/source directories.
Preserve all pre-existing dirty source/docs and frozen artifacts.

R07 actual execution review JSON26847B/SHA
88c2c7214dd7fc244401763b768c85a1e9019cb3ea333b58a5f4a83a817b4166,
MD9537B/SHAcb2b437bc0fe4fbf50796345baf2b3adc0154d60ee126f03650c037ddd9d3f42
is fully read/authenticated by rootba6503. It accepts failure/accounting/cleanup
and rejects control success: one bound call,0accepted/samples/proofs and seven
unrun;59Docker, installed14/HOME/effective FSIZE(-1,-1), owned cleanup pass.
Its native receipt2635B/SHA
bd8a6a41a169880b532748b56ecaeaf1fd75a3eaa10a1054ad2d5ba6a775a977
binds the exact415B source55c6ab086ae101670855f36945a89c4d9a0be7bdf7d527be783f80feda52a07e.
It requests only generated `Isolation.Typed.Valid`, despite a concrete Typed
body and only an unused nullable local in selected Scalar. Python renders the
native result; two independent read-only investigations trace the current source
mechanism. Binary/source installation bindings belong to the prior root gates,
not a revision field invented in this receipt.

CallGraphBuilder.AddTypeDependencyEdges adds caller-to-IteratorDecl for a local
type. The default broad ExecutionReachable traverses that declaration's generated
constructor/MoveNext contracts and discovers bodyless Member_Valid. MissingDrafts
admits ghost functions, so it asks for a nonexistent authored body before source
transformation. The existing capability query already excludes IteratorDecl
pseudo-edges privately, while both MissingDrafts sites use the broad default.
Existing transformer-level tests never call missing-draft discovery.

## Change table

| Owner / exact file or symbol | Change, necessity and preservation | Validation |
| --- | --- | --- |
| Native Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs::RuntimeExecutionReachable (new internal wrapper), UnsupportedRuntimeIterator | Expose the existing false-type-edge mode through an internal helper and reuse it for capability and discovery. Existing friend assembly gives Driver access; keep public broad methods/default/core behavior intact. | Real parsed source distinguishes actual calls from type-only dependencies; broad closure still retains generated Valid; constructor/advance guard preserved. |
| Native Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs::MissingDrafts | Make the exact production seam internal for friend tests and use RuntimeExecutionReachable. Both existing initial/post-generator sites therefore use the same corrected discovery. Preserve all draft ownership/contract/source-map/lemma/by-method filters. | Red/green real discovery and prepared-generator tests, exact legitimate helper lists and direct-call controls. |
| Native Source/DafnyDriver.Test/ContractRuntimeDraftDiscoveryTests.cs (new) | Bounded source-string regressions through SnapshotFileSystem, real resolver/selector and production discovery; no public campaign wrapper. | Audit setup/execution/deferred cleanup before running; no test-side directory/file writes, processes, compiler, solver, staging, fsync or installed-tree reads. |
| Native this plan/plan INDEX and wiki/pbt-unreachable-bodyless.md/wiki INDEX | Record source-only evidence, known conservative capability boundary and separate actual controls. | Scoped diffs, links and recursive Markdown-only audit. |
| Root iterator/parent plans, plan INDEX and wiki/architecture/pbt-runtime-image.md/wiki INDEX | Preserve R07 failure and independent audit; link this correction and later packaging gates. | Correct populations/limits and no live-input or scoring claim. |
| /workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/ | New isolated output/intermediates/logs and independent verification evidence. Never overwrite predecessor output or frozen capsules. | Exact finite reference/package/fixture bounds below; source/output hashes before each freeze. |

## Build and validation profile

Working directory is /workspace/cosyn/dafny. Use the existing SDK8.0.131 and
cached locked assets; no restore or dependency build. Let R be exactly
/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01. The implementation owns
R/out and R/obj; the fresh verifier owns R/verification/out and obj. Each uses
its own TMPDIR and bounded logs under that namespace. Preserve HOME. Set
DOTNET_CLI_TELEMETRY_OPTOUT=1, DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 and
DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1.

Reuse the predecessor's explicitly measured six reference DLLs/table and cached
asset metadata/copy profile. Seed only those six named regular references plus
the accepted predecessor TG.dll841216B/SHA286d1879c308a0339557f999f06fc76ca6b97e0ec29792943131dbd5c805e388
for the red access-seam build. Verify every copied input's full size/hash; never
copy a source/runtime tree or seed another TG. The source-level friend accesses
are already declared; no new AssemblyInfo or project/package change is needed.

For P in DafnyTestGeneration, DafnyDriver, DafnyDriver.Test use exactly:

```text
timeout 120s dotnet build Source/P/P.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo
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

Expand R/P to actual argv, record each exact command before consumption. For
Driver.Test only, set UseCommonOutputDirectory=false,
_GetChildProjectCopyToOutputDirectoryItems=false and
CopyLocalLockFileAssemblies=true. Before any build, authenticate the predecessor
cached-asset records and inspect the exact named package/copy inputs' current
metadata against those recorded bounds. Driver.Test's known299package leaves/
34572548B,20own fixtures/69307B and2Z3content leaves/58670216B are the limits;
refuse any new/missing/symlink/escaping input or excess, then amend this plan
before proceeding. Each of the two output prefixes may receive that finite
normal build-time set once; no per-test staging or tree traversal/copy. Use
PreserveNewest for green rebuilds. No actual MSBuild metadata query or runtime
digest-tree walk is released by this plan.

Implementation allowance: at most2red builds (Driver with access seam only and
Driver.Test), then3green builds (TG,Driver,Driver.Test); one red and one green
no-build/no-restore memory test invocation. Fresh verifier allowance:3builds and
one independent no-build/no-restore invocation. Each build/test is120s and every
raw log<=1MiB; log/hash failed prerequisites rather than automatically retrying.
No predecessor build/test allowance is reset. Any missing prerequisite or source
change requiring another attempt needs a documented bounded amendment first.

Memory test command from owning root:

```text
timeout 120s dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeDraftDiscoveryTests --results-directory R/test-results <same complete Driver.Test profile>
```

The outer vstest host needs its normal localhost control socket. Use the approved
escalated path if the sandbox denies that prerequisite; do not bypass safeguards
or add provider/network tests. The tests themselves remain entirely in memory.
Run only the affected selection during iteration. After source settles, scope
formatting to the three changed files with
`timeout 120s dotnet format whitespace . --folder --include <exact three files> --verify-no-changes`
and `git diff --check -- <exact source/docs>`. No broad native suite.

## Risks, approvals and handoff

A narrower draft consumer must not narrow proof/trust or source-preservation
closures. Yield-only and selected-spec helper controls distinguish those roles;
constructor/advance checks preserve the unsupported capability boundary. New
tests must call production discovery rather than recreate predicates. The
in-memory generator preparation path must be inspected transitively before use.

The local changes/builds are within the existing stabilization authorization;
no extra human approval is required for this bounded reversible source work.
Request no package, paid run or commit. Root owns any later explicit image plan
amendment, fresh source/input gates and actual execution. Keep R07 immutable,
including all failed acceptance/accounting, and do not silently substitute a new
fixture or classify unrun samples/proofs as passed.

Current state: source-ready; the announced implementation is limited to the internal
runtime closure seam, production missing-draft discovery and bounded in-memory
Driver.Test regressions. Independent source verification remains pending.

## Implementation record

The first metadata-only prerequisite script failed before inspecting inputs
because it assigned zsh's reserved `path` variable and made `stat` unavailable.
No source, artifact, build or test changed. The corrected bounded check authenticates
the predecessor's299 package leaves/34572548B and20 fixture leaves/69307B as
regular non-symlinks at their recorded paths. The two regular Z3 leaves remain
28132904B and30537312B. Existing locked assets are TG144208B, Driver260038B and
Driver.Test398914B; SDK is8.0.131. The six recorded references and accepted
TG841216B/286d1879c... match every planned size/hash and were copied individually
with mode0644 into the new output. No tree, package or predecessor artifact changed.

Before consuming red allowances, the exact commands are:

```text
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyDriver/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyDriver/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=false -p:_GetChildProjectCopyToOutputDirectoryItems=false -p:CopyLocalLockFileAssemblies=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeDraftDiscoveryTests --results-directory /workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/test-results -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=false -p:_GetChildProjectCopyToOutputDirectoryItems=false -p:CopyLocalLockFileAssemblies=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
```

Both red builds passed with0warnings/errors. The single red selection executed
four cases and failed4/passed0/skipped0. Two failures are the intended product
red: selected helper control additionally returned `M.Typed.Valid` and
`M.YieldOnly`; the real prepared generator additionally returned
`M.GeneratorYieldOnly` and `M.Typed.Valid`. Two are fixture defects to correct
before green: the raw R07 literal omitted its final newline (actual e2cbbb... is
the exact receipt text without its final byte), and `iterator` was used as a
reserved local identifier. Red source hashes are runner409eee37..., unchanged
transformer70c5d5c6... and test89dce4c9.... Bound assemblies are accepted-old
TG841216B/286d1879..., new Driver501760B/8e29ce62... and Driver.Test425472B/
ef6ab0c8.... Raw bounded logs are under `R/logs/red-*.log`. Red allowances are
fully consumed: Driver1, Driver.Test1 and memory-test1.

The fixture corrections and planned product change are now applied. Before
consuming green allowances, the exact build commands are:

```text
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet build Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyTestGeneration/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyTestGeneration/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyTestGeneration/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyTestGeneration/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyDriver/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyDriver/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
DOTNET_CLI_TELEMETRY_OPTOUT=1 DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1 DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 TMPDIR=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/tmp timeout 120s dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --no-dependencies -m:1 /nr:false -v:q --nologo -p:OutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/out/ -p:BaseIntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/ -p:IntermediateOutputPath=/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/obj/DafnyDriver.Test/Debug/ -p:MSBuildProjectExtensionsPath=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/ -p:ProjectAssetsFile=/workspace/cosyn/dafny/Source/DafnyDriver.Test/obj/project.assets.json -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=false -p:_GetChildProjectCopyToOutputDirectoryItems=false -p:CopyLocalLockFileAssemblies=true -p:CompileUsingReferenceAssemblies=false -p:DefaultItemExcludesInProjectFolder=obj/**
```

All three green builds passed with zero warnings/errors: TG exit0/chunk a1120f/
5.37s (MSBuild5.20s), Driver exit0/chunk ef27f8/5.44s (5.31s), and Driver.Test
exit0/chunk744df2/4.96s (4.79s). The single green invocation reused the exact test
command recorded above through the approved localhost-vstest escalation and passed
all4selected cases in32ms with0failed/0skipped, exit0/chunk65dbf0. These are list
and capability assertions through production seams; they do not claim a public
campaign status. Raw logs are `R/logs/green-*.log`; every red/green log is at most
2032B, below the1MiB bound. Implementation allowances are fully consumed:
2red+3green builds and1red+1green memory invocations. There were no automatic
retries. The only prerequisite failure remains the pre-build reserved-zsh-variable
mistake recorded above.

The final retained dirty native source set has five leaves, including predecessor
work: command test1492B/edba40660c6e17d9e364e221f1016b8c0bef6054b175b05504c87ec5f096d349,
runner79973B/1f0752973c063bed0f59236b3b489347abcbaaab661be7f8e42d86ed7f5aca0f,
TG test29884B/182cb1ed25d100d831f0d30327073f0d09e2c6a351de849f89f1c50211eccb97,
transformer99152B/59d9c2c8d9f7e92a605d1dcfce1669366251ad74db72d90683526ff5c8ac82d0,
and new draft test7554B/09ba403cbe069fd0803a704a5345c1efda44fef6b92070a8371894cba32d7f3f.
Scoped whitespace and diff checks pass. The new test contains the exact415B R07
source/hash, preserves public broad reachability as a control, proves zero runtime
drafts for the type-only iterator, keeps actual body/spec helpers, rejects a
constructed/advanced iterator, and runs real generator preparation before
discovering only its actual helper.

Locked asset bindings are TG144208B/c7608b2d02310fde6f285d31e4629e19b06d0d29e6554fd9fd549fb4ba1b9f59,
Driver260038B/9f73a4654ea61d6c01829aab81d7610863ef81da0d17fe772be57e28feaeda73,
and Driver.Test398914B/61fe5e71ad118ed340914905c7750f49bd4beb1cf5952f6fa660a78e2b58c9eb.
The accepted predecessor origin is `R03/out`: Core5359104B/a43f0c42...,
Pipeline1414144B/4e919e90..., Runtime178176B/f84079ab..., old Driver501760B/
2e5feffa..., LanguageServer355328B/09bf9434..., Core.Test893952B/cb5a3987...,
and old TG841216B/286d1879.... The individually seeded copies matched. The final
compile reference set retains the five unchanged Core/Pipeline/Runtime/
LanguageServer/Core.Test hashes and binds Driver to the new TG841216B/7a1803da....

The four new product payloads match output to intermediate byte-for-byte:
TG DLL841216B/7a1803dacc685912ed41987cc971532facc39f812316bb604fc8011f13494f77,
TG PDB213248B/1ba6fa7d5ddeb5c11205c4290cc4e4d6619db3e1b8c6287aba5f43da97e84792,
Driver DLL501760B/eddcc9f157487fcaa86318f7d8b025dd5a50967885bc28879e6deacdb4ffd422,
and Driver PDB135892B/c2ddd7ff0b20bc1902805b67b2b1e5d0b719a8be6e83afbdd1e17d013b10300c.
For test reproducibility the Driver.Test DLL425472B/e81069b7... and PDB86928B/
cb0250f4... also match their intermediates. TG deps56116B/afe4d65e...,
Driver deps94479B/49d15901... and Driver runtimeconfig285B/62c4c608... are
byte-identical to the accepted predecessor copies, so this build establishes no
new dependency or configuration payload.

The generated compiler inputs in the new prefix are also frozen. TG has
AssemblyAttributes194B/ae41ca1e..., editorconfig594B/20c37e61..., sourcelink137B/
2792058b...; Driver has the same194B attributes, editorconfig578B/54eca31e...,
and the same137B sourcelink; Driver.Test has the same194B attributes,
AssemblyInfo1003B/147e2673..., GlobalUsings287B/addb143f..., editorconfig588B/
dcfc644c..., and the same137B sourcelink. These are named-leaf source-build facts,
not an installed image, registered-tool, compiler, solver, proof or runtime result.

No wiki/index/parent record was edited in this implementation handoff: root
explicitly retained those records and the fresh-verification closeout. The
existing iterator knowledge page therefore remains predecessor-owned until root
reconciles this accepted correction. Plan and wiki recursive filename audits
find no non-Markdown leaves. The plan remains `in-progress` while fresh independent
verification is pending; source is frozen and no source edit may follow without
a new root update and review.

## Independent source acceptance and root handoff

Fresh independent5.6-sol/high verification starts from requirements/current
source and uses a separate verification/out and obj prefix. Its own effect and
finite prerequisite audits pass;3no-restore/no-dependency builds complete with
0warnings/errors, and one affected memory selection passes4/4with0skipped,
29ms. All five source hashes match before builds and after tests. Exact own
commands/profile/log bindings, copied origins, references, generated inputs,
outputs/intermediates and dependency compatibility are in exclusive0444:

- [source-review.json](../../../tmp/pbt-iterator-draft-discovery-20261023-r01/verification/source-review.json),25305B/SHAa60e53f9af97536b66ef4bcade131ee57532c8eebe1e94ec8e95e015c1cdc06e.
- [source-review.md](../../../tmp/pbt-iterator-draft-discovery-20261023-r01/verification/source-review.md),9721B/SHAaeba37c2e05336d2d93a24a994c9e3edd9287b45a669653492d0ec33f17622c2.

Root558a59 fully reads/authenticates both and c98011 checks actual schemaVersion,
accepted/source-only status, five frozen leaves218055B and exact accepted prefix.
Initial root0ae065 assumed the predecessor's schema key and failed without
mutation; the actual reviewed schema is used after correction. Root9cb7c8
compares only the two production leaves with authenticated R07 snapshots;
its earlier helper969cee used the wrong manifest key, also without mutation.
These are root inspection mistakes, not product or gate failures.

The only accepted packaging prefix for this new review is
/workspace/tmp/pbt-iterator-draft-discovery-20261023-r01/verification/out/.
Its4payloads total1692148B: TGdll841216B/73329a9a...,
TGpdb213264B/a9a4a091..., Driverdll501760B/e09ebd24...,
Driverpdb135908B/66325017.... Rootd49093 fully checks all four output/intermediate
pairs, exact path/size/hash binding and byte equality of the three product deps/
runtimeconfig files to the accepted predecessor. Do not substitute the separately
built implementation outputs; different isolated prefixes have distinct bindings.
No new dependencies/configuration payload is needed.

Durable findings and conservative capability limits are in
[iterator draft discovery](../wiki/pbt-unreachable-bodyless.md#iterator-types-and-implementation-draft-discovery-2026-10-23),
indexed in wiki/INDEX.md. Root has reconciled the previously overbroad full-
workflow claim with R07's actual earlier preflight defect. Source/local acceptance
is complete; actual image/registered PBT/target compilation/solver/csplit results
remain the [root control plan](../../../plan/2026-10-23-pbt-iterator-isolation-image.md).
All old artifacts/failures and completed cohort inputs/results are preserved.
No commit, paid provider or container operation was performed in this source plan.
