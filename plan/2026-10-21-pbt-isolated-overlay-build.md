# Build the repaired PBT library in an isolated native context

Status: done (r05 actual isolated native build independently accepted)
Date: 2026-10-21
Parent: [/workspace/plan/2026-10-21-pbt-stabilization-loop.md](/workspace/plan/2026-10-21-pbt-stabilization-loop.md)
Repair: [unrelated bodyless declarations](2026-10-21-pbt-unreachable-bodyless.md)
Controls: [unfinished public workspace](../../../plan/2026-10-21-pbt-unfinished-workspace-controls.md)

## Objective, ownership and acceptance

Prepare and then execute one separately reviewed offline build of the repaired
DafnyTestGeneration.dll. This is public native tool maintenance, not a candidate
turn, development-test compilation or paid experiment. The native repository
owns the build/source contract; root owns later public container composition.
Preserve the accepted old isolated tree, its package, image40d and all original
reports. Do not borrow mutable live outputs or absorb concurrent nested-match
changes. Do not rebuild Core, Pipeline, Runtime, Driver or the canonical launcher.

Acceptance is an independently reviewed processor/input gate, an exact fresh
native source context at b4f683fd85c9764c032346e0367df325f73dd4be plus the
accepted thirteen-product overlay, three exact inherited reference DLLs, a
successful offline restore of existing versions, checked MSBuild metadata and
one successful ordinary project build whose actual output/source/references/
configuration/logs are bound by a new immutable receipt and fresh independent
accounting. Source/local repair acceptance alone is not package acceptance.
Build acceptance is not image, native campaign, solver, benchmark or stability
acceptance. No packages, commits, private reads, provider, Docker, tag or paid
operations are authorized here.

## Inspected evidence and existing solutions

Applicable root/Cosyn/native AGENTS.md and native CLAUDE.md govern this work.
New scratch W=/workspace/tmp/pbt-unfinished-workspace-build-20261021.
The original /workspace/tmp/pbt-worker-failure-20261021/native is immutable.
Only its exact twelve unchanged reviewed production leaves may be read as
source inputs; only the corrected whole Transformer leaf comes from the newly
independently accepted live repair. Every other live change is excluded.
Original source acceptance is
/workspace/tmp/pbt-repeatable-proof-inputs-20261021/source-review.json SHA256
e88ebf21a2bebadec02db751ac0734d065a97be33e47e8e0e930004aad827f15.
New source/local acceptance must be the exact readonly
/workspace/tmp/pbt-unreachable-bodyless-20261021/verification.json and its
actual externally supplied digest; no report's presence grants authority.

Inherited reference inputs are only DafnyCore.dll, DafnyPipeline.dll and
DafnyRuntime.dll under the immutable public
/workspace/tmp/experiment/pbt-authored-generator-20261021-r03/context/app.
Validate their actual hashes against its accepted original manifest/package
records. They are deliberately inherited implementation references, not newly
compiled dependencies. The later public child image inherits all other native
and original0ff Cosyn leaves explicitly; this plan builds just one library.

Read-only Git/SDK/project inspection established a concrete normal-build path:

- b4 has6531tracked leaves/29,226,166blob bytes, maximum821315bytes/depth11,
  no gitlinks. Two tracked integration-test symlinks exist; never follow/read
  their targets. Compile/resource inputs must be regular leaves, not symlinks.
- The tracked TestGeneration subtree has50leaves/about648KiB. Overlay all thirteen
  accepted products to establish the agreed source state; no other source edits.
- TestGeneration references Pipeline, then Core, then Runtime. Default no-
  dependencies builds still request missing obj/ref assemblies and transitive
  Java Jar content, so three ordinary DLL seeds alone are insufficient.
- Installed SDK targets support common output, implementation-reference use
  and suppression of child content copying through the exact three properties
  below. This is an explicit C# build configuration; it changes no Dafny proof,
  runtime option or source project. Check those target paths before compilation.
- Old declared assets contain75package versions; their directories and extra
  Runtime restore prerequisites exist in the fixed global cache. Existence
  does not prove complete/intact cache content; actual offline restore must pass.
  System.Reactive.targets adds references without Exec. A dependency build
  could run Coco/Gradle, so no-dependencies is mandatory.

## Exact change table

| Path/symbol | Change, method and necessity; unmet behavior without it | Validation |
| --- | --- | --- |
| W5=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r05/{prepare_build.py,check_build.py}, then separately gated phase artifacts/reports already enumerated for W4 | Copy only the accepted W4 pair into a distinct namespace. Interpret only path-valued MSBuild metadata with MSBuild's Linux separator semantics before existing canonical-root/containment/import checks. Preserve literal receipt properties and all source/assets path contracts. | Realistic literal mixed-separator TG response, forward-slash compatibility, traversal/wrong-root/unexpected-import rejection and literal nonmetadata path controls; fresh independent exact-byte gate before once-only phases. No SDK/config/proof/DTO/cap change. |
| This plan and plan/INDEX.md | Register isolated build scope before processor/context creation; preserve owning repair and concurrent records. | Diff, reciprocal links, Markdown-only audit |
| W4=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r04/{prepare_build.py,check_build.py}, followed only by separately gated phase artifacts/reports already enumerated for W3 | Copy only accepted W3 scripts into a new namespace; compare the same75 reviewed asset content hashes against strict .nupkg.metadata contentHash, preserving each raw metadata identity in existing dependency map. Legacy whole-archive hashes are a different domain. Preserve W1/W2/W3 failures. | Signed-package fake with differing legacy hash passes correct metadata; wrong/missing/schema/source/extra-field metadata rejects; exact75bounded paths, no legacy/cache/archive fallback, unchanged success DTOs and phase limits; fresh independent gate before once-only phases. |
| W3=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r03/{prepare_build.py,check_build.py}, then separately gated source/restore/metadata/build inputs, claims, terminals, logs and verification reports already enumerated for W2 | Preserve failed W1/W2. Copy only the accepted W2 script pair and replace exact namespace/runId. Recognize the eight exact already-bound NuGet empty build selections without reading them as imports; preserve a returned restore-process observation on subsequent controlled filesystem/validation failure. | Fake exact-sentinel/no-read and malformed/other-sentinel rejection, real-import/Exec checks, returned-process/postfailure evidence and dedup/compaction; fresh independent exact-byte gate before any W3 phase. Successful DTOs, source/proof checks and all limits unchanged. |
| W2=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r02/{prepare_build.py,check_build.py}; source-manifest.json, preparation.json, restore.json, metadata.json, build-record.json, four exclusive phase claims, empty-feed/empty-template/NuGet.Config, native context, bounded restore/build logs and verification/{preparation-review,actual-build-review}.{json,md} | Preserve failed W1 unchanged. Copy its accepted two scripts into a distinct namespace/runId; correct the preexisting Binaries directory boundary and retain observed source-process outcomes on filesystem failure. Reuse the same thirteen products, three inherited references, SDK/configuration and source authority, with a fresh maximum-one-per-phase gate. | Reproduce existing-directory behavior in memory; fake symlink/non-directory or occupied-reference rejection and source-process/failure preservation; independent exact diff/input/check review before any W2 phase. Old W1 gate/claims cannot authorize W2. |
| W/prepare_build.py | Bounded public source/seed preparation and one-shot restore/metadata/build processor, with separately authenticated exact source/preparation gates and strict phase claims. Never modify old roots or silently retry. | Pure fake filesystem/process/Git/SDK boundaries, specific expected exceptions, fresh independent review before actual operation |
| W/check_build.py | Memory-only input/identity/bounds/failure/phase/output controls with no real directory, process, SDK, source staging, sync, installed-tree read or compiler operation. | Transitive I/O audit; serial fake checks; AST/Ruff; no real build inside tests |
| W/source-manifest.json, W/preparation.json, W/native source context, W/empty-feed, W/empty-template | Exact fresh b4 source context, approved thirteen overlays, three inherited DLL seeds and exclusive empty feed. Use normal Git worktree or isolated Git repository with literal b4 object provenance; no whole-runtime/toolchain/cache/obj copies. | Bounded source/Git metadata, no extra production delta, exact hash maps; no symlink source/resource/reference inputs; original records unchanged |
| W/NuGet.Config, W/metadata.json and generated native project assets | Clear external sources/credentials, only fixed empty local feed and existing /home/vscode/.nuget/packages. Preserve exact declared existing versions/content hashes; evaluate four project target paths and actual compile/resource/reference input sets with fixed properties. | Reject new/different/missing packages, network/fallback sources, wrong references, unreviewed Exec hooks and output paths |
| W/restore.log, W/build.log and W/build-record.json | Preserve actual command, config, SDK, source/references/assets, exits, bounded logs and newly compiled DLL identity, including explicit failures. | Exclusive creation, no overwritten evidence, actual observed completion distinguished from expected values |
| W/verification/preparation-review.{json,md} and actual-build-review.{json,md} | Fresh exact-byte pre-operation review then independent actual source/build accounting. No owner claims as verifier inputs. | Externally pinned readonly gate, actual source/output maps, honest source/build-only limits |

## Concrete commands, configuration and phase gates

The two processor/checker filenames use underscores so the memory checker can
import prepare_build normally. No importlib, runpy, dynamic compile/exec import
or module-name workaround is permitted. Imports perform no operational I/O.

First prepare only the processor and memory checker; no Git checkout, source/DLL
copy, restore, metadata process, build, freeze or runtime packaging until the
repair has fresh source/local acceptance and an independent verifier accepts the
exact processor/input closure. That review supplies a readonly externally pinned
gate with separate maximum-one preparation/restore/metadata/build claims. Do not
infer operation authority from a file's existence or an old report.

Fresh source construction may use one detached worktree or isolated repository
at literal b4. It may overlay exactly the thirteen accepted product paths and
seed exactly the three inherited implementation DLLs into native/Binaries/.
Bound checkout to8192leaves/64MiB/max1MiB/depth16, capture Git metadata before
materialization, and never follow the two unrelated tracked test symlinks.
Keep all copies outside plan/wiki. No reset/removal of another checkout or
original source. Independently authenticate the changed Transformer bytes and
the original twelve remaining product hashes before and after preparation.

Processor design selected before script creation: use a non-bare repository
whose work tree, index, HEAD, configuration and primary object directory are all
under W/native. Initialize it from W/empty-template with the fixed `source`
branch, then create only its local `.git/objects/info/alternates` file, mode0444,
pointing at the canonical public object database
`/workspace/.git/modules/cosyn/modules/dafny/objects`. Git writes therefore stay
inside W; the alternate supplies read-only object provenance and no ordinary
worktree/shared metadata is touched. Before materialization, parse the exact
NUL-delimited `ls-tree` inventory and enforce the leaf/byte/per-leaf/depth and
no-gitlink bounds. Bind the isolated HEAD to literal b4, populate its index with
`read-tree`, and use `checkout-index` once. Post-checkout scanning uses lstat and
runs one fixed `git diff --exit-code --no-ext-diff --no-textconv HEAD --` before
overlays so Git applies the pinned attributes while authenticating canonical
tracked content. A separate bounded nofollow pass accounts the actual regular
working-tree bytes and executable/symlink modes without opening the two tracked
symlinks.

Every source, restore, metadata and build phase creates an exclusive claim before
its first mutation or process and an exclusive terminal record on success or
failure; a surviving claim spends that phase and forbids retry. The external
preparation gate pins the exact processor/checker bytes, commands, source
contracts and four maximum-one claims in addition to the independently accepted
source-review digest. Metadata uses four fixed evaluation-only `dotnet msbuild`
property/item queries, with no target invocation, under one30-second/2MiB phase.
Package validation requires the exact75 TestGeneration package/version/content-
hash set, exact empty-feed/cache/config identities, and bounded selected NuGet
import files without Exec. These controls are checked with fake boundaries before
any claim or actual source/build operation.

From W/native, restore only existing project versions/cache, serially, using a
new minimal config that clears inherited package sources and credentials:

```sh
dotnet restore Source/DafnyTestGeneration --configfile ../NuGet.Config --source ../empty-feed --packages /home/vscode/.nuget/packages --disable-parallel -p:NuGetAudit=false -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=true -p:CompileUsingReferenceAssemblies=false
```

No ignore-failed-sources, downloads, package addition, cache copy or fallback.
NuGetAudit=false preserves the old accepted assets' offline configuration and
avoids an external audit lookup; it is not a Dafny verification option.
One restore maximum120seconds/4MiB captured public log. Validate newly generated
assets' exact fixed source/cache/declared version and content-hash sets before
proceeding. A missing prerequisite is a failed phase, not permission to retry.

Evaluate actual GetTargetPath and compile/resource/project-reference metadata for
the four named projects with the same fixed three properties. DafnyRuntime clears
the shared net8.0 TargetFramework and declares netstandard2.0;net452, so its one
evaluation-only query additionally fixes `-p:TargetFramework=netstandard2.0`, the
compatible inner build referenced by the net8.0 Core consumer; never accept its
outer cross-targeting build's empty TargetPath. Bind the exact metadata argv in
the processor before its independent review. One metadata
phase, maximum30seconds total/2MiB capture; require inherited three DLL paths in
native/Binaries, no missing ref assemblies or dependency-copy/Jar prerequisite,
and only the intended current TestGeneration compilation inputs. Verify SDK
imported targets relevant to this path do not execute Coco, Gradle or other
unexpected tools. Do not hash/read whole installed SDKs or package trees.

Then one ordinary serial build, maximum120seconds/8MiB public log:

```sh
dotnet build Source/DafnyTestGeneration --no-restore --no-dependencies -m:1 /nr:false -p:AppendTargetFrameworkToOutputPath=false -p:UseCommonOutputDirectory=true -p:CompileUsingReferenceAssemblies=false
```

Require actual exit0and a new regular Binaries/DafnyTestGeneration.dll, bind its
hash and the exact unchanged three references/source/assets/configuration after
compilation, and record generated outputs separately from input sources.
Processor output context is bounded512MiB/8192leaves/depth24, with at most1MiB
per metadata/source leaf except explicit assets/logs/DLLs; exact DLL limit8MiB.
Each structured terminal receipt is separately bounded12MiB, including its
already bounded process streams and input/output inventories. No library/image
fallback or extension of time/output limits without a plan
update and new reviewed unspent phase. Development checks fake all these paths.

## Processor preparation record

The first two inert script drafts were held for fresh independent pre-operation
review. `prepare_build.py` was81756bytes/SHA256
101d5f9f44733f5956ba4be52d4595d13075755a67d959a9ad7b1a83bc72d060;
`check_build.py` is22387bytes/SHA256
4ff570d4cf8d8395c17f7498a46b94a62da6ca23a21f3ab5e4808ffceee18546.
Their exported strict Pydantic schemas are SourceManifest6210bytes/SHA256
cbda175d6a4f032700351ea4a76a1dc707bb0a78a91654a87ffa0ad580b01c95
and BuildRecord7555bytes/SHA256
fd8d0383a42cae681fe96ca818cb9bc2a3694624a137ddc2e2b510b2f0789297.
The package map has75records and identity
f00106e2f93bb67f154ddbc20df6e0542580ac365992e72b828d9f28a5deea79.

From W, `PYTHONDONTWRITEBYTECODE=1 python3 -B check_build.py` passes all13
memory-only controls with zero declared filesystem/process operations. AST
parsing passes2/2; `ruff format --check --no-force-exclude prepare_build.py
check_build.py` and `ruff check --no-force-exclude prepare_build.py
check_build.py` pass. Static scans find no dynamic import, temporary-directory,
process or directory operation in the checker. These checks do not establish a
source checkout, restore, metadata result or build result. W contains only the
two scripts: no claim, terminal receipt, native tree, config, log, DLL or other
generated output exists. No durable wiki finding exists yet because this is an
unaccepted operation contract rather than an observed build result.

Fresh draft review rejected these script identities before any gate or operation.
`git ls-tree -l` right-aligns blob sizes, so parsing must tolerate whitespace
padding while retaining exact four-field mode/type/object/decimal validation.
Prior terminal admission must parse typed completed receipts and require their
gate/source/contract/script identities to equal the current authenticated gate.
Each process phase must authenticate its complete relevant input closure before
execution and again afterward: the b4 TestGeneration non-overlay leaves, four
projects and Directory.Build files; offline config/assets; package libraries,
paths and target/reference paths; imported build files; three inherited DLLs;
and generated metadata/output identities. Metadata must require reviewed,
nonempty exact compile/resource closures, exact output/intermediate directories,
symlink-free ancestors, exact installed SDK roots, and empty pre/post-build event
properties in addition to the reviewed project/SDK Exec hooks. Process cleanup
must kill the whole process group whenever descendants keep pipes open, even if
the direct child has exited, and setup failures must enter the same cleanup path.

The correction stays within the same two scripts. Internal immutable snapshots
will represent the exact source/config/project/asset and evaluated metadata
closures; injected reader/kind/writer/process boundaries will let the memory
checker exercise current-gate authentication, exclusive claim/terminal failure,
copy validation and process-group cleanup without filesystem, process, directory
or synchronization operations. Record new script/schema identities only after
these controls settle and receive another fresh review. The old draft hashes
above are historical rejected inputs and grant no operation authority.

The corrected closure design derives every TestGeneration source leaf from the
pinned Git inventory plus the approved overlays, records exact compile items and
all five direct Library resources with their logical names, and pins the four
projects, `Source/Directory.Build.props`, `global.json`, and absence of ancestor
or user extension imports. It records the exact75package and three project
libraries from assets, safe library/target paths, eight generated NuGet
props/targets leaves,75cache hash leaves, and the selected System.Reactive
target/reference. Only the TestGeneration metadata query requests Compile,
EmbeddedResource, ProjectReference and Content; the three dependency queries
request direct ProjectReference only. Their dependency XML remains pinned, but
the absent Pipeline Java JAR resource is lexical metadata and is never opened,
copied or built. Output directories are fixed at `Binaries/`, intermediate
directories at each project's `obj/Debug/`, and project extension directories
at each project's `obj/`; Runtime alone selects `netstandard2.0`.

One separately authorized bounded inspection read only the existing public old
TestGeneration `project.assets.json`:144408bytes,78libraries and one target. It
found the first corrected projection was62209bytes/SHA256
2c49add59da173a025bbb2b368d0853f5f45c2ce5cd7e6c2ad654aa5ac3420f9,
not the previously derived38826byte/a86da770... canonical projection, because
the script inserted absent item groups as empty arrays. The implementation now
projects only groups present in each target record. A second explicitly
authorized read of the same144408byte leaf confirmed that complete corrected
projection as52200bytes/SHA256
6c93c4439c6f1d15a94537ef0295c773d88388a41862825c003c9752f39a8041:
78library records retain type/path and package sha512 or project MSBuild path;
78target records retain type, sorted dependency version maps, framework, and the
sorted paths for each actually present compile/runtime/resource/build group.
This complete safe projection supersedes the smaller a86da770... projection.
Across both reads the aggregate was288816bytes, below1MiB. No restore,
SDK/package-tree read, Git operation or native build was part of either
inspection.

## Corrected held processor record

The corrected preparation-only leaves are now held for fresh independent exact
input review. `prepare_build.py` is114191bytes/SHA256
ac24e62b3de1977b4538c963ef7c1940f42ac357b8ef123062fd7ac32b85fd4e;
`check_build.py` is37349bytes/SHA256
9d1d8ee1dd52502b4e69f1d95c1bc5356061ef9c32ea9ee88e5c38ca43b0cf61.
Their strict Pydantic schemas are SourceManifest7810bytes/SHA256
435e22a4acca8a8ff8a6e00066191562e6ce8ae718f3ec2e4ae157891528dc22,
BuildRecord10733bytes/SHA256
0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664,
and ActualBuildReview3286bytes/SHA256
92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402.
The producer remains below the consumer's128KiB per-script input bound and
exports `ASSET_MAX_BYTES=524288`.

From W, `PYTHONDONTWRITEBYTECODE=1 python3 -B check_build.py` passes
all18 memory-only controls and declares zero filesystem and process operations.
Those cases cover strict gate and prior-receipt authentication, exclusive claim
and honest terminal failure writes, overlay copy routing, exited-leader process
group cleanup, source/assets/metadata contracts, output DTOs and command bounds.
`ruff format --check --no-force-exclude prepare_build.py check_build.py`,
`ruff check --no-force-exclude prepare_build.py check_build.py`, and AST parsing
of both scripts pass. A checker scan finds no dynamic import, temporary-directory,
subprocess, directory walk/create, open, lstat or exists operation. W contains
only the two scripts. These are owner-local preparation results; independent
review is pending and no preparation/source/restore/metadata/build claim has
been spent.

Fresh independent static review rejected those ac24e62b.../9d1d8ee1...
identities before running checks or issuing a gate. Runtime's netstandard2.0
evaluation has no System.Reactive import and an empty `UseWindowsRxVersion`, so
the metadata contract must require false only for TestGeneration, Pipeline and
Core and require empty for Runtime. Pre-restore validation must also establish
that the fixed empty feed is an empty nofollow directory, that fixed ancestor
and user import candidates are absent, and that the four project `obj/` trees
contain none of the generated NuGet/assets leaves before the sole restore.
`native.editorconfig` is a real Roslyn input and belongs in the exact source
configuration closure. The memory claim test must inject its clock rather than
read the real clock. These remain changes to the same two scripts; the rejected
hashes grant no operation authority, and final checks wait for the remainder of
the same static review.

The same reviewer completed its static trace and found six remaining concrete
issues before checks or a gate. Restore admission must compare the strict source
terminal's manifest identity and native-input payload with the current manifest,
not only validate a replacement manifest's structure. The shared metadata
deadline must be recomputed after gate/input authentication immediately before
each process and enforce a final30second total. Metadata JSON must type all
required queried properties so missing keys become controlled validation errors.
The fixed System.Configuration.ConfigurationManager content hash has one copied
character omission and must be replaced from the actual public assets record.
The semantic asset projection must retain target framework and complete
per-path metadata, including aliases, locale, asset type and RID, rather than
only path names. Fixed import absence must be checked immediately before every
restore/metadata/build process. Memory checks must cover fake process setup
failure, the descendant-pipe timeout path, and full claimed success/failure
terminal sequencing in addition to the existing prior-gate mismatch.

ROOT authorized one final bounded read of the same public144408byte assets leaf,
keeping the three-read aggregate below1MiB, to compare all75 content hashes and
compute the complete semantic projection digest after those changes. It permits
no other input read, restore, SDK/cache traversal, Git command, source operation
or build. The read will occur only after the projection is corrected; its exact
observations will supersede the prior incomplete semantic projection record.

The authorized final read observed144408bytes and exactly75package records. It
found one mismatch: the System.Configuration.ConfigurationManager/6.0.0 sha512
literal omitted `6t` after `...MIu6m`; the processor now uses the complete
actual record `7T+m0kDSlIPTHIkPMIu6m6tV6qsMqJpvQWW2jIc2qi7sn40qxFo0q+7mEQAhMPXZHMKnWrnv47ntGlM/ejvw3g==`.
The complete semantic projection, retaining target framework, dependency
versions and every per-path metadata object, is58868bytes/SHA256
9eff65ca16bd92cbcfce7399d0d3909d7c6e05813346cdbae37fd5bb73f712fc.
The three explicit reads total433224bytes, below the1MiB aggregate bound. This
digest supersedes both earlier projections; no further old assets read is
authorized or needed.

The reviewer also found that a metadata query can complete and be observed,
then fail JSON/property/import/source validation while the generic failed
terminal records only the ValueError text. The corrected failure contract must
carry every already bounded query command, exit, stdout and stderr into the
failed metadata terminal, including a success followed by malformed metadata or
a post-check failure. A fake full claimed sequence will require one claim, one
failed terminal containing that observation and no retry or second process.

## Final corrected held processor record

After the complete static-review batch, `prepare_build.py` is121219bytes/SHA256
0f51d8c70cd25b3e6a0027b053355332845fc5f410ae1b2fe151bb5a0ddc6ae1 and
`check_build.py` is47510bytes/SHA256
eeab25e44fcb3c7b26e4ae2b8ee10ed18bccd5d79210a59216804c934c2402cc.
The strict schemas remain SourceManifest7810bytes/435e22a4..., BuildRecord
10733bytes/0b63eb6e..., and ActualBuildReview3286bytes/92aa5b9a.... The earlier
ac24e62b.../9d1d8ee1... identities are rejected review history, not operation
inputs.

The one relevant final cycle passes21/21 memory-only controls with zero declared
filesystem and process operations. It additionally covers source-terminal/raw-
manifest binding, the fixed pre-restore environment, mandatory metadata
properties, framework/path-metadata-sensitive assets, fake selector setup
failure, descendant-held-pipe timeout reaping, and a full claimed malformed-
metadata failure whose terminal preserves the observed query without retry.
Ruff format/check, AST parsing and the checker's forbidden-I/O scan pass. W
contains only the two scripts. These results are owner-local preparation checks;
fresh independent review of the new identities is pending, and no actual claim,
source operation, restore, metadata process or build is authorized by them.
The corrected75-record package-map identity is SHA256
feb7f2c81e107d1014ad0d6d8c16ae9fcaad2d611a077e7eb833c01171f2dd69.

ROOT found one checkout blocker before final review of those identities. Literal
b4 `.gitattributes` applies CRLF working-tree conversion to project/config
files: the TestGeneration csproj blob is1127bytes with28LF/0CRLF and Pipeline
is6846bytes with131LF/0CRLF, while ordinary `checkout-index` produces CRLF.
Comparing working-tree bytes directly to Git blob sizes and object IDs therefore
rejects a legitimate clean checkout. The corrected source phase will run one
bounded standard Git check after checkout and before overlays:

```sh
git -C /workspace/tmp/pbt-unfinished-workspace-build-20261021/native \
  diff --exit-code --no-ext-diff --no-textconv HEAD --
```

It uses the same fixed environment, disabled global/system configuration and
replacement-object protection as every other Git command. Exit0 authenticates
the canonical tracked state with b4 attributes; any content change fails. A
separate bounded nofollow pass still reads every regular working-tree leaf,
checks executable/symlink shape, accounts actual post-conversion byte totals and
hashes the complete actual path/size/SHA256 projection. The source manifest's
exact build-input identities remain actual working-tree bytes after overlays.
This adds one fixed source command and aggregate raw checkout identity fields,
not an attributes parser or per-leaf Git processes. Memory controls will cover a
clean CRLF checkout, a failed canonical diff for changed content and a bound LF
Library resource. The 0f51d8c7.../eeab25e4... scripts are rejected pre-gate
history; no source phase has run.

## Checkout-corrected held processor record

The correction adds the fixed canonical diff as the last source-contract
command and executes it immediately after `checkout-index`, before any overlay.
`BaseInventory` retains the canonical Git tree count/bytes/depth/identity and
adds `rawBytes`, `rawMaxBytes` and `rawIdentitySha256`, where the last field
hashes the complete sorted path-to-size/SHA256 projection for regular checkout
leaves. Production reads remain bounded nofollow reads; symlinks are checked by
mode and never opened. Exact native inputs after the overlays remain separately
bound by `SourceManifest.nativeInputs`.

The held corrected `prepare_build.py` is122235bytes/SHA256
ab8159091569d448aa80ddd7043147a5402daaf25fa2ab9ca1bc481e7f83a30d and
`check_build.py` is50186bytes/SHA256
bd7baecba6b17d538744a47ce1ba19bf4ac353d17d7db050b6e2d92884b459a8.
The SourceManifest schema is8271bytes/SHA256
cac625209c96a3b7e0e899655a6fbc7b9428764602321f9141292cd7c4d14fd7;
BuildRecord remains10733bytes/SHA256
0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664 and
ActualBuildReview remains3286bytes/SHA256
92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402.
The 0f51d8c7.../eeab25e4... pair and every earlier pair remain rejected
pre-gate history.

The one owner-local affected cycle passes22/22 memory-only controls with zero
declared filesystem/process operations. The new control supplies a CRLF project
leaf and LF PbtRuntime.dfy leaf, accepts an injected successful canonical diff,
binds both actual byte identities, and rejects an injected dirty diff before any
leaf read. Ruff format/check, AST parsing, the forbidden-I/O scan and the W
two-file inventory pass. No Git process, checkout, source/DLL copy, restore,
metadata query or build ran. Fresh independent review of these exact identities
is still required before any source operation.

The final static batch found two additional blockers before a preparation gate.
First, the assets projection substitutes an expected target framework for the
observed target `framework` details and omits project/restore framework and path
groups, so meaningful SDK-consumed metadata can change without changing the
semantic digest. It also permits absent/empty `configFilePaths`. The correction
will preserve every actual target path-metadata object plus the complete
normalized project frameworks and restore frameworks; it will separately
require the exact project/packages/output paths, original TFMs and the sole
nonempty new NuGet.Config path. It will not synthesize observed framework data.
ROOT authorized one fourth bounded read of the same immutable public
`Source/DafnyTestGeneration/obj/project.assets.json`, at most512KiB, to derive
the exact complete projection. The known leaf is144408bytes; four reads will
total577632bytes, below the existing1MiB aggregate authorization. No other old
input or actual phase may be read or run.

That fourth read observed144408bytes/SHA256
6b76ae908e77efa2e0a601cf3116b4006f279fd18739767bb4d94769c04247c3,
bringing the four-read total to577632bytes. It confirmed a single `net8.0`
project framework with `Microsoft.NETCore.App` framework reference and the fixed
SDK runtime-identifier graph; restore has the TestGeneration project path,
global package path, project obj output path, original `net8.0`, and a Pipeline
project reference. The target detail `framework` values are
`.NETCoreApp,Version=v8.0` for Core/Pipeline and
`.NETStandard,Version=v2.0` for Runtime. The authorized process printed this
complete relevant shape but mistakenly omitted the final new projection digest;
its in-memory raw is gone. No fifth read is authorized at this point. ROOT was
asked either to supply the independent reviewer's equivalent digest/schema or
explicitly authorize one final digest-only read of the same leaf; do not guess
or retain9eff... as the corrected digest.

ROOT subsequently authorized up to three additional reads of that same public
assets leaf, each at most512KiB, with all owner reads capped at1MiB. At144408
bytes per observation, at most seven total reads consume1010856bytes. Use one
additional process after the final projection code is written to print only its
digest, encoded size and mismatch summary; reserve the remaining two reads only
for a concrete shape error. This amended input-read budget does not authorize
any other SDK/cache/tree input or source/restore/metadata/build phase.

The fifth read used the final implemented projection code against that same
parsed immutable input. It again observed144408bytes/SHA256 6b76ae90... and
produced a59845byte canonical projection with SHA256
5edb322fb230ed99f9738c6efc8b567b3d54c7d5ded7ec5ae7df2da160b580be.
The projection retains every target detail including the three observed
`framework` values, complete path-group metadata, project framework references
and runtime graph, plus normalized restore framework/path metadata. Five reads
total722040bytes, below1MiB; the two remaining authorized reads were not used.
Exact current project/packages/obj/config paths and original/current TFM sets are
validated separately because the old input intentionally names its old source
root and user NuGet config.

Second, failed terminals duplicate a PhaseFailure process in both `process` and
`processes`, and raw JSON escaping can expand an otherwise bounded child stream
beyond the12MiB terminal cap. A claimed phase can consequently fail while its
failed terminal also fails to serialize/write. The correction will emit each
observation once and keep full observations only when their encoded terminal is
within the existing cap. If controlled failure or completed-result
serialization would overflow, it will write one compact failed terminal under
the same cap containing the original bounded payload size/SHA256, observed
process command/state/exit/elapsed/stream byte identities and an explicit
truncation marker, without retry or a second artifact. Successful terminals
remain strict existing DTOs. Memory controls will cover a6MiB ASCII failed
process, escaping expansion, and completed-result serialization failure, each
with one claim and one failed terminal.

Fresh review rejected that held pair before an operation gate because only the
restore preflight bound current source-manifest raw bytes and native inputs to
the completed source terminal. Metadata/build preflights authenticated a typed
completed source receipt and compared the restore terminal's native inputs to
the current manifest, but a replacement manifest plus matching restore snapshot
could bypass the original source-terminal snapshot. The correction will factor
one shared completed-source-state validator: load and structurally validate the
current manifest, validate its declared source/product/reference/configuration
leaves, read the completed source terminal, and require its manifest byte
identity and native inputs to equal that same loaded manifest. Restore before
and after its process and every restored-state metadata/build preflight will use
this validator. The pre-restore-only absence check remains solely in the restore
preflight, so post-restore generated assets are not incorrectly rejected.

A memory-only regression will supply an altered valid manifest and a restore
record whose native inputs match that altered manifest while retaining the
original completed source record. The exact shared preflight used by metadata
and build must reject the replacement against the source-terminal manifest
bytes/native inputs. This adds no DTO field and performs no real filesystem,
process, Git, SDK or synchronization operation. The ab815909.../bd7baecb... pair
is rejected pre-gate history; the final check cycle waits for the reviewer's
remaining static findings.

## Final corrected held processor record

`load_completed_source_manifest` now binds one current manifest's exact raw
identity and native inputs to the completed source terminal. The shared
`validate_completed_source_state` then validates that same manifest's declared
leaves. Restore preflight, post-restore validation and restored-state validation
all call it; metadata and build therefore call it before every process through
their existing preflight paths. The restore record's matching native-input map
cannot replace the source terminal's earlier snapshot.

The assets model requires nonempty configuration and explicit project/restore
framework/path groups. The complete semantic projection preserves actual target
details rather than writing the outer TFM into a target's `framework` field.
Current restore project/package/output/config paths and net8.0 sets are required
separately. The pinned projection is59845bytes/SHA256
5edb322fb230ed99f9738c6efc8b567b3d54c7d5ded7ec5ae7df2da160b580be.

Failed terminals record each process observation once. A full failed receipt is
kept when it fits; an escaping-expanded receipt is compacted to original receipt
size/hash plus command/state/exit/elapsed and stdout/stderr identities. Completed
encoding, size or strict-validation failures are converted by `run_claimed` to
one failed terminal after the one claim, with explicit receipt identity when
encoding succeeded and explicit unavailable identity when encoding itself
failed. No action or process is retried, and successful DTOs are unchanged.

The final held `prepare_build.py` is128498bytes/SHA256
807e55c97a350c3de4765567c64a498b4481b35082566c8fbb0d9cf3bc20e0e3 and
`check_build.py` is58784bytes/SHA256
25c1d253a306c3b11f97492f228a7a91f63bc4376f39cbcdec11278f5d5cf3be.
The script remains below128KiB. External successful-receipt schemas are
unchanged: SourceManifest8271bytes/cac625209c96a3b7e0e899655a6fbc7b9428764602321f9141292cd7c4d14fd7,
BuildRecord10733bytes/0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664,
and ActualBuildReview3286bytes/92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402.
Every earlier script pair, including ab815909.../bd7baecb..., is rejected
pre-gate history.

The single settled owner-local cycle passes23/23 memory-only controls with zero
declared filesystem/process operations. New cases reject an altered manifest
even when a restore terminal matches its native inputs; bind actual target
framework and project/restore metadata; require a nonempty fixed config path;
and cover6MiB failure evidence, JSON escaping overflow, and completed terminal
encoding/size failures with one claim/terminal and no retry. Ruff format/check,
AST parsing, forbidden checker-I/O scan and exact two-file W inventory pass. No
Git, source/DLL copy, restore, metadata or build operation ran. Fresh Astra
review of these exact final identities remains required.

Fresh independent review confirmed the complete assets projection, all75
packages, three project libraries and13 targeted metadata mutations, then found
one remaining exact-path omission before a gate: restore `projectUniqueName` is
an SDK-consumed absolute TestGeneration csproj identity but was allowed as
untyped extra metadata and omitted from the strict current-path checks. The
minimal correction makes it a mandatory typed restore field and requires it to
equal both the current TestGeneration project path and restore `projectPath`.
The semantic projection digest need not change because the strict environment-
specific path check already covers this intentionally relocated value. Add one
memory-only invalid-unique-name case; successful receipt DTO schemas remain
unchanged. The 807e55c9.../25c1d253... pair is rejected pre-gate history. No
additional assets read or actual operation is authorized or needed.

The exact-path correction is now held. `prepare_build.py` is128786bytes/SHA256
a423624535fae73965ab4c764ea7913c34510ff9c3a97a4c1789ae318bc6bb9e and
`check_build.py` is59281bytes/SHA256
809cdae558150471bc0bb8f0c614b00114a69da13107bf5d40ab4cbac6d39e9c.
The23 memory-only controls, Ruff format/check and AST parsing pass; the new fake
`/unreviewed/project.csproj` unique name is rejected. Successful receipt schemas
and the5edb322f... assets projection are unchanged. The 807e55c9.../25c1d253...
pair is rejected pre-gate history. No additional input read or actual operation
occurred, and fresh independent review of these exact identities remains
required.

## First actual attempt and replacement scope — 2026-10-22

The registered first source command was executed once at2026-10-21
15:27:20.510987UTC. Its unified execution handle23662 terminated with exit1.
The readonly792-byte source-claim.json has SHA256
8b3517dc5709d89814736e1d2b786436717babd3fd0621ef493a0647b96ad86f.
The readonly1007-byte preparation.json is state=failed/phase=source, finished
15:27:22.821074UTC, SHA256
1abaa4adb118b9ac69f1414823aba98e13aeb4251a908487a6186d83f1d954c8.
Its error is FileExistsError on native/Binaries. The pinned base already has
Binaries/.gitignore, but seed_references incorrectly creates Binaries as absent.
ROOT inspected the existing directory and .gitignore only, no seed DLL or source
manifest. No later phase claim exists: restore/metadata/build/native/PBT/provider
counts are zero. The source claim is spent permanently; do not rerun its command,
overwrite terminal evidence, finish it in place or execute later W1 phases.

Failure evidence also omits previously observed Git subprocess records when the
action raises FileExistsError rather than PhaseFailure. The replacement must
preserve those bounded observations on this actual external failure path as well
as the already covered metadata failures, without duplicating streams or
changing terminal limits. Do not infer a completed subprocess population from
the empty old failure projection.

W2=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r02 is now authorized
for TWO-SCRIPT PREPARATION ONLY. Preserve every W1 file. Copy the reviewed W1
scripts, change only their exact workspace/run identity and the known directory/
observation defects. Reuse the existing directory only if it is a nofollow
regular directory in the clean checkout; require each of the three destination
DLL paths absent and retain exclusive writes/hash verification. Reject symlink,
non-directory and occupied reference destinations. Do not introduce a stale-DLL
fallback. Existing source/asset/metadata/proof checks and limits stay intact.
Record the exact reviewed diff, new script/contract identities and a distinct
fresh W2 gate before materialization. Do not copy old gates, claims, logs, DLL
outputs, obj or native tree; the new source context must be constructed normally.

The existing root public-control capsule has never frozen or run. Its owner may
update the W2 producer path/runId binding under its own plan before its eventual
input review; preserve prior source-only check scope rather than claiming the
old producer gate authorizes the new namespace. No image/paid/shared-tag change
is authorized here. The independent W1 actual-build-review artifacts may record
only actual source-preparation failure accounting, accepted=false and explicit
failure scope; they must not masquerade as an accepted successful build review.

## W2 replacement scripts held

ROOT independently authenticated the W1 failure-accounting reports at
2026-10-21 15:38UTC: verification/actual-build-review.json is7043bytes/mode0444,
SHA2566b99586ea35db97f77864acd412832d0dc4c2203b3524cf9898c2ce52e53c3cc;
the3585-byte/mode0444 Markdown report is
d8e850b0649491e89460135c70559dac7c3ffdf425bde932bd5ac498b93e75f2.
They are accepted=false with scope actual_source_preparation_failure_only,
explicitly fail the successful ActualBuildReview contract, preserve unknown
prior Git completion population and establish no restore/build/native result.
They do not authorize reuse of any W1 claim or gate.

The W2 scripts were copied from the exact accepted W1 pair; no W1 gate, claim,
native tree, obj output, DLL, log or manifest was copied. Only W/RUN_ID changed
to `/workspace/tmp/pbt-unfinished-workspace-build-20261022-r02` /
`pbt-unfinished-workspace-build-20261022-r02`, together with the two authorized
defect corrections.

Reference seeding now requires the tracked `Binaries` leaf to be a nofollow real
directory, preflights all three DLL destinations as absent before reading or
writing any reference, authenticates each immutable R03 source through the
existing bounded hash-checking loader, and retains exclusive destination writes.
Symlink/non-directory roots and any occupied DLL destination reject before a
partial copy. A source-local observer records only returned bounded
`ProcessResult` values. Controlled OSError/ValueError failures retain every
prior observation, merge the current PhaseFailure observation once, and render
the original cause type/message through the existing deduplicated/compacting
failed-terminal path. `gated_process`, `run_claimed`, terminal bounds and
successful external DTOs are unchanged; programming errors are not caught.

The held W2 `prepare_build.py` is131064bytes/SHA256
23ea151f29ceed0699b48aa0e5b62d8ed1860f1038f123f4d666b0be748f5bad and
`check_build.py` is63800bytes/SHA256
4b1e64bcaabdafa6c67dd42729c00ca55080fb21a572a11feeaa7fb8f169bd55.
The producer remains8bytes below128KiB. W1-to-W2 unified diffs are
8822bytes/SHA256 46e8fa2681d475c8609177ed412f963aaa4243b5dbc4fa078c76fd6037cc1875
and5183bytes/SHA256 064be34d6d13acb85e7688b4f46d46ec461098a99e64b6047033bbc2cae9de46,
respectively. The exact W2 contract JSON is12280bytes/SHA256
f5348c86bd5999f4f819fb64f93270df0a865d7b2a33f223ae3a5df537606a3a.
SourceManifest/BuildRecord/ActualBuildReview schemas remain8271bytes/cac62520...,
10733bytes/0b63eb6e..., and3286bytes/92aa5b9a....

The owner-local cycle passes27/27 memory-only controls with zero declared
filesystem/process operations. New cases cover the existing real directory,
symlink/non-directory roots, occupied destinations before any copy, and a
completed fake Git observation followed by FileExistsError producing one failed
terminal with the original process evidence and no retry. Ruff format/check and
AST parsing pass; W2 contains exactly the two regular0644 scripts. No W2 Git,
source/DLL preparation, restore, metadata, build, native PBT, provider or Docker
operation ran. A fresh exact W2 review/gate remains mandatory.

## Accepted W2 gate and exact one-shot commands

ROOT independently read, rehashed and strictly authenticated the new readonly
W2 preparation gate before any actual phase. JSON787bytes/mode0444/SHA256
8ac8c889b140bcb630e3afaba76ee1235989eca41de3a16e366649f630638e6a and
Markdown10278bytes/mode0444/SHA256
bebc2b7e39b31753716b9f9a0bafafa71d88e75e196715371c38ef787c835ef8
bind the held23ea151f.../4b1e64bc... scripts, exactf5348c86... contract and
source acceptancea8c4fbf5.... Fresh independent source/fake review found no
blocking finding, including actual source-path failure observation controls.
ROOT's ordinary authenticate call accepted the exact external digests and
current source/record/script identities. At that check W2 still had only its
two scripts and verification directory; no actual phase claim existed.

The gate authorizes exactly these four serial commands, each maximum once,
cwd=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r02. Inspect each
actual closed terminal and retain its execution handle before advancing. Any
failure stops the remaining phases and spends that attempt; no retry or W1 reuse.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py source --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 8ac8c889b140bcb630e3afaba76ee1235989eca41de3a16e366649f630638e6a
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py restore --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 8ac8c889b140bcb630e3afaba76ee1235989eca41de3a16e366649f630638e6a
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py metadata --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 8ac8c889b140bcb630e3afaba76ee1235989eca41de3a16e366649f630638e6a
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py build --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 8ac8c889b140bcb630e3afaba76ee1235989eca41de3a16e366649f630638e6a
```

No Docker, native PBT, provider, paid, tag or commit operation is included.
Actual source/restore/metadata/build outcomes and separate independent final
accounting remain required; this source/fake acceptance is not actual success.

### Actual W2 phase observations

Source command handle41246 was polled through terminal exit0. Its strict
CompletedSourceRecord is completed,2026-10-21T15:45:34.289903+00:00 through
15:45:37.007129+00:00. ROOT authenticated its original gate and manifest/result
binding before advancing. The new checkout accounts6531canonical leaves,
29,226,166blob bytes and29,227,724actual regular bytes; thirteen reviewed
products, all three exact inherited references and64native-input leaves bind.
The two unrelated tracked symlinks remain names only; their targets were not read.

| Actual source artifact | Bytes/mode | SHA256 |
| --- | --- | --- |
| source-claim.json |796/0444|7d2d6dfeded6e036bc3269e29a49a6dd121490c0d51db908bf33c8c1fd143cb7|
| preparation.json |22042/0444|0ed7d02b03fa38a3dcd43fa2282376ddf51cf359bf73cf891fcd904b7a395f89|
| source-manifest.json |22850/0444|b0fb7c32cd70f25f704b2ecc93827923035e575df1819a5d3a76912253ec63f4|

Restore was then launched exactly as recorded, handle80467, and polled through
terminal exit1. Its failed terminal spans15:46:06.136754–15:46:08.559081UTC and
records FileNotFoundError on the selected NuGet build/_._ pseudo-asset. This
stops all remaining W2 phases. Source success does not make this failed restore
successful; preserve its spent claim and do not retry or complete W2 in place.

| Actual restore artifact | Bytes/mode | SHA256 |
| --- | --- | --- |
| restore-claim.json |797/0444|aa3e34a1e7028a651149e62c4761d60adcf23a02597df2657659c9f1c872c037|
| restore.json |1046/0444|94c7eff1ffcaad245f9d82ae66d21c2cd0f95a2d368b496219b2946ace507d62|
| restore.log |584/0444|d2cd35ec273a65fc6b2a83f608289e33e1035635501393bcd543339e451ae9cc|

The log reports four restored projects and empty stderr, but the failed terminal
does not retain a subprocess state/returncode. Those observations remain unknown;
do not present a source-order inference as a persisted actual result. ROOT read
these exact artifacts; an independent failure-accounting reviewer is inspecting
the bounded original records without running another phase. Metadata/build
claims are absent and no new TestGeneration DLL exists.

### Ready W3 correction after the actual restore failure

Independent W2 failure accounting is now complete. ROOT read and rehashed its
two readonly0444 reports at15:54UTC: JSON15174bytes/SHA256
4c89f44993409847bc303a7c28c69cba8152142c042c1ff154a15f1d02ded42e and
Markdown11569bytes/SHA256 e4cb6d4d3975a30412a5d6bd6b855f3e5f421f4444ea8d11cca8603af4281a87.
The strict closed failure schema is accepted=false with scope
actual_offline_restore_failure_only and is rejected by successful ActualBuildReview.
It confirms record-only source binding, spent failed restore, the exact selected
asset mapping and fake reproduction; actual .NET state/returncode/census remain
unknown. It rechecks no complete source/cache tree and grants no later phase.

ROOT's single bounded144562-byte W2 assets read authenticated SHA256
50209c4d4cc7fc0b571b5a29dcc35a294e07624f59b6e9544afa887abccbb898 and
the unchanged complete semantic5edb322fb230ed99f9738c6efc8b567b3d54c7d5ded7ec5ae7df2da160b580be.
It selects eight empty build assets, all in target net8.0/group build/metadata{}:

| Package/version | Exact empty selected path |
| --- | --- |
| Microsoft.VisualStudio.Threading.Analyzers/16.7.56 |build/_._|
| Microsoft.Win32.SystemEvents/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Configuration.ConfigurationManager/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Drawing.Common/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Runtime.Caching/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Security.AccessControl/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Security.Cryptography.ProtectedData/6.0.0 |buildTransitive/netcoreapp3.1/_._|
| System.Security.Permissions/6.0.0 |buildTransitive/netcoreapp3.1/_._|

These exact bound selections must remain in raw assets and semantic identity,
but are not physical MSBuild imports. The native package validator incorrectly
read them as XML before reaching the real selected System.Reactive target.
Microsoft's [NuGet import documentation](https://learn.microsoft.com/en-us/nuget/concepts/msbuild-props-and-targets)
and [BuildAssetsUtils source](https://source.dot.net/NuGet.Commands/RestoreCommand/Utility/BuildAssetsUtils.cs.html)
identify .props/.targets imports; _._ is an empty selection. Do not create that
file, read a different unselected analyzer target or bypass meaningful imports.

W3 is ready for TWO-SCRIPT PREPARATION ONLY. Set this plan in-progress before
creating W3. Copy only the exact W2 accepted script pair, change its literal
workspace/runId to W3/ pbt-unfinished-workspace-build-20261022-r03 and add exact
empty-selection validation for these eight tuples. Validate safe relative names
and empty metadata; reject other/malformed _._ selections. Every real import's
physical bounded read, XML/Exec check and exact Reactive target/reference remain.
Preserve ordinary proof, thirteen products, three inherited references, full
asset/source/configuration authentication, DTO schemas and existing limits.
Host producer script limit remains the existing1MiB; do not change any cap.

After the sole restore process returns, preserve its bounded observation if a
subsequent controlled OSError/ValueError occurs in log/assets/dependency/source
postchecks, using the existing ObservedPhaseFailure representation. Deduplicate
an existing PhaseFailure observation; keep the original cause and terminal
compaction. Pre-process failures invent no process; programming errors remain
uncaught. Use local injection/fakes without a global observer/signature redesign.
Trace all fake setup/execution/cleanup paths before running them. No actual
directories, compiler, source/cache trees, processes or synchronization in tests.

Do not copy W2 gates, claims, native/obj, DLLs, logs or records into W3. W1/W2
are immutable historical attempts; any new source context is constructed normally
after its own fresh independent exact-script/contract/source gate and recorded
argv. W2's source/fake acceptance cannot authorize W3. The never-frozen root C
capsule may rebind producer namespace under its own plan before fresh source/
fake compatibility review. No image/native/PBT/provider/paid/tag/commit action
is authorized by this preparation correction.

### Held W3 preparation scripts

Fresh independent review rejected the first submitted W3 identities before any
gate or operation. Seven empty-selection paths begin with `buildTransitive/`,
but their JSON item group is still `build`; the processor incorrectly recorded
their group as `buildTransitive`. The normal memory fixture also generated its
inputs from the production expected tuple set, so it reproduced rather than
detected that error. Retire the7a498d0d.../7c5f4e0b... pair. Correct all seven
group literals while retaining their exact path strings, make the normal fixture
encode the independently observed net8.0/`build` mapping, and add a wrong-group
adverse control. This remains the same two-script preparation scope; W3 has no
gate, claim or actual phase.

The corrected W3 contains only the two scripts. `prepare_build.py` is
133739bytes/SHA256
4c9460b5e9f2da1b624a1671bb4873ee2d9da28746eb80b1c34f8cc96e480b3f;
`check_build.py` is69738bytes/SHA256
746c3a6b5345cbfcaed7e1d37e897fa74660c1ac3d64a1806c402b3e79f46ae9.
Their unified diffs from the immutable W2 pair hash to
0f7c70c36f239d604d51354919fe07b3dd3a35d457d4604a39766ae582807180
and5f763fb026715bbd6dac221baa8775fd93107fcca9cee334d5c95074f3b2467f.
The scripts bind run `pbt-unfinished-workspace-build-20261022-r03`; their exact
build-contract projection is12280bytes/SHA256
402b4674675a6361c98f6491f7bc8274b5dec241efdbe2d47aca3e691308de15.

The successful external schemas remain byte-for-byte unchanged:
SourceManifest8271bytes/cac625209c96a3b7e0e899655a6fbc7b9428764602321f9141292cd7c4d14fd7,
BuildRecord10733bytes/0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664,
and ActualBuildReview3286bytes/92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402.
The fixed package closure, semantic-assets digest, DTOs and limits are unchanged.

The checker passes29memory-only controls and reports zero filesystem/process
operations. Its normal fixture independently encodes the observed `build` JSON
group for all eight empty selections and the real Reactive target while retaining
their `buildTransitive/...` path strings. New cases assert placeholders cause no
reader call, retain the real Reactive XML/Exec and requisite checks, reject a
wrong JSON group plus malformed or additional `_._` selections, and preserve one
returned restore observation in one failed terminal after a fake post-process
FileNotFoundError.
AST parsing, explicit uncached Ruff check and Ruff format check pass. A static
scan finds no dynamic import, temporary-directory, filesystem, subprocess or
sync operation in the checker. W3 has exactly the two regular0644 scripts; no
gate, claim, source context, restore, metadata, build, log or DLL exists. These
are owner-local preparation results and require fresh independent exact-input
review before any W3 phase.

## Risks and handoff

## Accepted W3 gate and exact one-shot commands

ROOT independently read/rehashed and strictly authenticated the corrected W3
readonly gate and review before any operation: JSON787bytes/SHA256
a4a79953317691ba20f3b1558247540825154f948ca66baed3d79292193e4304,
Markdown11722bytes/SHA256
6fbf0e83aa199f41edfc7d64a8d15e87a55300c24706e2fa72da46f3ac5ca2ba.
Both are mode0444, bind producer4c9460b5.../checker746c3a6b... and contract
402b4674675a6361c98f6491f7bc8274b5dec241efdbe2d47aca3e691308de15.
Fresh independent memory/input review has no blocking finding; its initial
rejected draft and temporary model-capacity interruption remain historical.
ROOT's normal authenticate call accepted the exact external source/gate digest
and current scripts/records. W3 then contained only scripts and verification.

Record exactly these four serial maximum-once commands before execution,
cwd=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r03. Inspect each
actual closed terminal and retain its execution handle before advancing. Any
failed phase spends this attempt and stops remaining phases; no in-place retry,
old gate/claim reuse, package/source/configuration fallback or bounds expansion.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py source --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 a4a79953317691ba20f3b1558247540825154f948ca66baed3d79292193e4304
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py restore --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 a4a79953317691ba20f3b1558247540825154f948ca66baed3d79292193e4304
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py metadata --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 a4a79953317691ba20f3b1558247540825154f948ca66baed3d79292193e4304
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py build --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 a4a79953317691ba20f3b1558247540825154f948ca66baed3d79292193e4304
```

No Docker/native PBT/provider/paid/tag/commit operation is included. Actual
results and fresh independent actual-build accounting remain required before C
can consume any new output; accepted preparation is not build or proof success.

### Actual W3 observations and stop

ROOT ran source once, handle43984, polled terminal exit0, then authenticated the
strict completed source/gate/manifest binding before restore. Source interval
2026-10-21T16:07:32.630954+00:00–16:07:35.008336+00:00 binds the same6531-leaf
canonical/raw checkout, thirteen products, three references and64native inputs.
Source claim796bytes/0444 isb2d0744a42e4b49a1a0fbbc148eb6fd98dbe448c540764a68bfaae3ada4204ef;
preparation22042bytes/0444 is0ae1a4637c9defe85fc01ba53f56a37a81e432c78b695305c975bebfb8d3ffe8;
source manifest22850bytes/0444 is310c206a5a37258588147eccb411c7c3f1a23daff209307e975979b1a2446ac2.

Restore handle96926 was polled through outer exit1. The closed failed record
spans16:08:03.584962–16:08:05.872567UTC and records ValueError: package cache
content hash differs for Boogie.AbstractInterpretation/3.5.5. The new observer
retains exactly one actual completed .NET restore process: exit0,2.135seconds,
exact planned argv, stdout and empty stderr. The processor still failed its
postcheck. Metadata/build claims are absent; do not run the remaining W3 commands
or retry/modify this namespace. No new TestGeneration output exists.

| Actual restore artifact | Bytes/mode | SHA256 |
| --- | --- | --- |
| restore-claim.json |797/0444|ab05ea4693b1d1d7f687a5f07bc56a8062439b9fecef4fad194e1c16f7ded767|
| restore.json |2226/0444|d38f8911704f38898bf05a2df83602b8392f25b517ef5706b16be557bec56f6f|
| restore.log |582/0444|cefa2b2fb3740f32792c2f3612b739d03b712a28f2f826ba5c2e1b21b7f6af74|

ROOT's bounded read of the88-byte legacy .nupkg.sha512 leaf authenticated
851cbe41bc62118d111c3f2e4a68c1c4f0100ef38b4c5b234e290ec26b5b64b5
and differs from the expected assets hash. The same package's178-byte
.nupkg.metadata iscf8fab780544a2f2bcbaaeea65e8b9147a5af842e8a288b0029f5b3fc7a10734:
version2/contentHash matches the unchanged expected assets hash exactly.
[NuGet's original design](https://github.com/NuGet/Home/wiki/Nupkg-Metadata-File)
and [current extractor source](https://github.com/NuGet/NuGet.Client/blob/dev/src/NuGet.Core/NuGet.Packaging/PackageExtractor.cs)
distinguish whole signed archive hashes from signature-independent contentHash.
This motivates read-only investigation; it is not permission to weaken checks,
rebaseline, change shared cache, download packages or claim build success.

The owner may inspect only the exact75declared .nupkg.metadata leaves once,
each<=4096bytes/aggregate<=307200bytes, plus the corresponding75legacy hash
leaves only if needed (each<=1024/aggregate<=76800). No recursive SDK/cache
listing, package ZIP/DLL or unknown-package read, process or write is authorized.
Compare actual metadata to every unchanged expected content hash and verify the
relevant primary-source semantics before proposing any next-namespace code or
scope change. Independent actual W3 failure-accounting reports may use only this
failed attempt's fixed evidence and must remain accepted=false/failure-only.

### Ready W4 correction for NuGet content hashes

ROOT read and rehashed the independent W3 failure reports at16:18UTC:
verification/actual-build-review.json8131bytes/mode0444/SHA256
d19fba32e815ff1aeeb89f8c6cb08d3cda16e23e31b173f77df03be9c54b251e;
Markdown6955bytes/mode0444/SHA256
de2ece3b9b975542c3c746a798df5972993fb5a3e521d87733576783c69a1a4e.
Their closed strict failure-only schema remains accepted=false, rejects successful
ActualBuildReview and authorizes no retry/later phase. Independent record binding
and exact log reconstruction confirm the retained completed exit0 restore
observation alongside the failed postcheck; they establish no build output.

The bounded owner investigation reports all75 exact declared metadata leaves
matched the unchanged reviewed EXPECTED_PACKAGES values:75regular leaves,
13350actual bytes, each version2 with contentHash/source/version and public
nuget.org source. This owner observation awaits fresh independent input review;
ROOT independently read the one Boogie metadata/legacy pair and official NuGet
design/extractor sources establishing the two hash domains. No new package
version/content identity or dependency is proposed.

W4 is ready for TWO-SCRIPT PREPARATION ONLY. Set the plan in-progress before
creation. Copy only W3's exact4c9460b5.../746c3a6b... scripts, replace literal
W/runId with W4/pbt-unfinished-workspace-build-20261022-r04, and correct
validate_cache_hashes. Read exactly the75declared .nupkg.metadata leaves with
the existing<=1024-byte cache-leaf bound. Parse them through a strict extra-
forbidden Pydantic metadata model; require version2, contentHash equal the SAME
reviewed expected asset hash and source exactly https://api.nuget.org/v3/index.json.
The source string records historical cache origin, never network/feed authority.
Keep every raw metadata leaf's bytes/SHA256 identity in existing cacheHashes map
and revalidate before/after every consumer. Successful external receipt schemas
stay unchanged. Do not compare signature-neutral contentHash to a legacy whole-
archive hash, rebaseline expected hashes, weaken validation, inspect/recompute
archives, change cache, use a fallback or add/download packages.

Full raw/semantic assets, eight exact empty selections, real imports/references,
generated NuGet leaves, thirteen products, three inherited references, SDK,
ordinary proof checks/fingerprints, source/configuration checks and all existing
time/output/read caps remain. The metadata model is the only new external JSON
model; no dependency package or parser library is added. The canonical75-package
content identities and complete semantic5edb322f... remain unchanged.

Audit the fake checker before running it. Add a realistic signed-package case
whose metadata content hash equals expected while legacy archive hash differs,
and reject wrong content, missing/extra fields, schema/version/source and missing
metadata. Assert the exact75 metadata routes and<=1024reads with no legacy reads;
fake every filesystem/process/directory/native/synchronization/setup/cleanup
boundary. No actual cache scan/build inside development tests. Then hold exact
scripts/contract/schema/diff identities for a fresh independent review/gate.
No W4 source/restore/metadata/build, new actual input copies, claim or gate is
authorized before that review and ROOT's recorded argv/external pin.

### Held W4 preparation scripts

W4 contains exactly the two regular0644 scripts. `prepare_build.py` is
134031bytes/SHA256
dbac1662928bc0d15665a2c607c9dfef30a6b814a715c75153fe4d460d5c5808;
`check_build.py` is73974bytes/SHA256
770762e72f69f0c7ed69ecdd852da03bcddd3eb075e912f84042948295fdbbe6.
Their unified diffs from immutable W3 hash to
16eb1f66c41bae3da22108cf3749e5c830c402fddd9b36a41986506ace21700b
and8e8fb315d743a8f7f3b047aaca5c91c6659ddf374949c5154e1ea52c13f5f1e7.
The exact W4 build-contract projection is12280bytes/SHA256
b5873448725ec0f2d2348dcd8d23400743716521d60417d76a3459dadf3049dc.

Successful external schemas remain unchanged: SourceManifest8271bytes/
cac625209c96a3b7e0e899655a6fbc7b9428764602321f9141292cd7c4d14fd7,
BuildRecord10733bytes/
0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664,
and ActualBuildReview3286bytes/
92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402.
The new strict inert NuGetPackageMetadata schema is491bytes/SHA256
2021bb0bb273a7a9e9fe38495b637f36ca58f559ff4a40932e96b0760280f8a2.
The existing cacheHashes receipt field now records raw metadata leaf identities;
its successful DTO shape and every reviewed content hash remain unchanged.

The checker passes34memory-only controls with zero declared filesystem/process
operations. New cases route exactly75 reads to `.nupkg.metadata` with limit1024,
read no legacy `.nupkg.sha512`, distinguish a signed whole-archive hash from its
matching contentHash, and reject wrong content, missing/extra/coerced/version/
source fields and a missing metadata leaf without fallback. AST parsing, Ruff
format and explicit isolated/no-cache Ruff check pass; the checker source has no
dynamic import, temporary-directory, filesystem, subprocess or sync operation.
No W4 gate, phase, native source, cache read, build output, image, PBT or provider
operation exists. Fresh independent exact-input review remains mandatory.

The never-frozen root C capsule may rebind producer namespace under its own plan
AFTER the ongoing independent C prerequisite-original review completes; do not
change C during that review. W1/W2/W3 remain immutable failed attempts. No image,
solver/native PBT, provider/paid, shared tag or commit action is included here.

## W4 actual outcome and ready W5 correction

ROOT observed source84809 exit0, restore87061 exit0 and metadata62026 exit1.
Source ran16:25:22.229675Z–16:25:24.596843Z; strict completed source/manifest
and current gate bindings passed before restore. Its readonly source claim is
796bytes/SHA2568b796c6a03d418620d1ce5b59c91ed422312bf7c7c36bacbb00ffef1a4529b0b;
preparation.json22042bytes/5c78bac61175763d28ae7a68814343b05b70f0e90a4d535f5a44a6792bc16980;
source-manifest.json22850bytes/0c39b4a696a86405dbab590ac2588e4f7a5dc6ead97ed996dd7f20143a1235d9.
The bound manifest records6531base leaves,13products,3references and64native inputs.

Restore ran16:25:47.406226Z–16:25:49.775738Z. Both its command and complete
dependency postcheck succeeded; the retained process is completed/exit0/2.126s.
ROOT strictly validated CompletedRestoreRecord and current prerequisites before
metadata. Its readonly claim is797bytes/9500bd18cffd8a1c6bdc7a854c1226d4d6d623bf5cdbf2b8eb607d2e0dce12c3;
restore.json38284bytes/eb2f59fa9104da0b8bf7a864101d65bb35d0f44711d9cb32c31818f25c4e67f6;
restore.log582bytes/1e9559fdcbd0738b0c2a6213bfb824a5c0b841f9b80b6e3f40d05d0692807458.

Metadata ran16:26:14.851482Z–16:26:15.533125Z and failed its validator with
`MSBuild user extension root differs`. Exactly the first TG evaluation query
completed/exit0/0.589s with empty stderr; the other three queries did not run.
Its readonly claim is798bytes/3d92621fbf4f027b1cad05c74fecd35adf4d0eb5a1f246231159157c5cbf9639;
metadata.json58043bytes/5663c13f52bf9931827df938a560460cb8465cef02adc8d0680fa639d379f512.
Build must not run in W4. No build claim or new DLL exists; preserve all three
spent phases and do not retry or complete W4 in place. Fresh independent
failure-only accounting is accepted=false/actual_metadata_failure_only. ROOT
read/rehashed readonly verification/actual-build-review.json10583bytes/SHA256
398d4132b5936753c9f76ecbd96dfe0d4f5792430ef84458c1d7f3e37fa6c41e
and Markdown8002bytes/SHA256
a85c71326a0d1d7e8606ec3fcd701754a23d4b58a321c8e45e331abb242f2b6f.
Both retain exact current gate/claim/receipt binding and reject successful build
acceptance, retry and consumption. The successful source receipt has no retained
child-process records, so its child census remains unknown. Exactly one restore
and one first metadata process are retained; planned source argv is not a census.

Read-only retained-response/SDK investigation identified raw MSBuild values
`/home/vscode/.local/share/Microsoft\MSBuild`, `obj\` and `obj\Debug/`.
The POSIX Path consumer currently treats backslashes literally. MSBuild's own
[FileUtilities](https://github.com/dotnet/msbuild/blob/v17.11.4/src/Shared/FileUtilities.cs#L493-L495)
converts backslashes to slashes on Linux; its
[NormalizePath documentation](https://learn.microsoft.com/en-us/visualstudio/msbuild/property-functions#msbuild-property-functions)
describes OS separator normalization. The installed fixed SDK output-path targets
also contain these backslash defaults. All other semantic TG property and item
inventories agree with the bound manifest on the retained response. Filesystem
postchecks and the remaining queries have not passed.

W5 is ready for TWO-SCRIPT PREPARATION ONLY. Copy the held W4 pair and change
literal namespace/runId. Add one pure `msbuild_path(str)->Path` conversion at
the known MSBuild metadata boundary, routing metadata_full_path, evaluated_path,
MSBuildUserExtensionsPath, path-valued validate_metadata_value properties and
MSBuildTools/SDK/MSBuildAllProjects through it. Preserve raw strings in receipts.
Do not alter generic normalized/within, source/Git/assets/package paths, exact
roots, containment, nofollow, missing-import checks, proof scope/options,
commands, source/product/reference identities, DTO shapes or any time/read cap.

Before running the checker, audit its entire fake call closure. Exercise a
complete literal TG response with the observed mixed paths, ordinary forward
slashes, wrong mixed user roots, `..\\escape` intermediate/output/import paths,
allowed and unexpected backslash imports, and literal source/assets paths.
All filesystem/process/SDK/package/directory/sync/default/deferred boundaries
must be memory fakes. Then obtain fresh independent exact-byte preparation
review. ROOT must pin that gate and record literal serial argv before any W5
source/restore/metadata/build. No extra actual query or W4 retry is authorized.

### Held W5 preparation scripts

W5 contains exactly the two regular0644 scripts and remains preparation-only.
`prepare_build.py` is134352bytes/SHA256
8cf58f9693aee059afa31dc44983480a2e78d2bdbe14b4edb1ff4566f84a012f;
`check_build.py` is77539bytes/SHA256
9bf048d9ca6e6b762aad3b45769ce7779f5a06491ba7363535d9cfc7f6505f8d.
The deterministic `difflib.unified_diff` projections from immutable W4, labelled
`r04/<name>` to `r05/<name>`, are5607bytes/SHA256
a2436c2a72da1d79230192546b325ea1ec84bdfb85e52fea1e9a1153da5e106a
for the producer and7642bytes/SHA256
0e31ad56b8a9b478cebc031b04e3378814902d2c6bf6b7bc204b5d5961bd9a42
for the checker. The exact W5 build-contract projection is12280bytes/SHA256
ec96f6c895246f3bf9bb0a1c99a5213e45a36b7f754bde74baefc1e7d046fb7e.

The producer adds only `msbuild_path`: fixed-Linux conversion of backslash to
slash at path-valued `MetadataOutput` consumers. Metadata item `FullPath`,
evaluated output/intermediate paths, the user-extension root, project/target/
SDK/configuration properties and `MSBuildAllProjects` now pass through it before
the existing exact-root, containment, nofollow and import checks. Raw receipt
properties remain unchanged. Generic `normalized`/`within` and Git, source,
assets, package, proof, product and reference contracts remain byte-for-byte W4.

Successful schemas remain unchanged: SourceManifest8271bytes/SHA256
cac625209c96a3b7e0e899655a6fbc7b9428764602321f9141292cd7c4d14fd7,
BuildRecord10733bytes/
0b63eb6e772fcde968af1d56110148358db48ce57478f5ba8a4f506b2eadc664,
ActualBuildReview3286bytes/
92aa5b9a1a89905f12b080bc5c83a3acd1b00acdc9f4d2b174016af5e1910402
and NuGetPackageMetadata491bytes/
2021bb0bb273a7a9e9fe38495b637f36ca58f559ff4a40932e96b0760280f8a2.

`PYTHONDONTWRITEBYTECODE=1 python3 -B check_build.py` passes34/34
memory-only controls and reports zero filesystem and process operations. The
literal TG fixture retains raw `obj\`, `obj\Debug/` and
`Microsoft\MSBuild`, while forward-slash compatibility passes. Mixed-separator
wrong roots, traversing output/import paths and unexpected imports reject;
nonmetadata source and NuGet asset backslashes remain invalid. Every touched
kind/read boundary is injected. Python AST parsing passes. Ruff0.15.12 format
check and lint pass with the repository's explicit Python3.12/100-column
configuration, isolated lint, `--no-cache`, no Git-ignore and no forced
exclusion.

The first Ruff format probes omitted `--no-cache` and created `.ruff_cache`.
ROOT's census caught it before the two-file hold. The owner inspected exactly
four entries/210 regular-file bytes within the approved bounded cache: one
directory plus35-,43- and132-byte files, with no symlink or unknown type; removed
only that task-created cache; and reran both Ruff checks with explicit
`--no-cache`. W5's exact top-level census is again only the two scripts. An
initial lint call also respected the surrounding ignored scratch path and warned
that it found no Python files; the final lint disables that exclusion and checks
both exact scripts.

No W5 gate, claim, source copy, restore, metadata query, build, DLL, report,
image, native PBT, provider or paid action exists. The scripts are held unchanged
for fresh independent exact-input review; implementation checks do not authorize
an operation or claim build acceptance.

## Accepted W5 gate and exact one-shot commands

ROOT read/rehashed the readonly787-byte gate
d2255ad0686de7c2c2e3ddc2ef2385dd2534f361a7bc7b6bec69011baa01f7ae
and13236-byte report
de1d4ddf9f171d692c3719766b4111a0094f62c8ab5ebbfd3f98c916fca7bf22,
then normal authenticate accepted the exact8cf58f96.../9bf048d9...pair,
source authority and contractec96f6c895246f3bf9bb0a1c99a5213e45a36b7f754bde74baefc1e7d046fb7e.
Independent34guarded checker controls,27complete metadata-path memory scenarios
and additional adverse paths/imports/source/reference checks have no blocker.
The initial ROOT authentication program then used a nonexistent convenience
constant in its separate absence assertion and exited1; authentication itself
had passed, with no phase called. The corrected fixed-name nofollow check passed:
all four claims/terminals absent. ROOT's16:41:47UTC filename-only ten-tree audit
found692Markdown,0nonMarkdown and0symlinks; scoped root/native diffs also pass.

Record exactly these four serial maximum-once commands BEFORE operation,
cwd=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r05. Inspect each
actual strict typed terminal/current-gate binding before advancing. Any claimed
phase failure spends the attempt and stops every later phase, without retry or
fallback; a rejected pre-authentication CLI cannot consume an absent phase claim.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py source --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 d2255ad0686de7c2c2e3ddc2ef2385dd2534f361a7bc7b6bec69011baa01f7ae
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py restore --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 d2255ad0686de7c2c2e3ddc2ef2385dd2534f361a7bc7b6bec69011baa01f7ae
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py metadata --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 d2255ad0686de7c2c2e3ddc2ef2385dd2534f361a7bc7b6bec69011baa01f7ae
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py build --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 d2255ad0686de7c2c2e3ddc2ef2385dd2534f361a7bc7b6bec69011baa01f7ae
```

All source/reference/configuration/proof/SDK/caps remain unchanged. Independent
actual-build accounting must accept the exact successful output before root C
may consume it. No Docker/native PBT/solver/provider/paid/tag/commit action here.

ROOT's first CLI invocation was rejected BEFORE begin_phase/any source action:
the supplied source digest accidentally omitted `fd` from the recorded literal
and was `a8c4fbf515bedd8f3b59357055a70a00b3d5179a4116d01ced150e41d811be`.
Its outer exit was1/ValueError external review digest argument differs, with no
claim or terminal. A fixed-name nofollow check confirmed all eight claim/terminal
paths absent, and authenticate with the exact recorded full digest passed again.
Record one rejected pre-authentication CLI separately from zero claimed phases;
the corrected recorded source command may spend its sole still-unspent claim.
Do not relabel the rejected invocation as a source-phase result or silently drop it.

## W5 actual source, restore, metadata and build

All four sole claimed phases completed. ROOT observed source93579/restore14143/
metadata72516/build97825 outer exit0 and strictly validated current gate and
completed prerequisite DTOs before each later phase. The separately recorded
pre-authentication CLI rejection above remains excluded from claimed-phase
counts but retained as an outer rejected invocation; no claimed phase retried.

Source ran16:44:36.548793Z–16:44:39.015461Z. Its claim is796bytes/SHA256
5110dff7601a64fc032117ea04348b69e7bb5818557af0a15ba948e76035306a;
preparation.json22042bytes/5f4dddbd232de3d7d04ced2f17cbde438c587bec7dfd9eea7876cefe7f46fd6b;
source-manifest.json22850bytes/b98da3c1710003309ca24ba3fe4f637705954efe0fcf373f416fa9f2249d3b41.
The source child census is not retained; manifest/input binding is not a process
census. Strict source/manifest/current-gate checks passed before restore.

Restore ran16:45:00.508888Z–16:45:03.010820Z, one retained completed exit0
process/2.254s. Claim797bytes/8140ec547f6427f4132972759199c48789c6548e65cd4a5868ba97cec13d2498;
restore.json38285bytes/dfa68cc0d62ec3a2e1248b5472480da227ff1de9acba5d339e96a15c095b317b;
log583bytes/62c089e4794b138039499ab41490c9f61449fadea36cf5ca9dc46b82f81e2b08.
Complete dependency postchecks and strict current prerequisites passed.

Metadata ran16:45:25.312468Z–16:45:28.894311Z/3.581s total. All four exact
evaluation-only queries completed exit0 (TG0.646s/Pipeline0.579s/Core0.641s/
Runtime0.662s). Claim798bytes/e60bafeeedbd905b430542030b5a54b125a19b8451e66c3a0b618630ffae182f;
metadata.json118549bytes/9483e9087b49629abe0a39ab28da20c0fb13580e3f86d8ab2412803894ccb58c.
Strict typed complete metadata/current prerequisite bindings passed before build.

Build ran16:45:58.652297Z–16:46:06.031724Z. The exact ordinary no-restore/
no-dependencies command completed exit0/5.938s. The262-byte log records0warnings/
0errors and hashes5243720d7d6a6286fa6b7a3b46e0cc66a4ab3ca5e7cc57d1875c1ee3b3bbf584.
Claim795bytes/9a84285b5838ea2ba5f9cd7e0cb1c17fa6ac12824927e9fcc22e5a3d3dc9cd63;
build-record.json48709bytes/5e94c692227c44d04858b2a63aae9292d271a9f374c22e544d1fd8ace9b9dfea.
New Binaries/DafnyTestGeneration.dll837632bytes/SHA256
dc3bddf9e0d2e374005370653f5a69d9f0f4ceb8fa3344f406164fdde2c1c336.
ROOT parsed/validated BuildRecord, all three prior originals, exact gates and
actual log/output identities. This establishes a successful C# build; it does
not establish image execution, ordinary Dafny proofs, PBT or benchmark success.

Fresh independent actual-build accounting accepted the exact output with zero
blocking findings. ROOT read/rehashed both exclusive0444 records:
verification/actual-build-review.json1493bytes/SHA256
957da34ecd3fe926097f7451ac961797c366881001566f1a9c6e350d97fe1da3;
Markdown22667bytes/SHA256
a66c2da9241c3a0406824b66d0621a45540eb3ccb6b972b09416bbe3c3f0c912.
The strict existing ActualBuildReview passes validate_actual_build_review against
actual receipt5e94c692..., scope actual_isolated_native_build_only/accepted=true.
Independent191named paths/18,357,271bytes, exact64native inputs,13originals,
3+3references, actual metadata/assets/config/import/dependency/output binding and
48memory adverse cases passed. Metadata/assets were each physically read once;
no source/SDK/cache census or actual command replay. Source-child unknowns and
ROOT's pre-auth rejection remain explicitly attributed. This completes the
native build acceptance criteria. Root C may now consume only this exact output
under its separate input/preparation/operation gates. No image, ordinary Dafny
proof, PBT, benchmark or stabilization outcome is inferred.

No new durable native proof/runtime finding: no such operation occurred. Existing
native bodyless knowledge remains valid. The reusable build-preparer path/hash
observations are recorded in the existing root integration
[runtime-image topic](../../../wiki/architecture/pbt-runtime-image.md), which
links back to this owning source/build plan. ROOT's16:52:26UTC filename-only
ten-tree audit remained692Markdown/0nonMarkdown/0symlinks, and scoped diffs pass.
Remaining work belongs to the linked root public-control and stabilization plans.

## Historical accepted W4 gate and exact one-shot commands

ROOT independently read/rehashed and strictly authenticated W4's readonly
787-byte JSON gatef51e401e45036605fad286b40b90547e4f5c5637e68b024ce75adf9af93d3099
and12438-byte reviewa6c0847a2d7726c881fec7c08a4e034eed953ebafcd137028582b70086d0943a.
Both are0444 and bind134031-byte producerdbac1662.../73974-byte checker770762e7...
and contractb5873448725ec0f2d2348dcd8d23400743716521d60417d76a3459dadf3049dc.
Its independent exact75metadata/34checker/28metadata-adverse/29restore-path
controls and source/reference checks have no blocking finding. ROOT's normal
authenticate call accepted the current exact scripts/contract/source authorities;
W4 still had only scripts and verification. Root's separate16:22UTC filename-only
audit found692Markdown files, zero non-Markdown files and zero symlinks across
ten root/submodule plan/wiki trees. This is ROOT's audit, not the gate reviewer's.

Exactly these four serial maximum-once commands are recorded BEFORE execution,
cwd=/workspace/tmp/pbt-unfinished-workspace-build-20261022-r04. Retain each
actual handle and inspect its closed strict terminal before advancing. Any
failure stops all remaining W4 phases and spends that attempt without retry.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py source --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f51e401e45036605fad286b40b90547e4f5c5637e68b024ce75adf9af93d3099
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py restore --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f51e401e45036605fad286b40b90547e4f5c5637e68b024ce75adf9af93d3099
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py metadata --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f51e401e45036605fad286b40b90547e4f5c5637e68b024ce75adf9af93d3099
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py build --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f51e401e45036605fad286b40b90547e4f5c5637e68b024ce75adf9af93d3099
```

All original source/reference/configuration/proof/SDK/caps remain. No old gate,
cache, package, output or image fallback is allowed. No Docker/solver/native PBT,
provider/paid/tag/commit action is included. Independent actual-build accounting
must accept the exact successful output before root C can consume it.

## Historical W1 commands — source attempt spent

ROOT independently read and rehashed the fresh readonly preparation gate at
2026-10-21 15:26:23UTC: verification/preparation-review.json is789bytes/mode0444,
SHA256 f3b93ba304d4f7b9e1c7db04fb58fb5e5d50cda2c597ec5780ebd331c99fbfde.
Its readonly7327-byte report is3167116b084abea2c12f17b73ee00d945256e9b6958513f647aac50ed6507ec2.
Both bind the final a4236245.../809cdae5... scripts, contract
67db468e81b24a6f472de40b337975582096ec3e5063bab8927f2dc8fbe026b5,
the exact accepted source review and four maximum-one claims. The independent
review found no remaining preparation blocker after23audited fake controls,
17real-input metadata mutations and exact public-source/reference inspection.
This accepts preparation only; no actual phase result is inferred.

The accepted W1 preparation originally authorized exactly these commands,
cwd=/workspace/tmp/pbt-unfinished-workspace-build-20261021, serially. Its first
source command subsequently failed. It must never be rerun, and none of the
remaining three W1 commands may execute. Retain this historical argv and its
failed/spent claim without retry. W2 needs its own future exact gate and argv.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py source --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f3b93ba304d4f7b9e1c7db04fb58fb5e5d50cda2c597ec5780ebd331c99fbfde
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py restore --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f3b93ba304d4f7b9e1c7db04fb58fb5e5d50cda2c597ec5780ebd331c99fbfde
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py metadata --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f3b93ba304d4f7b9e1c7db04fb58fb5e5d50cda2c597ec5780ebd331c99fbfde
PYTHONDONTWRITEBYTECODE=1 python3 -B prepare_build.py build --source-review-sha256 a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be --preparation-review-sha256 f3b93ba304d4f7b9e1c7db04fb58fb5e5d50cda2c597ec5780ebd331c99fbfde
```

ROOT will retain each actual execution handle and inspect its closed terminal
before advancing. Exact SDK/configuration/time/output/source bounds above remain
unchanged. Gate existence alone is insufficient; the supplied external digest
and processor's repeated authentication bind every process. Source preparation
and C# restore/metadata/build are operational maintenance outside development
tests. No Docker/native PBT/provider/paid/alias/commit operation is included.
After the final actual receipt, independent actual-build accounting remains
mandatory before the existing root public-control capsule can consume its DLL.

## Remaining risks and handoff

Common output/reference configuration now has actual independent metadata/build
acceptance under exact r05 scope. The first four historical attempts remain
failed/spent and unchanged. Original accepted objects/artifacts and existing live
source/build outputs remain untouched. Installed SDK/cache are trusted runtime
prerequisites only; declared package equivalence is checked without claiming a
full installed-toolchain audit. A successful C# build establishes no Dafny proof,
generated-program runtime behavior or benchmark result.

The linked root public-control plan/capsule now consumes only the accepted new
TestGeneration DLL over immutable40d under its own actual-input/freeze/image/tool
gates. Its population is10registered calls/eight campaigns/up to24generated
samples, original nine cases with a bodyless configured Goal and a separate
unrelated-declarations fallback case. No native campaign/image action follows
from this completed build plan alone. Parent stabilization and the held paid
cohort remain open; shared-task-tag approval alone does not release old40d.
The next root action is independent C SourceReview acceptance, followed by its
once-only freeze/preparation/operation and actual result accounting.
