# Repair PBT worker null failures

Status: in-progress

2026-10-21 successor: [authored generator proofs](2026-10-21-pbt-authored-generator-proofs.md)
now owns replacement of the custom fingerprint/strengthened-generator mechanism.
Its frozen inherited patch preserves this repair exactly before replacement.
The null-draft and source-preparation fixes remain in the current tree; the old
fingerprint-specific evidence below is historical and does not establish the
new ordinary-verifier path or the private worker failure's cause.
Date: 2026-10-21

## Objective and acceptance criteria

Repair public native runtime/proof paths that can expose an unhandled
`NullReferenceException` during an ordinary proved-input PBT campaign. This is native repository
maintenance, not an evaluated run. The current closed live observation establishes only an NRE-shaped
failure with public campaign/proof/CLI frame classes and zero samples; it does not authenticate either
source candidate as that failure's cause.

Acceptance requires: (1) a malformed request containing a null draft is rejected with the existing
`ArgumentException` contract before any recorder, directory, parse, compiler, process, or sync path;
(2) a tiny valid string-backed Dafny program independently reproduces or rules out a null resolved
reference in `TryResolvedProgramFingerprint`; (3) every semantic reference remains represented in the
fingerprint, the valid ordinary binding path succeeds, and a deliberately unresolved/tampered reference
returns the existing bounded fingerprint failure rather than escaping as an NRE, without weakening source,
option, proof-coverage, solver, certificate, or anti-tamper checks; and (4) focused memory tests, the
supported native build, formatting, diff and Markdown-only audits pass. Unsupported genuinely unresolved
states must return the existing bounded fingerprint failure, never escape as an NRE. No broad exception
catch or reference omission is acceptable.

Implementation begins only after the root owner reads and announces this ready plan. Apply the inherited
source-preparation repair only after that announcement and preserve it as a separately attributable
two-file patch before adding this plan's worker fixes.

## Scope and boundaries

Owning repository: isolated native worktree
`/workspace/tmp/pbt-worker-failure-20261021/native`, detached clean base
`b4f683fd85c9764c032346e0367df325f73dd4be`. Applicable `/workspace/AGENTS.md`,
`/workspace/cosyn/AGENTS.md`, native `AGENTS.md` and native `CLAUDE.md` were read. No plan/wiki-local
instruction file or template exists. This work may read only public native source, tests, configuration,
and generic native plans/wiki pages. It must not read `/data`, private task/candidate/evaluator/reference
material, experiment histories or logs, and must not mutate `/workspace/cosyn/dafny`, its binaries, the
running treatment, images, containers, benchmark inputs, protocol, evaluator, dataset, scoring, provider
configuration or credentials.

The root owner supplied the exact inherited source-preparation patch at
`/workspace/tmp/pbt-worker-failure-20261021/preparation.patch`: mode `0444`, 13,974 bytes, SHA-256
`cca12fa66e188b56271c625667630750a8d10dcad2510c615363f1cfc1501ae8`. `git apply --check` succeeds on
this base. It changes only `ContractRuntimeSourcePreparation.cs` and its memory tests. The production-only
and test-only component hashes are respectively `f09b18486d7b79e42e080cf1eb5cb399ffecdb0b9033883641dd8e34a9abbd78`
and `f1164c8265083bb758fbd6e40cd9c438e4ffd7117530640c751ad1d0c23c8e2b`. This plan will record that
inherited diff separately and will not redesign it.

No package, dependency, commit, provider call, Docker action or campaign run is authorized. The user has
authorized repair of the PBT bugs. Root owns any later image rebuild, public operational controls, live
dispatch and causal interpretation.

## Inspected evidence and existing seams

- `ContractRuntimeCampaignRunner.RunAsync` calls `Validate` before constructing phase/profile recorders.
  `Validate` projects `(request.Drafts ?? []).Select(d => new ContractSource(d.Path, ...))` before its
  later `files.Any(f => f == null || ...)` check, so `Drafts = [null]` dereferences null instead of
  returning the request-boundary `ArgumentException`. Validation can reject the list element directly
  before projection and retain all existing path/hash/uniqueness/trusted-source checks.
- `ContractGeneratorProof.TryResolvedProgramFingerprint` enumerates every `Reference` from
  `IHasReferences` nodes and resolved/component types, then passes `reference.Referred` directly to
  `NavigationIdentity`. `ModuleQualifiedId.GetReferences` constructs a reference from
  `ResolveTarget(...)`, whose documented return may be null for unresolved or unused alias paths. This
  is a plausible NRE seam but not yet a reproduced ordinary valid-source cause.
- `ContractGeneratorProofTests` already parses bounded source strings with
  `ContractSourceSnapshot`'s dictionary-backed filesystem, resolves them in memory, calls the semantic
  binding/fingerprint seam, and never stages source, creates directories, syncs, invokes a solver/native
  compiler or starts a process. Existing CLI-prepared reference cases protect parentless but non-null
  declaration identities.
- `GeneratorProofResultTests` currently uses JSON and pure helpers. A direct `RunAsync` malformed-request
  case reaches `Validate` before its first `Path.Combine`/recorder construction; the supplied directory
  is an inert string if that precondition remains ordered correctly.
- `ModuleQualifiedId.GetReferences` is generic Dafny behavior outside this feature. This plan does not
  change it. The PBT fingerprint boundary must classify its result while retaining the fingerprint's
  reference count/order/source-node/referer-range and target-identity guarantees.
- Relevant source hashes before inherited preparation are:
  runner `925ed2a76973bffb097fdd119a9993573c34219174ac9b3ebf306631087d5dc6`, proof
  `fb1d0bb5213c1c9840ae5577cd858b752f6a8273fa5417c299062aaa11d13fdf`, Driver test
  `b8431e6f92b4cbeb614fd455b308d8e20e10d354abe950247af1fa27cd6ad690`, and proof test
  `df83a9a016a9d06d13c5facd75940eb053fcd8a3e11acff0c5c92cd039eceeaa`.

## Change table

| Exact owner file/symbol | Planned change, necessity and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan; `plan/INDEX.md` | Register native ownership, boundaries, exact inherited prerequisite, evidence, conditional fingerprint scope and executable checks before source changes | Status/link/diff and recursive Markdown-only audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs`; `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs` | Apply only the root-supplied exact combined preparation patch after announcement. This preserves the independently prepared default-module/include-first repair needed by the parent treatment; without it the parent preparation acceptance remains unmet | Exact input patch SHA/mode/size; capture inherited two-file diff separately; focused existing memory class later, with no redesign here |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs::Validate` | Validate every nullable draft element before dereferencing/projecting it, then retain existing file path, traversal, hash, URI uniqueness and trusted-source validation. Without this, malformed JSON can escape the request boundary as NRE | One direct `RunAsync` malformed-request test proves `ArgumentException` occurs before any disk/process path; source review confirms later checks unchanged |
| `Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs` | Extend the traced pure/memory boundary with one null-draft scenario and update its boundary comment. Construct one valid source and hash, use the inert absolute directory string `/workspace/unused-null-draft-campaign`, and assert early `ArgumentException`; no fixture/campaign helper, filesystem, recorder, process or cleanup | Exact class filter; call-path audit from `RunAsync` line 71 into `Validate` and no later instruction |
| `Source/DafnyTestGeneration.Test/ContractGeneratorProofTests.cs` | Add a tiny legal, resolved, string-backed source case using an unused qualified module alias; assert reporter success, non-null normal targets and the actual successful fingerprint. Separately clear that already valid alias's cached resolved root/target to reproduce a malformed/tampered AST boundary and assert the public fail-closed fingerprint result is `false` without an exception. Keep one scenario per fact and explicit one-line intent comments | The legal pre-fix case rules the ordinary alias hypothesis in or out. The tampered pre-fix case must reproduce the NRE before the defensive repair. Existing exact-source acceptance and semantic-tamper rejection stay positive. No directories/files/process/solver/compiler/sync |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs::TryResolvedProgramFingerprint` | If the direct tampered-AST fact reproduces the NRE, check `reference.Referred` immediately before `NavigationIdentity` and throw a precise `NotSupportedException` handled by the method's existing bounded failure contract. Do not accept unresolved state, skip a record, use an empty/sentinel identity, catch NRE, or alter proof/certificate/coverage policy. The passing legal alias requires no alternative target identity | Normal valid source remains completely hashed; explicitly unresolved synthetic state returns `false` without throwing; existing exact binding, lexical-owner and mutated-body/source cases pass |
| This plan; existing `wiki/pbt-generator-proof-integrity.md` and `wiki/INDEX.md` only if a durable fingerprint rule is verified | Record actual commands/results and either the durable nullable-reference identity rule or `No durable findings`. Do not infer the live receipt cause | Reciprocal links, source-backed limitations, fresh independent review, Markdown-only audit |

No `ModuleQualifiedId`, parser, resolver, grammar, runtime model/schema, proof policy, certificate, evaluator,
benchmark or experiment file is planned. Update this table before touching any different file or broadening the
fingerprint behavior.

## Test-boundary and reproduction design

The malformed request contains one tiny valid `ContractSource`, a valid schema/entry/seed and
`Drafts = [null!]`. The awaited public `RunAsync` call must throw `ArgumentException` at validation. It
must not use `CampaignHarness`, test fixtures, temporary paths, environment temp paths, a real file or a
recorder fake: execution beyond validation is itself a failure and would expose an unintended disk path.

The fingerprint reproduction starts with a legal module plus an unused alias/import whose resolved
program reports no errors. It records the concrete `ModuleQualifiedId` reference shape and calls
`TryResolvedProgramFingerprint`/`BindPreparedProgramAsync` through the existing memory parser helpers.
The legal qualified alias passed this check with a non-null target and complete fingerprint, so it does not
reproduce an ordinary nullable reference. A separate malformed-AST control may then clear that same parsed
alias's resolution cache and must establish an actual pre-fix NRE before the one-line defensive production
guard is added. That control justifies fail-closed API robustness, not acceptance of an unresolved target,
an ordinary-source defect, or a claim about the live failure. The implementation preserves anti-tamper
coverage by rejecting the whole fingerprint rather than deleting or inventing a reference identity.

Before running either focused class, re-audit all new helpers and invoked paths through setup, execution,
teardown and deferred cleanup. The allowed tests use bounded strings, fresh options, in-memory dictionaries,
AST inspection and hashing only. They may not create/read/write/delete a directory or file, use pytest/temp
helpers, run a process/native tool/compiler/solver/campaign, produce generated builds from test code, invoke
durable synchronization, or rely on copied runtime trees. Existing unrelated disk-heavy test files will not
be selected.

## Risks and compatibility

- Nullability annotations do not prove deserialized list elements are non-null. Boundary validation must
  retain the public exception type and fail before any observable campaign artifact.
- A null `Referred` value can mean a lazily materializable valid alias, a resolver error, or a malformed
  AST. The implementation may accept only the first with a stable identity evidenced by a valid source;
  it must reject the latter states through the existing bounded unsupported path.
- Reference order/count and source/referer framing are part of the semantic anti-tamper fingerprint.
  Filtering null entries, hashing a generic `null`, or using unstable object identity would weaken binding.
- The inherited preparation patch changes two files and tests independently. Worker diffs and validation
  will distinguish it so a reviewer can assess each repair and root can transplant/freeze exact sources.
- A focused unit pass establishes request/fingerprint behavior only. It does not establish solver proof,
  generated runtime correctness, live campaign recovery or causal attribution to the closed observation.

## Validation plan and prerequisites

Do not run any command below before the root announcement. The fresh worktree has no
`obj/project.assets.json` or build output. Use .NET SDK `8.0.131` and only the already installed local
package cache, which currently contains 401 `.nupkg` archives. A bounded restore of the solution's
existing declared dependencies is therefore an explicit operational prerequisite; it may generate
worktree `obj` assets but may not contact a network source, add/change a dependency, copy/link assets or
binaries from the current live native tree, or alter the installed package cache. No paid call, Docker,
campaign or benchmark suite is authorized. Store bounded non-sensitive logs under
`/workspace/tmp/pbt-worker-failure-20261021/`, outside plan/wiki. Native restore/build are operational
prerequisites distinct from the development tests.

From `/workspace/tmp/pbt-worker-failure-20261021/native`, after applying the exact inherited patch and
adding the failing regressions:

1. `dotnet restore Source/Dafny.sln --source /home/vscode/.nuget/packages --packages /home/vscode/.nuget/packages --disable-parallel -p:NuGetAudit=false -p:RestoreNoCache=true -m:1`
   - Bound to 10 minutes and an 8 MiB log. The explicit local folder is the only source, so no scratch
     NuGet configuration is needed and nuget.org is not queried. Expected: generate solution assets from
     already present archives without writing new package-cache entries. Inspect only the bounded restore
     outcome; do not recursively read or hash the installed cache. If the local source cannot satisfy an existing declared package, stop,
     preserve the failure and ask root for an approved build path; do not enable a network source, install a
     package, or copy/link `obj`, `bin` or `Binaries` from another worktree.
2. `./gradlew --offline build` from `Source/DafnyRuntime/DafnyRuntimeJava`, using the approved escalated
   execution path solely so Gradle may take its existing distribution/cache lock and emit this isolated
   worktree's `build/libs/DafnyRuntime-4.11.1.jar`.
   - Prerequisites: installed Gradle 8.14 distribution and cached modules. Bound to 10 minutes and an 8 MiB
     log. `--offline` forbids dependency download. Do not copy/link a jar or cache from another worktree,
     change dependencies, or write outside the existing Gradle cache locks and this worktree's build tree.
     If cached inputs are insufficient, stop and report the blocker.
3. `dotnet build Source/Dafny.sln --no-restore -m:1 /nr:false` through the approved escalated
   operational path so the solution's repeated supported Gradle target can use its existing cache locks.
   - Prerequisites: steps 1–2 assets and native Java runtime jar. Bound to 20 minutes and an 8 MiB log.
     Expected: success at the exact dirty b4-based source state; record all warnings. This is build evidence,
     not a proof/campaign result.
4. `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractGeneratorProofTests -m:1`
   - Expected: all selected bounded memory cases pass with zero skips, including the valid alias/reference
     reproduction and retained anti-tamper cases. The test command emits no build output.
5. `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter FullyQualifiedName~GeneratorProofResultTests -m:1`
   - Expected: all selected pure/memory cases pass with zero skips, including pre-artifact null-draft
     rejection. The test command emits no build output.
6. `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeSourcePreparationTests -m:1`
   - Expected: inherited preparation memory cases pass with zero skips. Keep their evidence distinct from
     this worker repair.
7. `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs Source/DafnyTestGeneration.Test/ContractGeneratorProofTests.cs Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs --verify-no-changes`
   - Expected: no formatting change. If the formatter writes during correction, record it and rerun verify.
8. `git diff --check`, review the inherited and worker diffs separately, and
   `find plan wiki -type f ! -name '*.md' -print`.
   - Expected: no whitespace errors, no scope drift, and no non-Markdown files.

Fresh verification must use a new independent agent context starting from this plan, requirements and the
current worktree; it must inspect source and execute its own checks without receiving implementation-agent
conclusions. Root will arrange that verifier and any later operational public native controls. Mark this
plan done only after required checks and independent acceptance pass; otherwise record the concrete blocker
and next action.

## Progress and handoff

Root read and announced the ready plan at 05:00 UTC. Inspected the clean detached base, source/test call
paths, generic native knowledge, build configuration, and corrected inherited patch metadata. No source
patch, build or test had run at that checkpoint. The exact inherited preparation diff now matches its
combined patch SHA. The local-folder-only NuGet restore passed for all solution projects. The first full
solution build generated parser/scanner output with zero errors, then repeatedly failed to acquire the
read-only installed Gradle cache lock and could not emit the Java runtime jar; it was interrupted after the
failure was certain and is not passing build evidence. The supported project target invokes
`DafnyRuntimeJava/gradlew build`; the installed Gradle 8.14 distribution and cache are present, so step 2
records the approved escalated offline prerequisite. That prerequisite passed and emitted the isolated jar.
A second full build with `--no-incremental` forced the Java target despite its fresh declared output and
again hit the read-only wrapper lock, so it too was interrupted and is not passing evidence. An ordinary
incremental full build also invoked the target repeatedly because the multi-target solution evaluates it
per runtime target; it was interrupted after the same lock failure and is not passing evidence. Step 3
therefore records the root-approved escalated solution build so each supported Gradle invocation can use
the already installed distribution/dependencies and existing locks. The completed offline prerequisite
establishes those dependencies are locally sufficient; no restore, package download or dependency change
is permitted during the escalated build. The malformed-draft defect
is established from public source ordering. The fingerprint null-target path remains a public hypothesis
pending the required legal-source memory reproduction. No live-cause claim is made.

### Blocked handoff at 05:21 UTC

The implementation agent was terminated by the runtime automatic content filter
before a final build/test/source handoff. Two separate read-only proof-entry
diagnosis agents had also been terminated by that filter. Root reported the
limitation to the user, did not replace the blocked implementation, and stopped
additional source work. Preserve this exact partial worktree; no commit, main
transplant, native image update or live treatment edit occurred.

The inherited preparation patch is present separately. The null-draft runner
guard and its Driver test are written. The ordinary legal-alias fingerprint
probe was reported by implementation as passing, but no fresh verification run
has occurred. An additional cleared-resolution regression exists only in source:
the fresh verifier checked that its timestamp is later than the proof-test DLL,
which includes the legal-alias name but not the new cleared-resolution test.
ContractGeneratorProof.cs has no production diff; the proposed null-target guard
was not implemented. Do not run or present the partial regression as a completed
repair. The request fix/test were compiled into Driver assemblies, but their
behavior remains independently unverified.

Root's poll of the known solution-build session 26888 returned Unknown process
id, so that session is closed. There is no preserved final full-build/test exit
record in adjacent scratch; do not infer a successful full solution build from
assembly timestamps or the earlier progress messages. Required focused class
runs, final formatting and final fresh acceptance remain incomplete. The
verifier has been asked for read-only current-state handoff only, not to resume
implementation or start .NET commands. Its report belongs in adjacent
`/workspace/tmp/pbt-worker-failure-20261021/verification.md/json`.

Next action: restore an approved supported execution path for this legitimate
maintenance task, review the existing partial diff, reproduce the unfinished
boundary scenario, then finish only the planned repair and required checks.
The actual live proof-worker failure remains unexplained and must be tracked
separately. No new verified durable code finding is published to native wiki
because the patch/reproduction acceptance is unfinished; source hypotheses and
partial checks remain in this plan.

### Resumed under the explicit stabilization goal at 05:38 UTC

The user activated the full stabilization-and-real-experiment loop. Root
revalidated this existing worktree and the accepted public cohort metadata;
the partial source state is unchanged. The earlier blocked handoff remains
accurate for its timestamp. Resume only the declared bounded native checks and
confirmed boundary repairs under the new parent
[stabilization plan](/workspace/plan/2026-10-21-pbt-stabilization-loop.md).
Earlier source-analysis agents' runtime terminations are not evidence of a
failed test or an unavailable normal dotnet command. Do not restart any exhausted
private observation or claim an ordinary-source cause from the synthetic test.

First build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj with
--no-restore -m:1 /nr:false in this worktree and run only the already written
ResolvedFingerprintRejectsAliasWithClearedResolution with --no-build --no-restore.
This establishes its actual pre-fix behavior before the planned smallest guard.
Then use the declared supported final solution build and three focused class
filters, scoped formatting and fresh independent verification. Existing assets
and isolated Java jar are present; restore is not needed absent a new concrete
missing prerequisite. Existing Gradle cache locks may use the already approved
escalated operational path. No dependencies, benchmark/input changes or new
paid dispatch occur in this native maintenance step.

Capture new bounded public operational logs in adjacent build-before-001.log,
build-after-001.log and checks-001.log, <=8MiB each. Preserve the original
verification.md as unaccepted historical evidence; a fresh independent review
will write verification-goal-001.md/json. Root will announce this resumed ready
plan before code/build execution and update in-progress. The actual live proof
failure remains a separate unmet stabilization requirement.

### Actual regression reproduced after resumption

The affected test project build passed (exit0,9.001s,4,706 output bytes) on the
preserved partial source. Existing warnings were CS0162, CS0618 and VSTHRD103;
no build errors occurred. The first default-sandbox test attempt aborted before
execution because VSTest could not open its local IPC socket. That is an
environment failure, not a reproducer. The approved local-IPC execution then
ran exactly ResolvedFingerprintRejectsAliasWithClearedResolution:1 failed,
0passed/0skipped, actual NullReferenceException at NavigationIdentity with the
AppendReferences/fingerprint stack. Evidence is in adjacent build-before-001.log
and checks-001.log, with both attempts retained distinctly.

Only after this actual pre-fix failure, root added the planned immediate
null-target check. It throws NotSupportedException into the existing bounded
fingerprint failure handler; no reference is skipped or accepted with an
invented identity. The ordinary legal-alias case remains separate and must pass
in the final focused class. Settled-source build, focused tests, formatting and
fresh independent acceptance are still required. No live-cause claim follows.

### Settled local repair independently accepted,05:53UTC

Supported full solution build completed with exit0,zero warnings/errors and
30.537s outer elapsed time; adjacent build-after-001.log is7,458 bytes. The
fresh independent verifier ran the three declared class filters itself:
ContractGeneratorProofTests124passed,GeneratorProofResultTests9passed and
ContractRuntimeSourcePreparationTests24passed, with zero failed/skipped.
The verifier confirmed exact hashes for all six changed source/test files,
the original inherited preparation diff, pre-artifact ArgumentException for
null drafts, fail-closed unresolved references, complete legal fingerprints and
unchanged fingerprint framing/proof coverage. Scoped whitespace verification
and diagnostic verification passed; their sole unmatched metadata warning is
outside the selected files, and all four selected-file projects loaded. Diff,
JSON and recursive root/native Markdown-only checks passed.

Evidence is adjacent verification-goal-001.md and verification-goal-001.json;
the earlier verification.md remains explicitly unaccepted historical evidence.
These local boundaries are accepted. The actual ordinary-source proof-worker
cause remains unknown, so root's full stabilization goal and this maintenance
record stay in-progress while separate public operational reproduction proceeds.
No live source/image, candidate inputs, solver policy or private evidence changed.

Durable finding: an unresolved reference invalidates the entire fingerprint;
it must never be silently omitted or represented by an invented identity. See
[the updated proof-boundary record](../wiki/pbt-generator-proof-integrity.md).

