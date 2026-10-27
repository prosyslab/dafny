# Construct immutable field aliases during PBT initial admission

Status: done
Date: 2026-10-26

## Objective and inspected evidence

Repair the next precise R11 construction failure before another image attempt.
The installed arithmetic repair passes its memory regressions, but full public
support still produces four initial-admission closed-query timeouts. The
bodyless IO global requires a finite class inhabitant; HasStructuralInhabitant
currently rejects every initialized instance constant, including the exact
identity alias `directoryStateRegion := dirHandlesRegion`. The source field is
an own bodyless immutable constant of the identical type. This is development
maintenance using declared public support, not a benchmark candidate solution.

Existing initial-construction, scope, trust, type-equality and recursive field
checks will be reused. Independent read-only semantic review recommends only
single-hop aliases; no general expression evaluator or alias graph is needed.
Parent: [extern runtime](../../plan/2026-10-26-pbt-extern-runtime.md).

## Acceptance, compatibility and non-goals

- Only the fresh-reference class inhabitance branch gains an exact identity
  alias rule. The resolved RHS must be an unlabeled MemberSelectExpr on this,
  targeting a distinct own nonstatic ConstantField with no RHS. Alias, selected
  expression and target types must match with keepConstraints:true.
- The target remains in the existing class field traversal and must independently
  pass recursive structural inhabitance. Reuse its value; allocate no additional
  witness for the alias. Retain generic, trait, inheritance and recursion guards.
- Literal initializers, mutable/static/foreign targets, conversions, calls,
  constrained-type mismatches and chains remain unsupported by this new rule.
- Keep complete declaration scope and native well-formedness requirements.
  No trusted-global exemption, extra trusted source, timeout increase, contract
  weakening, source filtering, schema change or concrete-heap change.
- Memory regression must reproduce the positive accepted construction and the
  negative boundaries. Independent review and tests precede CLI publication.
  A fresh installed-image run remains a separate acceptance gate; no live
  provider call is authorized by a unit-test result.

## Change table

| Exact file/symbol | Change and necessity | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs, HasStructuralInhabitant | Admit only the exact own immutable single-hop identity described above in fresh class construction; current unconditional initializer rejection causes unnecessary SMT fallback. | Positive finite construction, negative expression/type/ownership cases, unchanged abstract-global result and scope. |
| Source/DafnyTestGeneration.Test/ContractRuntimeGlobalAdmissionTests.cs | Add small SnapshotFileSystem-only scenarios through existing parse/scope/construction APIs. | Trace all helpers; no solver/process/tempdir/filesystem synchronization. |
| This plan, plan/INDEX.md, wiki/pbt-trusted-sources.md, wiki/INDEX.md | Record semantics, actual evidence and limits. | Diff review and Markdown-only audit. |
| Parent Cosyn plans/index and goal-PBT wiki/index | Correct R11 terminal status and link this separate repair. | Preserve historical failed-run evidence and unconsumed live authorization. |
| /workspace/tmp/pbt-immutable-alias-20261026/ bounded operator worker/logs | Derive reviewed test-project build worker with exact changed source/test identities and unique outputs. | Syntax/Ruff checks, tmux execution, bounded logs and matching artifacts. |
| Same scratch, public-construction.fsx and bounded launcher | Use installed SDK F# interactive to call current native snapshot/scope/construction APIs on the exact nine public support snapshots and unchanged SupportSmoke. No new executable/package or repository-test owner dependency. | Read-only reflection for existing internal stage queries; pre/post source and DLL hashes, no solver/campaign/process compilation, bounded tmux log. |

## Validation and execution

First inspect the complete test path. In-memory positives must retain the alias
in accepted scope and the bodyless global in the source-bound global set, reject
abstract empty-heap admission, and yield a
non-null independent construction with RequiresNativeProof=false. Untrusted
aliases must retain original native well-formedness checks. Add relevant negative
controls without parsing external benchmark artifacts in repository tests.

Run scoped whitespace formatting before build, from /workspace/cosyn/dafny:
`dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs Source/DafnyTestGeneration.Test/ContractRuntimeGlobalAdmissionTests.cs`.
Build separately in recorded tmux with existing bounded operator mechanism:
`dotnet msbuild Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj -nologo -t:Build -verbosity:minimal -maxCpuCount:1 -nodeReuse:false -p:SkipFocusedTestAssets=true`.
Then independently run only safe selected tests:
`dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractRuntimeGlobalAdmissionTests|FullyQualifiedName~ContractTrustedSourcesTests' -v:minimal`.
Run scoped whitespace verification and git diff --check. Broad heap-query/driver
admission tests are excluded because their helpers invoke native/disk workloads.
Publication and fresh image setup require their own updated operator records.

Before another image, run the separate full-public in-memory operator probe via
`dotnet /usr/lib/dotnet/sdk/8.0.131/FSharp/fsi.dll --noninteractive --exec public-construction.fsx`.
It uses the exact previously declared nine public Dafny source paths and SHA
trust identities plus the unchanged empty-input/heap SupportSmoke target. Load
only the current testhost or CLI assemblies and their declared dependencies.
Report parse errors, scope failure/native checks/acceptance, independent and
abstract-global stages, TryPrepare and RequiresNativeProof. Internal reflection
is read-only diagnostic access, not evidence fabrication or production wiring.
No CheckModuleAsync, solver, compiler campaign, provider, generated executable
or source rewrite. Bound the operator to 60 seconds and 64 KiB combined output;
use unique result names and explicit before/after file identities. This separates
remaining construction defects from costly installed-image runs.

## Risks and approvals

An overly broad alias rule could assume an impossible value or discard a type
constraint. Exact resolved ownership/type checks and the original target field
inhabitance check bound that risk. Do not skip checks because a source is trusted.
No new dependency, commit, benchmark edit or paid call in this source scope.
Preserve ongoing user commits and temporary pre-commit stashes. External scratch
writes use the approved escalation mechanism. No additional user decision needed.

## Progress

Implementation started with the frozen structural-inhabitant and memory-test
scope. The exact alias predicate and memory controls are implemented. The
selected test path uses SnapshotFileSystem parsing, direct structural/scope
checks and in-memory preparation only; it does not reach CheckModuleAsync, the
solver, native compilation, a process, a temporary directory or synchronization.
Scoped formatting of both source files completed successfully. Build and
independent memory validation remain pending under the parent operator workflow.

Static test review corrected an overstrong scope expectation before execution:
ConstructionScope supplies bodyless global types, not the bodyless constants as
roots, and CreateScope intentionally removes bodyless instance fields. Assert
the defined alias in scope and the global/source/field identities separately;
do not alter production scope discovery to satisfy a test. Exact single-hop
construction is also valid in the existing specifications:null fast path because
the terminal field must still satisfy every original structural leaf check.

## Frozen source and separate operator preparation

The two-file source scope is implemented and scoped whitespace formatting passes.
Production SHA256 is `0f936f59ba21f56f5910fbe484534201cf66c80280ea2fc019b6ca7093013117`;
memory-test SHA256 is `3b77e3130f9937d1d5b8fdc5c9382ea2297028df76d5a7cc33f883dc858a1251`.
Independent source/safety review is pending. Root prepared the existing bounded
worker at `/workspace/tmp/pbt-immutable-alias-20261026/native-test-build.py`,
SHA256 `97f8738d9213818d45db9cddd0664527025aa9d60e12a2e25136029b39693714`.
It differs from the accepted arithmetic worker only in these two source pins and
unique log/result names. Syntax and root-config Ruff pass. No build launched yet.

Independent source/safety review accepts the implementation. It requested one
additional foreign-instance-receiver rejection case; this test-only addition was
formatted before build. Final test SHA256 is
`427bb2adf58bd38c03d6ef5aef9a9f3f308c49f7f6cf3f51c92087742bf87d1b`;
production remains unchanged. Final worker SHA256 is
`874cf810ef9905aab59e420f2544ddf161075deeb88087e2bcbffe6faec7df8c`.

The separate test-project build in tmux/socket
`pbt-immutable-alias-test-build-20261026` exited 0 with all fifteen source pins
matching. Test assembly SHA256 is
`92e4a0050a27670cde73b669dd6f9dedda5c633adead809f7f4b67b245ab0afc`
(1,401,856 bytes). Testhost TG equals its freshly built obj output
`2b9976763dfd76b5b636c9251e45ecba40b0e2db573c3565736ea610dacc41a3`;
flat CLI TG remains the prior R11 publication, as expected. Independent memory
tests and full-public operator construction diagnosis are still pending.

Independent validation completed: 40 passed, 0 failed/skipped, 385 ms; scoped
whitespace and diff checks pass. Source/test and testhost/obj identities remained
unchanged. Reusable semantics/evidence are recorded in
[trusted-source documentation](../wiki/pbt-trusted-sources.md#immutable-field-identity-aliases-2026-10-26).

Public diagnostic helpers are frozen for independent review: Python launcher
`98937952d7b72f212c8ae5ddbbe339957fd823db81f14ebbd1c013e9f176af72`,
FSI script `9eafa2d4e5078f287762b8d5dd6244d4ab931ad4ef3707acb46dc0b1e1fd3fe0`,
after identities `2020f195e990c216a6c2456ead00bed0ba07350fce114032770ef4a87654c1fc`.
The six fixed FSI references include only Core, TG, three Boogie DLLs and
System.CommandLine; no framework tree enumeration. Separate before identities
bind old CLI products and explicitly make no matching-current-source claim.
After binds the successful build receipt, test assembly and exact fresh obj
Core/TG copies. Both use the same public9/source15 identities and unchanged
SupportSmoke. No diagnostic execution yet.

Independent diagnostic review found that current public IO.dfy and IOContract.dfy
bytes differ from R11's frozen input hashes. Preserve these user changes. Both
before and after diagnostic maps bind the same current public snapshot; this
comparison isolates old/new native behavior on current inputs, not a byte-identical
replay of R11. Before identity-map SHA256 is
`0c48fce18ed915fcd7e80d24a8dd09780d04322526e96fb898d4914b9e18d3a5`.
A future image must capture this current state afresh.

The first before/after FSI calls both parsed the public snapshot with zero errors,
but the operator serialized all informational trigger messages and exceeded its
60 KiB stdout cap. Both were stopped; identities stayed unchanged. This is an
operator reporting defect, not an admission outcome. Preserve r01 artifacts.
Ready correction: retain only the first eight parse errors, each capped at 512
characters, with the existing full parse-error count. Preserve the original FSI
script separately and use fresh r02 output prefixes; no native/source/input or
time/output-limit change.

## Actual full-public construction and closure

R02 before/after comparison is independently accepted. Both use byte-identical
current public9 plus SupportSmoke, stable source15/library maps and correct
loaded assembly paths. Before old CLI: parse0/scopeaccepted/nativechecks0,
abstractfalse/independentfalse/TryPrepare null. After fresh testhost: parse0/
scopeaccepted/nativechecks0, abstractfalse/independenttrue/TryPrepare non-null,
RequiresNativeProof=false and construction_ready=true. Output sizes15,793/28,146
bytes, stderr0. No solver or runtime campaign was invoked.

The only r02 helper change filters the reported parse messages to bounded errors;
FSI SHA256 is `bd607718020a9fb57f0f3b31ed577a8930f1e7cbca85b75b6c57268f0d0a5e09`.
Tmux/socket names are `pbt-public-construction-before-20261026-r02` and
`pbt-public-construction-after-20261026-r02`. Original r01 evidence is preserved.

Done for this source/local/public-construction scope. The parent plan owns actual
CLI publication, dedicated R12 image, installed sampling and Csplit trial. Its
publication worker is dispatched in `pbt-immutable-alias-native-publication-20261026`;
worker SHA256 `91a42317ebd5ec6072f8ae0138411b545ad81ba7614b4d2b1cb00d2a5f60de1a`.
No valid runtime sample or Csplit counterexample is claimed by this diagnostic.
