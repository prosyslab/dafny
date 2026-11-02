# Correct raw traversal in native contract-screen preparation

Status: done — source patch and independent verification complete; publication authorized on 2026-11-02
Written: 2026-11-02
Owner: independent native Dafny repository at /workspace/tmp/fold-native-screen-recovery/dafny-native
Base: 086ba8b875752dc791bf8dc2da9406d79b6bbae9

## Objective and acceptance

Prevent the native contract-screen preparation stage from traversing unresolved
AST nodes through their resolved Children view. A method with an explicitly
typed local variable must prepare without a NullReferenceException. Preserve
rejection of declaration/module source options, post-resolution reference
identity, logical proof checks, source identity and the published native wire.

Acceptance: generic typed-local reproduction is recorded; local raw traversal
uses PreResolveChildren in both raw source scans; in-memory regression coverage
includes typed locals and source-options rejection; native build and relevant
bounded tests/format checks pass; a fresh independent reviewer assesses the diff
and evidence. Prepare a reviewable patch only. No commit, push, pin or deployed
runtime change occurs without separately authorized final actions.

Non-goals: change global NodeExtensions, skip actual syntax, catch/ignore arbitrary
exceptions, change specs/datasets/scoring, read benchmark candidates/solutions,
change the evaluator compiler, add dependencies, or broaden PBT capabilities.

## Inspected evidence

Native AGENTS.md and CLAUDE.md were read in the original owning checkout.
ContractScreenSourcePreparation parses resolve:false and calls RawDeclarations
and CheckSourceOptions before clearing method bodies/resolving. Both use general
Descendants. LocalVariable.Children emits its resolution-filled type for explicit
syntactic types; PreResolveChildren emits SyntacticType. NodeExtensions recursively
visits Children and dereferences a null. The generic example is a complete Child
method with var z: int := 0; added. Bodylessness is not the established cause.
The original pin and the current remote expecto head are the same base commit;
no existing fixed successor is available. No candidate source was inspected.

## Change table

| File/symbol | Change and necessity | Unmet without it | Validation |
| --- | --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs | Add a small local raw traversal over PreResolveChildren; use it only in RawDeclarations and the module options scan | Unresolved locals crash; dropping global nulls would still use wrong-phase AST views | Generic preparation regression, options rejection, independent source review |
| Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs | Add focused in-memory AST/source regressions with no directory/filesystem/native-compilation fixture | Complete-body simple arithmetic probes miss this bug and security guard regressions | Selected prebuilt tests only; trace setup/body/teardown and production paths |
| plan/2026-11-02-contract-screen-source-traversal.md, plan/INDEX.md | Record native ownership, evidence, validation and approval boundary | Recovery lacks an owner record | Final diff and Markdown-only scan |
| wiki/contract-screen-source-traversal.md, wiki/INDEX.md | Record the generic raw/resolved traversal failure and verified recovery limits | Future raw scans can repeat a known phase-boundary bug | Current-source evidence, independent focused tests and native probe records; link owning plan |

## Validation and prerequisites

Use the native .editorconfig and two-space C# style, preserving nullable/namespace
style. Inspect supported Makefile targets. Native production build is separate
from test execution: dotnet build Source/Dafny.sln (or narrower supported project
when evidence justifies it), with output under ignored native build directories
and logs under /workspace/tmp/fold-native-screen-recovery/. Reuse existing public
Z3/Boogie/tool resources without copying an installed toolchain. Do not alter the
original compiler tree. Build-time generated files must never be hand-edited.

Before running a test, trace all helpers and assembly setup. Selected tests must
use in-memory source/AST, fake or memory output and no TemporaryDirectory/mkdtemp,
real synchronization, runtime compilation, recursive hashing or bulk I/O. Use
--no-build --no-restore for final selected test execution after production build.
Do not run broad existing contract/runtime or integration test classes. Format
only touched files through supported native formatting tooling; preserve unrelated
formatting. Record every command, cwd, versions, exact source state, result and
skip reason here. No provider/network model call is part of validation.

The supported reproducible deployment build requires a clean reachable Git commit.
Root policy forbids creating commits unless the user requests one. First finish
this patch and verification. Then request only any necessary final commit/publish/
pin authorization with the concrete reviewed diff. Do not silently bypass clean
build receipts, disable native isolation, or relabel a dirty artifact as pinned.

## Risks and compatibility

PreResolveChildren must retain source-options visibility across nested raw nodes.
Post-resolution ReferenceIdentity must remain untouched. Validate the whole
preparation path so later raw scans cannot reintroduce the same crash. No wire
schema change is expected. The benchmark/evaluator compiler remains unchanged in
this preparation phase. Test coverage and actual runtime applicability are
separate evidence.

## Records and progress

- Native source investigation complete; original source trees preserved.
- Implementation, build/format/selected in-memory regressions and fresh review pending.
- [Integration recovery plan](/workspace/plan/2026-11-02-fold-child-screen-comparison.md).
- Generated artifacts/logs: /workspace/tmp/fold-native-screen-recovery/ and current
  integration recovery artifacts, never plan/wiki.
- 2026-11-02 implementation started after reading the owning instructions,
  source, project settings and supported Makefile targets. No reusable raw
  descendants helper exists in Source/; NodeExtensions.Descendants always uses
  resolved Children. The local helper will retain descendants-only semantics.
- Tests will instantiate DafnyOptions with null input/output, apply defaults,
  construct a hashed ContractSource snapshot and call the complete preparation
  path. ContractSourceSnapshot uses SnapshotFileSystem/StringReader; the source
  has no includes. Parser printing, XML, project/library and custom plugin paths
  are inactive. ProgramResolver performs AST resolution without verification or
  target compilation. The new class has no Setup inheritance, fixtures, assembly
  initialization or teardown; assembly CollectionBehavior disables parallelism.
  Each scenario uses one source under 300 characters and no filesystem writes.
- Next action: implement the local traversal and focused in-memory regressions,
  then coordinate the separate production and test-assembly builds with parent.

### Implementation checks, 2026-11-02

- Added private RawDescendants using PreResolveChildren, preserving the existing
  descendants-only enumeration pattern. Only RawDeclarations and the module
  options check call it. ReferenceIdentity still uses resolved Descendants;
  global NodeExtensions, proof boundaries and native wire models are unchanged.
- Added three independent memory scenarios with intention comments: a complete
  ordinary Child method with var z: int := 0; prepares through both discovery and
  projection, preserves its contract and reports its omitted source-body range;
  declaration options fail closed; module options fail closed. Here "generic"
  means synthetic source, not a generic type-parameter callable (unsupported by
  the existing screening policy). Each snapshot is under 300 characters.
- Traced options hashing to ProofOptionsHash (memory), rather than
  ProofToolchainHash (assembly reads). AnalyzeSpans/SourceFacts use AST/tokens.
  SnapshotFileSystem and null writers bound all source/diagnostic operations.
  There is no verification, solver process, target compilation, real
  synchronization, staging, copy, directory creation or teardown in these cases.
- Cwd for all checks: /workspace/tmp/fold-native-screen-recovery/dafny-native.
  Base remains 086ba8b875752dc791bf8dc2da9406d79b6bbae9, with source/test and this
  plan/index dirty; no commits. dotnet --version reports 8.0.133.
- git diff --check passed after the source/test edits.
- dotnet format whitespace --folder --no-restore --verify-no-changes --include
  Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs
  Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs failed
  immediately because the CLI rejects combining folder mode with no-restore.
  Retried the exact command without --no-restore: passed, exit 0. Folder mode
  formats source without loading projects or restoring dependencies. Temporary
  log: /workspace/tmp/fold-native-screen-recovery/native-format.log (empty success
  output; the initial CLI error is recorded here).
- Build prerequisite review: DafnyCore generates Parser/Scanner with Coco;
  DafnyTestGeneration references DafnyPipeline with standard-library/runtime
  embedded assets; test assembly references DafnyCore.Test/DafnyRuntime, whose
  JAR target may invoke Gradle. SkipFocusedTestAssets=true prevents copying Z3
  trees and Core.Test fixture content. Separate production/test assembly builds
  are coordinated by the parent; no build or tests run by implementation agent
  yet. The intended final execution is dotnet test
  Source/DafnyTestGeneration.Test --no-build --no-restore --filter
  FullyQualifiedName~ContractScreenSourcePreparationTests.
- Code/test diff settled and sent to parent for fresh independent verification.

### Parent build evidence

The separate production CLI build passed: `dotnet build Source/DafnyDriver/DafnyDriver.csproj -p:SkipFocusedTestAssets=true` from this native root. SDK 8.0.133 completed in 38.95 seconds with zero errors and eight existing nullable warnings outside touched code. Log: `/workspace/tmp/fold-native-screen-recovery/native-driver-build.log`.

One unchanged pinned Java runtime JAR (159,922 bytes) was reused to avoid an unrelated Gradle rebuild. Its SHA256 is `8e77497178f61f0ace33bf0b05ea678f9fb4daf6fb768272f3096195d46af662`. The reuse receipt remains outside plan/wiki; original compiler source stays clean.

A separate test-assembly build uses the existing `SkipFocusedTestAssets=true` option to avoid unrelated recursive Z3/fixture asset copies. It does not skip any selected regression assertion. The fresh reviewer independently traced the new class/preparation calls as in-memory and approved executable checks after builds settle. No native test, commit, push or pin action has occurred yet.

### Final targeted property control

After typed-local inspection/screen and three selected regressions passed, the fresh reviewer will run one additional benchmark-independent negative property control in the existing native validation phase. A typed-local Child source with requires x>=0 and impossible ensures y<x && y>x will be inspected, then screened at x=0. Require an admitted input and native unrealizable/negative property decision with matching binding and validated query provenance. This addresses actual bad-contract detection in the user's requested checker rather than only positive/admission paths. Fixed small new scratch JSON/log records only; no build, new container, directory fixture, provider, sync or source changes. No broader tests or retries are planned.

### Final verification and handoff

The selected test assembly build passed in 24.99 seconds with zero errors and 33 pre-existing warnings. Output is `Source/DafnyTestGeneration.Test/bin/Debug/net8.0/DafnyTestGeneration.Test.dll`. A fresh reviewer ran only `ContractScreenSourcePreparationTests` with --no-build --no-restore: all three facts passed in 2.13 seconds after the initial sandbox-only local socket denial was retried through approved execution. Both logs are preserved outside plan/wiki.

The same reviewer executed the trusted typed-local native inspection and two-case screen against the separate development CLI. Both exited 0 with empty stderr. x=0 was admissible/realizable; x=-1 was precondition-rejected. Binding, source-set hash, inputs, counts and four query terminal tuples validated. A final contradictory postcondition y<x && y>x at x=0 also completed, with admissible/unrealizable and validated UNSAT/SAT/UNSAT domain/property outcomes. There were no source edits, provider calls, runtime compilations, new directories or Docker containers in those checks.

Evidence: `/workspace/tmp/fold-native-screen-recovery/native-independent-validation.json`, `native-independent-negative-validation.json`, `native-independent-tests.log` and `native-independent-tests-retry.log`. The original compiler remains source-clean. The two-file source/test patch is `native-traversal.patch` (4,881 bytes, SHA256 `82c8cb336e7ea96b1b34fe7334177f9b1be5be74d47838f1b9e5949f299cc7fa`); reverse application check passed. The native wiki records the durable raw/resolved phase distinction.

All acceptance criteria for this source-preparation phase are complete. No commit, push, pin or deployed-image action has occurred. The integration operator has requested explicit authorization for a clean native commit, remote expecto publication and linked pin update, because the supported reproducible build requires a reachable clean commit and the user's root rules forbid unsolicited commits. The final publishing/deployment action remains outside this completed source-only phase until approved. The broader benchmark comparison remains incomplete; no screening efficacy conclusion is available.

### Authorized publication, 2026-11-02

The user explicitly approved the concrete request to commit this verified fix and its records, publish it to `prosyslab/dafny` branch `expecto`, update the linked integration/Cosyn pins, rebuild the agent image, and resume the comparison. The authorization was “ㅇㅋ 허용”. The six files in the change table are the entire native commit scope. Use a normal fast-forward push after checking the remote head; never force. Publication and downstream deployment receipts will be recorded in the integration recovery plan because the native commit cannot contain its own final hash. Source acceptance and independent checks above remain complete. Deployment and benchmark efficacy remain separate, unfinished integration work.
