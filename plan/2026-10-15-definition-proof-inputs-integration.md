# Integrate native definition proof-input certificates

Status: done
Date: 2026-10-15
Owner: Cosyn native integration
Related: [Cosyn consumer](../../plan/2026-10-15-definition-proof-reuse.md),
[producer plan](../../../dafnyutils/dafny/plan/2026-10-15-definition-proof-inputs.md)

## Objective and acceptance

Integrate the independently owned native producer into Cosyn's canonical Dafny
runtime without altering the producer design or pre-existing native fixes.
Require exact frozen source correspondence, a local no-restore build, relevant
native tests and scoped formatting. Native proof-input certificates must preserve
ordinary unrelated method-body changes while invalidating relevant translated
inputs, retain warning qualification, and omit unsupported target projections.
No benchmark data/evaluator changes, dependencies, paid calls or commits.

## Inspected evidence

Read local AGENTS.md and CLAUDE.md, Makefile, owner plan/wiki indexes and working
tree. Native base revision dce5a96612b6516c5b180bb215d6eb3e3b430d5a has pre-existing
resource-statistics removal, internal error exits, trigger-variable fixes and
their tests. None of those files is part of the producer transfer. Core/Driver
test project assets already exist for offline builds. Generated sources are not
hand edited. At inspection the producer was not yet frozen; source transfer
waited for the final hashes and check receipts recorded below.

## Change table

| Native file | How/why and behavior unmet without change | Validation |
| --- | --- | --- |
| Source/DafnyCore/DefinitionAnalysis.cs | Integrate producer record/signature extension for optional proof-input document; consumer has no native authority without it | Exact producer hash, local Core tests |
| Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs (new) | Integrate complete translated input projection, native/tool policy binding and conservative unsupported handling | Exact producer hash, body/contract/recursion/visibility/option controls |
| Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs | Opt-in CLI flag/options, clean JSON stdout and retained stderr diagnostics | Exact producer hash, bounded Driver controls |
| Source/DafnyCore.Test/DefinitionProofInputsTests.cs (new) and Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs (new) | Preserve producer's generic in-memory/tiny-file regression controls | Scoped dotnet test, no provider or benchmark execution |
| plan/INDEX.md, this plan; wiki/definition-proof-inputs.md (new), wiki/INDEX.md | Record source provenance, local checks, conservative limits and host linkage | Markdown/link check and non-Markdown artifact scan |

## Validation commands

Cwd `/workspace/cosyn/dafny`, cached .NET/NuGet assets and existing solver/runtime
prerequisites. After producer freeze, compare untouched local producer baselines,
then copy only the five enumerated files and verify their SHA256s. Run
`dotnet build Source/Dafny.sln --no-restore` (no dependency installation),
`dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsTests`,
and `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsCommandTests`.
Run `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include`
with the five exact changed paths; broad `make format` would touch unrelated work.
Expected: source identity exact, local build/test/format success. If cached assets
or native sandbox prerequisites block a check, record it and use parent-approved
execution path; no skip is counted as pass. Parent owns final fresh independent
verification, image build and paid experiments.

## Compatibility, risks and approvals

The wire extension is optional; ordinary analysis remains compatible. The opt-in
producer supplies conservative authority, never proves a target or replaces SMT.
Existing global validation and target obligations stay mandatory. The user and
parent already authorized this cross-replica native integration. No new approval
needed unless a previously unknown destructive/dependency action is required.
Preserve all unrelated dirty source/tests/records and inspect final diff.

## Execution checkpoint

Producer frozen manifest accepted: `/workspace/tmp/definition-proof-reuse-20261015/native-benchmark/freeze.json`.
Producer reports Core21/21, Driver6/6 and scoped format success; these are
producer results, not local replica checks. The two existing target files match
producer HEAD baselines exactly, and three new files are absent. Recorded
pre-existing dirty-file hashes under maintenance scratch. Transferring the five
frozen source files, then building locally without further source edits.
Use serial `-m:1 -nr:false` with build commands; no parallel native builds.

## Local completion and frozen handoff

No-edit source/binary freeze:
`/workspace/tmp/definition-proof-reuse-20261015/native-cosyn/freeze.json`.
It contains exact five-file source hashes, local CLI/Core/Driver and test DLL/PDB
hashes, thirty preserved pre-existing dirty-file hashes, check logs and versions.
The two existing source files matched producer HEAD before transfer. No unplanned
tracked source changes resulted from the build, and all eight Python frozen
source/test hashes still match. No more native source edits or builds are pending.

Cwd `/workspace/cosyn/dafny`, .NET SDK8.0.131:

- `dotnet build Source/Dafny.sln --no-restore -m:1 -nr:false`: exit0,69.71seconds,
  zero errors, four warnings in untouched `DafnyTestGeneration.Test` sources
  (two unreachable-code, obsolete sequence accessor and synchronous cancellation).
  Log: native-cosyn/build.log under maintenance scratch above.
- Initial focused Core command aborted before test execution because the sandbox
  denied the .NET runner's local TCP listener. Original native-cosyn/core-tests.log
  retained. Narrow `require_escalated` reruns were automatically approved.
- `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 -nr:false --filter FullyQualifiedName~DefinitionProofInputsTests`:
  **21 passed,0failed,0skipped**; native-cosyn/core-tests-approved.log.
- `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 -nr:false --filter FullyQualifiedName~DefinitionProofInputsCommandTests`:
  **6passed,0failed,0skipped**; native-cosyn/driver-tests-approved.log.
- `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include`
  followed by the five exact source paths: exit0; generic workspace-loading
  warning recorded in native-cosyn/format.log.
- Local `Binaries/Dafny.dll` uses copied Core/Driver DLLs whose hashes equal the
  project CLI and both native-test output copies. Source hashes remain exactly
  the producer freeze; binary/PDB hashes are local build provenance.

Durable findings: [native proof-input integration](../wiki/definition-proof-inputs.md).
Parent and fresh independent verifier received the manifest. No provider calls,
images, dependency installs, commits or benchmark evaluations were run by this
owner.

## Final independent acceptance

The parent accepted the fresh independent report on 2026-10-15:
`/workspace/tmp/definition-proof-reuse-20261015/independent-cosyn/native-interface-verification-report.md`,
SHA256 `b04e6cccee621c343c0ca697024db24661442137ab93ce1a3d7b5a547a250fb7`.
The independent context reran Core **21/21** and Driver **6/6** without skips,
reviewed the producer/consumer authority boundary, exercised actual native/client
invalidation and warning controls, and verified the tiny caller with the real
`measure-complexity` path for all **3 mutations**. All 20 frozen native source
and binary identities matched after that review. This acceptance does not
erase the four untouched-source build warnings or the formatter loading warning.

At closure the five native and eight Python source hashes still match their
manifests. Only Markdown records were edited. The local native freeze and its
binary/PDB hashes are historical evidence: the parent's supported image build
began at 13:21 UTC and may regenerate those binaries. No later binary equality
is asserted. Owner implementation and independent acceptance are complete;
image and paid gates remain parent-owned. The host's default typecheck failure
(724 discovery errors), alongside passing canonical Pyright, remains disclosed
in the linked consumer plan.
