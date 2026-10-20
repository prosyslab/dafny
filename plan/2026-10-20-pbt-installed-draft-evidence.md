# Attribute runtime evidence to installed draft bodies

Status: done; independently verified development fix, active experiment unchanged.
Date: 2026-10-20

## Objective and acceptance

The user requests repeated inspection and repair of PBT interfaces while the authorized three-trial experiment runs. Current public native source confirms a generic attribution defect: a supplied draft for a helper with a concrete source body is validated but not installed, yet request membership still suppresses runtime type evidence and marks callee violations as drafted. Record the canonical symbols of bodies actually installed and use that collection for both decisions. Concrete source bodies must retain precedence and unused drafts must retain strict parsing and signature validation.

Acceptance: installed draft symbols distinguish actual substitution from an unused valid request; real helper bodies remain intact; malformed/signature-invalid unused drafts remain rejected; both downstream provenance decisions use the installed collection. Existing public constructor/deconstruction shape, full request/source fingerprints, native proof authority, verification coverage, target selection and diagnostic source mapping remain unchanged.

## Boundaries, evidence and compatibility

Owner: this native Dafny repository, baseline `8e5652221199a2ac4414d225266ef92d62965fd5`, initially clean. Read root/Cosyn/native instructions and native `CLAUDE.md`; no more specific instruction files or plan/wiki templates were found. Inspected `ContractRuntimeSourcePreparation.PrepareAsync`, `NeedsDraft`, runner drafted-symbol/type-evidence and callee-violation paths, source-preparation tests and their snapshot parser helpers. `ContractSourceSnapshot.ParseAsync` closes source reads over an in-memory dictionary; the selected tests neither create temporary directories nor compile generated campaigns. Inspect assembly initialization before extending/running them. Build artifacts are ordinary owner build output, separate from test-generated native campaigns.

This is development maintenance, not evaluation of a candidate. Read only current public generic source/tests and these records, not benchmark inputs, past solutions or private traces. The active csplit run uses an immutable image and frozen Python snapshot and must receive no updated source, guidance or observations. No live efficacy or causal explanation is inferred. Related records: [Cosyn refinement](../../plan/2026-10-20-pbt-observed-interface-refinement.md) and [root experiment](../../../plan/2026-10-20-csplit-pbt-main-experiment.md).

## Change table

| Exact file/symbol | Change, purpose and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan; `plan/INDEX.md` | Record owner scope, state and checks | Markdown/diff audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs::ContractRuntimePreparedSources`, `PrepareAsync` | Add a non-null empty-by-default `InstalledDraftSymbols` init property outside the record primary constructor. Collect canonical target names only after actual helper/body/attribute edits are queued; publish a copied set. Preserve current target/parse/marker/signature/NeedsDraft order | In-memory source-preparation cases and API/callsite review |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` draftedSymbols and callee violation creation | Use prepared installed symbols for runtime type-evidence and violation attribution; leave every other request draft use and fingerprint/certificate path intact | Source review plus native build; no costly new generated-campaign fixture |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs` | Extend real-body and replacement controls with exact installed-set assertions; add a small unused-invalid-draft regression only if not already covered | One scenario per test, memory snapshots only, trace helpers first |
| `wiki/pbt-installed-draft-evidence.md`, `wiki/INDEX.md` | Record generic source-precedence/provenance contract, evidence, limits and originating plan | Fresh independent review and links; no benchmark data |

## Validation and approvals

Run from this repository: `make exe` (supported owner native build, existing dependencies only), `dotnet test Source/DafnyTestGeneration.Test --no-build --filter "FullyQualifiedName~DafnyTestGeneration.Test.ContractRuntimeSourcePreparationTests"` (selected memory-only class), and `make format` (owner C# whitespace target), then `git diff --check`. Inspect formatter diff and preserve unrelated work. If a needed rebuild is required after a relevant change, record it; never run a generated-campaign test merely for broad coverage. Final independent verifier must start from requirements/current public source in a fresh context, inspect trust/fingerprint unchanged and run its own appropriate scoped checks. Build and formatting logs belong under `/workspace/tmp/pbt-installed-draft-evidence-20261020/`; never under plan/wiki.

No new dependency, paid call, image rebuild/retag, commit, protocol/specification/evaluator/scoring change or remote publication is needed. The user authorized interface repairs; no further approval is required for this reversible source fix. Root/Cosyn plan links will be updated before implementation. Default tests or command exits alone do not establish a native proof or benchmark success.

## Owner implementation evidence before independent acceptance

Implementation is complete at native revision `8e5652221199a2ac4414d225266ef92d62965fd5` with only the three planned C# files and this plan/index modified. `ContractRuntimePreparedSources` now exposes an empty-by-default non-null `InstalledDraftSymbols` init property outside its primary constructor. Preparation records a copied set of canonical `target.FullDafnyName` values only after helper/body/attribute edits for a real substitution have been queued. The runner uses that prepared set for runtime type evidence and callee `Draft` attribution; all other `request.Drafts` uses, source hashes, certificates, proof inputs, trust and target selection remain unchanged by diff review.

The test call path was traced before execution: the selected class has no fixture, its `Prepare` and `Resolve` helpers call `ContractSourceSnapshot.ParseAsync`, and that parser closes reads over a snapshot dictionary with `StringReader`; no temporary directory, campaign compilation or native subprocess is reached. The replacement control now requires exactly `M.Helper`, the concrete-body control requires an empty installed set, and a separate concrete-body case proves an invalid unused draft signature is still rejected after parse/marker handling and before `NeedsDraft`.

Validation from `/workspace/cosyn/dafny`:

- Two sandboxed `make exe` attempts, `dotnet build Source/Dafny.sln -v:diag`, `dotnet build Source/Dafny.sln --no-restore`, and `dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore` each exited in under one second during MSBuild project evaluation with zero warnings, zero errors and no usable compiler diagnostic. The bounded diagnostic log located the silent failure in `_FilterRestoreGraphProjectInputItems` / `Dafny.csproj (_IsProjectRestoreSupported)`; this establishes a sandbox-only build failure, not shared-build contention. The same authorized `make exe` outside that sandbox passed in 25.63 seconds with zero errors and four warnings in untouched `ContractRuntimeProfile.cs`, `PbtObservation.cs` and `ContractPhaseTimingTests.cs`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter "FullyQualifiedName~DafnyTestGeneration.Test.ContractRuntimeSourcePreparationTests"` passed all 20 selected in-memory cases with no skips in 157 ms.
- `make format` exited zero; it reported a workspace-loading warning and produced no unrelated tracked edits. `git diff --check` passed afterward.
- Recursive `plan/` and `wiki/` inspection found no non-Markdown files. No image, dependency, paid provider call, experiment, campaign fixture, commit or wiki edit was made.

Logs are under `/workspace/tmp/pbt-installed-draft-evidence-20261020/`, including the successful `make-exe-escalated.log`, `source-preparation-tests.log` and `make-format.log`, plus the failed sandbox diagnostics. At this owner handoff, wiki publication and fresh independent acceptance were pending; their completed results are recorded below.

## Independent acceptance and closure

Fresh independent review accepted the current three-file change, including canonical `FullDafnyName` agreement between installed symbols, clause-owner/dependency evidence and emitted callee obligations. All unused-draft target/parse/marker/signature checks still precede `NeedsDraft`. Public positional constructor/deconstruction, source mapping and all source/request/fingerprint/proof/certificate/trust/selection bindings remain intact. Independent approved `make exe` passed in 10.15 seconds with zero errors/zero warnings, the selected memory-only class passed 20/20 with no skips, `dotnet format whitespace --verify-no-changes` passed with a workspace-load warning and `git diff --check` passed. Initial sandbox build failed without a diagnostic and sandbox VSTest could not open its localhost socket; approved reruns passed. These facts do not establish shared build contention. Full audit: `/workspace/tmp/pbt-installed-draft-evidence-20261020/verify.md`.

Durable findings: [installed draft provenance](../wiki/pbt-installed-draft-evidence.md), indexed in `wiki/INDEX.md`. Source preparation/provenance acceptance is complete; no generated-campaign/native generator-proof/benchmark/provider/image check was run or claimed. No dependency, commit or live treatment change was made. Root/Cosyn observation plans continue to own the running experiment and separate wire-interface refinement. Remaining handoff: preserve this uncommitted development patch and scratch logs for future integration; a future live comparison needs its own authorized scope.
