# Original logical dependencies of scalar runtime clauses

Status: done (bounded implementation and validation; broader coverage limits remain)

Owner: embedded Dafny repository. Parent: [runtime optimization](2026-09-29-inconclusive-runtime-optimization.md); root [optimization plan](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).

## Objective and acceptance

Permit a closed scalar original requires/ensures clause to use independently checked original logical dependency certificates under existing query/time budgets. A positive callee clause with a valid logical function contract must cease blocking a later actual goal failure. False function contracts, trust/bodyless/opaque restrictions, mismatched original identities, zero/exhausted budget, and native nonproof must remain unchecked. Do not certify foreign diagnostic AST expressions or synthetic definition equalities.

## Evidence and boundaries

The runner currently certifies only entry heap postcondition dependencies. Scalar clauses retain UnvalidatedCallees even when the closed query proves them. BindOriginalOwner replaces only Owner and leaves Expression in a detached program. Existing LogicalScope and CheckModuleAsync check original declarations, native WD/contracts/trust and source-bound certificates; ValidateSpecificationsAsync enforces shared MaxClosedQueries, timeout and campaign deadline. Reuse these paths. No protocol/specification/evaluator/dataset/scoring changes, no frozen requests/artifacts, no paid runs, no packages or commits.

## Exact change table

| Files/symbols | Change, necessity and unmet behavior without it | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeClauseDependencies.cs | Bind unique original declared requires/ensures by source and source-set hashes, owner identity, original path/URI, exact location and text; otherwise return no scope. Detached Expression never enters LogicalScope. | Mapping identity rejection controls plus native Driver cases |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs dependency branch and campaign-local scope cache | Reuse original scope validation for mapped scalar dependencies under existing shared budgets; retain all admission and decision gates. Coordinate shared file with root. | Positive, invalid contract, trust/opaque/bodyless and zero/exhausted budget Driver cases |
| Source/DafnyDriver.Test/ContractRuntimeClauseDependencyTests.cs | Meaningful native campaigns and direct identity mapping controls using original contracts, fixed generators and retained query artifacts. | Focused dotnet test filter |
| This plan; plan/INDEX.md and wiki updates by root | Preserve ownership/evidence and handoff; root maintains shared indexes. | Diff review |

## Validation and sequencing

Prepare source/tests while existing frozen campaigns own the native lane. Do not build or test until root grants the lane. Cwd /workspace/cosyn/dafny with TMPDIR=/workspace/tmp: `dotnet build Source/Dafny.sln --no-restore -m:1`; `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeClauseDependencyTests`; relevant existing Driver runtime and TestGeneration ContractSpecificationChecker tests after focused controls. Root coordinates formatting/full checks/fresh independent review and final historical reruns. Native local probes establish only bounded engine behavior, never historical detection. Missing/failed checks remain explicit.

## Risks and compatibility

Source preparation can shift token offsets and function descriptors substitute results. Map via authoritative metadata rather than diagnostic AST identity; reject ambiguous or transformed clause text. Call precondition locations often identify call sites, so unsupported mappings remain unchecked. Existing opaque/native visibility restrictions and function contracts are retained. Mapping cache is campaign-local, keyed by unique clause id, and original source context is immutable.

## Progress

Inspected repository instructions, parent plan/index/wiki index, transformer metadata/source maps, native specification checker, runner gates and existing Driver fixtures. Preserved all pre-existing changes. Root registered the child plan and granted source/test preparation. Scalar validation follows a successful closed decision, before the existing dependency gate, preserving queries for unsupported/undecided clauses and the original diagnostic reason on failed certification. The constructor owner currently has the native lane; a focused red run precedes runner integration if lane sequencing permits. No new verified durable findings yet; root owns eventual wiki consolidation.

### Red baseline

Root granted the single native lane after constructor controls completed. `tmux scalar-dependencies-red-20260929` ran the planned solution build and dedicated Driver filter. Build exit 0, zero warnings/errors, 26.75s; tests exit 1 with the two expected new-behavior failures and six passing controls, duration 40s. Positive original scalar callee remains `callee_contract_unvalidated` with one unchecked callee/zero valid samples; invalid original function contract has no certification artifact before integration. Logs and exit files: `/workspace/tmp/experiment/pbt-inconclusive-20260929/scalar-red*`. Tested base Dafny revision `060d5ad532f67d5367450689225274fb0a0243e7` plus preserved dirty working tree; .NET SDK 8.0.131. Existing sandbox blocks tmux socket; authorized local escalated tmux path succeeded. Minimal Runner integration added after the red positive was observed; green pending.

After the focused green suite, regression commands (same cwd/environment, sequential native lane): `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractRuntimePrefixTests|FullyQualifiedName~ClosedClauseWithUnvalidatedCalleeIsUnchecked|FullyQualifiedName~HeapQueryBudgetExhaustionRemainsUnchecked|FullyQualifiedName~UnvalidatedSpecificationCalleeRemainsUnchecked'`; `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~ContractSpecificationCheckerTests`. These exercise existing prefix admission, failed scalar/heap dependencies, shared budgets and original checker contract/trust/WD boundaries. Root owns full suites and independent checks.

### Green validation and handoff

`tmux scalar-dependencies-green-20260929`: solution build exit 0, zero warnings/errors, 34.43s; dedicated Driver filter 8/8 passed, zero skips, 40s. `tmux scalar-dependencies-regression-20260929`: existing Driver filter 9/9 passed, zero skips, 31s; native ContractSpecificationCheckerTests 59/59 passed, zero skips, 11s. Both regression exits 0. Logs/exits are `scalar-green*` and `scalar-regression-*` under the same experiment directory. `git diff --check` passed for the current entire dirty Dafny working tree. This green build also incorporated the quantifier owner's already-stable free-variable correction; those new dedicated quantifier controls are owned by that agent/root, not claimed here.

Implementation complete within the exact table. The new helper matches original source/set hash, authoritative owner and URI, clause kind, exact original location and text, and uniqueness. Its result comes exclusively from original Req/Ens lists. The Runner only attempts a mapped scalar logical certificate when an otherwise decided clause would hit the existing unvalidated-callee gate; it uses the existing native budget, per-query timeout, deadline, source-bound proof cache and trace artifacts. No uncertain mapping or failed certificate bypasses that gate. Existing heap handling and execution admission are unchanged. The positive native fixture now admits the callee and reports the actual goal postcondition failure; invalid original function contract produces failed native proof and remains unchecked. Trust, opaque nonproof, bodyless admission and budget controls remain conservative. The bodyless campaign is rejected before a valid execution; this is not evidence of successful native verification for bodyless definitions.

Reusable finding for root's shared wiki consolidation: a detached runtime clause's Owner can be rebound while its Expression remains foreign; original logical dependency certification must instead recover a unique source-bound original declared expression. Scalar closed-query success alone cannot validate contracts of functions used by that expression. The mapping's unsupported cases (synthetic definition equalities, invariant clauses, call-site-origin preconditions that cannot map exactly, transformed/ambiguous text) remain unchecked. Source paths above and the 8-case native/mapping suite are the evidence; applicability is this original-clause certification path only, verified 2026-09-29 on the recorded dirty revision. Root owns wiki/index writes.

Remaining: root-coordinated formatting, fresh independent verification and final unchanged historical six-case reruns. The lane has been released to root; no experiment-level detection or throughput claim is made. Keep this plan in-progress until those owning workflow checks finish; no technical implementation blocker remains.

## Integrated closure, 2026-09-29

Root completed the combined workflow on recorded source hashes at engine
HEAD060d5ad532f67d5367450689225274fb0a0243e7 plus preserved dirty changes.
V3 independent Driver32/Core62/Query83 controls and final v4 independent
Core33/Query21/Driver14 controls passed in fresh contexts. These overlap; they
are not an additive unique-test count. Final makeformat changed no source bytes;
supported `make build-dafny` passed0warnings/0errors and transport4/4 passed.
Frozen v4 manifest1628files SHA256
f7f02a2e14e08e45fb5696da3ad6fbf0d6e1f58ef815a65d6a807db9c34bd402.

All six unchanged historical campaigns finished, preserving original requests,
seeds and budgets. h13 reports two validated finite-prefix violating samples;
representative ordinal1 replays with exact violation equality, exit0 in60.352s.
The other cases retain documented proof/runtime/coverage limits; this bounded
implementation plan does not claim all historical cases or broader M1/M2 solved.
Root orchestration plan tracks next work. Failed attempts, first reviewer quota
interruption, independent replacement review, source patches and native baseline
comparison remain explicit in the [report](../../../pbt-draft-exp/inconclusive-followup.md)
and [root plan](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).
Reusable findings: [contract-testing knowledge](../wiki/contract-testing.md#exact-reduction-and-finite-prefix-counterexamples-2026-09-29).
No package additions, paid runs, original specification edits or commits.
