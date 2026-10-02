# Call-specific PBT heap evidence, successful fact reuse and profiling

Status: done

## Objective and boundaries

Implement user-authorized immediately tractable call-state evidence, successful
source-bound fact reuse and runtime/native phase profiling. Parent scope and
fifteen fixed-request acceptance:
[root plan](../../../plan/2026-10-01-pbt-call-state-memo-profile.md).
Preserve original assertions, preconditions, type/WD checks, dependency proofs,
frames, exact request budgets, cancellation, finite-prefix evidence and existing
unrelated work. No guessed heap state, failed-proof reuse, benchmark changes,
general unbounded sequence solver, provider runs, dependencies or commits.

## Evidence and acceptance

Engine starts clean at 12065bbe8. Existing goal entry/return heap path, compiled
runtime old-value capture, exact membership proof reuse, specification checker,
ContractPhaseRecorder and finite-prefix boundary are the existing solutions.
Per-callee logical heap queries are the observed gap; h15 additionally has
original universal string/Bytes type obligations. Concrete precondition checks
must not be mislabeled as validation of an invalid universal function definition.

Each implementation agent adds a bounded child plan before changing its exact
files/symbols. Call-state agent owns transformer, heap checking, query helpers and
runner changes; profiling agent owns non-overlapping phase/bridge helpers and
supplies runner-hook changes for the call-state owner to apply. Shared native
build/test commands are serialized by the root coordinator. Agents do not edit
shared indexes/wiki simultaneously; root merges those records.

| Files | Change/necessity | Validation |
| --- | --- | --- |
| ContractRuntimeObligationTransformer.cs, ContractRuntimeHeapChecking.cs, ContractRuntimeCampaignRunner.cs and required helper/model files | Actual call-specific heap/query scope; exact successful fact reuse with separately checked call admission | Native/Driver true/false old/current/alias/frame/missing-state/dependency/invalidation/cancellation controls |
| ContractPhaseRecorder.cs, ContractRuntimeInstrumentation.cs or ContractStubRuntime.cs; profiling controls | Attribute preparation/runtime/record/classification/query costs without changing verdicts or observations | Timing/schema/counter controls and raw trace conservation |
| Child plans, plan/INDEX.md, wiki/contract-testing.md and wiki/INDEX.md | Exact symbols, evidence and remaining limits | Scope/diff/link review |

## Validation

Cwd /workspace/cosyn/dafny: `dotnet build Source/Dafny.sln --no-restore -m:1`;
affected Core/TestGeneration/Driver Contract tests with filters recorded in child
plans; `make format`. Cwd /workspace/cosyn: supported `make build-dafny` and
`COSYN_CONTRACT_INTEGRATION=1 python -m pytest -q -n 0 tests/test_goal_pbt_integration.py`.
Fresh independent verifier inspects current source and runs its own checks before
the root freezes binaries and reruns the fifteen exact original requests in tmux.

## Progress

Ready for child implementation plans; .NET SDK 8.0.131 and tmux are available.
Root owns plan/wiki index integration, native-lane scheduling and result reports.

Bounded engine implementation and fresh acceptance completed. Independent native
49/49, Driver16/16 and artifact13/13 pass; root supported final packaging has zero
warnings/errors and Cosyn integration4/4 passes. Exact evidence and hashes:
`/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/engine-acceptance.json`.
Root froze toolchain-final-01 (manifest37c11a36d3f70e669a25cf88d3a41ec670a7ac8dffed9238a29a27460f1d8c50)
and launched all15 original requests in tmux `pbt-optimization-20261001-final01`,
two serial lanes. Historical final outcomes/replays remain pending in the root
plan. Durable bounded findings added to
[contract-testing](../wiki/contract-testing.md#invocation-bound-callee-heaps-fact-reuse-and-profiles-2026-10-01)
and wiki index; historical per-callee unsupported claim is explicitly superseded.

## Final acceptance and closure

The actual h06 request exposed a second source-edit overlap; source instrumentation
now visits original quantifier expressions while logical dependency traversal
retains resolver split copies. Corrective independent native10/10 and Driver5/5
pass, supplementing the earlier49/16 checks and13 artifact controls. Supported
packaging02 and Cosyn integration4/4 pass. Root all15 common frozen02 runs and
seven representative replays are terminal and independently accepted: six
logical cases including new h06, nine exact violation-object checks covering
eight current obligations and the original h13 sentinel.

[Final report](../../../pbt-draft-exp/optimization-20261001.md),
[substantive receipt](/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/final-artifact-acceptance.json)
and [closure addendum](/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/final-artifact-acceptance-closure-addendum.json)
preserve source/frozen/result identities and limits. Root package integrity passes
4012 files/5062 checks/10 patch applications; original public requests and retained
copies are0444 and byte-identical. Source changes and plan/wiki indexes reviewed;
`git diff --check` passes. All engine processes/writes are terminal, no commits,
benchmark/specification changes, new dependencies or paid runs. Deferred general
sequence solving/type defects/topdown optimization are not claimed as completed.
