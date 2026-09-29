# Exact native membership proof reuse within a campaign

Status: done (bounded campaign-local native membership proof reuse)

Parent: [sequential contract optimization](2026-09-29-sequential-contract-optimization.md).
This is local engine maintenance using public retained inputs, with no paid run.

## Objective and acceptance

Reuse a completed proof of the identical unconditional pure-value membership
query within one campaign. Retained h09 v4 initial-type queries6 and16 have the
same bytes and both return Unsat. Whole-heap initial certificates currently miss
this opportunity when unrelated mutable fields differ. This narrower reuse must
save a native query without replacing any new-state admission checks.

Acceptance requires actual repeated-state campaign evidence: distinct captured
heaps containing identical refined pure values need one membership proof and
separate state certificates. Changed values/types/source views cannot reuse a
different proof, and an invalid second state remains invalid/unchecked. Unsuccessful
or cancelled native queries never populate the cache. Existing scope, reference,
alias, omission, global inhabitation, host/runtime membership, source/dependency,
initial precondition, observed transition and trust checks remain mandatory.

Only completed Unsat native membership queries are reusable. The identity contains
the entire query, all diagnostic source contents and paths, insertion path and
query name; solver context is fixed by the campaign-local cache lifetime. Initial
and observed roles may share a proof only when that full identity agrees. Neither
Sat nor host-only admission supplies a reusable native proof.

A hit can save the next closed-query slot even when the cap is exhausted, but it
cannot outlive cancellation or the campaign deadline. Recheck those boundaries
after query construction and identity computation. Misses retain the original
shared cap and per-query deadline, including query-construction cost. Write a
distinct reuse receipt referencing the original native query/result hashes and
current role; never fabricate another solver result artifact.

Implementation refinement after stage2 acceptance: keep the helper private to
`ContractRuntimeCampaignRunner`. Its exact identity material is the full query
text; every ordered diagnostic source's raw path, canonical path and content;
the exact replacement source path and canonical path; and the query name. The
campaign-local lifetime fixes the remaining solver context. A hit receipt is
named `membership-proof-reuse-{initial|observed}-{sampleOrdinal}-{reuseOrdinal}.json`
and links the current role/identity to the original actual query and result
filenames and SHA-256 hashes. The monotonic reuse ordinal prevents two hits for
one sample/role from overwriting each other. No additional source or test file
is needed.

## Inspected evidence and existing solutions

`ContractRuntimeCampaignRunner` owns campaign-local `initialHeapCache`, per-clause
decisions, specification admission and `QueryHeapAsync`. `ContractInitialTypeProof`
already constructs a zero-input, no-requires query with exact typed assignments.
`ContractSourceSnapshot` validates closed source collections and content hashes.
Reuse these contracts; do not implement a new type checker or weaken native WD.
Exact retained evidence lives in
`/workspace/tmp/experiment/pbt-sequential-20260929/read-only-reuse-evidence.json`.

## Change table and boundaries

| File/symbol | Change, necessity, unmet behavior | Validation |
| --- | --- | --- |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs, campaign state and QueryHeapAsync | Add campaign-local exact native membership reuse and provenance receipts after existing per-state preparation; misses retain all current native gates. Without it unrelated heap changes consume duplicate proof slots. | Repeated distinct-state campaign, changed/invalid values, unchanged failure and deadline controls. |
| Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs | Add observable proof-count/state/certificate/receipt controls and negative state variants using existing Positive-field patterns. | Focused actual local compilation/campaign tests. |
| This plan and INDEX.md | Record exact implementation, commands, frozen source and outcomes, including failed attempts. | Root diff and independent review. |

If an internal helper and separate focused identity test are needed, amend this
table with exact files before creating them. Do not expose a new public API merely
to test implementation details. Engine implementation and proof invocation layers
only; no protocol/model/schema, specification, dataset, evaluator or scoring change.
No per-value extraction, cross-campaign persistence, callee heap capture, package,
budget/seed/request changes, live providers or commit.

## Validation and handoff

Use the root-coordinated exclusive native lane, tmux launched from
`/workspace/tmp/experiment`, `TMPDIR=/workspace/tmp`; test cwd
`/workspace/cosyn/dafny`. Artifacts go under
`/workspace/tmp/experiment/pbt-sequential-20260929/reuse/` with unique attempts.
Name new campaign controls `MembershipReuse` so this filter includes them:

```bash
dotnet test Source/DafnyDriver.Test --no-restore -m:1 \
  --filter 'FullyQualifiedName~MembershipReuse|FullyQualifiedName~ValidatesResidualInitialFieldConstraint|FullyQualifiedName~NativeConstruction|FullyQualifiedName~ReusesExactNativeInitialCertificateForHeapDecision|FullyQualifiedName~ObservedConstruction|FullyQualifiedName~HeapQueryBudgetExhaustionRemainsUnchecked|FullyQualifiedName~InitialFieldConstraintCalleeRemainsUnchecked|FullyQualifiedName~CapturedGhostHeap' \
  --logger 'console;verbosity=normal'
```

Expected: all selected tests pass; actual native invocation count decreases only
for identical successful proofs, state certificates remain distinct, and failures
do not become violations. Add precise bounded identity/cancellation controls to
the table and command before implementation if campaigns cannot exercise them.
Record source hashes, commands/tool versions, results and limits, then freeze
and release the lane to a fresh independent reviewer. Final supported formatting,
package/transport checks and unchanged six-case campaigns belong to root.

## Risks and status

Key risks are incomplete source identity, confusing a pure proof with an entire
heap certificate, deadline bypass on hits, and accounting reuse as another native
solver call. Required observable controls and explicit provenance address these.

Owner implementation is frozen for independent review. Source hashes are
`43182c75ac680543ea6de8cf7b25fc29808c4420e2a6333c87ef01aece95cf42`
for `ContractRuntimeCampaignRunner.cs` and
`647909130d01573f373e84316051ab16d064707c4367512a0b74464f96ea0e0c`
for `ContractRuntimeHeapTests.cs`. The final owner tmux run
`pbt-sequential-reuse-owner-20260929-a3` passed 21/21 selected Driver cases in
2m03s with no build warnings; log and exit0 are under
`/workspace/tmp/experiment/pbt-sequential-20260929/reuse/owner-attempt-03/`.
It covers a successful hit after the shared cap is exhausted, exact initial to
observed reuse, changed values, two identical unsuccessful proofs, a valid initial
proof followed by an invalid observed value, and campaign/source-view isolation.
The hit receipt names and hashes resolve to the original native artifacts.

Attempt01 retained 15 inherited passes and three generator-resolution failures
from calling `r.Int` in expression context. Attempt02 retained six fixture
failures after correcting that syntax: actual artifacts showed the specification
proof consumes the first shared slot, so the new tests had undercounted their
unchanged prerequisites. Attempt03 changed only those fixture caps and passed.
These are test corrections, not production budget changes. Deterministic direct
hit cancellation/deadline scheduling remains for the fresh reviewer; production
per-query and campaign deadline checks run after full identity hashing and again
before atomic receipt/cache publication. Root owns the existing contract-testing
wiki update after independent acceptance.

Fresh independent review accepted the exact frozen source. Canonical tmux
`pbt-sequential-reuse-independent-a2` ran the prescribed filter with exit0,
21/21 passing in2.0390minutes; sources matched before/after. An independent
artifact audit checked actual state/query/result counts and every referenced
proof hash, including initial-to-observed reuse with no fabricated native result.
Evidence: `pbt-sequential-20260929/independent-reuse/attempt-02/` and
`independent-reuse/artifact-audit-01/`.

The artifact-only cancellation control `cancel-hit-03` passed: a FIFO writer-open
marker established that the hit receipt write had begun after identity lookup,
with the original native proof already Unsat. Cancellation during the write
prevented final receipt publication/admission; only the original native result
existed. Its pending artifact remained a FIFO. Direct internal-timer scheduling
was not independently tested; linked-token handling and monotonic deadline checks
were inspected. Source/path/query-name/source-order mutation is static-only
coverage because the campaign fixes that context.

Preserved independent setup failures are not passing controls: attempt01 lost
wrapper exit bookkeeping after21 native passes because zsh's `status` variable
is read-only; cancel-hit01 used a rejected dot-segment path; cancel-hit02 reached
the target but a non-draining FIFO produced BrokenPipe. The corrected control
drains slowly and observes actual cancellation before publication. No repository
edits were needed after owner freeze. Durable findings:
[exact native membership proof reuse](../wiki/contract-testing.md#exact-native-membership-proof-reuse-2026-09-29).
