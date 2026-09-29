# Runtime classification decoding and deadline boundary

Status: done (bounded independent source/native and historical acceptance passed)

Parent: [sequential contract optimization](2026-09-29-sequential-contract-optimization.md).
This is bounded Dafny engine maintenance against retained public h11 artifacts,
not an evaluated or provider-backed run. Root owns shared plan/index/wiki records,
the immutable v6 toolchain, six-case orchestration, reporting, and final package.

## Objective and observable acceptance

Make post-execution campaign classification return within its existing deadline
without changing which runtime checks execute or which records they emit. Avoid
materializing a `Dictionary<string, ContractValue>` and a copied raw JSON string
for every successful compiled runtime check, while retaining exact value
validation whenever a record can contribute values to a query, rejection, callee
violation, or goal counterexample. Stop initial-state validation fail-closed when
the campaign deadline has already expired, before deserializing or preparing an
uncached heap state.

Acceptance requires all of the following:

- `ContractRuntimeCampaignRunner` visits every `check` and `checkpoint` in its
  original order and increments the same runtime/closed/unchecked evaluation
  counters. It does not suppress generated checks, observations, errors, or raw
  records.
- A successful runtime `check` uses its already parsed `JsonElement` metadata and
  never calls `GetRawText` or deserializes its `values` object. A failed runtime
  `check` deserializes that exact element once before classification, including
  entry rejections; a `checkpoint` deserializes it once before its existing cache,
  heap-evidence, or query path. The existing canonical serialized-dictionary
  cache material remains unchanged.
- Malformed or invalid values still fail on every false runtime record and every
  closed checkpoint where values are semantically consumed. Actual false entry
  checks, callee violations, call preconditions, invariants, and postconditions
  retain their present classification, exact captured `Values`, iteration,
  inputs, and ordering while within budget.
- Before entry-heap deserialization and before each costly initial-state phase
  (`initial_type_check`, dependency-scope construction, `PrepareInitial`,
  construction-scope preparation, construction planning, and a native membership
  query), the runner checks external cancellation first and then the existing
  campaign clock. Once a guard observes `ElapsedMilliseconds >=
  TimeoutMilliseconds`, classification records `campaign_timeout`, sets the
  existing unchecked-precondition gate, and starts no later initial phase for
  that sample. A phase that started within budget may finish after the boundary,
  but it cannot authorize a subsequent phase after expiry. The expired state
  cannot admit a valid input or goal violation.
- Cancellation still propagates through the existing token; the new deadline
  branch does not convert external cancellation to campaign timeout. Existing
  valid-input, alias/reference, type, source/visibility/dependency, trust, WD,
  proof-reuse, closed-query, finite-prefix, and classification-precedence gates
  remain in place.
- The original request budgets remain 240 seconds campaign, 5 seconds per
  sample, 16 closed queries, and 10 seconds per closed query. No benchmark,
  request, source, generator, draft, proof policy, evaluator, scoring, provider,
  dependency, or package changes are in scope.

## Inspected evidence and existing mechanisms

The retained immutable v5 h11 campaign is
`/workspace/tmp/experiment/pbt-sequential-20260929/cases/h11-mv-numbered-backup/optimized-v5`.
Its `run.json` records 13 traces, exit `-9`, `outer_timeout: true`, elapsed
270.892 seconds, and no `result.json`. The traces contain between 54,633 and
73,877 `check` records each (13 traces total); no retained trace contains a
`"passed":false` record. Their sizes are about 73.5--99.0 MB each.

`campaign-phases.jsonl` shows runtime evidence for sample 2 ending at
239,999.985 ms. Nevertheless `initial_type_check:2` starts at 240,035.570 ms,
and initial type checking/preparation/construction continues for samples 2--10;
the last `initial_construction_plan:10` completes at 268,070.319 ms. These are
public historical diagnostics, not proof that any h11 sample is valid.

The current runner parses each complete JSONL line once into a `JsonElement`,
then line 361 copies `values` through `GetRawText` and eagerly deserializes a new
dictionary for every `check` and `checkpoint`. Downstream inspection shows the
dictionary is consumed only by closed-checkpoint cache/query construction and by
returned false-record violations. The existing `queryCache` intentionally hashes
the canonical reserialized dictionary; switching its identity to raw JSON bytes
could distinguish property-order variants and alter closed-query budget use, so
that is rejected. The plan reuses the exact parsed `JsonElement` only as the lazy
deserialization source and keeps the cache identity unchanged.

The current initial-state path already treats a timed-out constructive check as
`Passed = null`, reason `campaign_timeout`, and therefore
`PreconditionUnchecked`. Moving that same fail-closed decision before initial
heap deserialization/preparation removes post-deadline work; it does not turn an
unknown input into a valid or rejected one. Existing `ContractQueryDeadline`,
linked cancellation tokens, query caps, and completed native membership proof
reuse remain unchanged.

The inspected engine revision has substantial pre-existing dirty source and test
work from the accepted sequential stages. In particular the runner and focused
Driver tests are modified or newly present. Preserve all of it; never reset,
replace, clean, or stage another task's changes.

## Exact change table

| Owner / exact file or symbol | Planned change and why it is necessary | Validation |
| --- | --- | --- |
| Dafny engine: `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`, per-sample initial validation and check/checkpoint loop | Add one local guard that first calls `cancellationToken.ThrowIfCancellationRequested()` and then checks the existing stopwatch/request budget. Invoke it before entry-heap deserialization and again immediately before each costly initial phase: direct type check, dependency scope, `PrepareInitial`, construction scope, construction plan, and initial native membership query. On expiry, retain `Passed = null`/`campaign_timeout`, skip all later initial phases, and enter the existing unchecked-precondition classification. Replace eager `GetRawText` plus dictionary deserialization with a per-record nullable dictionary and local accessor that deserializes the existing `values` `JsonElement` at most once. Invoke it for every false runtime record and every closed checkpoint, and pass the same dictionary through current cache, heap-evidence, solver, callee, and violation paths. Keep obligation iteration/counter updates and classification branches in their current order. | Bounded exact Driver cases below; diff inspection proves no producer, proof, model, budget, or classification-order edits. The v6 h11 phase log must show that after the first guard observes expiry no later initial phase begins, and the campaign must produce a result before its outer guard. |
| Existing tests, no planned edits: `Source/DafnyDriver.Test/ContractRuntimeCheckTests.cs`, `ContractRuntimeObservationTests.cs`, `ContractRuntimePrefixTests.cs`, `ContractRuntimeHeapTests.cs`, and `ContractRuntimeClauseDependencyTests.cs` | The selected behavioral cases cover successful and false runtime records, entry rejection, call preconditions, counter ordering, captured scalar/reference values, both closed-query polarities, unvalidated callees, finite-prefix counterexamples, initial heap decisions, and exact membership reuse. Producer code is unchanged and its recording suite was independently accepted in stage3b, so it is not repeated here. Adding an implementation-count test would only mirror the lazy accessor; use retained h11 classification evidence for the performance regression instead. | Run only the exact method/class filters below with all cases passing and no skip. Inspect false violations and prefix/heap results, not private allocation counts. |
| Owner evidence only: `/workspace/tmp/experiment/pbt-sequential-20260929-v6/classification/` | Record source hashes/diff, exact native commands and logs, test result files, and a compact retained-v5 count/phase receipt. Do not copy or alter the roughly 1 GB raw v5 traces. Root places immutable v6 campaign receipts in its own versioned case directories and links the h11 result/phase evidence back here if desired. | Hash source before/after; `git diff --check`; retained receipt names the v5 `run.json` and phase-log hashes and reproduces counts without claiming a campaign verdict. |
| This child plan only | Record implementation hashes, commands, outcomes, failures, limitations, and handoff after approval. Root alone updates `plan/INDEX.md` and wiki. | Plan/source diff review; status remains ready until root sends implementation approval. |

No other production or test file is planned. If implementation reveals that a
new helper, cache identity, payload format, or test seam is necessary, stop and
amend this plan before editing it.

## Semantic risks and controls

Lazy decoding must key off decision semantics, not merely the obligation kind.
Every `passed == false` runtime record is decoded even when its entry-precondition
values are not returned, retaining strict validation at the rejection boundary.
Every checkpoint eligible for the existing closed-SMT branch is decoded before
cache or query work. Successful runtime checks remain compiler-produced,
fully parsed JSON records; their unconsumed structured values do not authorize a
query or counterexample and need no object materialization.

The accessor must deserialize directly from `JsonElement` and retain the same
`ContractJson.Options`. It must not hash raw text, normalize properties itself,
drop duplicate properties, share dictionaries across records, or mutate the
record DOM. Heap evidence continues to extend only the checkpoint-local mutable
dictionary exactly where it does now.

Deadline expiry is checked after runtime-evidence collection because partial
evidence is already discarded by the existing cancellation/deadline path. The
same guard runs before heap deserialization and each subsequent costly initial
phase. It always throws caller cancellation before inspecting campaign expiry;
campaign expiry itself does not cancel or replace the caller token. A phase that
begins while time remains may finish, but its result is not passed into a later
phase after a guard observes expiry. The expired sample stays
precondition-unchecked; it cannot yield a valid finite prefix, even if later raw
records contain a false goal check. Raw false records and their ordering remain
available in the trace and obligation evaluation counts. Within-budget false
counterexamples and callee violations remain unchanged.

## Root-coordinated validation after review and lane grant

Source implementation may begin only after root reviews this plan. Native work
waits for the explicit exclusive lane after the frozen v5 h13 replay finishes.
Run build/tests in tmux from `/workspace/tmp/experiment`, with
`TMPDIR=/workspace/tmp`; test cwd is `/workspace/cosyn/dafny`. Record tmux session,
exact command, engine revision/dirty state, source hashes, .NET version, exit
status, duration, and complete logs under `B6/classification`.

Planned native commands:

```bash
dotnet build Source/Dafny.sln --no-restore -m:1

dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj \
  --no-build --no-restore -m:1 \
  --filter 'FullyQualifiedName~ReportsPostconditionViolation|FullyQualifiedName~RejectsEntryPrecondition|FullyQualifiedName~ReportsCallPrecondition|FullyQualifiedName~CountsObligationViolationsByClassification|FullyQualifiedName~CapturesGenericCalleeResult|FullyQualifiedName~CapturesReferenceFieldValues|FullyQualifiedName~ChecksClosedQuantifier|FullyQualifiedName~ClosedQueryDoesNotReportUnprovenClause|FullyQualifiedName~ClosedClauseWithUnvalidatedCalleeIsUnchecked|FullyQualifiedName~ChecksConjunctiveQuantifiedCalleePostcondition|FullyQualifiedName~ContractRuntimePrefixTests|FullyQualifiedName~AcceptsOriginalTwoStateHeapPostcondition|FullyQualifiedName~InvalidCalleeExcludesHeapDecision|FullyQualifiedName~UnvalidatedSpecificationCalleeRemainsUnchecked|FullyQualifiedName~MembershipReuseAdmitsDistinctHeapsAfterQueryCap|FullyQualifiedName~MembershipReuseSharesExactInitialProofWithObservedState|FullyQualifiedName~MembershipReuseKeepsInvalidLaterStateUnchecked|FullyQualifiedName~ContractRuntimeClauseDependencyTests' \
  --logger 'console;verbosity=normal'

git diff --check -- \
  Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs \
  plan/2026-09-29-runtime-classification-deadline.md
```

Expected: build has zero errors; every selected test passes without skips; diff
inspection shows only the runner and this plan changed by this child. Root owns
final formatting, supported Cosyn package build, transport checks, immutable v6
freeze, unchanged six-case requests, exact representative replay, aggregation,
and reporting. A fresh independent verifier must start from requirements and the
current repository state, inspect the implementation independently, and run its
own controls; this implementation context is not reused for verification.

## Historical measurement and handoff

Before native work, write a compact receipt under `B6/classification` containing
the SHA-256 hashes of v5 h11 `run.json` and `campaign-phases.jsonl`, exact trace
sizes/check counts, the 239,999.985 ms evidence boundary, and the last
268,070.319 ms post-deadline construction boundary. This is a retained-artifact
classification-cost baseline only.

No separate paid run or altered-budget campaign is authorized. The root-owned
unchanged v6 h11 campaign is the observable correction measurement: preserve all
64/5s/240s/16/10s settings, all partial traces, failures, phase logs, exit status,
and result presence. Acceptance requires a serialized result before the outer
guard and no later initial-validation phase starting after a deadline guard has
observed expiry; a phase begun within budget may finish after 240 seconds. It does
not require h11 to become valid, complete 64 samples, or find a violation.
Compare counters, classifications, violations, and exact selected h13 replay
sentinel against prior accepted semantics, with differences explained from newly
completed work rather than relabeled as improvements.

Keep this plan `in-progress` after implementation until owner checks and handoff
are recorded. Root decides shared wiki updates after independent acceptance. If
the only durable finding is the existing deadline invariant, record it here and
let root decide whether it belongs in `wiki/contract-testing.md`.

## Implementation and owner validation record

Root approved the exact runner-only implementation and exclusive native lane.
The first source attempt had SHA-256
`66f4eecaae3dc39e705fe8b2e5b2f9aff53cc75212c19ebf7a995c515400165a`.
The solution build passed with zero warnings/errors in 15.25 seconds, and the
bounded Driver selection passed 30/30 in 1.0632 minutes. Those logs are retained
separately as attempt 1 under `B6/classification`.

Owner diff review then found one boundary refinement within the approved design:
a synchronous initial phase could begin just before the campaign deadline,
finish after it, and pass its result directly to final validity or the next
phase. The first implementation guarded every phase start but did not uniformly
guard phase-result consumption. Root confirmed that adding the same
cancellation-first guard immediately after direct type checking, dependency
validation, `PrepareInitial`, construction scope validation, and construction
planning remains within the planned fail-closed boundary. Preserve attempt 1;
rebuild and rerun the same exact bounded filter as attempt 2 before freezing the
source. No new file, cache, model, producer, query, or classification change was
introduced.

Attempt 2 source SHA-256 is
`d1e0291efb310d680002492478682d836a3e0464f79d82c2dd9f3c9aafaac87f`.
The solution build passed again with zero warnings/errors in 11.05 seconds. The
same bounded Driver selection passed 30/30 with no skip in 1.0671 minutes.
`git diff --check` passes for the runner and this plan. Direct comparison with
the frozen v5 runner (SHA-256
`43182c75ac680543ea6de8cf7b25fc29808c4420e2a6333c87ef01aece95cf42`)
contains only the planned deadline guard/result checks and lazy record-value
decoding. Both attempts, hashes, commands, logs, and the retained v5 h11 baseline
are under `/workspace/tmp/experiment/pbt-sequential-20260929-v6/classification/`.

Owner implementation and native controls are complete; the exact source hash
above is frozen for fresh independent verification. The native lane was released
to root. Root still owns formatting, packaging, transport checks, immutable v6
freeze, unchanged six-case campaigns/replays, and shared documentation. This
child remains `in-progress` until independent acceptance and root's v6 h11
deadline/result evidence are recorded. No durable wiki update is written by this
owner; the deadline-boundary finding is recorded here for root's documentation
decision.

## Final independent acceptance and root measurement

Fresh independent review passes on the unchanged final runner hash: build exit0,
zero warnings/errors, Driver23/23, no skipped controls, and clean scoped diff
checks. Root formatting changes0/1087 C# files; supported package build and
transport4/4 pass. Frozen v6 manifest SHA-256 is
`cb4ef654053cd5b939295ae7e0455dda965141671c8b69153d21d75d397478fd`.

The unchanged h11 campaign now serializes an inconclusive result at252.039s,
exit0, no outer timeout. No initial phase starts at/after240000ms; the last
initial phase completes at233127.479ms. Samples3–11 retain campaign_timeout
diagnostics and precondition-unchecked status. Population runtimeErrors=0 is the
execution-error count, not absence of diagnostic entries. All12 raw sample
traces end with complete, but valid samples remain0 because initial/callee
validation is incomplete. Retained v5 remains exit-9/no result and36 late initial
phase starts. No budget or target contract changed.

The independent h13 audit finds the v6 ordinal1 replay request and complete result
byte-identical to the immutable v4 sentinel, including267 ordered obligations,
counters/reasons, captured inputs and the selected violation. Its173-record
certified prefix is byte-identical; post-endpoint timed-out tails differ and are
excluded from the validated evidence. Replay exit0; all expected violations
reproduced. Exact boundary cancellation remains static coverage rather than a
new dynamic timing fixture.

Evidence: `B6/independent-classification/verification-report.md`, native logs,
raw h11 campaign and h13 replay artifacts. Durable finding is now recorded in
[runtime classification boundaries](../wiki/contract-testing.md#runtime-classification-deadline-boundaries-2026-09-29).
No required bounded work remains. Caller-specific heap proof coverage is a
separate next implementation scope; this result does not assert historical h11
bug detection.
