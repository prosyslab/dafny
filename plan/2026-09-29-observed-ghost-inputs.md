# Captured ghost inputs in observed goal heap queries

Status: done (bounded captured-input goal heap support; independently accepted)

Parent: [sequential contract optimization](2026-09-29-sequential-contract-optimization.md).
This is stage2 local engine maintenance using public retained historical inputs.
Implementation followed stage1 acceptance, root registration and announcement,
then independent stage2 verification on the serialized native lane.

## Objective and observable acceptance

Allow an original goal method's supported, fully captured ghost inputs to enter
its existing fixed entry/return heap postcondition query. A captured ghost value
is a concrete input under its original declared type; it is not guessed from
current heap state or substituted for old state. The original P, Q, !Q, native
definedness, source/dependency, frame and callee-trust checks remain mandatory.

Acceptance:

1. A goal with a ghost scalar input, mutable reference and Q using both the
   captured scalar and old(field) gets opposite native verdicts for matching and
   mismatching final states; the Driver reports a valid original counterexample
   only after every preceding admission gate passes.
2. Missing ghost inputs, unsupported types, ghost outputs, inconsistent aliases,
   native undefinedness and unvalidated specification callees remain rejected or
   unchecked. No inferred replacement for an absent input is permitted.
3. Aliased versus distinct ghost reference inputs preserve exact object identity
   and old/current field values. Original scope/hash/frame/topology controls pass.
4. Public ContractHarnessBuilder.Prepare behavior remains unchanged, including
   its rejection of ordinary ghost-input execution. Only an internal preparation
   route for captured observations accepts supported ghost inputs.
5. Replaying retained h15 ordinal0 produces actual entry/return captures and can
   prepare the original heap-query path when all state is available. The replay is
   unusable for this query if it lacks a complete return capture; record that limit
   rather than filling final state from entry state. Record native outcomes under
   original query/time budgets; do not promise a detected historical implementation
   bug. Existing v4 has only an entry heap, so it cannot substitute for a newly
   captured return heap.

## Evidence, existing solution and non-goals

Read-only design is retained at
`/workspace/tmp/experiment/pbt-sequential-20260929/heap-design.md`.
Transformer.Check currently requires all goal ins/outs to be non-ghost before
assigning EntryHeapPostcondition. Public HarnessBuilder.Prepare.ValidateSignature
also rejects ghost formals. Removing only the transformer guard cannot create a
usable query. PrepareInitial already has a separate original-input path.

Reuse ContractHeapFactory's exact references/aliases/declared types/omission audit,
ContractHeapPlan's initial/final assignments, ContractQueryBuilder's exact Ens
selection and ContractRuntimeCampaignRunner.DecideHeapAsync's existing gates.
No new query/heap algorithm, wire schema, benchmark source, generator, helper draft,
sample/seed/query/time budget, dependency/package, provider run or commit.

Ghost outputs remain unsupported by this observed path. Callee heap clauses need
separate call-entry/call-return snapshots, receiver/formal/actual/occurrence
identity and original-owner/frame checks; this slice does not fabricate them.
Retained h07/h09 can remain blocked at their earlier initial/callee gates.
h15 is an assertion-only unfinished target and must remain distinguished from
implemented historical mismatches even if its original Q is decided.

## Exact change table

| File/symbol | Change, necessity and unmet behavior | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs, Check | Permit a ghost goal input only when its type is compilable and its exact formal belongs to the captured/deghosted variables set. Keep outputs non-ghost/compilable and all existing postcondition, owner, heap/ref, type/fresh, source and callee checks. | Captured/missing/unavailable inputs and original-Ens eligibility; Driver controls. |
| Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs, Prepare/ValidateSignature | Add a named internal `PrepareObservedHeap` route permitting supported ghost inputs while still validating every output and rejecting ghost outputs; keep public preparation, reachable preparation and initial-only semantics unchanged. Do not expose this as a caller-selectable Boolean that can leak into ordinary execution. | Existing public ghost-input rejection, ghost-output/unsupported rejection, reachable-mode rejection. |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs, Prepare | Use only `PrepareObservedHeap`; retain unit-mode rejection, exact SelectFormals validation for every input/output, both request validations, heap-shape validation and exact captured heaps. | Native both polarities, missing ghost value, alias and WD controls. |
| Source/DafnyTestGeneration.Test/ContractRuntimeHeapQueryTests.cs | Add native controls for original captured ghost inputs, mutations, aliasing, missing state and WD. | Focused native suite plus existing heap/query gates. |
| Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs | Add complete campaign positive/negative and unvalidated-spec-callee controls using captured ghost inputs; counterexample evidence includes ghost input and initial/final cells. | Focused real local compilation/campaign tests with no provider. |
| This plan | Record inspected state, exact commands, source identities, observed outcomes and limits. | Root diff and final plan review. |

Core specifications and dataset/scoring remain unchanged. TestGeneration owns
eligibility/preparation; Driver is touched only for tests unless an inspected
failure requires a recorded plan amendment before implementation.

## Validation commands and sequence

All native work is serialized by root, in tmux launched from
`/workspace/tmp/experiment`, command cwd `/workspace/cosyn/dafny`,
`TMPDIR=/workspace/tmp`. Artifacts live at
`/workspace/tmp/experiment/pbt-sequential-20260929/heap/`.

```bash
dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 \
  --filter 'FullyQualifiedName~ContractRuntimeHeapQueryTests|FullyQualifiedName~ContractGhostInitialValidityTests' \
  --logger 'console;verbosity=normal'
dotnet test Source/DafnyDriver.Test --no-restore -m:1 \
  --filter 'FullyQualifiedName~CapturedGhostHeap|FullyQualifiedName~ObservedConstruction|FullyQualifiedName~OriginalTwoStateHeapPostcondition|FullyQualifiedName~HeapQueryBudgetExhaustionRemainsUnchecked|FullyQualifiedName~UnvalidatedSpecificationCalleeRemainsUnchecked|FullyQualifiedName~ReportsUnavailableGhostOutput' \
  --logger 'console;verbosity=normal'
```

Name new Driver controls with CapturedGhostHeap so the declared filter includes
them. Expected outcome: all selected tests pass, both original native polarities
are exercised, and invalid trust/WD/state does not become a violation.
Replay h15 with only sampleCount=1 and replayOrdinal=0 changed from the exact
retained request; keep seed/generator/drafts/sources and5s/240s/16/10s budgets.
Check all replayed input values against retained ordinal0. Retain newly observed
entry/return heaps and every native query/result, rather than inferring a missing
return heap from the entry state. Require a complete record and a real return
`heap_capture` before calling the query available; otherwise record the replay as
still missing final-state evidence. This is a diagnostic replay, not the final64
sample comparison. No sample value or original source may be edited. Root
owns final six-case campaigns, h13 replay, formatting/package/transport and a fresh
independent review context after implementation stops.

## Risks, progress and handoff

Primary risks: a permissive preparation flag leaking into ordinary execution;
accepting ghost inputs that were never captured; confusing pre-state ghost
values with current mutable fields; losing alias identity; treating an observed
Q failure as valid without initial/callee/type/source gates. Tests above address
these boundaries.

Read-only inspection confirmed the current boundary: transformer heap eligibility
requires every goal formal to be non-ghost; `ContractHarnessBuilder.ValidateSignature`
rejects ghost formals in ordinary preparation while its initial-only path has
different output semantics; `ContractRuntimeHeapChecking.Prepare` already selects
every exact formal, validates both initial and final requests, validates topology,
reifies old/current observations separately and checks the original frame. The
named observed route is therefore the smallest preparation extension and must not
reuse initial-only preparation as a proxy for a complete transition.

Implementation is frozen in the five files in the change table. The stable file
hash manifest is
`/workspace/tmp/experiment/pbt-sequential-20260929/heap/source-ready.sha256`
at repository HEAD `060d5ad532f67d5367450689225274fb0a0243e7` (with pre-existing
dirty work preserved). The implementation adds the internal named
`PrepareObservedHeap` mode, routes only complete observed transitions through
it, and permits a goal ghost input in heap eligibility only when the exact
formal is among the captured/deghosted variables. Outputs remain non-ghost and
all other gates remain in place.

Owner validation, run serially in tmux with `TMPDIR=/workspace/tmp`, passed:

- TestGeneration filter: 133/133, 17.33 seconds, log `heap/testgeneration.log`.
- Driver filter: 11/11, 59.68 seconds, log `heap/driver-final.log`, exit record
  `heap/driver-final.exit`. The retained `heap/driver.log` first attempt showed
  that a direct `old` expression was runtime-compilable and therefore did not
  test the native route; the fixture was corrected to use the original
  two-state predicate wrapper. The retained `heap/driver-rerun.log` then exposed
  one unrelated over-strong `Population.Valid == 0` assertion for an unchecked
  unvalidated-callee case; removing only that assertion produced the final
  11/11 result without weakening the required closed-SMT assertions.
- `make exe` rebuilt the CLI from the frozen source with zero warnings/errors;
  see `heap/build-cli.log` and `heap/build-cli.sha256`. The wrapper attempted to
  assign zsh's read-only `status` variable after the successful build, so it did
  not create a separate exit file; the complete MSBuild log records success.

The first h15 replay is retained at `heap/h15-ordinal0-stale-cli/` and is not a
stage2 result: its standalone CLI assemblies predated the source freeze and it
captured only entry state. After rebuilding, the exact derived request
`heap/h15-ordinal0-request.json` (SHA-256
`8662594f2eb2c4d391f2437e7d5159aa7d3fb3f842f385b82266a7961775e731`)
changed only `sampleCount` 64 to 1 and `replayOrdinal` null to 0. The corrected
run at `heap/h15-ordinal0-stage2/` exited 0 and captured 30 inputs exactly equal
to immutable v4 ordinal0, a 17-object entry heap, and a separate actual
17-object return heap with `exit = 0`; its trace includes `complete`. Both heap
payloads happen to have the same canonical hash because this unfinished
assertion-only candidate made no mutation; the return was captured independently
and was not inferred from entry state.

The h15 goal became `closed_smt`, confirming stage2 eligibility, but remained
unchecked at the existing `callee_contract_unvalidated` trust gate. The logical
specification proof (`specification-query-10.result.json`) verified 11 items and
reported three type errors, so no goal native proof was launched and no
historical implementation bug was established. Exact hashes, record counts,
captures, population and trust result are in
`heap/h15-stage2-summary.json`. This preserves the source, well-definedness,
trust, dependency and budget gates required by this plan.

Fresh independent review accepted the frozen snapshot with no findings:
TestGeneration133/133 (20.5814s), Driver12/12 (59.8638s, including the additional
unsupported ordinal-input control), source hashes before/after, unchanged binaries
and clean diff checks. Exact commands/logs are in
`pbt-sequential-20260929/independent-heap/attempt-1/`; session
`pbt-heap-independent-a1`. The reviewer independently audited h15 request/input
identity, actual captures, executable hashes and the original failed trust gate.

The corrected derived summary is `heap/h15-stage2-summary-corrected.json`:
the16-query budget is campaign-wide, not per sample. The first summary's mistaken
metadata label and all raw evidence remain retained. Bounded acceptance covers
the supported observed-input path; it does not assert h15 Q has been decided or
that callee heap snapshots exist. Durable findings are recorded in
[captured ghost goal heap observations](../wiki/contract-testing.md#captured-ghost-goal-heap-observations-2026-09-29).
