# Sequential historical contract-checking optimization

Status: done (bounded sequential stages and fixed-request acceptance)

Owner: embedded Dafny implementation/proof toolchain. Parent: [root continuation](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).
User authorizes ordered stages: quantified relation/proof composition, certified heap/ghost query coverage, exact membership proof reuse and measured runtime cost. This is local engine development using public retained historical artifacts, not a model evaluation. Preserve all pre-existing source and plans.

## Acceptance and boundaries

Each stage must demonstrate its general semantics with native positive/negative controls and retained diagnostics before the next implementation stage begins. Preserve original assertion, type/WD, source/visibility/dependency checks and original budgets. No benchmark inputs/contracts/drafts, provider experiment, dependencies, commits, expansion cap increases/resets, or guessed historical witnesses. Current h13 exact replay is a regression sentinel. Remaining unsupported fragments stay explicit.

## Change table

| Stage / exact candidate symbols | Why needed and unmet behavior | Validation |
| --- | --- | --- |
| 1 PartialEvaluatorEngine/Visitor, ContractExpressionReducer, ContractSolver; focused witness Core/native tests | h07/h08 nested predicates and unknown-length witnesses remain residual or unproved natively | Child plan must select exact algorithm/files and controls before edits; retained h07/h08 both polarities |
| 2 ContractRuntimeObligationTransformer.Check, runtime heap checking/query builders | Goal ghost formal and callee old/current heap coverage gaps prevent query construction | Child plan after stage1 acceptance; captured/missing/alias/WD/trust controls |
| 3 Initial certificate/campaign caches and runtime transport/recording | Repeated pure memberships consume shared query cap, repeated records delay h11 execution | Child plan after stage2; identity/context invalidation controls, exact ordered trace equality and measured cost |
| 4 `ContractRuntimeCampaignRunner` record decoding and initial-state deadline boundaries | Frozen v5 h11 emits more records but is killed before returning its result; preserve all consumed values and fail closed after expiry | [Classification deadline child](2026-09-29-runtime-classification-deadline.md), bounded existing Driver controls, fresh review, unchanged v6 h11 and h13 replay |
| This plan/child plans and INDEX.md; wiki/contract-testing.md and INDEX.md | Preserve owner decisions, validation and evidence limits | Cross-links, exact commands/hashes, final diff review |

## Validation

One root-coordinated native lane. Cwd engine for solution build and focused dotnet tests: `dotnet build Source/Dafny.sln --no-restore -m:1`; exact test filters are recorded by each child before running. Local experiments use tmux launched in /workspace/tmp/experiment with TMPDIR=/workspace/tmp. Root owns final makeformat, supported Cosyn makebuild-dafny, transport integration tests, immutable freeze and unchanged six-case campaigns/replays. Fresh independent reviewer per implementation stage starts from requirements/current state, without implementation-agent conclusions.

## Evidence and risks

Prior v4 resolves h13 finite-prefix invariant evidence but h07/h09/h11/h15 remain inconclusive and h08's main output condition is decided3/64. Current raw queries show h07/h08 depth residuals without native timeout; h09 has PE-true/original-nonproof and recursive sum/sequence residuals. Heap support lacks some ghost and callee state routes. h11 computation/recording cost and native classification are distinct. Relevant knowledge: [contract testing](../wiki/contract-testing.md#exact-reduction-and-finite-prefix-counterexamples-2026-09-29).

Stage1 starts with read-only design. A precise child plan is required before source/test edits; later stages are sequential, not parallel code changes. No changes to plan authority or restrictions are authorized.

Stage 1a now has a ready child plan: [compositional checked proofs](2026-09-29-compositional-contract-proofs.md). It adds an explicit native proof composition path with shared global budgets and retains ordinary reduction defaults. Its implementation and native validation precede any later-stage source changes.

Stage2's [captured ghost input plan](2026-09-29-observed-ghost-inputs.md) is drafted
from read-only source inspection. No stage2 implementation is authorized to start
until stage1 acceptance and independent verification complete. The first slice
adds goal observation support; callee heap capture remains an explicit separate
coverage limit.

Stage1a is accepted after its final independent ordering rerun: Core93/query87,
required h07 positive/negative gates, source hashes and diff checks pass. The
extra negated-witness3s timeout matches immutable v4 and remains an explicit
coverage limit; h08 unknown-length sequence relations remain nonproof. Evidence:
`pbt-sequential-20260929/independent-quantifier/ordering-*`. Stage2 implementation
and its exclusive native lane are now granted under the captured-ghost child.

The next [exact membership reuse child](2026-09-29-exact-membership-proof-reuse.md)
is ready from inspected current code and retained query identities. It permits
no implementation until stage2 independent acceptance; its cache replaces only
identical completed native pure-membership proofs, with new-state checks intact.

Stage2 independently accepted: native133/Driver12, source before/after identity,
binary identity and diff checks pass. h15 now has real entry/return capture and
closed-query eligibility, but original seq<char>/seq<RawByte> dependency failures
keep Q unchecked. The child is done with those bounds. Root announced and granted
stage3a source/native lane to the exact membership reuse owner.

Stage3b has a read-only [ordered runtime fragment plan](2026-09-29-ordered-runtime-check-fragments.md).
It is registered but implementation/measurements wait for independent stage3a
acceptance. The paired measurement must use the new generated fragment calls,
preserve embedded original-source metadata and every non-argument code span, and
report all fixed repetitions with exact common-prefix bytes and CPU/wall cost.

Stage3a independently accepted: focused21/21, raw artifact audit and deterministic
external cancellation during hit receipt writing pass; frozen sources unchanged.
Internal timer scheduling and campaign-immutable identity fields remain explicitly
static-only coverage. The child/wiki are closed with those limits. Root announced
and granted stage3b implementation/native lane; no final campaigns started yet.

Runtime measurement preflight correction: independent source inspection and root
raw-occurrence counting both find682 executable `Bridge.Check` calls across649
physical lines, plus268 `Bridge.Checkpoint` calls. The intended all-and-only
argument rewrite therefore covers950calls; the earlier917 count confused lines
with calls. This corrects derived metadata, without changing generated execution,
original source metadata, sample inputs, budgets or measurement scope. Require
explicit before/after metadata hashes and fresh attempt directories so reruns
cannot overwrite logs or append old traces. Measurements have not run yet.

Stage3b and its child/wiki are now closed after fresh independent22/22 and raw
byte/provenance audit acceptance. Final formatter changed no C# source; package
build has0warnings/0errors and transport4/4 passes. Exact pre-format source bytes
and hashes are retained. Root script failure-boundary controls are being reviewed
before the final immutable freeze and unchanged six-case campaigns.

Frozen v5 h11 exposed a post-execution classification regression:13 larger traces
were captured, but initial preparation continued after the240s deadline and no
result was returned before the270s outer kill. Add a bounded child for redundant
record decoding/expired initial preparation, with focused native semantic controls
and fresh independent review. Preserve v5 and original budgets; root owns a
separate corrected v6 freeze and unchanged six-case rerun. Current v5 native work
must finish before this child starts native validation.

All four stages are now independently accepted within their stated scope.
Stage4 Driver23/23, unchanged h11 deadline/result audit, and exact h13 v4 sentinel
replay pass; see the [classification child](2026-09-29-runtime-classification-deadline.md).
Final v6 package build/format/transport4/4 pass. Its immutable manifest is
`cb4ef654053cd5b939295ae7e0455dda965141671c8b69153d21d75d397478fd`.
All six unchanged root campaigns return results. h13 retains two violating
samples; no additional historical case is detected. h07/h09/h11/h15 remain
inconclusive, and h08 core goal coverage is3/64. The original v5 h11 failed
attempt and every earlier failed control remain preserved.

The bounded acceptance allows explicit remaining coverage limits. Next work is
per-callee two-state heap capture with reference/frame/WD/trust checks, checked
unknown-length sequence witnesses, and concrete call-specific dependency proof
where universal original specification well-formedness fails. No original
benchmark contract was changed to remove these limits. Durable stage findings
are indexed in [contract testing](../wiki/contract-testing.md); root owns the
final [comparison report](../../../pbt-draft-exp/sequential-followup.md).
