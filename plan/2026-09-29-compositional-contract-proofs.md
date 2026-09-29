# Compositional checked proofs for concrete contract predicates

Status: done (bounded stage1a; general sequence coverage remains open)

Parent: [sequential contract optimization](2026-09-29-sequential-contract-optimization.md).
This is a bounded engine-maintenance stage over the authorized retained h07/h08
public queries. It does not change benchmark sources, samples, seeds, provider
configuration, query count/deadline, original assertions, definedness, type or
visibility checks, or any numeric reduction budget.

## Objective and observable acceptance

Add an explicit native-proof-composition mode for closed applications of pure,
transparent, nonrecursive Boolean predicates. The ordinary `Reduce` path and its
inline-depth semantics remain byte-for-byte behavioral defaults. `ContractSolver`
opts into the new mode and receives one ordered sequence of separately checked
proof obligations. Every prerequisite, existential witness and parent predicate
must verify as an ordinary assertion before it can help the unchanged original
target.

Acceptance requires:

1. a general three-level concrete predicate chain can be proved without an
   unrestricted depth-zero inline or an increased/reset budget;
2. all compositional goals, candidate bodies, generated witnesses and emitted
   steps share the root expression-node and quantifier-instance counters;
3. no parent step is emitted unless every prerequisite selected for that parent
   has a complete ordered certificate; exhaustion leaves the parent absent;
4. recursive, bodyless, opaque/unrevealed, heap-dependent and escaping-binder
   calls remain residual;
5. dead conditional/short-circuit branches do not introduce a helper assertion
   or a definedness error that the original expression did not require;
6. h07 retained query 3 and 4 positive polarities obtain native `Unsat` under
   the original ten-second deadline, while both negative polarities do not obtain
   `Unsat`; h08 query 5 and query 6 are measured honestly with no expected verdict
   assumed in this stage.

## Non-goals and proof boundary

This stage does not add unknown-length sequence enumeration, finite-sequence
exhaustiveness lemmas, recursive predicate/datatype synthesis, heap capture,
heuristic witness selection, inline-depth fallback, cap changes, packages or
dependencies. It cannot label an auxiliary proof-step failure as a target
counterexample. A partial-evaluator `True` remains insufficient by itself: native
verification of the ordered obligations and original target is authoritative.
Stage 1b finite sequence consequences remains deferred until the h08 replay shows
the exact residual after this implementation.

The compositional policy is explicit. Inline depth remains the maximum nesting
inside each independently checked local goal. Local goals may start with the same
configured depth because each becomes a separate native assertion. A single
shared quantifier-instance counter and expression-expansion counter cover the
entire root plus dependency DAG; no local goal receives fresh global allowance.
Admitting a DAG node consumes one instance from the existing 100-instance limit,
and every cloned/substituted goal or emitted expression reserves nodes from the
existing expression-node allowance.

## Inspected evidence and existing mechanisms

The retained optimized-v4 h07 query 3/4 results are positive/negative native
nonproofs with `InlineDepthLimit`, one instance and no checked witnesses. Root's
fresh baseline probe at
`/workspace/tmp/experiment/pbt-sequential-20260929/query-probe/` reduces their
common proposition to `ValidNumberPrefix([], 0)` conjoined with an existential
`cuts` body containing `FragmentsConcatenate([], [], cuts)`; the root reduction
uses 778 nodes. Existing fixed-length structural reduction can derive the exact
`cuts == [0]` witness once that closed existential is treated as a local goal.

The retained h08 query 6 reduction contains ordered/membership constraints for an
unknown `positions` sequence followed by additional unknown line-partition
sequences and uses 2,120 nodes. This stage makes no false-decision claim for it.
The existing witness pipeline already checks closed concrete existential instances
as native `AssertStmt`s, preserves original targets and rejects escaping binders
with `ComputeFreeVariables(..., includeStatements: true)`. The new work extends
that checked ordering rather than creating assumptions.

## Planned changes

| Files/symbols | Exact change and necessity | Validation |
| --- | --- | --- |
| `Source/DafnyCore/ContractTesting/ContractReductionResult.cs` | Add a proof-step kind and an ordered proof-obligation value carrying the resolved expression, plus result statistics for considered/admitted compositional nodes and the ordered obligations. The opt-in entry point is `ReduceForNativeProofComposition`; `Reduce` and `ProofWitnesses` preserve default caller behavior without an unused mode enum. | Default reducer regression; ordering/statistics assertions. |
| `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs` | Add `ReduceForNativeProofComposition` (or an equivalent explicit mode overload) while leaving `Reduce`/`ReduceWithHeap` defaults unchanged. Introduce one internal reduction session owning the shared `QuantifierExpansionBudget` and `ExpressionExpansionBudget`; local-goal reduction reuses that session. Build a bounded, deduplicated postorder worklist only from closed eligible candidates reached by the live reduced expression. Admit a parent only after all prerequisite obligations are complete. | Deep-chain, shared-cap, incomplete-parent and unchanged-default tests. |
| `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs` | In composition mode only, record exact instantiated-body candidates during ordinary eligible inlines with depth remaining. Do not inline at depth zero. Candidate eligibility is Boolean, pure/heap-independent, transparent and revealed, nonrecursive, resolved, acyclic, and free of escaping bound variables. Preserve the call/body and live simplified residual needed by the reducer worklist. | Opaque/provided/bodyless/recursive/heap/free-binder controls; existing depth-limit tests unchanged. |
| `Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs` only if needed | Expose live-branch provenance needed to reject candidates reached solely through eliminated `if`, implication, conjunction or disjunction branches. Prefer existing simplification traversal and avoid a second expression evaluator. | Conditional and short-circuit invalid-WD helpers create no step/error when dead. |
| `Source/DafnyCore/Rewriters/QuantifierBounds.cs` | Preserve the existing finite-domain algorithm but recognize an empty integer-domain factor even when another factor is relational/unbounded. Return the quantifier's exact vacuous value without enumeration or budget reset. This is required by h07's generated two-variable `forall`. | Multi-variable empty-product `forall`/`exists` controls and retained h07 replay. |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs` | Opt only closed scalar assertion reduction into proof composition. Insert the returned single ordered sequence immediately before the unchanged target, using distinct error markers for witness/prerequisite/parent steps. Keep `original && reduced`. Report step/node counts and shared total instance use. Auxiliary assertion failure remains nonproof/error and never becomes target `Sat`/violation evidence. | Native positive/negative, WD, visibility, dead-branch and failure-classification controls. |
| `Source/DafnyCore.Test/ContractWitnessReductionTests.cs` | Add realistic reducer controls for a three-level acyclic chain, exact empty cuts, default-mode unchanged behavior, node/instance exhaustion, no incomplete parent, exclusions and dead branches. | Focused Core filter. |
| `Source/DafnyTestGeneration.Test/ContractWitnessQueryTests.cs` | Add native checks for ordered prerequisite/witness/parent use, both polarities, original WD, opaque/provided boundaries, dead conditional/short-circuit calls and auxiliary failure classification. | Focused TestGeneration filter. |
| This plan | Record implementation, commands, source state, outcomes, replay limits and durable findings. | Diff/plan review. |

Core owns reduction, candidate discovery and structured results. TestGeneration
owns query assembly and native outcome classification. No evaluator, dataset,
scoring, reporting, runtime-heap or provider layer changes.

## Algorithm and ordering

The root reducer runs normally with inline depth two. In composition mode only,
each successful ordinary inline may retain a detached candidate consisting of the
original resolved call, its exactly substituted body and the live simplified
body. Candidate collection itself grants no proof fact.

Starting from candidates reached by the root evaluation, the reducer processes a
real dependency DAG in postorder. Each candidate retains its exact instantiated
body as well as its simplified result. Calls in that body identify child nodes,
including a child whose simplified `True` result disappeared from the final root.
It flattens only logical conjunctions whose other factors reduce to `True`; it does
not invent decomposition for disjunctions or implications. Closed prerequisites
are reduced as local goals with the unchanged local inline depth and shared session
counters. A local `False`, residual, ill-resolved or open prerequisite, cycle,
unsupported call, or exhaustion rejects its dependent parent. Successful local
existential reduction contributes its existing checked concrete witness, then the
exact prerequisite expression, then the parent call. A leaf reduced to `True`
without witness facts needs no emitted prerequisite because the parent remains the
native proof gate; this avoids publishing the text of a dead branch merely because
it occurs in a transparent body. Deduplication may reuse a prior complete
certificate but never a partial one.

The first retained replay showed why empty-product reduction is necessary: h07's
three live candidates were found, but `ValidNumberPrefix([], 0)` locally reduced
to a two-variable vacuous `forall`, and the cuts existential locally reduced to
another vacuous `forall` (`proofNodes=0/3`, 1,796 shared expansion nodes, 6
instances). Both contain the exact empty integer interval `0 <= i < 0`; the
existing product-domain inference found that empty factor but discarded it when
the generated `_t#0 == i - 1` factor lacked two absolute bounds. Recognizing the
empty product is exact, consumes no instances, and is not another predicate
inline-depth boundary.

Composition-mode candidate and witness collection also follows evaluation
provenance. Items created while simplifying an eliminated short-circuit branch are
discarded while their already charged node/instance work remains charged. Items
beneath a symbolic conditional branch are not lifted unconditionally. Root
witnesses are appended only after their collected helper DAG; candidate-body
witnesses arise from the corresponding local prerequisite and therefore precede
that prerequisite and parent. This applies to root and local-goal reduction and is
covered by dead existential implication and `or` controls in addition to the
predicate-call controls.

Before lifting any obligation, compute free variables including statement bodies;
any free `BoundVar` rejects it. Generated assertions retain original resolved
calls, function preconditions and visibility. Live-expression reachability is
checked after branch simplification so a partial call under a false antecedent or
unselected conditional produces no obligation. The output is one list in native
dependency order. Final h07 query3 emits `NumberStatusAtRelation`, three checked
cuts/warning witness expressions, the exact `DuplicateWarningsRelation`
prerequisite, and `NumberAnalysisRelation`, followed by the unchanged target.
Its remaining original `ValidNumberPrefix` is covered through the native parent
assertion; no separate leaf assertion is claimed for it.

## Validation and native lane

All native commands require root's serialized lane and run in tmux. Working tree
is `/workspace/cosyn/dafny`, `TMPDIR=/workspace/tmp`; artifacts go under
`/workspace/tmp/experiment/pbt-sequential-20260929/quantifier/` without changing
the preserved baseline directory.

Planned focused commands:

```bash
dotnet test Source/DafnyCore.Test --no-restore -m:1 \
  --filter 'FullyQualifiedName~ContractWitnessReductionTests|FullyQualifiedName~ContractExpressionReducerTests' \
  --logger 'console;verbosity=normal'
dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 \
  --filter 'FullyQualifiedName~ContractWitnessQueryTests|FullyQualifiedName~ContractQueryTests' \
  --logger 'console;verbosity=normal'
```

Expected focused outcome is all selected tests passing with no network/provider
calls. Then run the root-provided retained harness in
`/workspace/tmp/experiment/pbt-sequential-20260929/query-probe` for h07 query 3/4
positive and negative and h08 query 5/6 positive and negative, preserving each
original ten-second native deadline. h07 positives must be `Unsat`; h07 negatives
must not be `Unsat`. h08 outcomes are observations and cannot be relabeled.
Record command, cwd, session, source hashes, exit, elapsed/query timing, reduction
decision, exhaustion, instance/node/step counts and native outcome. Run
`git diff --check` on owned files. Root owns broader suites, campaign reruns,
formatting coordination and fresh independent review.

## Approvals, risks and handoff

Root authorized this bounded stage 1a and owns parent-plan/index/wiki updates.
The main risks are accidentally processing a dead branch, resetting a global
budget in a local goal, publishing a parent after partial prerequisites, or
allowing an auxiliary failure to masquerade as a target counterexample. The
controls above are acceptance gates. No dependency approval, paid execution or
benchmark change is required. Implementation starts only after root registers and
announces this ready plan and confirms the serialized native lane.

No durable finding is recorded yet. If the implementation validates, record the
compositional depth/budget boundary and retained replay result in the existing
contract-testing wiki through the parent owner; otherwise record the concrete
blocker and leave this plan `blocked` or `in-progress`, not `done`.

## Progress

Root registered and announced this child plan and granted the exclusive native
lane. The first retained replay completed with h07 query 3/4 positive and negative
all `Sat`, h08 query 5/6 positive and negative all `Sat`; h07 therefore did not
meet acceptance. Exact local residual evidence above narrows the correction to
composition-only empty-product detection, an exact-body dependency DAG, and live
witness provenance.

Implementation is complete and awaits independent review. The final bounded
implementation keeps ordinary `Reduce` behavior unchanged and enables only the
explicit ContractSolver composition path. It records exact instantiated bodies,
builds a deduplicated postorder dependency DAG, charges detached calls/bodies,
local working copies, witnesses and emitted nodes to the shared budgets, and
publishes a parent only after its child nodes and witness-bearing prerequisites
are complete. Recursive calls can still follow existing bounded ordinary
reduction, but are never admitted as new composition nodes. Candidate and witness
collection is rolled back across dead, symbolic-guarded and negated contexts;
the simplification work remains charged.

The empty-product rule is also composition-only. Integer-domain inference follows
nested `forall` implications and returns the vacuous result when any product
factor has proven lower bound greater than or equal to its exclusive upper bound,
even if another factor remains relational. It does not enumerate a domain,
increase a cap, or reset a counter.

Final focused validation from `/workspace/cosyn/dafny`:

- `core-final4.log`: the planned Core filter passed 87/87.
- `native-final2.log`: the planned TestGeneration filter passed 83/83.
- `git diff --check` passed for every file in the change table.
- Earlier failed logs remain preserved. In particular, `native-final.log` exposed
  an `Error` from positive witnesses lifted through a negated existential; the
  final polarity-aware rollback fixed it without broadening the expected result.

Final retained replay artifacts are
`/workspace/tmp/experiment/pbt-sequential-20260929/quantifier/final-*.jsonl`.
Under the unchanged ten-second query deadline, h07 query 3 positive was `Unsat`
(6.61s) and query 4 positive was `Unsat` (6.84s), each with 6 proof steps, 2/2
composition nodes and 11/100 shared instances. Their negative polarities were
`Sat` (5.73s and 6.13s), with zero composition steps; these are target
counterexamples, not certificates. An earlier intermediate build timed out on
both negative polarities at 21.63s and 20.27s wall time after cancellation; those
timeouts were not decisions and were superseded by the final polarity fix.

h08 remains observation-only: query 5 and query 6 are `Sat` in both polarities.
Positive queries considered one candidate but admitted none (`proofNodes=0/1`,
9/100 instances); negative queries collected no composition node and used 4/100
instances. No unknown-sequence enumeration or stage 1b work was added.

The first frozen source manifest and base revision are preserved in
`/workspace/tmp/experiment/pbt-sequential-20260929/quantifier/source-manifest.sha256`
and `source-revision.txt`. No debug instrumentation remains.

Independent frozen-source controls then found two material gaps, so this plan is
still `in-progress`. First, a `forall` simplified its body before discovering a
false or empty range and leaked a nested existential witness; the auxiliary
assertion changed native `Unsat`/`Sat` targets into `Error`, at both root and local
prerequisite reduction. The correction adds an explicit composition-session
provenance flag to root and local evaluators and rolls back candidate/witness side
channels produced beneath `forall`, while leaving already charged work charged.
Existing conditional/negation rollback is gated by this flag so ordinary
`Reduce` witness behavior remains unchanged.

This `forall` rule is deliberately conservative: even a valid closed nested
witness is not lifted from a quantified body. The reduced/original quantified
target and its ordinary well-definedness checks remain for native verification,
so this can leave a proof residual but cannot manufacture a proof or auxiliary
error. Full quantified-witness composition is outside this stage.

Second, a `Support()` predicate inside a concrete existential witness was first
visited beneath a symbolic conjunction and correctly discarded. Literal helper
interpretation, and then a possible literal cache hit, returned before candidate
collection, so the ordered certificate omitted Support. Composition candidate
collection bypasses those literal shortcuts for Boolean calls, repeats the
ordinary eligible inline with the same global accounting, and retains the exact
candidate. Proof-expression keys normalize concrete-syntax wrappers so a
completed child is reused rather than reduced again as a duplicate prerequisite.
The unchanged independent controls under
`/workspace/tmp/experiment/pbt-sequential-20260929/independent-quantifier/` are
the correction gate. After they and the focused/retained gates pass, create a new
source manifest rather than overwriting the failed frozen-state evidence.

The first correction passed 6/7 independent controls: all vacuous-`forall`
classifications, recursive exclusion and expression exhaustion passed, and
normalized keys removed the duplicate `Middle` prerequisite. `Support()` was
still absent because its concrete revisit remained beneath symbolic-conjunction
rollback. The remaining bounded change keeps rolled-back, already charged
candidates in a deferred provenance pool. Deferred candidates are never roots and
are not traversed as generic conditional-body dependencies. Witness activation
walks only positive conjunction factors and accepts a direct Boolean predicate
call; it does not descend through implication, disjunction, negation, conditional
or quantifier contexts. A candidate reached by that live positive path is then
processed before the witness through the same DAG state and shared budgets. This
preserves guarded/dead-branch exclusion while establishing
the required `Support`, witness, existential prerequisite, `Middle`, `Outer`
ordering.

The second correction still passed 6/7. A temporary candidate-state diagnostic
(removed before validation) showed active `Middle`/`Outer` and no deferred
`Support`: the call occurs at ordinary inline depth zero inside the existential,
so neither literal shortcut was the final cause. For a direct positive-conjunct
Boolean call in a retained closed witness only, the composition DAG may therefore
materialize one candidate from its exact substituted declaration body. This is
not an ordinary inline and does not alter the reduced expression or local depth;
it applies the same pure, transparent, revealed, nonrecursive, heap-free and
closed eligibility checks and charges the call, substitution and detached body
to the existing shared node budget. Recursive, opaque, bodyless, heap-dependent,
open, guarded and negative calls remain absent. The candidate is then subject to
the same DAG instance charge and native assertion ordering as every other node.

The frozen twelve-case independent gate exposed one remaining compatibility
regression: decisive Boolean left operands skipped their right operand even in
ordinary reduction, suppressing the historical inline-depth exhaustion signal.
The correction limits that live-branch shortcut to the explicit composition
session; ordinary reduction again visits the right operand and keeps its prior
witness/depth behavior. The same gate also requires a negated retained witness
with a dead partial-call branch to remain a native `Sat` target. That timeout is
investigated as a classification/performance issue without relaxing its expected
outcome or publishing a negated witness.

The correction refreeze restored the ordinary dead-branch depth signal. The
exact frozen fixture hashes were
`f5d84ae078a9328c254871bd4fd53c757da186332dd0ab7ea0ceebabdfe10dd5`
for `IndependentQuantifierCompositionTests.cs` and
`dfcdaf3b013a3c87de926f1289f43a0e6d3dbb9580220f4a97ab737092afd9bd`
for `independent.targets`. Eleven of its twelve controls passed. The remaining
`NegatedRetainedWitnessKeepsFalseTargetPolarity` raised the monotonic deadline
exception after three seconds before native outcome classification; an isolated
diagnostic also exceeded ten seconds at the post-translation deadline check.
This is retained as a conservative timeout/nonproof limitation. No witness,
predicate step, false verdict or relaxed expected outcome was introduced for it.

The refreeze focused suites passed 91/91 Core tests and 87/87 native query tests.
The retained h07 replay passed all four outcome gates under the unchanged
ten-second query deadline: queries 3 and 4 positive were `Unsat` at 9.62s and
9.53s, each with seven ordered obligations and 3/3 predicate nodes; their
negative polarities were `Sat` at 5.85s and 5.44s with no proof obligations.
The exact logs are the `*-correction-refreeze.log` and
`correction-h07-*.jsonl` files under the plan artifact directory. The plan stays
`in-progress` pending the fresh independent comparison of the preserved timeout
against baseline behavior and the frozen corrected source.

Independent replay of the correction then timed out on both h07 positive
queries (10.84s and 11.01s). The correction had inserted the newly materialized
`FragmentsConcatenate([], [], [0])` predicate before all three already staged
sequence witnesses, increasing query 3 from six to seven obligations and moving
facts useful to that predicate after its assertion. This comes from
`TryComposeWitnessDependencies` writing nested candidates directly to the global
obligation list while `TryComposeCandidate` retains prior witnesses in its local
`staged` list.

The bounded correction changes proof assembly, not candidate eligibility or any
budget. Each root candidate or root witness builds one transaction-local ordered
certificate. Body dependencies are appended first; prerequisite witnesses retain
their source order; a predicate discovered in a later witness is appended after
earlier witnesses but before the witness that contains it. The certificate,
prerequisite keys, completed candidate states and admitted-node count become
global only when the parent succeeds. A failed transaction publishes no
obligation, leaves all expression/instance work charged, and marks its newly
visited candidate states failed so no uncommitted `Complete` state can be reused.
Previously committed complete nodes remain reusable and deduplicated.

Add Core controls for both sides of the order (`Support` before its dependent
witness and an earlier independent witness before `Support`) and for a later
failing dependency publishing neither the earlier witness nor an incomplete
parent certificate. Re-run the focused Core/native suites, the unchanged frozen
twelve-case independent fixture, and retained h07 query 3/4 in both polarities.
Acceptance still requires h07 positives `Unsat` under ten seconds; no deadline,
solver option, native parameter or reduction limit changes.

The transactional ordering correction passed all added controls and the full
focused suites: 93/93 Core tests and 87/87 native query tests. The unchanged
frozen independent fixture remained 11/12, with only its previously recorded
negated-witness deadline exception; all ordering, failed-parent, ordinary-depth,
dead-branch, recursive and shared-budget controls passed.

The retained h07 gate now passes with the unchanged budgets and deadline. Query
3 positive is `Unsat` in 6.89s and query 4 positive is `Unsat` in 6.44s; both use
15/100 shared instances, seven obligations and 3/3 admitted predicate nodes.
Their sequence is `NumberStatusAtRelation`, the first two sequence witnesses,
`FragmentsConcatenate`, the witness containing that call, the exact
`DuplicateWarningsRelation` prerequisite, and `NumberAnalysisRelation`.
Negative queries 3 and 4 remain `Sat` in 6.43s and 5.95s with no proof
obligations. h08 queries 5 and 6 remain observation-only `Sat` in both
polarities, with no admitted proof node. Exact outputs are
`ordering-h07-*.jsonl`, `ordering-h08-*.jsonl`, and the
`*-ordering-final.log` files in the artifact directory. Preserve all earlier
timeout snapshots for comparison and leave the plan `in-progress` until the
fresh independent frozen-source rerun completes.

## Final bounded acceptance

The fresh independent ordering rerun accepted stage1a on2026-09-29. Source hashes
match `quantifier/source-manifest-ordering.sha256` before/after; HEAD remains
060d5ad532f67d5367450689225274fb0a0243e7 plus the recorded working tree.
Core93/93 and native query87/87 pass, including ordering and failed-transaction
atomicity controls. The unchanged extra adversarial fixture remains11/12: its
strict3s negated-witness test times out, as does immutable v4 on the same source
at3s and10s. That test is not relabeled passing; it records an existing unsupported
proof-performance fragment rather than violating the bounded acceptance above.

Independent retained h07 positives are Unsat6.619/6.708s, negatives
Sat5.864/6.021s. h08 query5/6 both polarities are Sat/nonproof. All original
ten-second limits remain unchanged. Exact commands, logs, initial/correction
archives and final source manifests are under
`/workspace/tmp/experiment/pbt-sequential-20260929/independent-quantifier/` with
the `ordering-*` prefix for final evidence. `git diff --check` passes. Native
lane is released; root starts stage2. This closes the bounded proof-composition
implementation, not six-case detection acceptance or general sequence support.
Durable mechanism and limits: [contract-testing knowledge](../wiki/contract-testing.md#ordered-native-proof-composition-2026-09-29).
