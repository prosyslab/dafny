# Checked concrete bindings and existential witnesses

Status: done (bounded implementation and validation; broader coverage limits remain)

Parent: [inconclusive optimization](2026-09-29-inconclusive-runtime-optimization.md).
This is engine maintenance, using the retained public h13 request and query artifacts.
No benchmark source, sample input, seed, budget, provider, scoring or proof gate changes.

## Objective and acceptance

Admit all already-supported concrete values at the closed-query boundary and expose
exact finite existential structure to the existing reducer. Original assertions,
definedness and checked equivalence remain authoritative. Validate the original h13
closed queries under their existing budget; report remaining inconclusive queries.
Unsupported shapes, cycles and resource exhaustion remain residual.

## Evidence and planned changes

The native h13 #4/#15 binding contains map displays and a bitvector conversion,
which ContractSolver's narrow concrete recognizer rejects. #11/#13 quantify three
dependent sequences; #5/#16 quantify a single-constructor product with sequence
fields. The sequence recognizer accepts one binder, and point elimination currently
requires simultaneous independent assignments for every binder.

| Files/symbols | Change, necessity and remaining gap without it | Validation |
| --- | --- | --- |
| Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs; Rewriters/PartialEvaluatorEngine.cs concrete-value recognizer | Share the existing concrete predicate across the assembly boundary through the reducer API; avoid a second divergent recognizer | Native nested map/conversion bindings, positive/negative and WD controls |
| Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs ReduceConcreteAssertion | Use the shared predicate for captured equality bindings and the query owner's resolved signature visibility, matching existing heap reduction | Existing retained h13 #4/#15; imported revealed/opaque/export controls |
| Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs existential handlers; QuantifierBounds.cs if necessary | Exact progressive acyclic point elimination, fixed-length sequence and single-constructor product decomposition; preserve type constraints and shared caps | Dedicated reducer true/false/residual/cap tests and native queries |
| Source/DafnyCore/ContractTesting/ContractReductionResult.cs; ContractExpressionReducer.cs; PartialEvaluatorEngine witness evidence; ContractSolver checked witness assertions | Preserve fully concrete witnesses derived by exact elimination as separately checked original predicate instances before the unchanged target. A true literal alone cannot introduce existential witness terms to native verification, as native-1 demonstrates | Native witness positive/negative/WD gates; no witness assertion may be assumed or bypass verification |
| PartialEvaluatorVisitor.VisitOneExpr, NestedMatchExpr.Flattened dispatch and known-constructor MatchExpr reduction | Select the resolved constructor branch and substitute only that branch's bound variables; source replay3 leaves concrete matches untouched | Constructor identities, bound fields, nested matches, unknown source residual |
| PartialEvaluatorEngine.ExpressionExpansionBudget.TryReserveSubstitution and callers | Charge a conservative occurrence-aware substituted-expression bound rather than multiplying every body node by every argument's size; preserve the same absolute node cap and fail before oversized expansion | Repeated occurrences, unused arguments, binder shadows and exhaustion; original h13 #4 |
| PartialEvaluatorEngine.SimplifySeqMembership | Reuse the existing concrete structural equality for datatype/collection sequence elements, including `Stdin in [File(...)]`; leave unknown elements residual | Constructor distinction, nested nonprimitive arguments, unknown element residual |
| PartialEvaluatorEngine.TrySimplifyContractConstructorEquality (new); PartialEvaluatorVisitor.SimplifyBinaryExpr | Under ContractConcrete only, expose equal ordinary resolved inductive constructor arguments as field equalities; reject distinct constructors of the same compatible datatype. Reserve the generated expression against the existing shared node cap, preserve subset constraints, original target and WD. This exposes exact existential assignments currently hidden inside constructors | Same/different/nested/generic constructors, refined fields, conflicting equalities, unknown operands, node-cap residual; native original assertion and WD controls |
| PartialEvaluatorVisitor.RecordConcreteExistentialWitness; ContractWitnessReductionTests.cs; ContractWitnessQueryTests.cs | Reuse FreeVariablesUtil to exclude only genuinely free BoundVar identifiers from lifted checked witnesses, retaining locally bound nested quantifiers. The descendant-based check incorrectly rejects closed witnesses | Nested local forall positive, escaped outer binder remains excluded, original WD error, and unchanged h08 #4/#6 replay |
| Source/DafnyCore.Test/ContractWitnessReductionTests.cs; Source/DafnyTestGeneration.Test/ContractWitnessQueryTests.cs | Independent behavioral coverage of the above generic shapes and original proof gate | Focused native tests |
| This plan | Record commands, results, limitations and remaining work | Diff review |

Core owns expression/implementation changes; TestGeneration owns native-query
composition. No specification, proof, dataset, scoring or report-layer change.
Cross-assembly reuse may require one documented static reducer API; no package or
new behavioral heuristic is authorized. Exact syntactic identities are the scope.

## Validation and execution

Native build/test lane is serialized with root. Cwd `/workspace/cosyn/dafny`,
`TMPDIR=/workspace/tmp`: `dotnet build Source/Dafny.sln --no-restore -m:1`,
`dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter
FullyQualifiedName~ContractWitnessReductionTests`, and analogous TestGeneration
filter `FullyQualifiedName~ContractWitnessQueryTests`. Root coordinates formatting,
full relevant regression checks, independent review and unchanged campaign reruns.
Native artifacts: `/workspace/tmp/experiment/pbt-inconclusive-20260929/quantifier/`.
No paid calls. Preserve all pre-existing dirty files and original artifacts.

## Progress

Read source and retained h13 outcomes; no validation run yet. Root registers this
child plan and maintains shared indexes/wiki. Ready for bounded implementation.

First implementation compiled in tmux `quantifier-focused-1`. `dotnet test
Source/DafnyCore.Test --no-restore -m:1 --filter
FullyQualifiedName~ContractWitnessReductionTests` passed 9/9; corresponding native
test filter passed all three structured-binding controls but failed the two
existential proof controls (positive nonproof, negative deadline). Logs:
`quantifier/core-1.log`, `quantifier/native-1.log`. This justifies preserving checked
concrete witness instances instead of losing all witness terms in a true literal.

`quantifier-focused-2` preserved 9/9 Core checks and proved the minimal native
positive existential with checked witnesses; its negative still exceeded the 3s
test deadline (not a detected failure). Original retained h13 #11/#13/#5/#4 were
replayed in `quantifier-replay-1`, each with the unchanged 10s deadline: all remain
native nonproofs. Diagnostics establish no imported predicate was inlined (zero
instances for the existential clauses), because scalar query reduction uses only
the owner's local visibility rather than its resolved signature. Reuse the exact
`program.ModuleSigs[owner].VisibilityScope` already used by heap reduction; do not
reveal any otherwise inaccessible or opaque function.

`quantifier-focused-3`: Core reducer regression+new tests passed 51/51; native
controls passed 8/8 (negative-true witness safety control explicitly permitted the
documented 3s timeout). Replay2 then proved original h13 #13 (`unsat`, 3.53s),
while #11 reduced to true but still lacked its complete original predicate
instance. #5 exposed a null `Bounds` invariant in a remaining generated
`ExistsExpr`; replay exited 134 before #4. The crash is preserved in
`quantifier/replay-2.log`, not counted as a query result. Generated residuals now
use `ModuleResolver.DiscoverBestBounds_MultipleVars`; a dedicated native residual
translation test covers that path. Successful derived witness values now fold
closed slices/arithmetic at depth zero before deciding whether the complete
original predicate instance is concrete. Replay3 and focused regressions pending.

Toolchain: .NET SDK 8.0.131, Dafny HEAD
`060d5ad532f67d5367450689225274fb0a0243e7` plus preserved pre-existing changes and
this child plan's dirty changes. Parent records whole-tree source provenance.

Replay3 proves original h13 #11 in 6.68s and #13 in 3.42s under the unchanged 10s
deadline. #5 remains native nonproof with InlineDepthLimit; #4 remains native
nonproof with ExpressionNodeLimit. No target/specification/input change. Core51/51
and native9/9 pass (the explicit negative-true safety timeout remains unsupported).
Root authorized the two exact structural/accounting extensions above; do not reset
or raise inline depth or any budget to obtain a pass. Runtime owns the native lane
while this next source batch is prepared.

Focused5/replay4: native11/11 passed. Core57/62 passed; three new accounting
assertions initially omitted existing syntax-wrapper nodes (expected counts
corrected against resolved source); two branch-selection checks exposed the
missing `NestedMatchExpr.Flattened` dispatch, now added with budgeted detached
cloning. Replay4 #4 remains native nonproof but no longer exhausts the expression
node budget; #5 remains a depth-limited residual. Raw failures remain in
`quantifier/core-5.log`, and query receipts in `quantifier/replay-4.log`.

## Focused validation and handoff

Final serialized session: `quantifier-focused-6`, cwd `/workspace/cosyn/dafny`,
`TMPDIR=/workspace/tmp`. Commands and receipts:

- `dotnet test Source/DafnyCore.Test --no-restore -m:1 --filter
  'FullyQualifiedName~ContractWitnessReductionTests|FullyQualifiedName~ContractExpressionReducerTests'
  --logger 'console;verbosity=normal'`: build succeeded and **62/62 passed**,
  `quantifier/core-6.log`, exit 0.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter
  'FullyQualifiedName~ContractWitnessQueryTests|FullyQualifiedName~ContractQueryTests'
  --logger 'console;verbosity=normal'`: build succeeded and **66/66 passed**,
  `quantifier/native-6.log`, exit 0. This includes original WD rejection,
  imported provided-only/opaque boundaries, false-existential negation proof,
  and translatable unsupported residuals. The negative-true existential safety
  control still documents a 3s timeout, not a counterexample or detection.
- In the artifact directory: `dotnet run --project Replay.csproj --no-restore --
  4-positive 5-positive 11-positive 13-positive`: exact original retained h13
  sources and snapshots, each native deadline 10s, `quantifier/replay-5.log`,
  exit 0. #11 **unsat, 3.649s**; #13 **unsat, 3.492s**. #4 **sat, 9.066s**
  and #5 **sat, 3.866s** remain incomplete native proofs with an unchanged
  InlineDepthLimit; these are not confirmed violations.
- `git diff --check` on the owned source/test files: passed.

Source hashes for the tested owned batch are in `quantifier/source-batch6.json`;
the broader pre-existing dirty tree and other owners' work remain preserved.
Native lane released to the runtime owner. No provider calls or historical input
changes. No commits. Parent owns final formatting, fresh independent review,
shared indexes/wiki, and frozen-toolchain campaigns; those checks are not claimed.

## Authorized h08 constructor-equality follow-up

Root authorized this bounded follow-up after the frozen v3 campaigns. The retained
`cases/h08-paste-unlinked-entries/optimized-v3/runtime/closed-query-4-positive`
is a true selected-lines invariant with `Entry(selected,true)==Entry([],true)`;
it remains RequiresSolver with no checked witnesses. Query-6 has nonempty
preStdin and empty output lines and both polarities are native nonproofs; source
reasoning suggests a false output relation, but this is not a certified violation.
These frozen artifacts are the before receipts; no historical input is changed.

Scope is only constructor injectivity/disjointness and dedicated controls in
`ContractWitnessReductionTests.cs` and `ContractWitnessQueryTests.cs`. No recursive
sum witness synthesis, sequence-domain heuristic, inline-depth change, initial
membership cache, heap-capture change, or public API is included. Unknown,
coinductive, ghost, or incompatible datatype operands remain residual. Proof of
query-6 is an evaluation goal, not assumed acceptance: its additional unknown
sequence/depth gaps may remain. Core/native focused commands above and original
h08 #4/#6 positive and negative queries will run serially only after root grants
the native lane, each original replay with the unchanged 10-second deadline.
Parent will freeze a separate v4 only after checks and review; v3 remains intact.

Constructor follow-up validation (after root granted the native lane): tmux
`quantifier-constructor-focused-1`, started from `/workspace/tmp/experiment`,
executed the Core and TestGeneration filters above sequentially with builds.
**Core 72/72 and native 71/71 passed**, both exits 0; logs
`quantifier/constructor-core-1.log`, `quantifier/constructor-native-1.log`.
`constructor-source-1.json` records exact owned source hashes (confirmed unchanged
after testing), revision, session and working directories. `git diff --check`
passed. Native refined-constructor WD rejection passed; the previously documented
negative-true existential timeout remains an unsupported control outcome.

Retained h08 replay ran serially in tmux `quantifier-constructor-replay-1` using
`dotnet run --project Replay.csproj -- 4-positive 4-negative 6-positive 6-negative`
from `quantifier/h08-constructor-replay/`, original request snapshots, and original
10-second native deadlines. Receipt `quantifier/constructor-replay-1.log`, exit 0:

- #4 positive: **sat/nonproof**, 5.505s; reducer now True, 2 instances, no
  exhaustion, zero checked witnesses. The original target still fails.
- #4 negative: **timeout**, 11.032s wall including cancellation handling; the
  requested native deadline remains 10s. This is not a detected violation.
- #6 positive: **sat/nonproof**, 2.967s; negative **sat/nonproof**, 3.258s. Both
  retain InlineDepthLimit, 4 instances, zero witnesses. Constructor equality now
  exposes selected=[], but unknown positions/line counts and FragmentsConcatenate
  remain in the residual. No historical native decision improved in this replay.

Native lane released to root for the Driver owner's checks. No further source
edits are included in this follow-up. One source-backed next investigation is
`RecordConcreteExistentialWitness`: its conservative descendant BoundVar check
rejects locally bound variables inside an otherwise closed nested quantifier,
not only free outer-binder variables. Reusing free-variable analysis could retain
closed witnesses while still excluding escaping variables; this needs separate
authorization, regression controls and replay before claiming a fix.

Root authorized the free-variable correction above. The Driver owner confirmed
its current red build has finished reading Core; source edits may proceed while
its tests run, and source stability will be reported before its green rebuild.
No concurrent native command is authorized. Scope is only existing witness
capture, its Core/native tests and this plan. Original WD, separately checked
witness assertions, target, depth and all expansion/query budgets are unchanged.
After the Driver lane is released, run the same focused filters and exact h08
#4/#6 positive/negative replay; reduced True alone is not a proof result.

Fresh independent review found an additional scope boundary before validation:
`FreeVariablesUtil.ComputeFreeVariables` defaults to excluding statement bodies.
A `StmtExpr` witness can mention an outer bound variable only in its assertion,
while Boolean reduction discards that statement expression. Add a Core/native
statement-only escaping-binder control, record the Core failure before correction,
then use the existing `includeStatements: true` overload (no new walker). Keep
local nested binders, expression-only escaping binders and original WD controls.
Root granted the serialized native lane after the Driver owner's completed checks.

The requested statement-only source control passed against the old
`includeStatements:false` guard (`witness-scope-red-1.log`); local-bound positive
and expression-free negative also passed (`witness-scope-red-2.log`). Thus the
statement issue is a static traversal coverage gap, not a reproduced escape or
historical soundness failure. Applied `includeStatements:true` conservatively.
First green session passed Core75/75 and native73/75. The two escaping-binder
native controls incorrectly expected proof of an unbounded original forall;
native returned Sat/nonproof. Their scope assertion is retained and their outcome
assertion now permits Sat or Unsat, requiring successful translation and zero
checked witnesses, never Error or Timeout. These controls do not claim proof of
the original quantified clause. Failed receipts remain in
`witness-scope-native-1.log`; local quantified positive and original WD tests passed.

## Final witness-scope validation and source freeze

Serialized sessions `quantifier-witness-scope-focused-1`,
`quantifier-witness-scope-native-2`, and `quantifier-witness-scope-replay-1`, started
from `/workspace/tmp/experiment`; tests run from `/workspace/cosyn/dafny` with
`TMPDIR=/workspace/tmp`. Commands use the existing focused filters above. Results:

- **Core75/75 passed**, `quantifier/witness-scope-core-1.log`, exit 0.
- **Native75/75 passed**, `quantifier/witness-scope-native-2.log`, exit 0, after
  correcting only the two scope-control outcome expectations. This includes
  locally bound witness proof, expression/statement escaping-variable rejection,
  and original nested-function/constructor WD errors. Earlier failed/nonreproduced
  attempts are retained, not relabeled as successful proof runs.
- Exact h08 #4/#6 positive/negative replay with original snapshots and 10-second
  native deadlines, `quantifier/witness-scope-replay-1.log`, exit 0:
  **#4 positive Unsat, 5.382s**, two instances, one separately checked witness,
  unchanged original target retained. This is an actual native proof improvement.
  #4 negative remains Timeout (13.081s wall including cancellation; requested
  deadline unchanged at 10s). #6 positive Sat/nonproof 3.214s and negative
  Sat/nonproof 2.819s both retain InlineDepthLimit, four instances, zero witnesses.
- `quantifier/witness-scope-source-3.json` records final owned hashes, confirmed
  unchanged after all validation; `git diff --check` passed.

Native lane released and production/test source frozen for parent independent
review. No further constructor expansion, budget change, source input edit, or
provider call. The exact h08 negative candidate remains uncertified because
unknown sequence structure and the depth boundary persist. Parent owns final
formatting/review/shared documentation and any separately frozen v4 campaign;
those results are not claimed here.

Remaining limits are explicit: #4 reaches imported path-resolution helpers beyond
the original inline depth, and #5 retains dependent unknown-length sequences with
`FragmentsConcatenate` at that boundary. Solving them needs additional general
theorem support; no guessed sequence length, hardcoded historical witness, or
budget increase was introduced. Reusable findings to preserve in the parent wiki:
resolved import visibility must be passed to scalar reduction; exact existential
reduction needs checked original predicate witness instances; generated residual
quantifiers need resolved Bounds; substitution accounting must count actual
variable occurrences, including syntax wrappers and shadow identity.

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
