# Contract testing boundaries

- Status: verified bounded implementation; partial logical heap slice locally verified.
- Verified: 2026-09-14, working tree based on `336ae4ce66176cf8360d107894d5a4ad5a7a3a2d`.
- Origin: [implementation plan](../plan/2026-09-12-expecto-residual-constraint-solving.md).
- Symbolic-entry extension: [implementation plan](../plan/2026-09-13-symbolic-entry-contract-checking.md).
- Pattern/logical-heap extension: [implementation plan](../plan/2026-09-13-pattern-guided-contract-pbt.md).
- Commands and failures: [execution record](../../../plan/2026-09-12-hybrid-contract-testing-implementation.md).

## Diagnostic queries

`ContractSolver` reuses Dafny resolution, Boogie translation, and the existing
execution engine. The final `ContractSourceSnapshot` supplies a closed, hash-validated filesystem to
the native parser, preserving each file's URI, offsets, and verification-root identity. Every include
must be supplied explicitly. It does not use the ambient-file fallback of `Utils.Parse` or
`InMemoryFileSystem`; the legacy single-string query entry rejects includes before parsing. During
early implementation, parsing only a text fragment left named modules outside translation. Source
identity is required even when a diagnostic file is synthesized in memory.
The default library printer is `NullPrinter`. Model queries
need a per-query `DafnyConsolePrinter` or a verifier failure can have no captured
diagnostics or model. Neither situation is a satisfiable-model result.

Premise consistency, original preconditions, the original observed postcondition,
and bodyless-contract realization are separate queries. The observed property is
an assertion, never an assumption introduced through a call to the method under
test. Both truth polarities may remain possible for an unobserved abstract
function; that is inconclusive rather than a concrete violation.

Actual functions' and external functions' unproved ensures are removed from the detached diagnostic
query source so they cannot justify the property being tested. Bodyless pure contracts retain their
model relation. `ContractExpressionReducer` works on copies with cumulative evaluation/unrolling
budgets. Original assertions remain conjuncts with the reduced copy; residual formulas are preserved.
All verifier errors must belong to the intended query assertion before classifying it as SAT.
Separate definedness errors remain query errors.

## Symbolic entry verification

`ContractSymbolicChecker` uses the same closed `ContractSourceSnapshot`, but it does not synthesize
inputs, a runtime wrapper, or a compiled assembly. It resolves the exact method entry, computes calls
from the implementation and specification AST, and keeps either only that entry implementation or the
default reachable internal implementation closure. All other bodies are removed before
`BoogieGenerator.Translate`. Dynamic calls also add every resolved override candidate. An extern
declaration contributes calls from its retained `requires`, `ensures`, `reads`, and `modifies`, but
never from its removed implementation body.

Reachable `{:extern}` methods and functions are always summarized: method bodies, function expression
bodies, and `by method` bodies are removed after resolution. Their original `requires`, `ensures`,
`reads`, and `modifies` remain available to callers. The result lists these extern symbols separately
and records extern contracts, bodyless contracts, `assume`, `{:axiom}`, `{:verify false}`, and verifier
assumptions such as `decreases *` or `assert {:only}` as trust dependencies. It does not check that a
native implementation satisfies an external contract. The result also carries the path and SHA-256
of every source in the closed snapshot so callers can retain exact source evidence.

The entry `requires` clauses are checked in a separate verifier query by replacing the resolved method
body with `assert false` and removing its postcondition and modifies obligations. If that assertion
verifies, no entry state exists and the result is `inconsistent_premise`; it is never counted as
`verified`. The implementation query distinguishes `obligation_failed`, `unknown`, `timeout`, and
pipeline `error`. The CLI supervisor additionally distinguishes cancellation and invalid versioned
input. A failed obligation is a modular proof failure, not a runtime counterexample.

The selected entry is currently an implemented method without `{:extern}` or `{:verify false}`.
Reachable functions, including ghost functions over ghost-only class state, are verified in the same
closure. The checker relies on ordinary Dafny loop invariants and modular verification; it performs no
bounded unrolling and makes no path-completeness claim.

Negated unbounded quantified assertions sometimes need Z3 model-based
instantiation. Enabling it on all premise/model queries caused slow model search
in the background theory. The current local setting is restricted to the relevant
negated quantified assertion. It does not bound the integer domain or install a
global sequence-length axiom.

## Models and concrete observations

`ContractModelRealizer` keeps correlated outputs from one model state, then fixes
them and rechecks the original relation. Primitive values omitted from a partial
model can be completed as candidate type witnesses only with an explicit
`modelCompleted` flag and successful original-relation rechecks. Such a value is
not a runtime observation. Sequence model constraints need related values expanded
for both the cardinality and index constants before decoding elements.

Pure abstract choices persist across queries in the same test. Replay records the
actual choices instead of depending on a seed or asking the solver for a fresh
model. A missing method's inconsistent contract is distinguished from an invalid
call precondition; bounded input-search UNSAT is not an unbounded contradiction.

Heap-model calls receive the heap observed immediately before that call. In a
nested call, `old` refers to this call-entry heap, including earlier actual parent
mutations. Outputs and permitted next-state cells are extracted from one model
state and rechecked together. An exact replay fixes both outputs and post-heap;
it cannot change object identities, array dimensions, or cells outside the
original modifies frame. Heap-space UNSAT remains inconclusive because the
represented allocation/reference shapes are incomplete.

Concrete class heaps may omit a declared field only when it is ghost and no relevant expression in
the selected entry's transitive resolved-call closure references that exact `Field`. Each outgoing call
is extracted from the same relevant AST: internal executable callables contribute their full contracts
and bodies; extern or bodyless callables contribute contract, frame, and decreases expressions without
trusting or executing a source body. The dependency extraction mirrors the resolved call graph's
expression and statement targets, including direct function/method calls, first-class function member
selections, constant initializers, and datatype values; prefix declarations and resolved overrides are
added conservatively. Internal executable declarations and other fully relevant callable vertices use
the resolved intra/inter-module graph directly, which also preserves user-provided type dependencies.
Extern and bodyless declarations reconstruct those type edges from input/output signatures and explicit
types in their relevant contract AST, excluding local types from an unexecuted extern body. All callable
vertices additionally expand their declaration and relevant-node type components directly, because Dafny's
resolved call graph records type-declaration edges only within one module. This makes an imported subset
constraint reachable from an entry signature without scanning unused imported types. A helper reached
only from an extern source body therefore does not block omission,
while a helper called from an extern contract does. Unknown fields, omitted runtime fields, and different
supplied field sets for objects of one class fail closed. Diagnostic constructors accept only supplied
fields and initialize each omitted ghost field inside its declaring class with a fresh ghost
assign-such-that witness. Runtime metadata, the logical sidecar, snapshots, model application, queries,
observations, frame checks, and post-state assignment all use the same supplied ghost subset. The source
edits remain confined to the hash-bound diagnostic snapshots. For cross-module allocation, the
constructor and supplied hidden fields are added to every existing export view that reveals the heap
class, including the named view selected by a caller; no-export, wildcard, and same-module cases retain
their native visibility behavior.

Concrete heap value diagnostics retain their root cell and nested shape path. Collection elements use
`[index]`, map components add `.key` or `.value`, and datatype components add the formal field name. For
example, a bad datatype constructor nested in a map reports `box.payload[0].value.inner` while preserving
the original constructor/type mismatch text. This context is generated by the general typed renderer and
does not depend on a benchmark declaration.

One-dimensional arrays use stable heap object identities, one dimension, and
typed elements. Aliased arguments identify one array. Empty arrays are valid
shapes; resizing an existing array in a model replay is invalid. The array model,
alias, and write-restore behavior passed the combined 82-test contract regression
and actual probes in `/tmp/contract-array-events` before the later A14 work.

## Actual execution and frames

Diagnostic compilation preserves source snapshots and maps the selected declaration
to its original symbol, location, and hash. The generated entry must work both with
and without a user `Main`. A method with a body executes that body; its unproved
ensures do not justify silently replacing it with a contract model.

Final heap differences alone cannot check Dafny `modifies`: a write outside the
frame is forbidden even when it writes the same value or restores the old value.
Tests must observe attempted writes and nested method frames. Independent review
also found that real function preconditions and assertions in other classes must
be instrumented before claiming a pass. The execution record distinguishes the
initial false passes, their fixes, and the completed independent regression checks.

Mutable Dafny class fields can compile as C# properties. Runtime heap observation
and application must inspect the compiled metadata instead of assuming public
fields. Default-module CLR class names also include the compiled module prefix.
Receiver method/function probes and the eight public stateful guard cases caught
these metadata mistakes; the successful corrected run is recorded in the plan.

## Generation and source identity

`ContractTypeShapeGenerator`, `ContractPathExplorer`, and `ContractScenarioExtractor` supply bounded
type/P, actual-body-path, and specification-case goals. Precondition-only inputs remain available even
when a specification relation is unsatisfiable. Short-circuit alternatives and preceding branch negations
are retained, and independent suppliers are scheduled fairly. A symbolic target is a proposal until
execution confirms its ordered trace and the original input conditions.

`entry_reachable` executes the actual outer prefix and captures the selected invocation's inputs,
receiver, and pre-heap. Prefix model choices replay exactly before fresh later choices are allowed;
final counterexample replay consumes the complete choice list strictly. The expected declaration,
invocation, and source hash are checked even when the target path has no branches.

Selected generic entries use native type parsing/substitution and type-characteristic checks.
Reachable generic helpers use their resolved concrete call-site types, recorded in model choices and
validated on replay. Diagnostic identifiers avoid names from every source file/module. Heap-backed
values nested inside datatypes and sequences use typed expressions rather than top-level-reference
special cases. Atomic generation checkpoints contain only completed original-relation rechecks and
survive both CLI and outer Python timeouts without extending the budget.

## Evidence and limits

Concrete refinement membership first substitutes the sampled, resolved value into a detached copy of
the original subset/newtype constraint. `ContractExpressionReducer` alone selects the opt-in
`ContractConcrete` partial-evaluation profile. This profile recognizes closed datatype and finite
collection values through resolved syntax wrappers, preserves datatype constructor declaration identity,
evaluates matching discriminators and destructors, finite-map keys and lookup, and unfolds recursive
pure predicates only for closed arguments within explicit depth, quantifier-instance, and expression-node
budgets. Function and quantifier substitutions reserve node budget before constructing expanded ASTs.
Opaque, unrevealed, bodyless, reads-dependent, non-concrete, absent-key, wrong-constructor, and exhausted
cases remain residual. A residual is sent to SMT as the preserved concrete-substituted original membership,
not as a partially reduced formula.

The pattern P filter has an end-to-end regression for a recursive `ValidForest` constraint over
`map<int, Tree>`. A map containing `Branch([Leaf(7)])` reduces to true and is accepted with zero SMT
queries; a map containing `Leaf(12)` reduces to false and is rejected with zero SMT queries. This tests
the input-pattern, resolved carrier, reducer, and P-filter boundary together. It does not infer a missing
entry precondition or establish complete exploration of a recursive input space.

The contract-only concrete profile also normalizes resolved literal `ConversionExpr` nodes before
function-call eligibility, datatype/collection equality, and concrete cache identity. It accepts only
integer-based, bitvector, or character literal sources and uses `ConstantFolder.TryFoldInteger` for
Dafny's definedness and target-range semantics. Before folding, the target is normalized while retaining
constraints: every subset target, including `nat`, is rejected, as is every newtype for which
`ConstantFolder.AsUnconstrainedType` returns null. Supported targets are constraint-free integer or
bitvector types. The resulting literal retains the resolved target type. Symbolic operands, out-of-range
bitvectors, real and ordinal sources, subset/constrained-newtype targets, and unsupported targets remain
residual; the default partial-evaluation profile is unchanged. General regressions cover a nested
`493 as bv32` that reduces to true and residuals for `256 as bv8`, `1.0 as int`, `(-1) as nat`, and
`0 as Positive`.

The corrected fixed `MvCore.RunCore` r19 P-only run confirmed that its concrete filesystem now passes the
contract-concrete argument gate. At the default 10,000-node budget the opened predicate reaches
`ExpressionNodeLimit` after bounded quantifier work and restores the original membership for sound SMT
fallback. A diagnostic 1,000,000-node budget removes both the conversion and the top-level
`ValidInodeFileSystemData` call; the next unsupported residuals are three set comprehensions and calls to
`InodeNamespaceIds` and `InodeNamespaceIdPaths`. The actual run accepted two generated inputs; the first
used one `Unsat` SMT query for the preserved filesystem membership and the second reused cached
obligations. The raw run artifact was generated locally for validation, then deleted and left unversioned
under the repository's experiment-artifact policy. This run did not execute the implementation or check
Q/replay, and did not invoke `spec_check` or a provider.

The node exhaustion is a conservative accounting limit rather than a 10,000-node realized AST. The
substituted membership contains 50 nodes, leaving 9,950 expansion nodes. Each function or quantifier
substitution reserves `template nodes * (1 + sum(substitution value nodes))`, without counting the actual
formal occurrences. Three quantifier instances reserve 9,346 nodes before the next reservation is
rejected. With the 1,000,000-node diagnostic limit the same deterministic reduction reserves 14,351
nodes cumulatively while producing a 187-node residual. An occurrence-aware preflight count and local
subexpression rollback would retain the same resource bound with substantially less overestimation.

The fixed CoSyn G0 manifest passed all 20 actual cases and exact replays. See
`../../tests/test_contract_testing.py` and the execution record for the command.
The final full TestGeneration project passed 209/209 in an independent context; related Core
reducer/partial-evaluation/unrolling tests passed 103/103. Actual Python/CLI integration passed 92 tests,
with the eight expensive comparison tests run separately: 8/8 passed on a frozen binary. Both public
missing-guard faults were reproduced with actual and absent callees. This is a small, one-repetition
population, with timeout and replay denominators preserved in the execution record and
[CoSyn wiki](../../wiki/architecture/hybrid-contract-testing.md), not a general performance claim.

The supported full `make build-dafny` from CoSyn passed with zero warnings/errors and refreshed
`Binaries/Dafny`. New contract testing/generation CLI tests, the existing unrolling CLI, and C#
AllExterns/TestedExterns wrappers passed. Selected proof checks verified eight fixed-fixture obligations
and one existing unrolling obligation. `make format`, `make format-dfy`, and final changed-C# whitespace
verification passed. Formatting reported a Runtime reference-metadata warning; affected Core/Driver/
TestGeneration and test projects loaded, and no changed files required formatting.

For the 2026-09-14 partial logical heap slice and its independent-review corrections, the focused heap
tests passed 43/43, the complete DafnyTestGeneration `Contract` filter passed 257/257, and the
DafnyDriver `Contract` filter passed 4/4.
The focused tests include rejection through a first-class `Select -> Read` function dependency and
through entry, internal, extern, and imported cross-module formal subset-type constraints. They accept the same function or type
dependency when it exists only in an extern source body. The driver test
compiled and executed a diagnostic object whose irrelevant omitted ghost field has a
function type; the existing native-extern non-execution test remained green. `dotnet build
Source/Dafny.sln --no-restore -m:1` succeeded with zero warnings and errors. Whitespace verification
restricted to the five touched C# files passed. Whole-solution whitespace verification remained
non-actionable because it reported existing violations in generated files that repository rules forbid
hand-editing; `git diff --check` passed.

For the 2026-09-14 concrete-reducer slice, independent verification passed 22/22 reducer tests and
97/97 default partial-evaluator plus bounded-quantifier tests. The complete DafnyTestGeneration
`Contract` filter passed 260/260, the DafnyDriver extern-execution filter passed 4/4, and the solution
built with zero warnings and errors. The full Dafny test suite and every low-node-budget combination of
older materialization paths were not run.

Concrete refinement carriers use the datatype constructor selected while checking a pattern against its
resolved expected type. Before rendering the detached carrier, the shape recursively replaces constructor
spellings in datatype fields, finite collection elements, and map keys and values with the resolved
declaring datatype's fully qualified name. This lets a caller with a non-open import use the same short
constructor spelling accepted by type-directed pattern checking, without changing the raw pattern or
source snapshot. Independent regression used `Store` and `Client` modules with a nested
datatype/map/sequence/recursive-datatype subset: the valid sample reduced to true and the invalid sample
to false with zero SMT queries. The final TestGeneration `Contract` filter passed 262/262 and the default
partial-evaluation regressions passed 97/97.

When a concrete membership remains residual, its SMT query is emitted in the original supplied source
and lexical module of the resolved subset or newtype declaration. The internal obligation retains a
source path, source SHA-256, and scanner byte position separately from the semantic cache key. The query
is inserted only after an exact snapshot match and conversion from Dafny's UTF-8 token byte offset to a
UTF-16 string index at an exact scalar boundary. A missing or stale site fails closed only when SMT is
needed, so direct decisions for system refinements such as `nat` remain available. Independent tests
covered a non-open imported residual with a Korean source prefix, same-module position-zero residuals,
budget exhaustion, system `nat`, and imported direct true/false; pattern tests passed 54/54.

The fixed `MvCore.RunCore` P-only acceptance run used 18 source snapshots, seed `332160582228`, three
candidate slots, and a 60-second limit. It accepted two generated inputs with no unknown, unsupported,
or false-precondition results. The first input required one `Unsat` SMT query for the residual
`BenchWorld.FileSystem` membership in its declaring module; the second reused five cached obligations
and required no SMT query. The baseline was rejected for its known null structural mismatch. The run
passed its pytest wrapper (`1 passed, 9 deselected`) in 34.80 seconds. The source-exact request, result,
manifest, log, exit status, and binary/worktree provenance were generated locally for validation and
later deleted rather than versioned. This result establishes
automatic original-P filtering for this fixed entry and bounded sample. It did not execute the entry or
check Q/replay, and it did not invoke `spec_check` or a provider.

The supported shapes are integers, booleans, characters, bounded sequences/datatypes, one-dimensional
arrays, and acyclic class heaps. Classes must be visible, concrete, non-generic and non-extern without
parents/traits. Every non-ghost instance field requires a complete concrete value. Supplied ghost fields
also require supported concrete values; only irrelevant ghost fields may be omitted under the resolved
reachability audit above. Internal object allocation, generic receivers, polymorphic recursion/multiple instantiations
per helper, real/bitvector/ordinal inputs, multidimensional arrays, higher-order/infinite models, and
inaccessible independent ghost state remain unsupported or inconclusive. Alias-only imported
constructors and generic reachable targets have additional generation limits. Testing cannot infer a
missing intended specification or replace the original Dafny proof.

Limited builds with `BuildProjectReferences=false` are not full solution builds.
The Java runtime can build offline using a writable copy of the installed Gradle
cache, but Gradle and the .NET test runner require their local communication
permissions. The final environment used .NET SDK 8.0.131 and system Z3 4.8.12. These environment facts
are not proof or experiment results.

## Runtime obligation checking (verified development snapshot)

- Status: authorized implementation complete with bounded independent verification; support limits below remain explicit. Original fixed/generation/symbolic modes remain separate.
- Origin: [runtime obligation plan](../plan/2026-09-26-runtime-obligation-checking.md).
- Verified locally: 2026-09-27, working tree based on `f775837e648a3aede8521a99904fa744b4b8d4c1`.

The final root r5 evaluation and independent artifact audit are complete:
[offline results and limitations](../../../wiki/experiments/pbt-offline-evaluation.md).
M1 detects 6/6 injected implementation mutants, with no spurious report on five
included proof gaps; one verifying proof gap is excluded. All eight M2 campaigns
are unsupported before sampling because the unchanged IO drafts call ghost
functions in executable contexts. Their evaluable denominators are zero, and
their rates are null. This is the recorded IO limitation, not operational IO
acceptance; the original `IO.Init requires false` remains unchanged. These local
catalog results do not establish agent performance or general correctness.

`test-contracts request.json --runtime-check` accepts the version-1 runtime campaign
wire contract in `ContractRuntimeModels.cs`. It executes a model-supplied Dafny
generator and a detached diagnostic copy, once per sample ordinal in separate
processes. The fixed seed/ordinal random stream uses the existing counter-stream
byte layout with the `pbt-random` domain. The original source snapshots, benchmark
contracts, candidate files, and evaluator results are not changed.

The diagnostic preserves compilable ghost values and functions, strips proof-only
statements, and wraps entry/callee contracts. Loop entry, repeated loop heads, and
the final normal loop head are checked; a break does not create a final invariant
obligation. Runtime checks record concrete observations. Non-executable clauses
with capturable values use a bounded, deduplicated closed query whose only
premises bind those values. Unavailable values, heap-dependent residual clauses,
solver uncertainty, and query exhaustion remain `unchecked` with explicit reasons.
This is a runtime counterexample diagnostic, not verification and not an assertion,
frame, or termination checker.

Entry precondition rejection and unchecked preconditions are excluded from valid
samples. Callee contract violations/uncertainty, runtime failures, and sample
timeouts are counted separately. A false direct-call precondition terminates the
runtime sample before executing a callee outside its domain. Nested helper calls
are checked for executable preconditions and callee postconditions. Only valid
samples contribute goal violations, and zero valid samples is inconclusive.

Draft preparation retains the original contract and replaces only missing/scaffold
implementations after signature checking. Imported native extern bindings are
removed on replaced diagnostic declarations. Generator formals match the goal's
inputs, including compilable ghost formals and an instance receiver. Diagnostic
source mapping uses byte-offset segments to recover the supplied original source
path, line, column and hash after draft/generator insertion.

The first full build passed with zero warnings/errors. The initial behavioral
checkpoint passed 20 Driver execution tests, 7 transformation/wire tests, and 9
source-preparation tests. Follow-up tests found an invalid export fixture and a
real imported-static-receiver rendering issue; the plan records later corrections
and exact test counts. Actual root offline probes also exposed a parser-recovery
bug: parsing failures leave `Program.ModuleSigs` unset, so recovery must not call
`RawModules()` before resolution exists. The worker now returns those parser
diagnostics and preserves `transformed-sources.json` for general fixture reduction.
No paid provider calls were made.

Known current limits include generic wrapper specialization, collection-valued
`unchanged` frames, independently unavailable ghost values, nested helper
preconditions requiring a non-runtime decision, and construction of arbitrary
function-valued ghost regions. These produce unsupported/unchecked diagnostics.
The completed root offline evaluation and bounded independent reviews retain
these limits.

### T8 follow-up findings (H-E1–H-E5, 2026-09-26, implementation checks; independent review pending)

- Diagnostic scope follows the native call graph rooted at the goal (or its original
  function-by-method) and the generator. Only reachable ghost constructors, fields and
  functions become executable; unrelated logical initialization (for example a
  `requires false` constructor allocating ghost regions) stays ghost. Unreachable
  non-ghost method/function/by-method bodies become runtime traps, so unrelated native
  `{:extern}` users need no C# implementation. Contracts, constructors and overrides are
  not rewritten. A trap that executes is a runtime error, never a valid sample.
- Ghost fields actually compiled by the diagnostic are passed to the runtime bridge and
  captured as flat `name.field` values; reference values still carry no `fields`.
- A function-by-method goal additionally checks `result == <original definition>` as a
  `postcondition` obligation located at the definition text, with the definition value in
  `values` under `Goal(args)`. Goal-function calls inside obligations evaluate a compiled
  copy of the definition, never the implementation under test; a non-compilable
  definition makes such clauses non-runtime.
- Top-level calls of contract-bearing, non-generic compiled functions inside goal
  obligations go through one validity wrapper per function: evaluable `requires` must
  hold (otherwise runtime error) and `ensures` are `callee_postcondition` obligations, so
  a wrong spec function invalidates the sample instead of producing a goal violation.
  This initial restriction was superseded by R-1–R-4 below: generic and nested spec calls are wrapped too.
- Native AST facts: a `reveal`/`hide` statement range excludes its semicolon; members of
  a parse-only program have no enclosing class, so `FullDafnyName` is unavailable; a
  resolved by-method call statement keeps untyped call syntax beside its `CallStmt`, and
  calling `.Resolved` on it fails a debug assertion.
- Evidence (source working tree, Debug test build): Driver `~ContractRuntime` 46/46,
  TestGeneration `~Contract` 279/279, Driver `~Contract` 50/50, Core reducer 27/27; details
  and probe results are in the plan progress log.

### Verifier follow-up findings (D-0–D-15, 2026-09-27, implementation checks; independent review pending)

- Native facts: the resolver stores a trigger-split form of quantifiers, and `Printer`/`Substituter` emit that form;
  `forall e :: e in r ==> A && B` then prints as a conjunction of separately ranged implications, which is not
  compilable. Ghost inference silently turns such a check's local into ghost code, so the check disappears from the
  compiled program without a resolver error. Runtime rendering therefore rebuilds the unsplit quantifier.
- Structural safety net: after each diagnostic resolve the runner collects `PbtBridge.Check`/`Checkpoint` id literals
  from compiled (non-ghost) code. Any obligation missing there is re-transformed as a closed query, then as unchecked
  (`runtime_check_not_compiled`); a rendered check that fails to resolve falls back the same way. Valid samples
  support `no_violation_found` only when a goal obligation was decided in them.
- Closed queries decide a violation only when the negated clause is proven under the captured values; unprovable or
  timed-out clauses are unchecked. Solver evaluation uses function bodies, so closed clauses calling
  contract-bearing functions never indict the goal (`callee_contract_unvalidated`).
- Declared subset/newtype constraints of goal inputs/outputs and callee inputs/outputs are runtime obligations via a
  generated membership predicate placed beside the type and called through the call site's import name (resolved
  type names lose their written qualifier). Non-null reference types are subset types natively; the initial exclusion was superseded by R-6 explicit checks below.
- Execution reachability adds edges the native call graph omits: trait members to overrides, subset/newtype
  constraints and witnesses of used types, and class constant initializers read by object capture. Abstract trait
  members are never drafted. Missing drafts are limited to supplied sources and reported at original locations.
- A resolver error in an imported module (for example a draft body that uses ghost state) leaves dependent modules
  unregistered (members without an enclosing class); the runner reports this as `unsupported` with draft/generator
  locations instead of searching the partial program.
- `BoogieGenerator.Translate` keeps thread-static type-scope state; enumerating it lazily across awaits can fail an
  assertion under concurrency, so `ContractSolver` materializes the translation first.
- Evidence and probe outcomes: plan progress log entries dated 2026-09-27.


### Independent-review fixes (R-1–R-4, 2026-09-27, bounded independent review accepted)

Origin: [runtime obligation plan](../plan/2026-09-26-runtime-obligation-checking.md),
source HEAD `f775837e` plus the recorded dirty implementation. These are local engine
findings; they establish no benchmark proof or paid experiment result.

- `ContractRuntimeObligationTransformer.HasContract` and `CalleePostconditions` include
  function-by-method defining equality even when there are no explicit ensures. Detached
  definition functions preserve definition recursion; evaluated callees receive validity
  checks. Goal and callee mismatches retain their distinct classification.
- `SpecWrapper` retains non-runtime requires as callee validity checkpoints. Closed-query
  success may validate a domain, failure invalidates it, and unavailable/query-exhausted
  evidence excludes the sample as `calleeContractUnchecked`. The existing
  `callee_postcondition` validity category represents these domain checkpoints; no wire
  fields or enum members were added. Executable false spec domains remain runtime errors.
- `Check` wraps calls in callee contracts, and `CaptureOld` wraps calls when their value
  is captured in the entry heap. An invalid function evaluated only on either path can
  no longer produce a valid goal counterexample. Closed callee validity with unvalidated
  contract-bearing function dependencies remains unchecked.
- `GuardContracts` and the diagnostic `EnterContract`/`ExitContract` bridge avoid infinite
  wrapping for mutual contracts. A pending validation can be shared only for a static
  function with no declared reads and immutable scalar/collection inputs and result, using native Dafny tuple
  equality over function identity, inputs and result. Different arguments/results get
  separate checks. A reference, instance receiver, datatype or generic type may hide
  mutable state: repeating such a pending validation emits `recursive_heap_contract`
  unchecked evidence. No frame purity of an unverified by-method body is assumed.
- Evidence: new Driver regression cases cover the four reported defects plus valid
  recursive FBM definitions, decreasing and mutual scalar contracts, valid/invalid closed
  domains, valid old-state transitive calls, and a mutable-heap mutual-contract case.
  Final commands, results and build hashes are maintained in the originating plan.


### Type-constraint predicate validity (R-5, 2026-09-27, bounded independent review accepted)

`ContractRuntimeObligationTransformer.MembershipHelper` must render executable
constraint expressions through `Render`, like ordinary contract expressions.
Printing the raw constraint bypassed validity wrappers: a predicate returning true
could admit an input while violating its own requires or ensures. The fixed helper
checks predicate bodies through the existing spec-call path. Failed runtime domains
are runtime errors, unavailable domain evidence is callee-contract unchecked, and
failed predicate postconditions are callee-contract violations. None admits a goal
counterexample. No original constraint or wire field changed.

Evidence: 12 focused Driver cases passed (55s) for false/unchecked predicate domains
and good/bad postconditions on integer subsets, nested subset collections, newtypes,
nested newtype collections, and datatype-backed subsets. R-5 covers the helper path
for a subset whose base type is a datatype; R-6 below adds declared constructor-field
constraint traversal. Final owner regression/build evidence
is in the [runtime obligation plan](../plan/2026-09-26-runtime-obligation-checking.md).


### Structural declared-type validation (R-6, 2026-09-27, bounded independent review accepted)

`HasConstraint` must inspect both map key and value types and every datatype
constructor formal after type-argument substitution. Returning false beyond a fixed
depth silently admitted invalid values; finite collection nesting now has no such
cutoff. `Membership` checks finite nonrecursive datatype values with constructor
matches, then recursively checks each declared field type. Recursive datatype
membership, ghost/codatatype structure, and unsupported value membership explicitly
remain unchecked. Analysis detects declaration cycles instead of treating them as
unconstrained values. Existing serialization support limits still apply.

Dafny resolution/compilation accepts `null` assigned to a non-null class formal or
a datatype field of that type without verification. Explicit non-null membership
checks therefore belong at declared input/output boundaries. Spec and nested
function/method calls retain their declared input constraints even when no written
requires or ensures exist. Direct goal-call type failures retain call-precondition
classification; invalid spec/nested domains exclude the sample as callee validity
failures. This adds no arbitrary class heap invariants or object construction.

Evidence: 17 focused Driver cases passed (1m18s), covering invalid/valid datatype
nat fields, datatype collection fields, map ranges, five nested sequence levels,
recursive datatype unchecked results, non-null formals/fields, and spec/nested
callee formal domains. The raw null probes before this refinement falsely reported
valid=1/violation_found for both null shapes; paths and full validation checkpoints
are in the [originating plan](../plan/2026-09-26-runtime-obligation-checking.md).


Final independent evidence for R-1–R-6: required 26 structural/domain probes matched,
10 selected existing Driver regressions passed, and 4 actual CoSyn integration tests
passed against Driver `5cf53cadfd87cdd8a336050ebeb35d8e4b9d5c7874d7e443921069d17dc7727e`
and TestGeneration `d37a454ffe5f2abb4fc4dca70d9fe70d711aa6bbc5d9d56ec9e764e778e36ba3`.
The report is `/workspace/tmp/pbt-engine-structural-final-review-20260927-codex/REPORT.md`;
source and production binary identities were unchanged during review. This is bounded
engine evidence, not a proof or an M1/M2 benchmark result. Owner commands, the full
Driver run's 113-pass/1-fail stale assertion result and its corrected 1/1 scoped
recheck are recorded in the plan. TestGeneration Contract passed 279/279 and Core
reducer passed 27/27. A test-only rebuild preserved every production DLL hash;
the failed full Driver aggregate is not relabeled as passing.

The independent extra `datatype Packet<T> = Wrap(v:T)` probes with formal
`Packet<seq<nat>>` expose an existing observation-serialization limit: both `Wrap([7])`
and `Wrap([-7])` fail with `Unsupported runtime observation type`, `runtimeErrors=1`,
`valid=0`. These two predictions did not match (the complete matrix is 26/28), and
neither value was silently accepted. Recursive datatype domain validation also remains
unchecked for valid values, while supported nonrecursive counterparts remain usable.
Ghost/codatatype handling was inspected but not dynamically probed by that review.

The existing M2 ghost-draft limitation is separate: draft bodies must compile under
plan §5.1. A non-ghost body that calls ghost functions or reads ghost fields can fail
resolution; the engine returns `unsupported` with draft diagnostics. Arbitrary IO
construction and class heap invariants remain outside the authorized implementation.
Root owns fresh frozen-toolchain M1/M2 evidence.


### Multi-result output checks and backend diagnostics (R-7, 2026-09-27, bounded independent review accepted)

Dafny multi-result methods compile to C# out parameters. Datatype match expressions
compile to immediately invoked lambdas, so a generated structural membership check
that directly references an output formal fails with CS1628. Single-result methods
compile to ordinary return values and do not reproduce this defect. The diagnostic
transformer now copies executable output values into fresh locals before evaluating
their declared membership; original formal names still label captured observations.
Valid datatype/collection outputs remain accepted and invalid outputs retain goal or
callee classification. This preserves the constraints themselves.

`ContractCompilerWorker.CompileSourcesAsync` now captures backend messages via an
optional `SynchronousCliCompilation.CompileDafnyProgram` output writer. Failed compiler
results include actual backend output and reporter errors in the existing reason
field. Previously only reporter messages were returned, often hiding C# errors behind
trigger/induction information; public supervision discards unrelated worker stdout.
Other compiler callers use their original output writer by default.

Initial 11 focused regressions passed, including valid/invalid multi-result goal and
callee datatype outputs, nested seq/map outputs, and a public CLI call with a deliberate
invalid C# dependency that reports CS0103 and its undefined symbol. Final build passed
with zero warnings/errors. Final affected Driver checks passed 43/43 (3m28s), and TestGeneration Contract passed 279/279
(1m26s) after restoring missing test-output prerequisites as documented below. Full
commands and independent review are recorded in the [runtime obligation plan](../plan/2026-09-26-runtime-obligation-checking.md).
The R-7 follow-up did not rerun the entire Driver suite. Frozen r4 campaign results remain unchanged.


For no-build owner tests, verify test-output dependencies as well as the public build:
`Source/DafnyDriver.Test/bin/Debug/net8.0/` and
`Source/DafnyTestGeneration.Test/bin/Debug/net8.0/` must contain `DafnyCore.dll` and
`DafnyPrelude.bpl`. One R-7 post-build attempt lacked these files and failed Driver
12/31 and TestGeneration 200/79 (passed/failed); this was not a passing regression
result. Missing-file timestamps correlated with the preceding full build, but the
precise build-copy cause was not proven. Sequential test-project-only builds with
`-p:BuildProjectReferences=false` restored the dependencies, and before/after hashes
of every public/net8.0 production DLL matched. Preserve initial failed logs and report
retry results separately; do not rebuild production merely to repair test artifacts.


Fresh independent R-7 review accepted the bounded compiler follow-up:
`/workspace/tmp/pbt-engine-output-final-review-20260927-codex/REPORT.md`. Nine independently
authored structural campaigns / 18 samples matched expected goal/callee/draft classifications;
runtime and legacy compile-worker backend diagnostics, legacy worker success, and ordinary
CLI execution (output 42) passed. Four actual CoSyn integrations passed in 9.57s. All 40
selected source/binary identities remained unchanged, including Driver
`10d811c8f5b70f6307af073cad2dd116176de039e03eb26726b0e877dbd03489` and TestGeneration
`36f61694b37cc02cd621bc3722fd11e8ec3b15d4c23203451ffb9d1166305816`. This does not certify
unrelated generic/recursive datatype support or benchmark outcomes; owner retry results
and root frozen-toolchain acceptance are separate records.

### Entry heap runtime extension (2026-09-27, bounded implementation verified)

The [entry heap plan](../plan/2026-09-27-runtime-entry-heap-checking.md) extends the
earlier ghost-draft and recursive-membership limits described above. Generator methods
may request a separate diagnostic constructor with an ordered annotation:
`{:pbt_heap_constructor "Store.Cell", "Store.Cell.value"}`. The first argument is
the canonical fully qualified class name; following arguments are canonical instance
field names in constructor-parameter order. `ContractDiagnosticCreate` exists only in
detached campaign sources. It neither replaces an original constructor nor changes its
preconditions. A class-only annotation is allowed only when every omitted field is an
irrelevant ghost field. The existing fixed-heap validation and transitive omission
audit run against original contracts and the resolved draft/generator graph.
(2026-09-29: nested paths and default allocation of non-null object fields extend
this; see [recursive and nested heap construction](#recursive-and-nested-heap-construction-2026-09-29).)

`ContractDiagnosticResolver` defers a fixed set of ghost-context errors only for
dependency discovery. `ContractRuntimeObligationTransformer` then makes supported
ghost dependencies executable, and an ordinary clean resolve remains mandatory before
compilation. Deferred diagnostics are retained; name/type errors are fatal. Unreachable
original constructor bodies may be replaced with typed traps in the detached executable
when selected ghost fields become runtime fields. Reachable constructors retain and
check their own preconditions. Synthetic wrappers preserve `decreases *` permission.

Entry/return captures reuse `ContractStubRuntime` identities and heap serialization.
`ContractRuntimeHeapChecking` validates the original entry's complete relevant state,
unchanged object/type/field shape, immutable fields and original modifies frame.
Initial captures now apply to every entry, including runtime-only postconditions.
Concrete field checks preserve declared non-null/natural-number and nested finite
datatype/collection constraints. Ordinary nullable cycles are checked object by object
without requiring synthetic construction or solver budget. Residual refinements use
the original typed SAT premise; unavailable or unvalidated constraint dependencies
exclude the input. This also catches generator mutations after valid construction.
`ContractQueryBuilder` reconstructs the initial heap and applies captured final cells
before asking about one original postcondition; it never calls the body under test.
The runtime runner checks satisfiable initial/observed premises, original preconditions,
and native two-state Q/not-Q proofs. All actual heap queries consume the existing query
budget. Heap cache identity binds original sources, entry, inputs, initial/final heaps
and outputs, and invalid callee/state decisions precede cache reuse. Public schema 1
is unchanged; existing values maps expose initial/final evidence.
Specification exclusions follow transitive call, type, recursive and by-method
dependencies and block both heap verdict polarities. Scalar closed-query sources and
results are now retained beside heap query artifacts for failure diagnosis.

Non-generic finite recursive inductive datatype membership now uses recursive helpers
that retain nested subset constraints, including map children. Generic recursive
datatypes, codatatypes, unavailable logical values, allocation topology changes and
explicit allocation predicates remain outside this extension. Intermediate two-state
checks are not added. Unsupported or incomplete state cannot become a goal violation.

Focused evidence so far: initial Driver 11/11, then obligation/query/preparation
34/34 including the preserved allocation boundary. Expanded Driver checks passed
11/12, with the remaining rejection test corrected to expect the direct runner's
existing unsupported exception and rechecked 1/1. The first broader TestGeneration
run passed 296/297; its explicit-allocation classification regression is corrected.
Parent development probe 01 found missing synthetic-wrapper nontermination permission;
the generic entry/nested-call regression now passes. The obsolete full Driver run
was cancelled without an aggregate result. Final full owner results and fresh
independent review remain pending; these findings do not establish an M2 detection rate.

The fresh independent review reproduced three validity defects in the initial M2
implementation: invalid initial typed fields could reach runtime-only goal evidence,
transitive spec contracts were missed, and an unvalidated direct spec contract could
earn a positive heap decision. The fixes above passed 23 focused heap cases (1m50s)
and the parent observation suite passed 7/7 (30 seconds). Final dependency closure
and supported Q regressions passed 10/10 (48 seconds); final independent revalidation
remains pending. The original
review is `/workspace/tmp/pbt-m2-engine-review-20260927/REPORT.md`; its failing
reproductions remain preserved and are not relabeled as passing evidence.

The resumed review corrected the original three reproductions but found two more:
omitted empty ghost refinements and higher-order predicate references in constraints.
Omitted direct refinements now require explicit inhabitance predicates in their
original declaring scope; native reference typing alone is insufficient. Ordinary
unrefined arrows retain omission support without extra predicates. Omitted structures,
arrows or refinement chains whose nested inhabitance is erased remain explicitly
unchecked; concrete captured generic values still receive full field validation.
Dependency audits include function references used by higher-order application.

Scalar closed queries now insert into the original callable's source and use the
immutable original source set, retaining captured rewritten expressions and local
bindings. Detached ghost-backed draft bodies no longer enter native scalar query
resolution. Synthetic owners without an original declaration remain unchecked.
The parent query renderer preserves visible module aliases and imported datatype
constructors. Static names are derived from resolved declarations and the actual
query insertion module, including cloned function descriptors and class methods.
Residual type-refinement queries carry their declaration module separately from
the selected entry module, so a query inserted inside `Store` does not incorrectly
refer to its own declarations as `Store.Member` through a caller's import alias.
The final nine focused omitted-field/higher-order/source-binding cases
passed 9/9 (42 seconds); query-scope cases passed 17/17 (6 seconds). Earlier failures
and the precise unsupported nested-inhabitance boundary are recorded in the owner
plan. Final packaging, full owner suites and independent acceptance remain pending.

Generic runtime observations must carry the resolved Dafny type application: CLR
representations alone cannot distinguish `bv7` from `bv8`. Detached generic callable
signatures and diagnostic wrappers now accept explicit shape-token parameters;
nested generic calls compose them with the shared `TypeShape`/`ResolveShape`
serializer machinery. Unresolved parameters still fail closed. Generic first-class
function references are explicitly unsupported until their shape arguments can be
forwarded; generated shape-formal names are reserved to prevent shadowing.

Ghost-constructor discovery defers the assignment-specific ghost diagnostic as
well as the constructor-call diagnostic. A promoted constructor allocation must
also survive the transformer's ghost-proof-call erasure. Final ordinary resolution
and runtime checks of the original constructor preconditions remain mandatory;
ordinary and ghost `requires false` constructors both fail before goal execution.
Final packaged-suite failures that led to these corrections are retained in the
independent report; focused correction evidence belongs to the owner plan, with
full independent acceptance still pending.

Final owner acceptance supersedes the pending development checks above: supported
packaging passes; the independent reviewer ran TestGeneration 313/313 and Driver
168/168, zero skipped, plus ten independent raw regression probes. All 43 required
production/binary identities stayed fixed. Exact commands, hashes and prior
failures are linked from the owner plan and
`/workspace/tmp/pbt-m2-engine-review-20260927/REPORT.md`. Cosyn transport separately
passes 4/4. The public `cat` probe06 still has zero valid samples despite complete
entry/return captures, so this bounded engine acceptance establishes no M2
detection rate. The parent r6 population and omitted-state/solver limitations
remain separate from these passing local implementation checks.


## Runtime query optimization (2026-09-28, development)

The [optimization plan](../plan/2026-09-27-runtime-query-optimization.md) remains
in progress on dirty source based on `060d5ad532f67d5367450689225274fb0a0243e7`.
This is separate from the previous independently verified bounded slice.
Original compiled contract wrappers now preserve resolved module qualification,
including imported constructors and recursive by-method definition checks.
`ContractPhaseRecorder` retains frontend, reduction, translation and native proof
phases even on cancellation. Scoped native translation preserves the complete
visible declaration closure and checks exact query implementation coverage.
Premise queries disable verification-oriented axiom pruning; native specification
proofs retain the ordinary verifier setting. Original opaque definitions are
revealed only through the native source-visible reveal mechanism.

`ContractSpecificationChecker` certifies original callable bodies, by-methods,
refined-type constraints and witnesses in separately budgeted owner modules.
Coverage includes every emitted selected native implementation and distinguishes
assertion-free native procedures from missing declarations. Pure type aliases
have no independent native WD obligation, but their dependencies remain reached.
A source `verify false` attribute is removed only in the private certificate AST,
and every resulting obligation must actually verify; other trust escapes remain
rejected. Native cancellation now reaches `ExecutionEngine.InferAndVerify`, while
monotonic deadlines additionally prevent late verdicts or certificate caching.
The original eight-argument `DafnyMain.BoogieOnce` binary signature is retained.

`ContractInitialTypeProof` can replace global initial-heap model search only for
a fully covered compositional state. It requires the complete original type and
function WD closure, then proves exact pure captured carriers and entry inputs
using typed locals in a query with no parameters or requires. Existing host checks
validate references and heap shape; every omitted field needs affirmative
structural or natively certified inhabitance. Initialized immutable fields and
unsupported carriers keep the full consistency path. Complete native UNSAT admits uncovered carriers; the source-bound Runtime
evidence extension below can cover exact pure values already checked by compiled
original membership predicates. Exact full-request cache reuse avoids repeating its
initial consistency query; final-state consistency and original property checks
remain separate. Native false membership and failure-to-prove stay unchecked.

Local evidence before frozen integration: solution builds passed with zero
warnings/errors; initial focus112/116 exposed three incomplete fixtures and an
import-alias rendering bug, all retained and corrected. Final focused native
construction/cancellation tests15/15 passed in5s; Driver admission/cache/polarity
tests12/12 passed in57s. `make format` and diff checks passed (existing workspace
load warning). Logs are under `/workspace/tmp/pbt-m2-optimization-checks-20260928`.
Frozen04 mathematically detected one public loop mutant but exceeded10s in its
initial SAT query; frozen05 correctly rejected that late result. MBQI, additional
witness constraints and predicate type encoding did not improve the measured
query. These results establish no all-four detection or full64-sample acceptance;
those frozen public probes, full owner suites and a fresh independent review
remain outstanding. The runtime thread limit currently prevents a fresh reviewer.


The compiled-membership extension reuses existing `TypeConstraintChecks` only
when a real passed Runtime record covers the same pure constrained type and
serialized value. Metadata binds every original source path/content hash,
including imports; collected evidence also binds the exact original resolved
Program. Function result descriptors are rebound to the original function's
result formal. Draft owners/dependencies, arbitrary predicates, stale source
metadata, malformed/missing records and conflicting outcomes cannot authorize
reuse. Complete original native WD certification remains mandatory. Initial
root inputs, receiver, reference/alias shape, immutable initializer exclusions and
affirmative omitted-type inhabitance remain gates. Uncovered values still require
native typed construction. If every carrier has Runtime evidence, an internal
certificate records its exact obligation ids without issuing an empty native
query or claiming an SMT decision. Existing failed callee checks still invalidate
the sample, and final observed consistency/property checking is unchanged.

Local extension validation: build3 passed14.06s with zero warnings/errors;
29/29 native construction/provenance tests passed in7s and8/8 Driver tests passed
in21s. The actual compiled recursive getter fixture explicitly reused a function
`contractResult` type check; false carrier and invalid callee contract cases
remained inadmissible. Imported stronger-type tests reject both stale clause
metadata and an old evidence object, with native membership failure confirmed.
Logs use the `runtime-evidence-` prefix in the checks directory above. Frozen
public acceptance remains pending; this is bounded local evidence, not an
all-four detection or full-population claim.


Observed-state construction extends that certificate only when the initial cache
explicitly records constructive provenance for the exact full request. A plain
SAT result or host-only type check cannot authorize this route. Existing native
original P checking remains before observation admission. Equal captured object
identities/classes/array lengths/field sets, unchanged immutable cells, valid
references and the original frame are still checked. Full original native WD and
pure-carrier membership cover final fields and every output formal, using exact
Runtime evidence or remaining native typed assignments. Omitted inhabitants stay
unchanged across the two heaps; unsupported omissions and initialized constants
retain the full consistency path. Final positive/negative Q and callee validity
remain separate gates. Internal observed certificates record the initial key,
exact observed material, component check ids and native-proof requirement.

Evidence collection now binds original signatures without cloning function bodies
or repeatedly scanning for synthetic result names. Full-source/Program/type/value
and draft checks are unchanged. It checks external cancellation and the monotonic
campaign deadline before returning; interrupted collection publishes no partial
evidence because later records could contradict earlier positives. Per-binding
and campaign collection/preparation phases expose remaining host costs. The
function-result fixture includes an original name collision. Focused native
heap/evidence/cancellation tests69/69 passed in16s and Driver composition/evidence
admission tests12/12 passed in41s. Full owner Contract regressions are running;
new frozen performance and all-four/full64 acceptance remain pending.


The full-suite follow-up exposed two native quantified-proof regressions and a
qualification error on injected runtime helper calls. Exact frozen query profiles
showed that native proof pruning proves the original positive existential and
negative universal within the existing3s fixture bound, while broadly enabling
MBQI made the false positive universal time out. Consequently only non-model
`ClosedClause`/`ObservedPostcondition` queries use proof pruning; SAT from these
queries is a nonproof, never a state/model certificate. Premise, realization and
all model-producing queries retain every original axiom. Existing MBQI polarity
handling is unchanged. Original AST qualification now occurs before insertion of
owned runtime shape helpers. The three previous Driver failures pass4/4 locally.

Static constants create unconditional native type/allocation assumptions, and
initialized constants also create RHS equations. Constructive initial/observed
certificates therefore include their original type/witness and RHS WD closure.
Global types require structural inhabitants independently of their own native
certificate; initialized values must be closed acyclic literal, bounded conversion,
constructor or collection values with exact component compatibility. Unsupported
refined globals, function RHS expressions and unknown carriers use the original
full consistency path. Abstract nonnull references otherwise require an exact captured
original class/array witness whose complete heap is independently certified.
A bounded independent structural path can instead construct finite acyclic
logical class heaps from every instance field, including ghost/immutable fields;
constructors are not executed or assumed correct. It excludes refinements, generic
or inherited classes, nonnull cycles/arrays and initialized member constants.
Nullable references and finite datatype constructors can supply components.
Datatype member constants are excluded from structural and carrier-only paths.
An extern annotation is never evidence for called external behavior.

To avoid circularity, `ContractGlobalAssumptions` removes every axiom referring to
an exact abstract static constant Boogie function from detached specification and
proof-only query contexts, including native definition-axiom metadata. This weakens
proof premises while retaining all original assertions/procedures, so successful
proofs remain sound; SAT/model contexts are unchanged. Removed symbol/axiom identities
and counts appear in internal diagnostics. The host primitive-field shortcut now
returns unknown when static globals lack independent structural inhabitants,
including empty captured heaps. Only bodyless independently inhabited globals
retain that shortcut; initialized globals still require original native RHS WD. Native tests reject direct and transitive false witnesses;
complete campaign tests reject inconsistent globals with ordinary integer fields.
This can reduce support for empty-heap sources containing uncaptured abstract
reference globals; frozen M1/M2 performance and full-population results remain pending.


Latest local native regression:439/439 Contract TestGeneration tests pass in2.7742min
on the global-gate build (zero warnings/errors). The earlier full Driver run had
183/186 passing, with the three failures diagnosed above and retained; corrected
focused Driver cases4/4 and complete global rejection cases2/2 pass. Its complete
rerun is pending. No independent verification or all-four/full64 acceptance is
claimed by these local results.


The zero-query unrelated-native-host fixture initially exposed a conservative
support regression (Driver full2:187/188). Its original expectations and budget
were preserved. Independently inhabited bodyless globals can now retain the host
shortcut when complete finite logical class heaps are constructible; unsupported
shapes still require native consistency. Focused original isolation and inconsistent
global campaigns pass3/3. Final native suite:451/451 Contract TestGeneration cases
pass in2.7703min on build9 (zero warnings/errors); full Driver3 passes188/188 in
9.8336min. These complete suites precede the final admission guards below.

The final source audit adds two conservative gates: any original datatype member
constant blocks host/constructive admission even with empty captures, and any
captured initialized constant requires original RHS well-definedness plus original
state consistency. Omitted ghost primitive fields are included. Native SAT of an
unused readonly definition does not demonstrate full consistency: a retained raw
query returned SAT while explicitly asserting the original field equation made
the contradiction provable. Unsupported datatype member constants therefore fail
closed instead of relying on a vacuous native witness certificate.

Native query sources now exclude unused synthetic allocation constructors; the
executable allocation protocol is unchanged. They retain field exports and expose
original initialized readonly definitions through already revealed class views,
so exact captured values cannot silently replace those definitions. Same-module
and imported matching/mismatching readonly controls pass, including a previously
provided-but-opaque field. Final guard focus passes10/10 native cases and7/7 Driver
cases on build14 (zero warnings/errors). Earlier5/6 native and5/7 Driver attempts
are retained with their resolver/visibility causes in the owner plan. Full suites
on this final slice, frozen M1/M2 population acceptance and fresh independent
verification remain pending; parent runs immutable M1 probes before the next
complete suite to measure the conservative global gate's performance.

Frozen08 exposed a concrete M1 compatibility failure: initial preparation rejected
an unused ghost output, while the scalar case required another global consistency
query for every distinct input. Initial-only preparation now validates inputs and
receiver without imposing the executable output restriction. Ordinary executable
preparation and final-output checks retain their existing gates.

Constructive admission can reuse an independent global inhabitance certificate
bound to the exact resolved Program and full original source fingerprint. Complete
original type/RHS WD must already pass in the native context with abstract-global
axioms removed. Finite acyclic fresh class heaps may then use certified leaf
witnesses and pure constant arrows with inhabited codomains. The independent
certificate never borrows captured references, inputs or runtime records; the old
conditional captured witness route remains separate. Initialized static constants
retain the stricter closed structural RHS/type gate. Unsupported global shapes,
opt-out/false witnesses, cycles and initialized instance constants remain excluded.

Each input still needs exact membership and original P. Decisive host membership
now precedes residual planning; only unknown constraints use source-bound compiled
evidence or native construction. Internal certificates record independent global
scope/source/context plus host/runtime/native membership provenance. Local native
correction focus10/10 and Driver focus13/13 pass on build2 (zero warnings/errors).
The Driver fixture admits20 distinct structured inputs with a ghost output using
one native source proof under max3 queries, with no per-input query. The broader
first native run126/131 had five invalid constructor-less fixtures, corrected and
rerun separately; raw failures remain in the owner plan. Successor public64-sample
M1 probes, final complete suites and independent review remain pending.

Frozen09 subsequently validates both public M1 populations again: digit-order
64valid/63violating in168.630s and blankstreak64valid/33violating in131.105s,
each with two native queries and no unchecked/errors/timeouts. This remains slower
than the retained r6 timings25.468s/52.254s. Phase evidence identified duplicate
same-sample initial preparation and source-scope traversal inside planning.
An opaque preparation handle now owns one attested prepared object, full request
fingerprint, checker identity and exact scope. The runner certifies that scope once
and reuses the same prepared state; source/input/heap/prepared mutation or a
different checker fails closed. Existing raw preparation wrappers and every exact
membership/global/P/Q/deadline gate remain. No cross-sample shape cache was added.

Native repros also confirmed that revealing an initialized readonly field while
only providing its function or constant dependency admits a wrong captured value
in the weaker import view. Eight raw query/source/result artifacts preserve that
finding. Initial consistency queries now require visibility of the complete
original initializer function/constant definition closure, otherwise explicitly
unsupported. Captured root readonly definitions still use the query-only reveal;
no additional private dependency is exported. Same-module/revealed positive cases
remain supported, and WD certification is still separate. The bounded native
focus passes145/145 plus four private/opaque/transitive controls on the final
production slice; successor timing probes and final complete suites remain pending.

Final stable-source validation on 2026-09-28 supersedes that pending-check status:
root's supported package10 passes28.91s with zero warnings/errors; complete Contract
suites pass486/486 TestGeneration (2m50s) and195/195 Driver (9m53s), with no skips;
Cosyn transport passes4/4 (8.64s). Logs are `package10.log`,
`observed-testgen-full4.log`, `observed-driver-full4.log`, and
`cosyn-transport10.log` under `/workspace/tmp/pbt-m2-optimization-checks-20260928`.
The handed-off32-file Source set/content hashes remain unchanged. Frozen10's2205
files have manifest SHA256
`5f982bdfd41842d53474b3eba0bae8773c5beb31a5fa6c14c742b5495c19122b`.

Frozen10 probes18–21 report digit-order64valid/63violating103.047s,
blankstreak64valid/33violating109.927s, drop-stdin1valid/1violating64.705s, and
invert-exit1valid/0violating65.808s with CoreSummary still unchecked. Same-sample
reuse measurably reduces the frozen09 timings, but M1 remains slower than r6;
neither performance parity nor all-four detection is established. Actual r7-dev
populations are root-owned and underway; fresh independent review remains blocked
by the runtime thread limit. See the linked owner plan for exact commands,
artifact directories and the still-in-progress acceptance record.

Read-only proof-role analysis identifies two remaining, distinct boundaries.
Native function well-formedness validates original bodies, result refinements,
ensures and termination separately from by-method correctness. The current
contract scope and source-name implementation selection combine both roles;
there is no existing safe switch to omit the latter. A future logical-only
certificate would need separate role-aware dependency/coverage/cache identity and
must preserve actual runtime callee validation and every original P/Q/type gate.
It is unimplemented. PadLeft's original by-method invariant fails seq<char> to
seq<RawByte> membership despite six concrete runtime type/equality checks passing
in probe17. HelpTextSpec separately fails its original Bytes result membership;
it is a literal concatenation, not Utf8.Encode. Existing reducer folding supplies
no original-definition type proof, and native hint attempts did not establish one
within budget. Neither declaration may be silently trusted. Current downstream
Q cost remains unknown while this proof gate blocks it.

The full frozen10 r7-dev M1 population subsequently completes36 rows/12 variants
in1441.191832s: detection6/6 mutants and spurious reports0/5, excluding the one
verifying original from those denominators. Its11 PBT campaigns return704
generated/executed/valid samples and282 violating samples, with zero errors,
unchecked samples or timeouts. There are36 violation records,277294 runtime clause
evaluations and zero closed-SMT clause evaluations; native validity certification
is a separate activity. PBT campaign times are97.537–117.985s,1200.807s total.
Full M1 wall time materially regresses versus r6's670.248s despite preserved
detection and validity. Root's mechanical audit passes2754 checks/117 summary-field
comparisons (`/workspace/tmp/pbt-r7-dev-mechanical-audit-20260928/m1-evidence.json`);
this is not fresh independent verification. Full M2 is running in root-owned
`pbt-r7-dev-m2-20260928`, with results under
`/workspace/tmp/experiment/pbt-offline-20260928-m2-r7-dev`. Full M2/all-four acceptance
and independent review remain pending; no further engine change was made.

Full frozen10 r7-dev M2 subsequently completes24 rows/eight variants in2082.009492s:
3/4 mutants detected and0/4 spurious reports, with invert-exit still undetected.
167 samples are generated/executed,159 valid and54 violating; all eight campaigns
have one sample timeout, with no other population error/unchecked-precondition/
callee counters. Separately,159 original CoreSummary clause evaluations remain
unchecked (`callee_contract_unvalidated`);1563246 runtime clause evaluations and
zero closed-SMT decisions produce nine retained loop-maintenance violation records.
PBT campaigns take181.446–194.539s. Root's mechanical audit passes2582 checks/117
summary comparisons (`/workspace/tmp/pbt-r7-dev-mechanical-audit-20260928/m2-evidence.json`),
without constituting independent verification. All-four detection is not achieved.

A subsequent recording-only draft reuses a process-local append writer while
flushing every completed record, and caches only immutable parsed shape metadata
by its complete encoded token. It does not reuse processes, values or verdicts,
drop records, or change budgets/reservation policy. Build1 and nine generated-runtime
cases plus13 existing runtime controls pass; final handoff/measurement is still
pending. Frozen10's full-suite results apply to frozen10 only. The checked sequence
proof-step follow-up remains planned after the recording baseline; the separate
logical/by-method certificate split remains design-only.

Recording-only local checks complete: build16.33s with zero warnings/errors;
9/9 generated bridge cases (2s),13/13 existing runtime observation/timeout/isolation/
generic controls (29s), and4/4 non-runtime serialization controls (23s), all without
skips. The cases retain every repeated/mutated value record, generic shape widths,
Unicode/reference identity, completed lines visible before abrupt process kill,
explicit early exits, error-after-complete and malformed/unsupported rejection.
Format and diff checks pass; exact commands/exit statuses and33-file source hashes
are in `recording-source-manifest.json` (SHA256
`700770318bfdc8c2c77f9955e10d59ecda391efe3a6d27979f181fbb3ca66c2a`) under the existing
check directory. Only Instrumentation/StubRuntime and the new RecordingTests differ
from frozen10's source handoff. Source/native ownership returns to root for
recording-only freeze11 measurements and complete-record conservation checks;
performance and final-source full validation remain pending.

Frozen11 recording diagnostics now finish. Common18 completed stdin samples have
byte-identical ordered traces (186706 records/237853519 bytes); their mean sample
time falls4.147538s→3.760453s in this development comparison. The new stdin campaign
admits20 samples versus18, taking185.856s versus181.446s; this is not an end-to-end
latency improvement or statistical claim. Exit admits19 samples with no violation,
and both M1 diagnostics preserve64 valid samples and prior violation counts.
Original CoreSummary remains unchecked. The root retains immutable file checks
and exact comparison evidence; these results apply only to recording-only frozen11.

The separate sequence-refinement draft inserts plain native checked assertions
for original sequence elements/prefixes/appends while retaining every original
command, assertion, predicate, token and attribute. It recognizes only the actual
unique native prelude identities and preserves unsupported/exhausted obligations.
Focused native/import/checker/deadline controls pass61/61; global-witness/source
controls pass9/9. However, original CatSpec cold module proof (`sequence15`) and
isolated original HelpTextSpec (`sequence16`) both cancel under the unchanged10s
limit. Separate structural inspection of the latter retains15 commands and one
original assertion, adding2668 assertions without exhaustion. That inventory is
not a successful native proof. Long synthetic concatenations pass, but the public
original sequence proof and exit detection remain unresolved. No logical/by-method
role split is implemented, and no final-source full-suite result is yet available.

The subsequent actual-route warm replay (`sequence17`) resolves this distinction:
both original initial scopes exactly match the74 saved probe22 declarations.
BenchWorld and IOContract certify in6.874s/4.474s on one checker, retaining each
10s limit; then original entry-scope CatSpec verifies2/2 implementations with zero
errors in7.128s (2.008s translation,57.57ms checked-step insertion,5.039s native
Boogie pipeline). The timed proof retains all15 HelpTextSpec commands and its
original refinement assertion plus2668 verified steps. Unsupported ErrorMessageSpec
receives no steps and still passes its original proof. Cold15/16 timeouts remain
limitations, but actual cached-frontend CatSpec proof now succeeds. This does not
accept the whole CoreSummary scope, any input or a campaign; the separate PadLeft
execution-role gate and all-four detection remain pending. Driver controls pass7/7;
format/diff and post-format build6 pass. Final full suites and independent review
are still pending on the eventual final source.

The following role slice is implemented and focused-checked (2026-09-28),
superseding the earlier unimplemented-role status above. Only original entry
heap-postcondition dependencies request logical certification. Their traversal
excludes the separate by-method body while retaining original logical definition,
defaults, pre/postconditions, types/witnesses and invoked proof methods. Native
well-formedness, correctness and override evidence has distinct declaration-role
identity; logical acceptance cannot authorize runtime callee/type evidence.
Original execution reachability remains unchanged.

Focused native checks pass98/98 and actual Driver campaigns14/14. They include
invalid executed by-method rejection, invalid logical definition rejection despite
a contract-matching by-method return, direct proof assumptions, source/import
identity, logical override checks and unused contradictory ensures. Initial
compile errors and48/51 fixture-label failures remain recorded in the owner plan
and `role-*` logs. Original CoreSummary/exit campaign proof remains unmeasured on
this source until frozen12; full suites and independent review are still pending.

Frozen12 actual one-sample probes26/27 both pass all original logical and observed
state gates. Stdin detects its loop violation; exit remains unchecked: positive Q
is only a nonproof and negative Q times out at10.108s. User steering selected
bounded partial evaluation instead of MBQI adjustment; the MBQI diagnostic never
ran. This supersedes the prior unmeasured-role campaign statement above.

The first state-aware reduction implementation is now focused-checked. It derives
entry/current field facts from original query requirements and straight-line writes,
canonicalizes explicitly equal reference formals, and invalidates all possible
aliases unless original disequalities separate them. Readonly fields remain fixed.
Old changes heap reads, never evaluated formal/local values; read-dependent calls
are unfolded only after caller actual values are captured. Original expression and
function bodies are detached before mutable rewriting, and heap-context literal
cache reuse is disabled. Exact original visibility and resolved reveals remain
required. Unknown cells, labels, higher-order calls, proof statement expressions,
unsupported effects and exhausted/deeper terms remain residual.

The query keeps all original commands and the original target assertion. A separate
checked iff may make a residual form available, but a failed iff is a native error,
never a target counterexample. Existing native WD, declaration coverage, state
admission, both-polarity, deadline and runtime-callee gates remain unchanged. Shared
depth2/100 quantified instances/10000 nodes are unchanged, including partial results
on exhaustion. `old(Delta(c))` for a two-state function is rejected by the native
resolver; it is not supported by projection.

Final focused Core reducer/PartialEvaluator tests pass98/98, native heap/query/phase/
certificate tests141/141 and actual Driver transitions/admission/callee/role/budget
controls15/15. Failed syntax/export fixture attempts are retained in `heap-pe-*`
logs and the [owner plan](../plan/2026-09-27-runtime-query-optimization.md). Frozen13
actual reduction counts, residuals, timing and exit detection remain unmeasured;
full final-source suites and fresh independent review are pending. General trace
existentials and deeper definitions may remain residual, so this is not all-four
M2 completion or a performance claim.

### Checked heap-equivalence boundary (2026-09-29 development)

Frozen13 probes28/29 did run and report a non-target
`contract_reduction_equivalence` failure; this supersedes the preceding unmeasured
status. The resumed [owner plan](../plan/2026-09-27-runtime-query-optimization.md)
records immutable sources and diagnostics under
`/workspace/tmp/experiment/pbt-m2-pe-equivalence-20260929`.

The query reducer now receives `program.ModuleSigs[owner].VisibilityScope`, as the
existing body expander/heap factory do. ModuleDefinition's own scope omitted
imported reveals, including the diagnostic DisableScopes route. New import tests
fail3/4 before this change and pass4/4 afterward, including the genuinely hidden
body control with scopes enabled. This fixes missed unfolding but does not solve
the retained large query: its existing depth2 is consumed before imported getters.

A small generic native fixture reproduces the failed iff after rewriting an
unbounded existential body; removing let/match or getters does not fix it, while
removing the quantifier does. A native one-level function expansion preserving the
quantified body verifies. A checked pointwise body equality is insufficient to
prove the rewritten existential equality. These observations establish a native
proof-support boundary, not an unsound concrete heap substitution or a proven
backend cause. The earlier canCall/trigger hypothesis remains unconfirmed.

Heap reduction therefore attempts existing finite-domain unrolling before touching
quantified bodies, using the same shared instance/depth/node limits. An unavailable
domain preserves the original body, range and triggers and records
`unbounded_quantifier`; scalar reduction is unchanged. Original target, native WD
and checked outer iff remain mandatory. Owner validation passes Core100/100 and combined TestGeneration157/157, including
finite-positive projection and finite-negative failed-iff rejection. That negative
case remains explicitly unsupported: reduction's literal false does not become a
counterexample without the original checked equivalence.

Retained Q28 completes8.214s with only the original target nonproof and no failed
auxiliary iff; it keeps all9 original statements and all original function bodies.
Its unbounded residual uses1 inline/60 nodes/532 expansion nodes and0 reads. Q29
hits10s (10.113s measured) and remains unchecked. These direct, warmed diagnostics
are not full campaigns or latency comparisons. Final format/package, Driver checks
and fresh review transfer to root; no actual CoreSummary detection, general
existential support or speedup is claimed. Exact preformat source/artifact identity
is in the owner plan and `owner-source-manifest.json` (SHA256
`8051016fe29f865dafc076527920ab8b3d6a1092f819769538159850c86f7472`).

### Captured ghost inputs and closed-clause names (2026-09-29)

Supported ghost formals now enter initial-state-only preparation. Their exact
captured values still undergo the original type/requirement/dependency checks;
ordinary executable/final-state preparation retains its ghost restriction.
Missing captures, wrong value kinds, unsupported higher-order types and invalid
refinement membership do not become valid samples. This extends initial
certificate construction, not ghost lemma execution.

Closed-clause parameters and captured datatype values now reuse the resolved,
type-directed qualification used by initial type proofs. Inferred local types
can lose their source import spelling; printing Type.ToString alone may produce
an unresolvable or shadowed name. Preserve subset constraints and qualify nested
collection/generic declarations and runtime constructor identities in the actual
insertion module. Original target assertions and native WD checks are unchanged.
Captured declarations can also originate from another resolved snapshot: built-in
nat recognition must use its canonical declaration and system-module identity,
not object reference equality against the current program. The first historical
attempt exposed this gap; four cross-context controls reproduce it before the
fix, and all12 closed-type controls pass independently afterward.

Plans: [ghost initial validity](../plan/2026-09-29-ghost-initial-validity.md),
[closed-clause types](../plan/2026-09-29-closed-clause-types.md).
Final source at060d5ad plus recorded working tree passed owner157 native controls,
191 affected controls after the nat fix, and fresh independent44 affected
native/42 reducer/7 Driver/12 final type controls. Root historical reruns are
complete with no additional confirmed counterexamples. Their outcomes and
remaining limits are separate from engine unit/proof validation and recorded in the
[root follow-up](../../../plan/2026-09-29-pbt-m2-historical-followup.md).

### Exact reduction and finite-prefix counterexamples (2026-09-29)

Status: implementation independently checked against revision060d5ad plus the
source manifest in `/workspace/tmp/experiment/pbt-inconclusive-20260929/independent/`.
Originating [optimization plan](../plan/2026-09-29-inconclusive-runtime-optimization.md)
and [prefix plan](../plan/2026-09-29-runtime-prefix-counterexamples.md). Historical
campaign outcomes are tracked separately in the root plan.

Closed concrete bindings reuse the PE concrete-value predicate, including
maps/sets/multisets/bitvector conversions and datatypes. Exact existential
reduction can decompose single-constructor products, fixed-length sequences and
acyclic point equalities under the unchanged shared expansion budgets. Concrete
witness instances are separately checked assertions; the original target and WD
checks remain mandatory. Native failure of an auxiliary assertion is not target
SAT or a counterexample. Unresolved dependent sequence products and deeper
function definitions remain residual. The solver uses the resolved module
signature's visibility scope; hidden definitions remain hidden. Substitution
reservation counts actual identifier occurrences, including duplication, while
retaining the shared node cap. Source: `ContractSolver`, `ContractExpressionReducer`,
`PartialEvaluatorEngine`, `PartialEvaluatorVisitor`, and their witness controls.

Control characters are emitted as `(code as char)` in captured-value Dafny
source, valid in Unicode and legacy modes. Concrete char conversions decode
escapes rather than indexing their raw source spelling. Non-BMP conversions
without an exact mode-independent fold remain native obligations. Original
bounds/definedness checks remain present (`ContractModelCodec`, character tests).

Runtime structural reuse accepts only exact known immutable Dafny containers and
recursively immutable generated datatype graphs. Keys include object identity,
full shape and, for named fragments, exact name. Every reference registration
clears structural caches so nested identity changes cannot leave stale encodings.
Mutable graphs and custom external sequence implementations keep their existing
paths. Cached encodings do not replace any check or record. The preparation name
family is shared per transformer; mutable callable descriptors are not shared.

For an incomplete execution, a finite prefix ending in a recognized compiled
false original loop invariant may establish a counterexample. The runner selects
it before collecting inputs, type evidence, heap captures or called contracts.
Every prior initial/entry/callee validity gate still applies. Missing input or
entry capture, earlier malformed records/runtime errors, and unchecked or failed
callee contracts cannot support it. Suffix evidence is never used. A separate
`prefix-certificate-<ordinal>.json` retains source identity, endpoint/count, raw
trace SHA256 and original timeout/error/completion flags. `population.valid` can
therefore include validated prefixes and must not always be described as normal
termination. Full raw traces remain intact; a postcondition without return is
not admitted by this route.

Fresh independent checks passed Driver32/32, Core62/62 and native query83/83,
with no skipped tests and unchanged source hashes during validation. This proves
the tested engine behavior, not historical detection or absence of further bugs.

The second pass expands equality of compatible resolved inductive constructors
into all field equalities under the same shared node budget; disjoint compatible
constructors reduce to false. Ghost constructors/fields, coinductive values and
unknown/incompatible types remain residual. A concrete existential witness may
contain locally bound expression variables, but no free bound variable may
escape. Statement expressions participate in this guard. The existing utility
can conservatively reject statement-local binders; this limits coverage without
authorizing an invalid witness.

Scalar runtime clauses now validate their original specification dependency
closure after a closed clause has been decided. `ContractRuntimeClauseDependencies`
requires exact source-set/content hashes, owner, path, kind, location and source
text before returning an AST expression from the original program. Unsupported
or ambiguous mapping remains unchecked. Native dependency checks reuse trust,
well-definedness, query-count and deadline gates; a successful detached clause
query alone never certifies its pure function definitions. This path is separate
from existing heap dependency validation. UTF-8 token-end mapping may fail
conservatively for some non-ASCII-ending clauses; no unsupported mapping is
accepted to improve coverage.

Fresh independent second-pass review passed Core33/33, native query21/21 and
Driver14/14 focused controls. Broader owner controls passed Core75/75 and native
75/75; these overlap and must not be added into a unique-test count. The earlier
reviewer's static-only attempt ended at a provider usage limit and is not a
completed native verification. Source hashes and actual review are retained in
`/workspace/tmp/experiment/pbt-inconclusive-20260929/independent-v4-sol/verification.txt`.
Origin: [engine plan](../plan/2026-09-29-inconclusive-runtime-optimization.md),
[dependency plan](../plan/2026-09-29-scalar-clause-dependencies.md), and the linked
root historical follow-up. Verification date2026-09-29, engine HEAD060d5ad with
recorded working-tree source hashes; historical results are recorded separately.

### Ordered native proof composition (2026-09-29)

Status: bounded implementation independently verified at HEAD060d5ad plus
`pbt-sequential-20260929/quantifier/source-manifest-ordering.sha256`.
Origin: [compositional proof plan](../plan/2026-09-29-compositional-contract-proofs.md).
Source: `ContractExpressionReducer`, `ContractReductionResult`,
`PartialEvaluatorEngine`, `PartialEvaluatorVisitor`, `QuantifierBounds` and
`ContractSolver`.

`ReduceForNativeProofComposition` is an explicit closed-scalar query path.
Ordinary `Reduce`/`ReduceWithHeap` keep their previous depth and witness behavior.
Each local prerequisite uses the configured inline depth, while root and all
proof goals share one node allowance and one quantifier-instance allowance.
Node admission and cloned/substituted expressions consume those shared budgets.
This is compositional proof search, not a globally identical inline-depth policy.

Eligible pure, transparent, revealed, closed nonrecursive Boolean calls become
native predicate assertions. Concrete existential witnesses, prerequisites and
parent calls form one ordered certificate; every assertion and the unchanged
original target must verify natively. Native auxiliary errors never authorize a
target violation. Recursive/opaque/heap-dependent or escaping-binder calls remain
residual. A direct positive-conjunct call in a retained closed witness can create
a new bounded proof node without inlining the ordinary expression at depth0.

Preserve causal order across nested candidate discovery. Earlier witnesses must
be emitted before a newly discovered predicate they can establish; that predicate
must precede a later witness that uses it. Buffer the entire root candidate or
root witness transaction, and publish obligations and reusable completion state
only on success. A failed transaction retains spent work but publishes no partial
certificate. Correct order materially affects native solver cost even when the
number of assertions and budget are unchanged.

Composition-only empty-product inference handles a proven empty integer factor
even when another generated trigger binder is relational. Witness/candidate
side channels must not escape vacuous forall, dead branches or negative/guarded
contexts. Local forall witness collection is conservative; general nested
quantified or unknown-length sequence support is not established.

Independent checks pass Core93/93 and native87/87. Additional frozen controls are
11/12: a negated-witness3s deadline test also times out on immutable v4 at3s/10s
and remains a recorded coverage limitation, not a passing test. Retained h07
positives verify at6.619/6.708s under10s; opposite assertions are not proved.
Retained h08 relations remain nonproof. These diagnostics do not establish
historical case-level detection; final campaigns belong to the root plan.

### Captured ghost goal heap observations (2026-09-29)

Status: bounded implementation independently verified at HEAD060d5ad plus
`pbt-sequential-20260929/heap/source-ready.sha256`. Origin:
[observed ghost input plan](../plan/2026-09-29-observed-ghost-inputs.md).
Source: `ContractRuntimeObligationTransformer.Check`,
`ContractHarnessBuilder.PrepareObservedHeap`, `ContractRuntimeHeapChecking.Prepare`.

A supported ghost input can participate in an original goal heap postcondition
only when the exact formal has been captured. The named internal observed
preparation route permits these inputs while public execution preparation and
reachable preparation keep their previous restrictions. Ghost outputs remain
unsupported. Every input is selected exactly, even when irrelevant to the clause;
entry and return heaps retain distinct observation roles, original aliases,
old/current values, type/omission checks, frame and source/dependency/trust gates.
This does not add per-callee entry/return/receiver/occurrence snapshots.

Independent native133/133 and Driver12/12 controls pass, including both original
postcondition polarities, unsupported/missing values, ghost/reference aliasing,
native definedness and unvalidated specification behavior. Commands and frozen
source identities are in `pbt-sequential-20260929/independent-heap/attempt-1/`.

Retained h15 ordinal0 now records an actual17-object entry and17-object return
heap, exact original30 inputs, exit0 and completion. Its original goal is eligible
for closed SMT, but no Q query is decided: original logical dependencies fail
three seq<char>-to-seq<RawByte> checks. Preserve `callee_contract_unvalidated`;
capturing return state does not license skipping these failures. The target is
an unfinished assertion-only implementation, not an established historical bug
detected by this change. The first stale-CLI attempt is separately retained;
the corrected derived summary and actual DLL hashes identify the usable replay.

### Exact native membership proof reuse (2026-09-29)

Status: independently accepted at HEAD060d5ad plus
`pbt-sequential-20260929/reuse/owner-attempt-03/source-manifest.sha256`.
Origin: [membership reuse plan](../plan/2026-09-29-exact-membership-proof-reuse.md).
Source: `ContractRuntimeCampaignRunner.QueryHeapAsync` and campaign-local state;
behavioral controls in `ContractRuntimeHeapTests`.

Completed native Unsat proofs of unconditional pure-value membership queries can
be reused within one campaign. Exact identity includes full query text, ordered
diagnostic source contents with raw/canonical paths, replacement source path and
query name. The campaign lifetime fixes solver context. Every new state's
original source/scope/dependency, host/runtime membership, reference/alias,
omission and global inhabitation checks still run. This cache cannot stand in for
an entire heap premise or a changed original postcondition.

A hit saves a closed-query slot, including after the shared cap is exhausted;
misses and specification checks retain the same shared budget. Query construction
and identity work stay within the deadline, and token/deadline checks precede
receipt/cache publication. Only completed native Unsat results are reusable;
host-only, unsuccessful, timed-out or cancelled attempts cannot populate the cache.
Each unique reuse receipt links exact original query/result filenames and hashes;
hits never create a second native result file.

Independent21/21 campaign controls and a separate artifact audit establish exact
distinct-heap and initial-to-observed sharing, invalid-state rejection, changed
value and campaign/source isolation, and unsuccessful-proof nonreuse. A controlled
FIFO write verifies external cancellation after lookup prevents final publication.
Internal timer scheduling and immutable source/path/order/name context are
static-only coverage. Evidence and retained setup failures are under
`pbt-sequential-20260929/independent-reuse/`. This is proof reuse coverage, not a
historical detection or broad speed claim; full campaigns remain root-owned.

### Ordered runtime check fragments (2026-09-29)

Status: verified for the bounded transport change at engine HEAD060d5ad with the
four-file manifest `pbt-sequential-20260929/runtime/source-freeze.json`. Origin:
[ordered runtime fragment plan](../plan/2026-09-29-ordered-runtime-check-fragments.md).

Generated Check/Checkpoint calls now transport ordered fragments instead of
constructing and parsing the full values object on each call. The exact returned
Rune object weakly identifies its complete materialized JSON object, including
flat runtime fields. The converter emits every property in original order,
including duplicate labels. Existing identity/label/full-shape/recursive immutable
checks remain the only cross-call reuse gate. Mutable observations remain fresh;
registration clears the associations. Any unknown fragment uses the complete
legacy object parse before Write, preserving malformed-input error behavior.
InputValues and heap captures keep their existing encoding. Boolean evaluation,
record order, failed-call completion/exit, newline and per-record flush remain.

Independent Driver22/22 and a separate raw measurement audit pass. The frozen h11
program uses seed3454598619081119827, ordinals0/1, three alternating pairs each,
and the unchanged5s limit. Baseline arms all time out; new ordinal0 completes in
3.425–3.575s and ordinal1 in4.176–4.228s, each with exit0 and one final complete
record. All6 overlapping raw prefixes match (301781 records total). This is a
specific runtime observation, not a historical campaign verdict or statistical/
general speed claim. Raw traces, CPU/wall values, failures and all source hashes
are retained under `pbt-sequential-20260929/runtime/`; independent evidence is
under `independent-runtime/`. An initial fixture-offset failure and a generic-comma
measurement-parser failure are preserved rather than counted as passing checks.

The executable-only rewrite preserves source metadata and every non-argument
span. There are682 Check calls across649 physical lines plus268 Checkpoint calls:
950 actual edits, not917. Count occurrences, not matching lines, when auditing
nested generated calls. Final supported formatting changes no C# file; package
build and transport4/4 pass. Full campaign results remain a separate root report.

### Runtime classification deadline boundaries (2026-09-29)

Origin: [classification deadline plan](../plan/2026-09-29-runtime-classification-deadline.md).
Status: bounded source/native checks and root historical artifact acceptance pass.
Frozen runner SHA-256:
`d1e0291efb310d680002492478682d836a3e0464f79d82c2dd9f3c9aafaac87f` at
engine HEAD `060d5ad532f67d5367450689225274fb0a0243e7`.

The campaign classifier retains each parsed record but materializes its complete
values dictionary only when consumed. Every false runtime check and every
ClosedSmt checkpoint still decodes directly from the JsonElement with the same
ContractJson options, at most once per record. False entry checks retain strict
decoding even when no counterexample is emitted. Canonical dictionary
serialization still identifies query cache entries. Counts, record order,
finite-prefix bounds and emitted counterexample values retain their semantics.
Separate successful type-constraint evidence may still decode an individual
nested value because exact type proof reuse consumes it.

Cancellation is checked before the existing campaign clock at every expensive
initial-state phase boundary. Guards before and after synchronous type,
dependency, preparation and construction work prevent expired results from
starting later phases or admitting an unvalidated initial state. Existing query
and constructive result checks remain conservative. An already-started phase
may finish; observed campaign expiry marks precondition-unchecked with
campaign_timeout. Caller cancellation propagates. This is a campaign validity
boundary, not permission to omit false records or claim the remaining trace is
verified.

Owner30/30 and fresh independent Driver23/23 pass. Independent build has zero
warnings/errors; frozen source and dirty-state receipts remain unchanged.
Exact between-phase timer scheduling and cancellation at these new guards have
static control-flow coverage, not a dedicated dynamic fixture. Independent raw
artifact audit confirms h11 returns its result at252.039s with no initial phase
start after240000ms; nine expired inputs stay unchecked and valid samples remain0.
The h13 ordinal1 replay request/result and173-record certified prefix are
byte-identical to the immutable v4 sentinel. Its post-endpoint tail differs but
does not enter the validated prefix. These results preserve an existing detection
and correct result return; they do not establish h11 goal validity.
Evidence: `pbt-sequential-20260929-v6/classification/` and
`independent-classification/`. Final packaging preserves this source byte for
byte, with no formatting changes and transport4/4 passing.

## Recursive and nested heap construction (2026-09-29)

Plan: [recursive and nested heap construction](../plan/2026-09-29-recursive-and-nested-heap-construction.md).

- `object` references: heap values, cells and inputs typed `object`/`object?` accept any
  captured heap object (class instance or array); other reference types still need the
  exact class. Initial validity decides such references by captured-object existence.
  This admits the standard recursive `ghost var repr: set<object>` / `Valid()` idiom,
  which previously failed every sample with `Reference value has an incompatible heap
  type`.
- Cycles: fixed-state preparation (initial and observed-heap queries) accepts cyclic
  heaps such as a node whose representation set contains itself, because query objects
  are parameters. Executable unit-mode allocation still rejects cycles.
- Nested construction: `pbt_heap_constructor` arguments may be paths `C.f.g...`. The
  field `f` is allocated inside the generated constructor with an engine-generated
  constructor of `f`'s class taking the remaining segments; the root constructor takes
  the leaf values in annotation order (parameters named by path, for example
  `fsRegion_value`). A field cannot be both a parameter and a nested allocation.
- Defaults: every unmentioned non-null field whose class is diagnostically
  constructible (by the same class rules) and does not recurse is allocated with a
  default object; otherwise a ghost field keeps the omitted witness and a runtime field
  is rejected, as before. This also applies to class-only annotations.
- Names: the annotated class keeps `ContractDiagnosticCreate`; other shapes of a class
  get `ContractDiagnosticCreate_<n>` (the whole prefix is reserved). Each generated
  constructor lists its supplied fields in `{:pbt_supplied_fields ...}`; the
  transformer and resolved omission audit read that list instead of parameter names.
- Evidence: M2 `m2-drop-stdin` with the existing 17-annotation, 106-line generator and
  with a one-annotation, 53-line nested generator (4 samples each) both give
  `violation_found`, 4/4 valid, 3 reported violations (scratchpad `heapexp/`).
- Validation: build 0 errors; Core 93/93, TestGeneration 649/649, Driver 251/251 (7 new
  Driver cases, 4 new preparation cases); Cosyn goal-PBT integration 4 passed; fresh
  independent review found requirements met.
- Limits: one allocation per node remains inherent for variable-length structures
  (generator loops); trait-typed references other than `object`, generic or trait
  classes, and recursive default allocation are unsupported. Unit-mode hybrid testing,
  including model heap realization/replay, still rejects cyclic heaps.
