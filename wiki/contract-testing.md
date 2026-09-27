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
