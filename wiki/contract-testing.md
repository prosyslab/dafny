# Contract testing boundaries

- Status: verified bounded implementation; local acceptance and independent review completed.
- Verified: 2026-09-13, working tree based on `1eb9fc5fa2661483de151ff85b21eed0b695878a`.
- Origin: [implementation plan](../plan/2026-09-12-expecto-residual-constraint-solving.md).
- Symbolic-entry extension: [implementation plan](../plan/2026-09-13-symbolic-entry-contract-checking.md).
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

The supported shapes are integers, booleans, characters, bounded sequences/datatypes, one-dimensional
arrays, and acyclic class heaps. Classes must be visible, concrete, non-generic and non-extern without
parents/traits; every declared field must be visible, mutable, non-static and non-ghost, with a complete
snapshot. Internal object allocation, generic receivers, polymorphic recursion/multiple instantiations
per helper, real/bitvector/ordinal inputs, multidimensional arrays, higher-order/infinite models, and
inaccessible independent ghost state remain unsupported or inconclusive. Alias-only imported
constructors and generic reachable targets have additional generation limits. Testing cannot infer a
missing intended specification or replace the original Dafny proof.

Limited builds with `BuildProjectReferences=false` are not full solution builds.
The Java runtime can build offline using a writable copy of the installed Gradle
cache, but Gradle and the .NET test runner require their local communication
permissions. The final environment used .NET SDK 8.0.131 and system Z3 4.8.12. These environment facts
are not proof or experiment results.
