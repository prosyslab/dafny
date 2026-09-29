# Recursive heap structures and nested diagnostic construction

Status: done

Engine maintenance requested by the user (2026-09-29): make generators for
recursive class structures work, and let one `pbt_heap_constructor` annotation
allocate nested objects instead of one annotation plus one manual allocation per
object. Local controls only; no provider call, no benchmark or evaluator change.
Owner: this engine. The main agent implements (context already loaded); a fresh
independent agent verifies.

## Inspected evidence (local campaigns, scratchpad `heapexp/`)

- Plain `Node { value; next: Node? }` lists built node by node already work
  (diagnostic or original constructor; both polarities decided).
- The standard `ghost var repr: set<object>` + `Valid()` list fails every sample
  with `initial_heap_validation_unavailable: Heap value at 'pbt-reference-0.repr[0]':
  Reference value has an incompatible heap type.` `ContractHeapFactory.IsExactReferenceType`
  requires the expected type's class to equal the object's class, so `object`/`object?`
  never matches. `ContractRuntimeHeapChecking.CheckWithPlan` also leaves `object`
  references undecided.
- With `set<Node>` the same list works until a postcondition needs a fixed-heap
  query (for example a twostate predicate): `ContractHeapFactory.Prepare` always runs
  `TopologicalOrder`, which throws `Cyclic synthetic heap graphs are not supported.`
  because `repr` contains the node itself. Queries bind slots as parameters and do
  not need allocation order; only executable allocation does.
- Nested construction (M2 cat): 17 annotations, 16 field names and 16 manual
  allocations for one `BenchIO.IO`. `ContractDiagnosticConstruction.Parse` accepts only
  one-segment field names; the transformer and `AuditResolved` infer supplied fields
  from constructor parameter names.

## Objective and acceptance

1. `object`/`object?`-typed references (fields, collection elements, inputs) accept any
   captured heap object in fixed-state preparation and initial validation.
2. Cyclic heaps are accepted when no executable allocation order is needed (initial
   and observed-heap queries); executable unit-mode allocation keeps rejecting cycles.
3. `pbt_heap_constructor` accepts multi-segment paths `C.f.g...`: `f` is allocated
   inside the generated constructor with an engine-generated nested constructor of
   `f`'s class, whose parameters are the remaining segments; the root constructor takes
   the leaf values in annotation order. Unmentioned non-null class-typed fields are
   default-allocated when their class can be default-constructed by the same rules;
   otherwise the existing rules apply (ghost: omitted witness; non-ghost: error).
   One class gets one generated constructor; conflicting shapes are rejected.
4. Generated constructors record their supplied fields explicitly
   (`{:pbt_supplied_fields ...}`); the transformer and resolved omission audit use it.
5. Existing behavior is unchanged for annotations without nested paths and without
   omitted non-null class-typed fields; all existing contract suites pass.

Non-goals: builders from inductive datatype values, variable-length recursive
allocation without generator loops (one allocation per node remains inherent),
trait-typed references other than `object`, changing the M2 cat generator or prompts.

## Change table

| File / symbol | Change | Validation |
| --- | --- | --- |
| `ContractHeapFactory` `IsExactReferenceType`, `IsReferenceType` callers, `TopologicalOrder`, `Prepare` | `object` compatibility; cycle-tolerant ordering when allocation order is not required | New Driver controls; existing suites |
| `ContractHarnessBuilder.Prepare` | Request allocation order only in execution mode | Existing suites |
| `ContractRuntimeHeapChecking.CheckWithPlan` | `object` references decided by captured-object existence | New Driver control |
| `ContractDiagnosticConstruction` (`Parse`, `AuditResolved`, declaration text) | Path parsing, nested/default allocation, supplied-field attribute | New preparation and Driver controls |
| `ContractRuntimeObligationTransformer` constructor | Supplied fields from the attribute | Driver controls |
| `ContractQueryBuilder.QualifiedType` | Internal reuse for nested parameter types | Build |
| `DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs`, `DafnyDriver.Test/` new heap-construction tests | Behavioral controls | dotnet test |
| `wiki/contract-testing.md`, `wiki/INDEX.md`, this plan, `plan/INDEX.md` | Records | Review |

## Validation

cwd `/workspace/cosyn/dafny`: `dotnet build Source/Dafny.sln --no-restore -m:1`; the three
contract suites (`--filter FullyQualifiedName~Contract`, baseline 93/645/244 plus new
tests); touched-file whitespace check. `/workspace/cosyn`: `make build-dafny` and the
goal-PBT integration test. Scratchpad experiments rerun for evidence.

## Progress log

- 2026-09-29: inspection and reproduction complete (evidence above). Plan ready.
- Implemented: `IsCompatibleReferenceType`/`IsHeapReferenceType` (object accepts any slot);
  `PrepareFixedState` + cycle-tolerant `TopologicalOrder` (execution keeps rejecting);
  `CheckWithPlan` object acceptance; `ContractDiagnosticConstruction` rewritten around
  shape trees (`ParsePath`, `BuildShape`, `DefaultClass`, `Emit`, `Declaration`,
  `SuppliedFieldNames`); `IsDiagnosticConstructible` and a reserved
  `ContractDiagnosticCreate*` family; transformer and `AuditResolved` read
  `{:pbt_supplied_fields}`; `QualifiedType` internal. The internal three-argument
  `ContractHeapFactory.Prepare` overload is kept (an existing reflection test binds it).
- Scratchpad reruns (`heapexp/`, TMPDIR there, 4 samples): `set<object>` list correct →
  no_violation_found, buggy/original-constructor buggy → violation_found (runtime);
  twostate `Same(head)` over the cyclic repr (both `set<Node>` and `set<object>`) → correct
  no_violation_found, buggy violation_found via closed SMT (later samples hit the
  16-query budget); nested Store/Client pair → both polarities decided.
- M2 cat `m2-drop-stdin` from dafnyutils HEAD (`cat_m2.py`, 4 samples): existing
  generator (17 annotations, 106 lines) 146 s, concise nested generator (1 annotation,
  53 lines) 143 s; both violation_found, valid 4/4, 3 violations.
- Tests added: Driver `ContractRuntimeHeapConstructionTests` (7 cases); TestGeneration
  source-preparation cases (2 facts, 2 inline data) and the updated header assertion.
- Checks (cwd cosyn/dafny): build 0 errors; Core 93/93; TestGeneration 649/649 (first run
  648/649: the reflection-bound 3-argument overload, fixed as above); Driver 251/251;
  whitespace check exit 0 on the 9 touched files. Cosyn: `make build-dafny` 0 errors,
  goal-PBT integration 4 passed.
- Independent verification: fresh Sonnet agent (no effort setting in the Agent tool; one
  rate-limit interruption, resumed in its own context). It reviewed every hunk and ran
  build (0 errors/0 warnings), Core 93/93, TestGeneration 649/649, Driver 251/251 and the
  whitespace check (exit 0); requirements 1-5 met. Findings: (medium) unit-mode heap
  realization (`ContractHeapModelRealizer` replay validation via
  `ContractHarnessBuilder.Prepare`/`ContractHeapFactory.Prepare`) still rejects cyclic
  heaps; this is the executable unit-mode path this plan keeps strict (cyclic class-typed
  heaps were already rejected there), so it is recorded as a limit, not changed. (low)
  the reserved-name family is broader by design; (low) identical field sets listed in a
  different order produce separate constructors (extra generated code only).
- No provider call, campaign acceptance run or benchmark change. Remaining: none for
  this plan; follow-up candidates are unit-mode cycles and builders from datatype values.
