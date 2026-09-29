# Runtime entry heap checking

- Status: done for the bounded engine extension; independently verified. Parent M2 population and its validity/detection limits are separate.
- Created/updated: 2026-09-27.
- Owner: Dafny fork, `/workspace/cosyn/dafny`; repository maintenance, not an evaluated agent run.
- Baseline: `060d5ad532f67d5367450689225274fb0a0243e7`; clean before this plan/index write.
- Parent: [M2 integration plan](../../../plan/2026-09-27-pbt-m2-entry-execution.md).
- Previous work: [runtime obligation checking](2026-09-26-runtime-obligation-checking.md).
- Knowledge: [contract testing](../wiki/contract-testing.md).

## Objective and acceptance

Enable generic runtime campaigns with ghost-backed draft implementations and explicitly generated partial logical heaps, then decide original entry postconditions against observed entry/return heaps. The root application is the existing eight `CatCore.RunCore` M2 variants. Engine code must contain no benchmark-specific names, branches, contracts, or expected answers.

Observable owner acceptance:

1. A cross-module draft may use a compilable ghost observer or ghost field while retaining its original callable signature and contract. Valid drafts execute; invalid drafts exclude their samples from goal evidence.
2. An explicitly requested diagnostic constructor creates supported class shapes independently of an original constructor whose precondition is false. Original source bytes, constructor preconditions, and goal contracts remain unchanged. Calling the original constructor does not gain permission or succeed through a diagnostic redirect.
3. Relevant ghost fields are represented; irrelevant unsupported ghost fields may be omitted only after the existing transitive dependency audit accepts the omission. Runtime fields may not be omitted.
4. A completed sample with supported, consistent entry/return heaps can decide an original two-state postcondition through the existing fixed-state query machinery. Neither the tested body nor its postcondition is assumed by a diagnostic call in the query.
5. Premise inconsistency, omitted relevant state, unsupported heap shapes, invalid callees, solver timeout/unknown, and exhausted budgets cannot produce a goal violation or an unearned decided postcondition.
6. Generic focused regressions, affected contract suites, build, formatting, and a fresh independent verification pass complete. The root owns frozen M2 runs, exact generator/catalog provenance, reported detection denominators, and any later experiment configuration changes.

All-four mutant detection is a root campaign acceptance target, not a conclusion of source inspection. Unchanged existential contracts may remain solver-expensive; unresolved outcomes must remain explicit and trigger a recorded follow-up instead of contract weakening.

## Boundaries, non-goals, and approvals

- Authorized: this plan/index now; engine implementation after the root checkpoint handoff; local fake/generic tests and bounded local verification. No paid provider run.
- No new packages, benchmark edits, evaluator changes, specification changes, hidden inputs, or reference solutions. No changes to Dafnyutils.
- Preserve `IO.Init requires false`; do not execute arbitrary nondeterministic ghost initialization, fabricate callback values, or narrow a benchmark predicate to fit runtime enumeration.
- Diagnostic construction exists only in detached campaign sources. Original immutable source snapshots remain the authoritative query and source-location basis.
- Initial scope is generic entry pre/post heap capture and final entry-postcondition decision. Arbitrary intermediate two-state checkpoints, changed allocation topology, cyclic synthetic heaps, generic/inherited/extern class construction, and unavailable logical values may remain explicitly unsupported.
- Existing transport schema and public result models remain compatible. Do not add public fields without first updating this plan and coordinating strict Python DTO consumers.
- The implementation and fresh verification agents use independent contexts. This planning/implementation agent does not provide independent verification.

## Inspected evidence and existing machinery

Applicable instructions read: repository `AGENTS.md`, `CLAUDE.md`, parent `/workspace/cosyn/AGENTS.md`, and `/workspace/AGENTS.md`. No plan/wiki-specific instructions or plan template were present. No deeper instruction files were found in the affected Driver/TestGeneration directories.

- `ContractRuntimeCampaignRunner.RunAsync` currently resolves installed executable draft bodies before deghosting. An imported module's ghost-context errors can prevent resolution of the goal module.
- `ContractRuntimeObligationTransformer.MakeGeneratorVisible` currently prepares selected ghost constructors after a reachability pass; `Transform` selects compilable ghost functions/fields. `EraseUnreachableBody` explicitly exempts constructors.
- `ContractHeapFactory` already validates finite explicit class heaps, supplied fields, omitted ghost dependencies, consistent field sets, object identities, and constructor collisions. `BuildConstructorInsertions` supplies a separate `ContractDiagnosticCreate`; omitted ghost witnesses stay erased. Reuse this implementation.
- `ContractHeapPlan.QueryAssignments` reconstructs final mutable cells and rejects changed immutable cells. Its frame check only accepts receiver/formal frame references; `ContractHeapModelRealizer.ModifiedFields` already resolves member-selected frame references.
- `ContractStubRuntime` already serializes typed values, tracks stable object identities, and snapshots concrete/logical heap cells. Reuse its representation and metadata.
- `ContractQueryBuilder.Build` binds an initial heap, assigns observed final cells, and asserts the original postcondition. `ContractTestRunner` demonstrates the premise-consistency and opposite-query checks required before a verdict.
- The current scalar `BuildClosedClause` does not supply a two-state heap. Runtime `Check` refuses heap-dependent closed fallback and excludes two-state functions from compilation. Preserve these safeguards outside the newly supported entry boundary.
- Read-only public IO/World and Cat contracts establish the integration need. `Footprint()` references all region handles, so omission of unused region *values* does not authorize omission of those handles. Those public contracts remain unchanged and are not copied into generic engine tests.

## Generator annotation contract

The annotation lives on the one `{:pbt_generator "Module.Goal"}` `Generate` declaration and may be repeated for different classes:

```dafny
method {:pbt_generator "Client.Goal"}
  {:pbt_heap_constructor "Store.Cell", "Store.Cell.value"}
  {:pbt_heap_constructor "Store.Handle", "Store.Handle.cell"}
  Generate(r: PbtRandom.Source) returns (handle: Store.Handle)
{
  var value := r.Int(-2, 2);
  var cell := new Store.Cell.ContractDiagnosticCreate(value);
  handle := new Store.Handle.ContractDiagnosticCreate(cell);
}
```

The first string is the canonical fully qualified Dafny class name. Subsequent strings are canonical fully qualified instance field names belonging to that class. They are ordered: generated constructor parameters follow the annotation order and use the original field names/types. A class-only annotation selects no fields and is valid only when every omitted field is an auditable irrelevant ghost field. The annotation does not provide a body or override a contract.

Validation rejects non-string arguments, absent/ambiguous/non-class targets, duplicate class annotations, duplicate fields, foreign/unknown/static fields, unsupported class shapes, omitted runtime fields, reachable omitted ghost fields, and collision with `ContractDiagnosticCreate`. Classes must meet the existing factory's concrete/non-generic/no-parent/no-extern and visibility requirements. Preserve consistent selected field sets for all instances of a class. Ordinary export handling follows the existing detached diagnostic visibility policy; do not alter original exports.

This source-only contract avoids request/response wire changes. The root generator can build explicitly sampled values and call `new QualifiedClass.ContractDiagnosticCreate(...)`; it must not call the original false-precondition constructor. All annotation bytes remain part of existing generator hashes and receipts.

## Implementation stages

### A. Shared diagnostic construction

Extract the existing constructor shape validation/rendering and omitted-ghost auditing into a reusable helper where needed. The legacy fixed-heap API retains behavior. Runtime preparation parses generator annotations against the original resolved source, inserts constructors into the detached source map, and includes them in generator reachability.

Audit omissions against goal contracts, frames, relevant callable bodies/type dependencies, installed drafts, and generator dependencies. Do not treat an omitted field as irrelevant merely because it is initially absent from the original draft-free call graph. The final audit uses the clean resolved diagnostic graph.

When selected fields become executable, unused original constructors may have incompatible erased initialization. Preserve the original constructor declaration/specification in the detached copy but replace its unreachable body with a well-typed trap initializer, reusing field initialization rules and the existing `UnreachableValue<T>()`. Omitted ghost fields retain erased witnesses. This path must never be used for reachable ordinary constructors. Final clean resolution and a regression establish Dafny constructor-initialization legality before treating this approach as complete.

### B. Ghost-backed draft preparation

Separate dependency discovery from final executable resolution. A diagnostic-only `ProgramResolver` subclass can install a `BatchErrorReporter` that defers a fixed list of ghost-context diagnostics while ordinary name/type resolution constructs the complete graph, including imported drafts. Deferred diagnostics are retained as artifacts; all other resolution errors remain fatal. This uses the existing public resolver/reporter extension points without changing Core or ordinary resolution. Reuse the existing compilability analysis on that graph, then require a completely clean ordinary resolution of the transformed executable. No deferred-error program may be compiled, queried, or treated as successful evidence directly. This replaces a speculative iterative partial-module approach after inspection established the supported resolver extension point.

Keep unrelated logical initialization and native declarations out of the executable dependency closure. Preserve source mapping through all insertions/replacements. Non-compilable dependencies retain precise unsupported/exclusion diagnostics rather than being guessed or silently removed.

Inspection identified a further necessary validity dependency: filesystem values use finite recursive datatypes with nested subset constraints. Existing membership generation marks recursion unchecked and would invalidate every otherwise-correct IO observation. Extend that same structural validator with generated recursive membership helpers for non-generic inductive datatypes, preserving every nested constraint and normal/error classification. Generic recursive shapes, codatatypes, and ghost constructors remain unsupported. Update the existing recursive-membership regression and add a recursive-map case; no depth cutoff or skipped recursive field is permitted.

### C. Entry/return heap observations and original postconditions

Capture immutable copies of supported typed inputs and complete relevant heaps at the actual entry and successful return boundary, with outputs at return. Reuse stable reference IDs and heap shapes from `ContractStubRuntime`; internal observation JSON may carry structured heaps without changing public campaign DTOs. Persist observations in existing campaign artifacts and expose necessary flattened heap evidence through existing `Values` maps.

For an otherwise-valid sample, prepare the original method/source with a fixed request built from captured inputs and initial heap. Validate relevant-field coverage, representable values, identity/type/topology consistency, immutable cells, and final frame behavior. Share nested-member frame resolution with the existing heap model realizer.

Use the existing `ContractQueryBuilder.Build` pattern for satisfiable concrete premises, entry preconditions where needed, original final postconditions, and their negations. The query starts in the captured initial heap and applies observed final mutable assignments before asserting the original clause; this preserves Dafny's native `old`/two-state semantics and unbounded specification quantifiers. Do not call the tested method or use its ensures as an assumption. Keep per-clause locations and decision accounting.

Recheck concrete premise satisfiability before accepting either polarity, preserve unvalidated-callee exclusions, and account for every actual query, including premise checks, within existing campaign/time limits. Cache keys must bind the clause, inputs, outputs, initial/final heaps, and source identity. Unsupported topology or incomplete state stays unchecked. Do not infer success from process completion or an SMT countermodel that does not prove the opposite clause on the fixed observations.

### D. Probe-driven observation and specification-dependency corrections

Development probe 02 reached the entry but exposed unsupported observation of a
concrete generic datatype (`Result<Bytes>`). Extend runtime datatype metadata to
identify generic constructor definitions and carry resolved Dafny type-argument
shapes through nested fields/collections. Preserve bitvector widths even when CLR
representations erase their distinction from integers. Unresolved type parameters
remain unsupported; no value guessing or benchmark-specific constructors. Keep
legacy fixed-mode generic construction outside this observation-only extension.

Fresh independent review also produced a false goal violation when a two-state
specification predicate called another function with an invalid, unvalidated
explicit contract. Traverse specification function/type dependencies transitively
with recursion guards before either heap verdict; checking only the direct call
is insufficient. Retain native typed-premise checks for type-only constraints and
exclude genuine unvalidated contracts. The root owns observation source/tests;
the original implementation agent owns the initial-heap and specification-callee
validity corrections after the verifier released its runtime slot. The verifier
remains read-only and will check the final implementation independently.

Probe 03 completes actual entry execution but retained scalar query artifacts
show two source-rendering defects: imported datatype constructors lose their
module qualifier and imported static functions print `_default` instead of the
resolved import container. Extend the existing `QuerySubstituter` and use it for
closed clauses, preserving resolved declaration identity and source-scope names.
Add native query regressions in `ContractQueryTests.cs` for imported constructors
and functions, testing both truth polarities. The root owns these two files.
Reuse `ContractHeapFactory.SourceTypeName`'s existing import-signature traversal
for datatypes as well as classes, matching canonical declaration names when the
clause and insertion owner originate from separate parses of the same snapshots.
The engine implementer owns runner binding of scalar clauses to original source
snapshots, so executable drafts cannot invalidate specification query resolution.
No contract/source authority changes or benchmark-specific rendering are allowed.

Independent recheck also requires omitted refined ghost state to retain typed
inhabitation checks and higher-order member-selected function references to enter
all type-constraint dependency audits. Preserve safe ordinary arrow omission and
classify unavailable/residual checks conservatively; add generic Driver cases.

## Exact change table

Paths are relative to this owning repository. Implementation/protocol layers only; benchmark specification/proof/evaluator/dataset/scoring layers remain fixed.

| Files/symbols | Planned change and necessity | Unmet without change | Validation |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractHeapFactory.cs`; new `ContractDiagnosticConstruction.cs` | Share shape/field validation, constructor rendering, and omitted-field auditing; expose ordered runtime construction without duplicating legacy machinery | No sound sampled partial logical construction | Legacy heap tests plus annotation/construction cases |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs` | Parse/validate annotations and insert mapped diagnostic constructors; preserve draft/generator origin mapping | Generator cannot resolve generated constructor calls | Source preparation tests, hashes and UTF-8 mappings |
| `Source/DafnyTestGeneration/ContractTesting/ContractSourceSnapshot.cs`; new `ContractDiagnosticResolver.cs` | Optional diagnostic-only resolver with explicitly deferred ghost-context error IDs; normal parser/resolver remains default | Imported draft errors prevent building a complete typed dependency graph | Ghost-draft execution and ordinary/error rejection regressions |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` | Stage compilable ghost visibility; prepare unreachable constructors; capture entry/return state and retain heap-capable postcondition checkpoints | Ghost drafts fail before goal resolution; final heap clause stays unchecked | Driver runtime tests and existing pure M1-style regressions |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Orchestrate staged resolution, original program retention, heap decision, budgets/caching and validity accounting | Cannot decide original entry postcondition from runtime state | Driver heap campaign tests including timeout/invalid callees |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeInstrumentation.cs`; `ContractStubRuntime.cs` | Reuse typed snapshot/identity machinery for entry/return observations | Missing old/new heap evidence | Observation tests with mutation and aliases |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryBuilder.cs`; new `ContractRuntimeHeapChecking.cs`; `ContractRuntimeModels.cs` internal records only | Reuse fixed-state queries per original clause and provide typed internal observed-state checks | No sound two-state postcondition decision or premise audit | Query and Driver tests for Q/not-Q/inconsistent state |
| `Source/DafnyTestGeneration/ContractTesting/ContractHeapModelRealizer.cs`; `ContractHeapFactory.cs` | Share existing member-selected frame resolution without broadening allowed frame effects | Entry region frames unsupported or falsely ignored | Nested-frame legal/illegal mutation tests |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs`; `ContractHeapTests.cs`; `ContractQueryTests.cs`; new `ContractRuntimeHeapQueryTests.cs` | Add observable generic constructor, omission and two-state query regression cases; root owns the new heap-check helper and its query tests while the engine implementation agent owns runner integration | Shape/query soundness unverified | Focused and complete affected contract test filter |
| `Source/DafnyDriver.Test/ContractRuntimeCheckTests.cs`; `ContractRuntimeObservationTests.cs`; new `ContractRuntimeHeapTests.cs` | Replace ghost-draft unsupported expectation with execution tests; add generic heap campaign behavior tests | Runtime integration and classification unverified | Focused and affected Driver contract tests |
| `plan/2026-09-27-runtime-entry-heap-checking.md`; `plan/INDEX.md`; `wiki/contract-testing.md`; `wiki/INDEX.md` | Record scope, commands, revisions, failures, support limits and durable findings with reciprocal links | Handoff/provenance incomplete | Diff/link review |

The root separately owns its generator/catalog tests, plan/wiki, frozen campaign configurations, artifacts, and reports. These are coordinated through the parent plan rather than edited here.

## Test matrix and actual commands

All commands run from `/workspace/cosyn/dafny`. Prerequisites: installed .NET SDK, existing restored repository dependencies and Boogie checkout, configured local Z3, writable local temporary artifacts, and no concurrent production build. Actual SDK: `8.0.131`. No package installation is authorized. Results below distinguish intermediate failing builds/tests from later reruns.

| Scope | Command | Expected outcome |
| --- | --- | --- |
| Owner build | `dotnet build Source/Dafny.sln --no-restore` | Successful build with no new diagnostics; record exact output/time |
| Source preparation focused tests | `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractRuntimeSourcePreparationTests'` | Annotation and mapped preparation scenarios pass |
| Heap focused tests | `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractHeapTests'` | Construction/omission/frame scenarios pass |
| Query focused tests | `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractQueryTests'` | Fixed-state consistency and postcondition scenarios pass |
| Runtime focused tests | `dotnet test Source/DafnyDriver.Test --no-restore --filter 'FullyQualifiedName~ContractRuntime'` | Supported cases execute/decide and invalid cases classify honestly |
| Affected TestGeneration contracts | `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~Contract'` | Existing and new contract regressions pass |
| Affected Driver contracts | `dotnet test Source/DafnyDriver.Test --no-restore --filter 'FullyQualifiedName~Contract'` | Existing runtime/legacy contract regressions pass |
| C# formatting | `make format` | Format owner changes; inspect all resulting diffs and preserve unrelated work |
| Final whitespace/diff | `git diff --check` | Clean; reviewed changes remain within this plan |

No `.dfy` repository sources are planned to change, so `make format-dfy` and benchmark proof suites are not required here. If scoped test execution is constrained, record the concrete prerequisite/blocker and obtain an authorized scope adjustment; an unrun test is not a pass. Parent `make build-dafny` may be used by the root for packaging, but is distinct from this owner's build evidence.

Required generic scenarios: valid and violating ghost-backed cross-module drafts; draft-only transitive dependencies; annotation validation/collision/order; false-precondition original constructor and separate diagnostic constructor; unused nondeterministic constructor; irrelevant function-field omission versus transitive relevant read rejection; all frame-visible handles retained; immutable original hashes/UTF-8 mappings; correct/incorrect two-state postconditions; alias-preserving snapshots; changed immutable field/topology and missing field rejection; inconsistent observed premise; nested member frame violation; invalid callee exclusion; timeout/query exhaustion; M1-style scalar campaigns unchanged.

Root scored M2 experiments run only after owner checks and a fresh independent verification handoff, in new artifact directories and `tmux`, using frozen tool/source/generator identities. After focused generic checks, bounded one-sample development probes against unchanged public contracts may diagnose integration failures before final review: preserve the existing 5-second sample/240-second campaign/16-query/10-second query limits, use new artifact directories, and record source/binary/generator identities. These probes do not establish a detection rate or replace the final independent handoff. No benchmark detection percentage is claimed by owner tests.

Validation order after the first probe: build corrected source, run new/corrected focused regressions, package for the next bounded public probe, and repeat only the affected checks for new integration fixes. Run the complete affected suites once that probe reaches execution, then obtain fresh independent review. The parent authorized cancelling the obsolete full Driver run before rebuilding; retain its cancellation explicitly rather than presenting an aggregate pass.

## Risks, compatibility and handoff

- Ghost resolution is phase-sensitive: proof-only/unsupported dependencies must not be promoted speculatively. Final resolution remains mandatory.
- Constructor initialization rules may reject a naive trap body. Establish a legal generic implementation with focused tests; update this plan before changing the agreed strategy or scope.
- Partial logical state is sound only if omitted state cannot affect relevant contracts, bodies, frames, type constraints or drafts. Reuse and extend audits; do not add benchmark exceptions.
- Heap-sensitive cache keys, snapshot timing, SAT premise checks and callee validity are correctness boundaries, not optimizations.
- The original existential postcondition can time out. Preserve bounded budgets and classify undecided obligations; do not alter contracts to improve detection.
- Public annotation semantics are fixed above for root generator coordination. Existing request/result schema remains version 1; existing generators without annotations retain behavior.

Implementation authorized by the parent after owner checkpoint `060d5ad53`; root/Cosyn checkpoint work uses immutable frozen r5 engine artifacts. Stages A–C, owner validation, fresh independent review, knowledge updates and final diff review remain. No commits or paid experiments are authorized. An attempted bounded construction subagent could not start because the runtime thread limit was reached; the parent was asked whether its completed investigation agent can be reused for implementation.

### Implementation observations and checks — 2026-09-27

- The parent now implements the bounded query-state helper and its separate query test file while this agent owns construction, deferred ghost resolution, instrumentation and campaign integration. This is implementation collaboration, not independent verification.
- Sandbox `dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore` exited immediately with no diagnostics, twice (quiet/minimal), matching the recorded MSBuild sandbox limitation. Authorized host `-m:1` build then exposed eight ordinary compile errors and two warnings from the constructor AST hierarchy and shared partial-class name. These were corrected; no native Core change was needed.
- First host focused Driver run: 1/3 passed, 2 failed during generator parsing because Dafny attribute arguments require commas. The public syntax examples and generator coordinator were corrected before further execution; field ordering/meaning did not change.
- Second host `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeHeapTests -v:minimal`: **3/3 passed**, 9 seconds. Covered valid ghost-backed draft over a partial logical heap, invalid draft exclusion, and preservation of the original false constructor precondition.
- Expanded focused Driver run covering heap state, recursive constraints and cross-module ghost draft: **8/9 passed**, 26 seconds. One false two-state result remained unchecked because a non-null function formal was classified as an unvalidated explicit function contract. The fixed-heap path now relies on its typed satisfiable premise/native well-definedness for type-only requirements while preserving explicit-contract and runtime-callee exclusions. The corrected expanded run passed **11/11**, 36 seconds; no full-suite passing claim yet.
- Host `dotnet build Source/DafnyTestGeneration.Test --no-restore -m:1 -v:minimal` succeeded with zero warnings/errors (12.15 seconds). Source-preparation tests passed **15/15**. The parent collaborator's query tests initially passed **10/12**; the two failures were fixture resolution errors for a non-null field without a constructor. After adding its ordinary constructor, all **12/12** passed (2 seconds). Logs: `/workspace/tmp/pbt-m2-root-checks-20260927/heap-query-tests{-retry}.log`.
- Heap decision caching now binds the exact original fixed request (source identities, entry, inputs and initial object shapes), outputs and final observations. Heap/frame/callee validity is checked before using a cached decision. Each actual heap query, including consistency checks, consumes the configured query budget.
- `make build-dafny` from `/workspace/cosyn` succeeded (28.06 seconds, zero warnings/errors) and packaged the consistent current engine for the bounded public development probe. `make format` succeeded with a workspace-loading warning; `git diff --check` passed.
- The broad TestGeneration contract run exposed `FreshRemainsUnchecked`: entry heap selection had classified explicit allocation predicates as closed queries. Preserve the planned unsupported allocation boundary by excluding `fresh_or_allocated` from this selection; its existing regression remains unchanged. The current broader runs use the pre-correction binary, so final builds/rechecks are still required.
- That intermediate TestGeneration run completed **296 passed / 1 failed** (1m26s); the failing allocation assertion is not relabeled as a pass. Additional generic Driver regressions now cover omitted state introduced only by a draft, invalid executed callees before final heap decisions, and an unvalidated spec function's explicit contract.
- Parent bounded development probe 01 reached final resolution, then returned unsupported: a synthetic wrapper called an original method with `decreases *` without preserving that permission. Extend existing method/function wrappers and generated main to copy nontermination permission from the called declarations; add a generic terminating sample whose declaration permits nontermination. This preserves original declarations and sample timeouts. Probe artifacts: `/workspace/tmp/experiment/pbt-m2-dev-20260927-01/runtime`; 82 seconds, zero generated samples, no detection claim.
- The intermediate full Driver `--no-build --no-restore -m:1 --filter FullyQualifiedName~Contract -v:minimal` run was cancelled by its tracked execution session (Ctrl-C, exit 1, `Attempting to cancel the build...`) at the parent's request after the wrapper fix made its binary obsolete. It had emitted no failure but no aggregate result; this is a cancelled check, not a pass. New focused checks precede the next development probe and the final broad suites.
- Corrected solution build `dotnet build Source/Dafny.sln --no-restore -m:1 -v:minimal` passed (14.72 seconds, zero warnings/errors), with matching root/net8.0 packaged DLLs. Focused obligation/query/preparation checks passed **34/34**, including the preserved allocation boundary. New Driver heap checks passed **11/12** (53 seconds); the omitted-field case correctly rejected the draft by throwing the existing `NotSupportedException` boundary, while its test mistakenly expected the CLI-translated result from the direct runner. Corrected that fixture assertion without changing production behavior. Nontermination, runtime invalid callee and unvalidated spec-function cases passed.
- Test-only `dotnet test Source/DafnyDriver.Test --no-restore -m:1 -p:BuildProjectReferences=false --filter FullyQualifiedName~RejectsOmittedStateReadOnlyByDraft -v:minimal` passed **1/1** after correcting the assertion. Public production hashes remained Driver `bb8453261bd81d08dda00515c9b3e4dc4f5206bb91166c8e8a69e3387ba9b04c`, TestGeneration `9bdc43b6ef3dd2637ab74b65f3ef64397c10d6a6af43320a1052e5c39f69e464`.

### Implementation handoff

The parent owns probe 02 and later bounded integration fixes/review coordination. Current runnable package is `/workspace/cosyn/dafny/Binaries/Dafny.dll`; its public/net8.0 production DLLs match the hashes above. No builds or tests remain running in this implementation agent. Probe 02 snapshot is parent-owned at `/workspace/tmp/experiment/pbt-m2-dev-20260927-toolchain-02`. The cancelled Driver transcript is preserved at `/workspace/tmp/pbt-m2-engine-checks-20260927/driver-contract-intermediate-cancelled.log`.

Remaining after a public probe reaches execution: run both complete affected `FullyQualifiedName~Contract` suites with `--no-build --no-restore -m:1`, retain their aggregate results; run `make format` and `git diff --check` after any further edits; verify final production identities; obtain fresh independent review; update this plan/wiki and indexes with final evidence. The plan stays in-progress. No commits were made and no benchmark source/contracts/packages changed.

### Independent-review validity corrections

The fresh review at `/workspace/tmp/pbt-m2-engine-review-20260927/REPORT.md` reproduced three blocking defects with retained generic requests/results: invalid `nat` heap fields admitted by a runtime-only goal, a transitive invalid specification callee blamed on the goal, and an unvalidated direct specification contract counted as a positive heap decision. Earlier focused passes do not establish these boundaries.

Before further acceptance, extend entry capture/validation independently of postcondition decision selection. Reuse original fixed-state typed premise validation for captured reference/diagnostic-construction heaps before admitting any goal evidence, including runtime-only clauses. Reuse budgets/caches and classify unavailable/inconsistent state explicitly; constructor parameter checks alone are insufficient because generators can mutate fields afterward. This touches `ContractRuntimeObligationTransformer.cs`, `ContractRuntimeCampaignRunner.cs`, and `ContractRuntimeHeapChecking.cs`, plus generic regressions in `ContractRuntimeHeapTests.cs`.

Preserve existing cyclic ordinary-reference support: validate each captured field/array element against its original declared type using shared factory shape checks and exact non-null/natural-number/nested finite collection/datatype membership. Iterate captured objects once; follow concrete datatype values without a depth cutoff. No query is required when all declared constraints are decided this way. Only genuine residual subset/newtype constraints require the existing typed SAT premise; unsupported residual shapes remain unchecked. Share `ContractHeapFactory.cs` array-type/value-shape helpers internally instead of duplicating their checks. Add cyclic/nested invalid-field and generator-after-construction mutation regressions.

Reuse the existing guarded execution/specification/type dependency traversal for closed heap clause dependencies, rather than scanning only direct calls. Unvalidated explicit requires/ensures/by-method dependencies block both polarities before query/cache reuse. Type-only constraints retain the original fixed typed premise and native well-definedness treatment. Add direct-positive, transitive and recursive/type-dependency regressions. The root concurrently owns only concrete generic datatype serialization in `ContractStubRuntime.cs` and its observation tests; coordinate the production build after both source changes are ready. No broad suites until source integration and the bounded public probe stabilize.

Preserve scalar closed-query sources/results as `closed-query-<decision>-positive|negative.{dfy,result.json}` in the existing diagnostic directory, matching the heap query artifacts. Parent probe 02 exposed a closed-query error whose previous scalar path discarded diagnostics; this artifact-only change does not alter schema, budgets or query semantics.

Coordinated serializer/validity solution build passed (20.34 seconds, zero warnings/errors). Focused heap Driver cases passed **23/23** (1m50s); parent observation cases passed **7/7** (30 seconds), including prior cyclic capture and new generic values. Follow-up closure coverage adds expression type/member-selected-function roots and refuses unvalidated callees inside residual initial-field constraints. Additional type/by-method/recursive dependency regressions await the final focused rebuild; no full-suite or fresh-review acceptance is claimed yet.

Final closure solution build passed (19.52 seconds, zero warnings/errors). `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~Specification|FullyQualifiedName~InitialFieldConstraintCallee|FullyQualifiedName~DecidesOriginalTwoStateHeapPostcondition|FullyQualifiedName~AcceptsOriginalTwoStateHeapPostcondition' -v:minimal` passed **10/10** (48 seconds), covering new type/by-method/recursive closures and both supported Q polarities. `make format` passed with the existing workspace-loading warning; `git diff --check` passed. Current matching public/net8.0 Driver hash is `e63299420a31744f75a7b9212fb3b787f4cfcacc6493a587db69964af8ab3a95`; TestGeneration is `9371775b863497d01232ab046512f6fd9f44903cf307b1d26eb9138d3ccba426`.

Validity correction handoff: no builds/tests remain running; parent owns probe 03, final full affected suites after integration stabilizes, and fresh independent revalidation. Earlier independent failures remain preserved. Source contracts/snapshots and result schema remain unchanged. No commits were made.

Root imported-name query regressions and existing `ContractQueryTests` passed
17/17 (6 seconds) after the coordinated solution rebuild. Command:
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractQueryTests' -v:minimal`.
Log: `/workspace/tmp/pbt-m2-root-checks-20260927/query-scope-tests.log`. This validates
visible datatype constructors and imported static functions in fixed/closed
queries with same-name shadowing and both truth polarities; it does not establish
the final Driver or public M2 campaign result.

### Remaining review and scalar-source corrections

Final full-suite regression correction scope (before edits):

| Files/symbols | Correction / necessity | Validation |
| --- | --- | --- |
| `ContractTypeShapeGenerator.cs` / `ContractRefinementQuerySite`; `ContractInputGenerator.cs` / `TryRefinementQuerySource`; `ContractQueryBuilder.RenderExpression`; factory source-name scope helpers | Carry the original refinement declaration module to name rendering, because its query is inserted at the type declaration rather than the entry method | Existing `ImportedResidualRefinementUsesDeclarationQuerySite`, query suite, full TestGeneration contracts |
| `ContractRuntimeObligationTransformer.cs` / generic wrapper observation; `ContractStubRuntime.cs`; affected Driver generic observation tests | Preserve the concrete Dafny type shape when observing generic callable formals/results; the new unresolved-parameter guard exposed missing call-site metadata. Do not guess widths from CLR representation or remove the guard | Existing `SeparatesGenericSpecFunctionViolation`, concrete generic bitvector/collection cases, full Driver contracts |
| `ContractDiagnosticResolver.cs`; existing hidden-ghost-constructor and false-constructor Driver regressions | Defer the existing `r_assignment_to_ghost_constructor_only_in_ghost` discovery diagnostic so supported ghost constructors reach controlled transformation, still requiring final clean ordinary resolution and original preconditions | `ConstructsHiddenGhostRegion`, original false-constructor checks, full Driver contracts |

The independently packaged TestGeneration run passed 312/313 (1m32s), failing
the declaration-site case with unresolved `Store` in its own declaration module.
The Driver run has a reproduced generic `Pick<T>` observation error
(`kind:parameter,index:-1`) instead of the two expected invalid-callee samples.
Keep production/binaries unchanged until that suite produces its full aggregate;
root owns the query-scope correction and the engine implementer owns generic
metadata. No final review manifest, frozen r6 toolchain or scored run exists.

The progressing Driver suite also reproduced `WrapsGenericCallSite` with the same
unresolved generic-shape error and `ConstructsHiddenGhostRegion` with the missing
ghost-constructor discovery diagnostic above. The latter is a separate regression
in previously supported constructor transformation, not an authorization to skip
ordinary resolution or constructor preconditions. Preserve all failures in the
independent final logs before corrections.

Probe04 retains a static-name rendering defect after descriptor cloning discards
`StaticReceiverExpr.ContainerExpression`. Resolve static receiver qualification
from its resolved declaring class/module and the query owner's visible module
signatures, reusing the factory's import traversal. Do not depend on optional
surface syntax surviving prior AST rewrites. Extend `ContractQueryTests.cs` with
function-descriptor imports and class-static calls whose query is inserted outside
the class, in both fixed/closed paths and both truth polarities. Root owns this
bounded correction in `ContractQueryBuilder.cs`, `ContractHeapFactory.cs` and
`ContractQueryTests.cs`; no validity gate or benchmark input changes.

Root correction build `dotnet build Source/Dafny.sln --no-restore -m:1 -v:minimal`
passed (20.67 seconds, zero warnings/errors). Query focus
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractQueryTests' -v:minimal`
passed 25/25 (9 seconds). Logs are
`/workspace/tmp/pbt-m2-root-checks-20260927/query-descriptor-{build,tests}.log`.
These include cloned function descriptors and query insertion outside a class;
earlier raw-method-only tests did not cover the probe04 failure. Probe05 uses an
immutable copied toolchain; supported final packaging and full review still wait.

Probe05 completed (247.30 seconds, process exit 0) with actual entry/return
execution and explicit inconclusive classification, not a goal violation.
Omitted structured refinements remain unsupported; the correctly qualified
scalar query sources hit existing query/campaign deadlines without completed
solver verdicts. The complete parent population will retain these budgets and
report the limitation. Final `make format` passed with the existing workspace
warning, `git diff --check` passed, and parent supported packaging is in progress.

Read the resumed independent report and raw `recheck/omitted-empty.request.json` / `higher-order-constraint.request.json`. An omitted refined ghost field still contributes typed-state inhabitance even when no relevant expression reads it. Extend `ContractRuntimeHeapChecking.cs` to inspect omitted field types recursively, retain safe unrefined arrow omission, and require original typed-state consistency for omitted refined/dependent types (with unchanged budgets). Type constraints must audit member-selected higher-order function references as well as direct calls. Extend the shared transformer type-dependency traversal accordingly, preserving recursion guards. Add empty/nonempty omitted refinement, no-budget, ordinary arrow and higher-order dependency regressions in `ContractRuntimeHeapTests.cs`.

Probe 03 completed an entry/return execution, but scalar queries still parsed detached draft snapshots. Bind the runner's scalar query prepared program/snapshots to the immutable original sources and remap each clause's insertion owner to its original resolved callable through a transformer helper reusing `DescribeFunction`. Keep the evaluated expression/free-variable bindings used by runtime captures. A synthetic/draft-only owner without an original declaration is explicitly unsupported, never silently queried from detached source. Add a cross-module ghost-draft regression with closed scalar callee contracts for valid/mismatching observations. Root owns `ContractQueryBuilder.cs` and rendering tests for cross-module qualification; coordinate before building. Existing JSON models and source contracts remain unchanged.

First coordinated correction build passed (19.56 seconds, zero warnings/errors); root query tests passed **17/17**, including imported alias/shadowing scenarios. The new Driver focus aborted before an aggregate result: broad dependency traversal called `.Resolved` on a synthetic builtin-arrow expression whose AST contract disallows it. Inspect function-call/member-reference nodes directly in this traversal; existing normalized expression traversal remains unchanged. Omitted-type auditing also evaluates all nested fields/types before requesting a residual query, avoiding short-circuit omission of later invalid dependency contracts. No passing Driver result claimed for the aborted run.

Probe 03's 92 static `recursive_heap_contract` obligation records had zero unchecked evaluations in total. They are generated guarded-recursion fallback sites, not observed validity exclusions in that sample. No recursion-guard support expansion is justified by that count alone.

The corrected focused retry passed **6/9** (44 seconds): the direct/nested empty omitted types were still admitted because native reference typing does not assert inhabitance of unread fields. Add explicit original-scope ghost predicates (`exists value: <declared field type> :: true`) through shared heap source edits, and require them as initial query choice constraints. `ContractHeapFactory.cs` gains only `ContractHeapPlan.WithAdditionalSourceEdits`; the parent-owned type-name renderer is unchanged. The scalar valid-case fixture also timed out on nonlinear squares; replace its unbounded relation with linear divisibility, preserving both valid/mismatch scenarios and the closed-query/source-binding behavior under test.

The explicit-inhabitance retry passed **8/9** (42 seconds). Direct omitted empty/nonempty refinements, exhausted budgets, ordinary arrows, higher-order dependencies, and both scalar source-binding cases passed. The remaining `Box<Empty>` case showed that native generic type arguments erase nested subset inhabitance even under an existential binder. With parent authorization, keep omitted structured/arrow/refinement chains requiring erased nested inhabitance explicitly unchecked rather than extending symbolic generic inhabitance now. Concrete captured generic values retain their complete field checks. Reuse the full omitted-type audit in `PrepareInitial` to add predicates only for types that need them, avoiding quantified premises for ordinary unrefined arrows. Audit all nested dependencies even if an earlier type already requires a residual query.

Final bounded correction build passed (19.99 seconds, zero warnings/errors). The nine focused omitted-field/higher-order/scalar-source cases passed **9/9** (42 seconds). Root query-scope tests previously passed **17/17** (6 seconds); log `/workspace/tmp/pbt-m2-root-checks-20260927/query-scope-tests.log`. Formatting passed with the existing workspace-loading warning, and final `git diff --check` passed.

Probe 04 handoff: no builds/tests remain running. Public/net8.0 hashes match: Driver `463742001aa9f40ab1dfb80e5160c4abc5c149141ebb00bc12fe0d2eb258e725`, TestGeneration `364396214463c9dba870a33dde1eae1e332862d62e63fd5ef9a18b0d20352376`. Parent owns the immutable probe 04 snapshot/run. Required final `make build-dafny` packaging precedes final affected suites and independent final source/binary identities; none is claimed complete here. No commits made.

Generic-call correction implementation detail (in-progress): add explicit shape-token formals to detached generic executable callables and their diagnostic wrappers; supply tokens from resolved call-site type applications and forward tokens through nested generic scopes. `ContractRuntimeInstrumentation.cs` adds a runtime-only shape composition bridge; `ContractStubRuntime.cs` reuses `TypeShape`/`ResolveShape` with declared type-parameter indices. The unresolved-parameter rejection remains mandatory, and CLR types never determine Dafny bitvector width. `ContractRuntimeObligationTransformer.cs` owns generated signatures/calls and scoped serialization; `ContractRuntimeCheckTests.cs` adds nested generic collection/bitvector method and specification-call regressions. Original sources and public request/result schemas remain unchanged. `ContractDiagnosticResolver.cs` adds only `r_assignment_to_ghost_constructor_only_in_ghost` to discovery deferrals; final ordinary resolution and original constructor domain checks stay mandatory. Validation starts with the three independently failed Driver tests, nested generic regressions, and false-constructor regression; then owner formatting, supported packaging and independently rerun full suites. The prior Driver 160/163 and TestGeneration 312/313 failures and packaged hashes remain historical, not acceptance.

Root declaration-scope focus passed **26/26** in **8 seconds** on the completed
development build, using
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ImportedResidualRefinementUsesDeclarationQuerySite' -v:minimal`.
Log: `/workspace/tmp/pbt-m2-root-checks-20260927/query-declaration-scope-stable-tests.log`.
This includes the formerly failing imported residual declaration-site case and
all imported/function-descriptor/class-static query regressions. An earlier
26/26 run overlapped a build due to crossed coordination messages and is retained
separately, not used as stable-build evidence. Full owner acceptance still waits.

The first coordinated generic correction build passed after compiler-API fixes; its four-test focus passed only the original false-constructor case. Generic cases exposed a newly generated nullable static receiver spelling (`PbtBridge?`); hidden ghost construction progressed past resolution but its constructor CallStmt was erased as a ghost proof call, yielding null/rejected inputs. Correct the generated static receiver and preserve promoted constructor calls in the existing transformer proof-call removal rule. No heap-check weakening or extra production file is needed. Retain logs `generic-shape-{build,build-retry,initial-tests}.log`. Add explicit generic higher-order-reference exclusion and reserved shape-formal name validation, rather than silently changing first-class function signatures.

`ContractRuntimeHeapTests.cs` extends `OriginalConstructorRemainsUncallable` to ordinary and ghost constructors and asserts an observed runtime domain error, so a deleted allocation cannot accidentally satisfy the exclusion assertion. `ContractRuntimeCheckTests.cs` also checks explicit generic higher-order-reference and shape-formal collision exclusions. Build-02 passed (19.45s, zero warnings/errors). Root query focus overlapped this development build due crossed coordination messages; it will be retained as such and rerun on stable binaries before acceptance.

The next focused retry passed 9/11 (20s): all execution regressions passed, including both prior generic failures, hidden ghost construction, ordinary/ghost false constructors, nested specification exclusion, and nested generic `bv7`/`bv8` observations. The two new exclusion tests expected a returned status instead of the existing direct-run `NotSupportedException`; their assertions were corrected without changing production behavior. Formatting passed with the existing workspace-loading warning. Final development solution build passed (13.49s, zero warnings/errors); the root query/declaration-scope stable focus passed 26/26 (8s). Logs remain under `/workspace/tmp/pbt-m2-engine-checks-20260927/generic-shape-*` and root query log `/workspace/tmp/pbt-m2-root-checks-20260927/query-declaration-scope-stable-tests.log`. `git diff --check` passed.

Final generic/constructor focus passed **11/11** (20s), using
`dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~Generic|FullyQualifiedName~ConstructsHiddenGhostRegion|FullyQualifiedName~OriginalConstructorRemainsUncallable' -v:minimal`.
No build/test processes remain. Development public/net8.0 DLL hashes match:
Driver `19553d0339e0fe11f510cff830055e0c0c0fc6d1d3a24581da746289d70dec3e`,
TestGeneration `06b6c7a5e0f0e7f1e6f4e127d742ead8b22663084c5f25984af9f66368a65bab`.
These are probe06 handoff identities only. Parent owns immutable probe06, supported
`make build-dafny` packaging, final affected suites and fresh independent review.
No final acceptance/benchmark detection is claimed; original full-suite failures
and prior packaging identities remain preserved. Wiki records the generic metadata
requirement and promoted ghost-constructor allocation boundary. No commits made.

### Final independent owner acceptance

Supported `make build-dafny` from `/workspace/cosyn` passed in 30.66 seconds with
zero warnings/errors after the corrections. The independent read-only reviewer
then ran ten retained raw regression probes and both complete Contract suites:
TestGeneration **313/313** (1m32s), Driver **168/168** (9m23s), zero skipped.
Commands were `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~Contract -v:minimal`
and the equivalent `Source/DafnyDriver.Test`, from this repository root, using
.NET SDK 8.0.131 and authorized local IPC. All 43 required production/binary
identities stayed unchanged through the checks; root/net8.0 DLL copies match.
Final Driver SHA-256 `97b6e00b67b3c25673008327f11e8a8239e40a6b54033d87cb0a705d2dbd5169`;
TestGeneration `fed8899e6332201ccb99821db61b91ae2f70249b0a403eb23af58dd58bac1f00`.
Formatting and diff checks pass; source remains uncommitted over `060d5ad53`.

Independent evidence: `/workspace/tmp/pbt-m2-engine-review-20260927/REPORT.md`,
`identity.final`, `review2/` logs/requests/results. Previous findings, failed
aggregates and cancelled attempts remain in `REVIEW_HISTORY.md` and their original
artifact directories. Cosyn transport integration separately passed 4/4 (22.66s).
No package, provider-backed run, benchmark contract change or proof skip was used.

The bounded engine acceptance criteria are met. The public parent probe06 reaches
entry/return with 17 objects but remains **valid0/inconclusive** because omitted
structured refinements lack supported inhabitance checks and closed queries hit
existing limits. It does not establish an M2 detection rate. Parent frozen r6
M1/M2 populations now own the integration outcome and denominator audit. Further
omitted-state/solver support is a separate extension; preserve the conservative
boundary and original contracts. Durable findings are in the linked contract
testing wiki; parent plan links this owner record.
