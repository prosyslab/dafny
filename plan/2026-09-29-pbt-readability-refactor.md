# PBT readability refactor before commit

Status: done

Root plan: [Prepare core PBT commits](../../../plan/2026-09-29-pbt-core-commit-preparation.md).
Engine maintenance only; no model evaluation, provider call or benchmark input.

## Objective and acceptance

Simplify the uncommitted contract-testing (PBT) code for readability without
changing behavior: identical public API, artifacts, diagnostics text, budgets,
deadline checks, proof gates and classification order. Phase instrumentation is
kept by user decision. Acceptance: build 0 errors; contract suites equal the
pre-refactor baseline; touched files whitespace-formatted; fresh independent
review of the diff.

## Change table

| File / symbols | Change | Validation |
| --- | --- | --- |
| `DafnyCore/ContractTesting/ContractExpressionReducer.cs` `ComposeNativeProof`, `TryComposeCandidate`, `TryComposeWitnessDependencies` | Bundle the shared recursion state into one private composer; one transaction helper for candidate and witness roots; reuse the engine's closed-expression check | Core reducer/witness suites |
| `DafnyCore/Rewriters/PartialEvaluatorEngine.cs` `IsClosedProofExpression` | Shared static check used by engine and reducer | Core suites |
| `DafnyCore/Rewriters/PartialEvaluatorVisitor.cs` proof-artifact rollback sites | One mark/rollback pair instead of paired counters | Core suites |
| `DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` `ExecutionReachable`, `LogicalReachable`, `InstrumentCalls`, wrapper builders | Shared type-dependency helpers, `WithShapes` in call instrumentation, formal/argument list helpers | TestGeneration and Driver suites |
| `ContractRuntimeHeapChecking.cs` | Captured-class lookup, captured-entry helper, simplified post-guard returns | TestGeneration and Driver suites |
| `ContractInitialTypeProof.cs` `TryPrepareObserved`, `Plan` | Shared carrier planning and shape guard | Driver heap suites |
| `ContractSpecificationChecker.cs`, `ContractSolver.cs`, `ContractQueryBuilder.cs`, `ContractHeapFactory.cs`, `ContractSequenceRefinementProof.cs`, `ContractStubRuntime.cs` | Scope-context constant, query-method/target-error helpers, one constructor-name matcher, budget reservation helper, runtime interface lookup helper | TestGeneration and Driver suites |
| `DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Record-kind/capture/input helpers, finite-prefix function, shared query options/result writing/deadline helpers | Driver suites |
| This plan, `plan/INDEX.md` | Owner record | Review |

## Validation

See the root plan for commands. Results are recorded below.

## Progress log

- 2026-09-29: baseline build passed; Core 93/93, TestGeneration 645/645,
  Driver 244/244 (`dotnet test <project> --no-build --filter FullyQualifiedName~Contract`,
  13.8 minutes total). Pre-refactor sources are snapshotted in the session
  scratchpad (`baseline2/`: HEAD diff plus untracked tarball).
- Implemented, all mechanical: `NativeProofComposer`/`ProofTransaction` replace the
  13-parameter recursive composition signatures and the duplicated candidate/witness
  transaction loops; `PartialEvaluatorEngine.IsClosedProofExpression(options, e)` is
  shared; `ProofArtifactMark` replaces paired counters; transformer
  `TypeConstraintExpressions`/`RelatedTypes`/`DefinedConstants`, `CallSiteWrapper`
  (uses `WithShapes`), `FunctionWrapper`, `ShapedFormals`/`ShapedArguments`;
  `ContractHeapFactory.ClassDeclarations`/`NamesConstructor` (five identical
  predicates, including three pre-existing ones in `ContractPatternCompiler`,
  `ContractHeapFactory`, `ContractTypeShapeGenerator`); heap-check
  `CapturedClass`/`CapturedEntry` and post-throw return simplification;
  `HasUnsupportedCarrierShape`/`PlanCarriers`; `ScopeContext`; solver
  `QueryMethods`/`CountTargetErrors`; sequence `TryReserve`; embedded runtime
  `IsRuntimeSequence`/`GenericInterface`; campaign runner `Kind`, `Decode`,
  `SampleInputs`, `HeapCaptures`, `CounterexamplePrefixLength`,
  `ValidateInitialHeapAsync`, `CertifyInitialHeapAsync`, `PrepareObservedHeap`,
  `ClosedQueryOptions`, `WriteJsonAsync`, `QueryExpired`. Artifact names, JSON
  members, messages, deadline checks and call order are unchanged.
- After refactor (cwd `/workspace/cosyn/dafny`, dotnet 8.0.131): build 0 errors/
  0 warnings; touched-file `dotnet format whitespace --verify-no-changes` exit 0;
  Core 93/93, TestGeneration 645/645, Driver 244/244 (same as baseline, 13.8 min).
  One later line-wrap in the campaign runner: rebuild 0 errors, format exit 0.
- Cosyn (`/workspace/cosyn`): `make build-dafny` exit 0 (0 errors), then
  `COSYN_CONTRACT_INTEGRATION=1 python -m pytest -q -n 0 tests/test_goal_pbt_integration.py`
  4 passed. No provider call, no campaign or benchmark run.
- Independent verification: fresh Sonnet agent from requirements and the baseline
  snapshot (the Agent tool exposes no reasoning-effort setting; default used).
  It reconstructed the baseline itself, found the same 16 changed sources, and ran
  build (0 errors/0 warnings), Core 93/93, TestGeneration 645/645, Driver 244/244,
  format exit 0. One finding: the embedded runtime's `RequireGenericInterface`
  replaced `.First(predicate)` and so changed the (practically unreachable)
  missing-interface exception message. Fixed by restoring `.First(predicate)`;
  rebuild 0 errors, format exit 0; full suites rerun below. Its note that
  `ContractQueryBuilder.QualifyExpression` became public is not a refactor change:
  it was already public in the baseline.
- After the fix: build exit 0, Core 93/93, TestGeneration 645/645, Driver 244/244
  (13.1 min); Cosyn goal-PBT integration 4 passed.
- No durable findings: the refactor adds no reusable behavior or knowledge; no wiki
  page references the renamed private symbols.
- Remaining: none for the refactor. Commits follow the root plan's commit plan on
  explicit request.
