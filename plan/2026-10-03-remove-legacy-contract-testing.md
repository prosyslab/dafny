# Remove legacy fixed-input contract testing (engine)

Status: done — implementation and fresh independent verification complete

## Objective and authorization

User decision 2026-10-02/03: remove the legacy fixed-input contract-testing
feature end to end and keep only the runtime PBT campaign
(`dafny test-contracts --runtime-check`). Engine half; Cosyn half (the
`contract_testing` policy, its only caller) is
`/workspace/cosyn/plan/2026-10-03-remove-legacy-contract-testing.md` and lands
first so the engine modes have no callers. Follow-up test merge:
[contract test fixture merge](2026-10-03-contract-test-fixture-merge.md).
No paid run, no dependency, no benchmark change.

## Acceptance criteria

- `test-contracts` accepts only `--runtime-check` (and its hidden worker); the
  fixed-input default, `--generate`, `--generation-checkpoint`, `--symbolic` and
  their workers are gone. A request without `--runtime-check` fails with a clear
  structured error. Removed options such as `--generate` are ignored by the CLI
  (`DafnyNewCli` sets `TreatUnmatchedTokensAsErrors = false`) and yield the same
  structured error (amended 2026-10-03 after verification).
- Removed: fixed-input executor (`ContractCompilerWorker.CompileAsync`/`ParseAsync`,
  `ContractTestRunner`, `IContractProgramCompiler`, `DriverContractProgramCompiler`),
  the legacy diagnostic harness in `ContractHarnessBuilder`, the SMT file RPC
  (`Library/PbtSmt.cs`, `PbtSmt.dfy`, parent-side `ContractRuntimeSession` in
  `ContractStubRuntime`), `PbtObservation.dfy`, input generation (generator,
  pattern, path, scenario, type-shape, trace validator, `ContractBodyExpander`),
  symbolic checking (`ContractSymbolicChecker`/`Models`), model realizers, state
  observer, trace models, logical-effect analyzer.
- Shared helpers the runtime path uses are kept or moved, not deleted:
  `ContractHarnessBuilder` preparation core (`Hash`, `ValidateRequest`,
  `PrepareInitial`, `PrepareObservedHeap`, core `Prepare`, `ValidateSignature`,
  `SupportedType`, `Insert`, `InputExpression`, `ReachableCallables`);
  `ModifiedFields` -> `ContractHeapPlan`; `TrustDependencies`/`TrustKind` ->
  `ContractSpecificationChecker`; runtime config generation and
  `TypeShape`/`TypeShapeToken` -> `ContractRuntimeInstrumentation`;
  `ContractBodyNames`; runtime parts of `ContractTestModels`,
  `ContractHeapFactory`, `PbtObservation.cs` (encoding/serialization/heap snapshot).
- Runtime campaign behaviour unchanged: observation JSONL, verdicts, wire
  shape of `ContractEntry`/`ContractSource`/`ContractDependency` and the
  runtime request/result. The runtime sample program no longer compiles the
  unused Smt RPC class. The `<obs>.legacy` unsupported-record path is preserved.
- Legacy-only tests deleted with the feature (no "feature absent" tests added);
  split test files keep their runtime cases.

## Non-goals

Merging/shrinking surviving tests (separate plan), renaming `.legacy`, trimming
`ContractEntry`, upstream DafnyCore `--test-assumptions` (`TestContracts` /
`ContractTestingMode` in DafnyOptions are unrelated and stay).

## Inspected evidence

Design investigation 2026-10-03 (Opus, read-only) at engine 2d8e11dcc:
- Runtime path reuses `ContractTestRequest` + `ContractHarnessBuilder.ValidateRequest/
  PrepareInitial/PrepareObservedHeap` (`ContractRuntimeHeapChecking.cs:406-454`),
  `ContractModelRealizer.ModifiedFields` (`ContractHeapFactory.cs:139`),
  `ContractQueryBuilder.Build` (`InputExpression`, `Insert`),
  `ContractCompileResult`/`ContractTestStatus` (`CompileRuntimeAsync`),
  `ContractStubRuntime.RuntimeSource(... runtimeReferences: true)` and
  `TypeShapeToken` (`ContractRuntimeObligationTransformer.cs:860`),
  `ContractSymbolicChecker.TrustDependencies/TrustKind`
  (`ContractSpecificationChecker.cs:122-176`).
- `--generate`/`--symbolic` have no runtime-path or root/dafnyutils user.
- Lit tests `cli/contractTesting.dfy`, `cli/contractGeneration.dfy` and their
  `cli/Inputs/*.request.json` exercise removed modes.

## Change table (engine)

| Step | Files / symbols | Change | Validation |
| --- | --- | --- | --- |
| E1 CLI + executor | `TestContractsCommand.cs` (keep Request, RuntimeCheck, RuntimeWorker, runtime branch, SuperviseRuntimeAsync, result write; drop other options/branches/supervisors), `ContractCompilerWorker` (drop CompileAsync/ParseAsync), delete `ContractTestRunner`, `IContractProgramCompiler`, `DriverContractProgramCompiler`, lit tests + inputs, `ContractExternExecutionTests`; `ContractRuntimeRecordingTests` fixture uses `ContractSourceSnapshot.ParseAsync` + direct `ContractPreparedProgram` | Remove fixed-input mode | build; Recording tests |
| E2 generation | delete `ContractInputGenerator`, `ContractInputModels`, `ContractPathExplorer`, `ContractPattern*`, `ContractScenarioExtractor`, `ContractTypeShapeGenerator`, `ContractTraceValidator`, `DafnyCore/ContractTesting/ContractBodyExpander.cs`; split `ContractBodyExpansionResult.cs` (keep `ContractBodyNames`); delete their tests | Remove `--generate` | build; DafnyCore reducer tests |
| E3 symbolic | move trust helpers into `ContractSpecificationChecker`; delete `ContractSymbolicChecker`, `ContractSymbolicModels`, `ContractSymbolicTests` | Remove `--symbolic` | SpecificationChecker tests |
| E4 harness + RPC | move runtime config + TypeShape into `ContractRuntimeInstrumentation` (runtime-only: always runtime references, no concrete calls/types, no tracked ghost fields, no PbtSmt.cs); delete `ContractStubRuntime`; move `ModifiedFields`; delete model realizers, `ContractStateObserver`, `ContractTraceModels`, `ContractLogicalEffectAnalyzer`; trim `ContractHarnessBuilder`, `ContractTestModels`, `ContractHeapFactory`, `PbtObservation.cs`, test config stub; delete `PbtSmt.cs`, `PbtSmt.dfy`, `PbtObservation.dfy`; split tests (`ContractEntryTests`, `ContractHeapTests`, `ContractQueryTests`, `ContractClosedClauseTypeTests`, `ContractGhostInitialValidityTests`, `ContractRuntimeHeapQueryTests`, `ContractExecutionTests`, `ContractRuntimeLibraryTests`; delete `ContractModelRealizerTests`, `ContractBodyExpansionTests`, `ContractInputTests`, `ContractPatternTests`, `ContractScenarioTests`, `ContractPathTests`) | Remove harness and Smt RPC | full filters below |
| Records | `wiki/contract-testing.md` (mark legacy sections removed/stale), `plan/INDEX.md` | Knowledge | review |

Each step must build and pass its tests before the next.

## Risks

- Hidden runtime reliance on legacy helpers: trim/move before delete; build
  `DafnyTestGeneration.Test` (compiles `Library/*.cs` and the config stub).
- `RequestHash`/certificate keys change when `ReplayChoices`/`ReplayPrefix` are
  removed from `ContractTestRequest`; in-process caches/artifacts only.
- Library text changes (PbtRuntime.dfy unaffected unless edited); update pins only if text changes.

## Validation (cwd `/workspace/cosyn/dafny`)

1. `dotnet build Source/Dafny.sln --no-restore -m:1`; `make format`
2. `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~Contract'`
3. `dotnet test Source/DafnyCore.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractExpressionReducer|FullyQualifiedName~ContractWitnessReduction'`
4. `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractRuntimeLibraryCommand'` plus the full `FullyQualifiedName~Contract` filter once at the end (long; ~13 min wall)
5. Smoke: `dotnet Binaries/DafnyDriver.dll test-contracts <old fixed request>` -> structured error; `--generate` -> unknown option
6. From `/workspace/cosyn`: `make build-dafny`; `COSYN_CONTRACT_INTEGRATION=1 python3 -m pytest -q tests/test_goal_pbt_integration.py`

## Progress log

- 2026-10-03: plan written from design investigation.
- 2026-10-03 E1 done: `TestContractsCommand` keeps only Request/`--runtime-check`/`--runtime-check-worker` (a request without either flag returns a structured runtime `Error` result "Contract testing supports only --runtime-check."; `IsRequired` was not used because the supervisor spawns the worker with `--runtime-check-worker` only). Removed `ContractCompilerWorker.CompileAsync/ParseAsync`, `ContractTestRunner`, `IContractProgramCompiler`, `DriverContractProgramCompiler`, `ContractExternExecutionTests`, lit tests `cli/contractTesting.dfy`, `cli/contractGeneration.dfy` and 5 `cli/Inputs/contract*.request.json` (no `.expect` files existed). `RuntimeFixture` now parses with `ContractSourceSnapshot.ParseAsync` and builds `ContractPreparedProgram` directly. Build succeeded; `ContractRuntimeRecordingTests` 22/22 passed.
- 2026-10-03 E2 done: deleted `ContractInputGenerator`, `ContractInputModels`, `ContractPathExplorer`, `ContractPatternCompiler/Models/Sampler`, `ContractScenarioExtractor`, `ContractTypeShapeGenerator`, `ContractTraceValidator`, `DafnyCore/ContractTesting/ContractBodyExpander.cs`; `ContractBodyExpansionResult.cs` renamed to `ContractBodyNames.cs` keeping only `ContractBodyNames`; deleted `ContractBodyExpansionTests`, `ContractInputTests`, `ContractPatternTests`, `ContractScenarioTests`, `ContractPathTests`. Build ok; DafnyCore reducer/witness tests 93/93; DafnyTestGeneration `Contract` filter 573/573.
- 2026-10-03 E3 done: `TrustDependencies`/`TrustKind` moved into `ContractSpecificationChecker` as private members (private `TrustDependency` record, inline extern/body checks); deleted `ContractSymbolicChecker`, `ContractSymbolicModels`, `ContractSymbolicTests`. Trust coverage already lived in SpecificationChecker tests (assume/axiom/extern); added one `{:only}` (assert_only) case to `LogicalScopeRejectsTrustEscapes` for the `nontermination`/`assert_only` kinds that only the symbolic tests asserted. Build ok; `ContractSpecificationChecker` tests 60/60.
- 2026-10-03 E4 done (implementation agent, engine working tree on HEAD 2d8e11dcc):
  - Moved: runtime config generation + `TypeShape`/`TypeShapeToken` into `ContractRuntimeInstrumentation.RuntimeSource` (runtime-only: `RuntimeReferences`/`ProfileRuntime` always true, no `ConcreteTypes`, no tracked ghost fields because runtime `Prepared.Heap` is null, heap shapes without `mutable`/`logicalFields`, no `PbtSmt.cs`; `<obs>.legacy` path preserved); `ModifiedFields` into private `ContractHeapPlan.ModifiedFields`.
  - Deleted: `ContractStubRuntime` (`ContractAbstractChoice`, `ContractRuntimeSession`), `ContractModelRealizer`, `ContractHeapModelRealizer`, `ContractStateObserver`, `ContractTraceModels`, `ContractLogicalEffectAnalyzer`, `Library/PbtSmt.cs`, `PbtSmt.dfy`, `PbtObservation.dfy`, `ContractModelRealizerTests`.
  - Trimmed: `ContractHarnessBuilder` (no `Execution` mode, `RuntimeSource*`, `ExecutionRequest`, `MainName`/`ObservationName`/`SmtName`, serializers; `ValidateRequest` drops replay validation and rejects reachable-mode entries; `PrepareInitial`/`PrepareObservedHeap` now public; `ContractPreparedProgram` lost `ReachableTarget`, `ConcreteCalls`, `ConcreteTypeArguments`, `TypeSubstitution` with `ContractCallableSelector.ConcreteCalls`), `ContractTestModels` (removed `ContractViolationKind`, `ContractReachability`, `ContractExecutionEvidence`, `ContractTestResult`, `ContractCompileRequest`, `ReplayChoices`/`ReplayPrefix`), `ContractHeapFactory` (no allocation/capture/constructor edits, `LogicalFieldsBase64`, `TrackedGhostFields`, `SourceInsertions`, `SourceEdits`; `PrepareFixedState` is the only public preparation and is public for tests; `HeapCell.RuntimeVisible` removed), `PbtObservation.cs` (kept `Text`, `Encode`/`EncodeValue`, `InstantiateShape`, `SerializeNamed`, `PrepareValues`, `SnapshotHeap`/`RuntimeHeap`, `Shape`, `Serialize`, `Unsupported`; removed ConcreteTypes, frames/write/branch counters, logical-field sidecar, `Register`, `ApplyHeap`, `Decode`, `Capture`, `Snapshot`, `Trace`, `Unreachable`, `AssertionFailed`, `EnterFrame`/`ExitFrame`, `Write`, `SameJson`), test stub `ContractRuntimeConfigurationStub.cs`. `PbtRuntime.dfy` unchanged, so both SHA pins stay valid (the `RuntimeDeclaration` pin was deleted with its test).
  - Tests: deleted legacy-only cases in `ContractEntryTests` (8 reachable/extern/ghost-write/runtime-source cases), `ContractHeapTests` (`NoncyclicReferenceFieldsUseDependencyOrder`), `ContractRuntimeHeapQueryTests.PublicPreparationStillRejectsGhostInput`, `ContractRuntimeLibraryTests` (Observation/Smt declaration tests and `RuntimeDeclaration` pin); migrated the rest to `PrepareObservedHeap`/`PrepareFixedState`/`DiagnosticSourceSnapshots` (renamed `MultipleSnapshotsPreserveQueryFiles`, `HiddenModuleFieldDiagnosticSourcesResolveWithoutChangingSnapshots`, `DistinctHeapObjectsProduceResolvableQuerySource`, `GhostFieldsAreAssignedInQueries`); `ContractGhostInitialValidityTests.SupportedGhostInputIsInitialOnly` kept as `SupportedGhostInputParticipatesInInitialCertificate` without the removed-preparation assertion (deviation: the positive initial-certificate checks are still meaningful); `ContractExecutionTests.NullSourceSnapshotIsRejected` kept (still exercises kept `ValidateRequest`).
  - Wiki: `wiki/contract-testing.md` legacy sections marked STALE with a removal section and updated library role table; `wiki/INDEX.md` entry.
  - Checks so far: Source/Dafny.sln builds with 0 errors; `make format` introduced no extra churn; DafnyTestGeneration.Test `Contract` filter 499/499 passed; `grep` for removed names across Source/docs/Scripts/Makefile finds no references.
- 2026-10-03 final validation (cwd `/workspace/cosyn/dafny`, engine HEAD 2d8e11dcc plus this uncommitted working tree; no commit made):
  - `dotnet build Source/Dafny.sln --no-restore -m:1`: 0 errors. `make format`: no unrelated churn.
  - `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~Contract'`: 499 passed, 0 failed (573 before the removals; 60 SpecificationChecker tests include the added `{:only}` case).
  - `dotnet test Source/DafnyCore.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractExpressionReducer|FullyQualifiedName~ContractWitnessReduction'`: 93 passed.
  - `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~Contract'`: first run 230 passed / 27 failed: 22 `ContractRuntimeRecordingTests` failed because the test C# fixture still called the removed `Observation.Register` (the `RegistrationInvalidatesParentEncodingAfterCaughtMetadataFailure` test and its `register-child` scenario were deleted with `Register`); 5 others (`CertifiedSpecificationDecidesBothHeapPolarities`, `ConstructsPartialHeapAndExecutesGhostDraft`, `ValidatesResidualInitialFieldConstraint`, `ChecksStructuralTypeConstraint(Box(1))`, `CapturedGhostHeapDecidesOriginalTransition`) failed after 49-59 s under machine load average ~20-25 (concurrent agent) and passed 16/16 in isolation at load ~14. Final full rerun: 256 passed, 0 failed (10 m 12 s).
  - `grep -rnE` for every removed type/option name across `Source`, `docs`, `Scripts`, `Makefile`, `README.md`: no matches.
  - From `/workspace/cosyn`: `make build-dafny` succeeded (0 errors, 3 pre-existing-style library warnings). Smoke: `dotnet Binaries/DafnyDriver.dll test-contracts <old fixed request>` returns the structured runtime `Error` result "Contract testing supports only --runtime-check."; `--generate`, `--symbolic`, `--generation-checkpoint` and any other unknown option are ignored by the global Dafny CLI (`RootCommand.TreatUnmatchedTokensAsErrors = false` in `DafnyNewCli.cs`), so they yield the same structured error rather than a parser "unknown option" failure.
  - From `/workspace/cosyn`: `COSYN_CONTRACT_INTEGRATION=1 python3 -m pytest -q tests/test_goal_pbt_integration.py`: 4 passed.
  - Remaining: independent verification by a fresh agent; plan not marked done. Note: `git rm --cached` was used (by mistake of convenience) for ContractStubRuntime.cs, ContractTestRunner.cs, IContractProgramCompiler.cs, DriverContractProgramCompiler.cs, ContractExternExecutionTests.cs and the deleted lit tests/inputs, so those deletions are staged; `ContractBodyExpansionResult.cs` was `git mv`ed to `ContractBodyNames.cs` (staged rename). Nothing is committed.
- 2026-10-03 independent verification (fresh agent): requirements 1-5 PASS; build ok; DafnyTestGeneration `~Contract` 499/499;
  DafnyCore reducer/witness 93/93; Driver Recording|LibraryCommand|Observation|Prefix 35/35 plus 4 sampled Check tests;
  CLI smoke (no flag, --generate, --symbolic, --generation-checkpoint) -> structured error; Cosyn integration 4/4.
  Moved helpers proven equivalent for runtime inputs; dropped config entries (ConcreteTypes, logicalFields, mutable) unused at runtime.
  Long Check/Heap Driver suites not rerun independently (user direction; implementer 256/256). Leftover dead fields
  `ContractConcreteMethod.ConcreteTypeArguments`/`TypeSubstitution` to clean up in the fixture-merge step.
- 2026-10-03 follow-up (fixture-merge implementation agent): removed the leftover dead fields `ContractConcreteMethod.ConcreteTypeArguments`/`TypeSubstitution` and their constructor parameters in `ContractCallableSelector.cs` (assigned only, never read; `grep` across `Source` confirms). DafnyTestGeneration `~Contract` 499/499 and DafnyDriver `~Contract` 254/254 after the change; coverage diff shows only the deleted assignments. See the [fixture merge plan](2026-10-03-contract-test-fixture-merge.md).

