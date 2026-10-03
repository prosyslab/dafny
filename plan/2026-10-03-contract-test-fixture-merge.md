# Merge contract runtime tests onto shared fixtures

Status: done — implementation and fresh independent verification complete

## Objective and authorization

User direction 2026-10-02/03: do not merely cut test count; merge test cases
onto fixed shared fixture programs so each behaviour is checked once and all
duplicated checks are removed. Main cost today is per-campaign C# compilation
(~4.3 s of ~4.9 s per campaign; DafnyDriver contract wall 12m40s, slowest class
`ContractRuntimeCheckTests` 768 s serial). Cosyn Python test half:
`/workspace/cosyn/plan/2026-10-03-contract-test-fixture-merge.md`.

## Acceptance criteria

- Every surviving behaviour (named by code branch) has exactly one check; a
  mapping CSV maps each old test (file:line, name, intention) to its new test
  and bucket/clause, or marks it exact-duplicate (target named) or legacy-removed.
- Shared harness `Source/DafnyDriver.Test/ContractRuntime/CampaignHarness.cs`:
  spec/run records, content-keyed cached campaigns (`Lazy<Task>`), global
  throttle, one `Hash()` helper, bucket helpers (`Size()`-based buckets of 4
  samples; `MaxViolationsPerObligation = SampleCount`), per-fixture xUnit class
  fixtures (`IClassFixture` + `IAsyncLifetime`) starting campaigns concurrently.
- Fixture programs under `ContractRuntime/Fixtures/*.dfy` (content items).
- Rules: scenarios needing different campaign-wide settings or whole-program
  declarations stay separate; callee-invalid and goal-evidence scenarios never
  share a sample; status branches (ViolationFound, NoViolationFound, both
  Inconclusive reasons) have dedicated campaigns; `Assert.Single` replaced by
  clause-filtered counts.
- Each `[Fact]`/`[Theory]` row asserts one behaviour on its slice with a
  one-line intention comment; the shared campaign is setup.
- Coverage of engine contract code (coverlet cobertura, union of
  DafnyTestGeneration.Test + DafnyDriver.Test, `~Contract` filters) after ⊇
  before, with any lost line/branch justified; baseline taken after legacy removal.
- Wall time of DafnyDriver contract filter measured before/after (target ≲ 3 min).

## Non-goals

Engine compile cache or production changes (`IncludeRuntime`, shared compiler)
— separate approval; DafnyTestGeneration.Test restructuring beyond
coverage-proven duplicates.

## Design (investigation 2026-10-03)

Fixture groups (compiles now -> after): D1 obligation kinds 21->2, D2 module
boundary 10->2, D3 sample classification 21->3, D4 input validity 24->1-2, D5
callee type contracts 25->2, D6 closed queries 13->2, D7 ghost availability
4->1, D8 function-by-method goal 4->2, D9 nontermination 7->1, D10
pre-compilation 0, D11 CLI boundary 1, D12 value encoding 8->1, H1 two-state
heap 20->3, H2 spec dependencies 11->2, H3 heap budget reuse 11->~8, H4
initial admission 41->~22, H5 internal calls 7->2-3, ClauseDependency 6->3,
Recording unchanged. Totals ~215 -> ~60 compiles. Exact duplicates found:
Heap :337 vs :349, Heap :282/:293 vs :162, Prefix :34/:70 vs Check :209/:272,
Check :263 vs :201, :1052 vs :1043. Whole-program-sensitive tests keep own
programs (Heap :199, :211, :227, :699; membership/fact reuse :456-:574, :904).
Pre-existing failure to check: `DafnyTestGeneration.Test.ContractHeapTests.NoArrayHeapSkipsResolvedArrayTypeScan` (2026-09-29 TRX).

## Change table

| File / symbol | Change | Validation |
| --- | --- | --- |
| new `DafnyDriver.Test/ContractRuntime/CampaignHarness.cs` (`CampaignSpec`, `CampaignRun`, `Campaign`, `CampaignFixture`), `DafnyDriver.Test.csproj` content item `ContractRuntime\Fixtures\*.dfy` | Shared harness | builds; all classes pass |
| new `ContractRuntime/Fixtures/*.dfy` (18 files, named `// == source/generator NAME ==` sections) and 19 test classes `ContractRuntime/*Tests.cs` | Merged fixtures | per-class filter, full `~Contract` |
| deleted `ContractRuntimeCheckTests.cs`, `ContractRuntimeHeapTests.cs`, `ContractRuntimePrefixTests.cs`, `ContractRuntimeObservationTests.cs`, `ContractRuntimeHeapConstructionTests.cs`, `ContractRuntimeClauseDependencyTests.cs` | Migrated per [mapping](2026-10-03-contract-test-fixture-merge-mapping.csv) | coverage diff |
| `DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs` `ContractConcreteMethod` | Drop dead `ConcreteTypeArguments`/`TypeSubstitution` (legacy-removal leftover; recorded in that plan) | TestGeneration `~Contract` 499/499 |
| DafnyTestGeneration.Test survivors | No removal: no duplicate was proven by coverage (per-test coverage not run) | n/a |
| `wiki/contract-testing.md`, `wiki/INDEX.md` | Shared-campaign/bucket test pattern section | review |

## Validation (cwd `/workspace/cosyn/dafny`)

1. Baseline after legacy removal: coverage + TRX for `~Contract` in both test projects (runsettings in scratchpad, cobertura, include `[DafnyTestGeneration]DafnyTestGeneration.ContractTesting.*,[DafnyDriver]Microsoft.Dafny.Contract*`).
2. Per fixture: `dotnet test Source/DafnyDriver.Test --no-build --filter 'FullyQualifiedName~ContractRuntime.<Fixture>'`.
3. Final: full `~Contract` filters, coverage diff (after ⊇ before), TRX wall time/counts vs baseline, `make format`.

## Progress log

- 2026-10-03: plan written from design investigation.
- 2026-10-03 implementation (engine HEAD 2d8e11dcc + uncommitted legacy removal; cwd `/workspace/cosyn/dafny`; no commit):
  - Baseline: Cosyn's `make build-dafny` PDBs map sources to `/_/` (`ContinuousIntegrationBuild`/`PathMap`), so coverlet instrumented nothing (first baseline: empty cobertura). Rebuilt with `dotnet build Source/DafnyDriver.Test --no-restore -m:1 --no-incremental` plus `Source/DafnyTestGeneration.Test` (this also rewrote `Binaries/` from the same sources without the CI path map). Runsettings (scratch `merge/contract-cov.runsettings`): cobertura, Include `[DafnyTestGeneration]DafnyTestGeneration.ContractTesting.*,[DafnyDriver]Microsoft.Dafny.Contract*,[DafnyDriver]Microsoft.Dafny.TestContractsCommand*,[DafnyCore]Microsoft.Dafny.Contract*`, Exclude DAST/DCOMP. Baseline commands: `dotnet test Source/<P> --no-build --filter '<F>' --settings .../contract-cov.runsettings --collect 'XPlat Code Coverage' --results-directory .../cov-before/<P> --logger 'trx;LogFileName=.../cov-before/<P>.trx'` with F = `FullyQualifiedName~Contract&FullyQualifiedName!~DafnyDriver.Test.ContractRuntime.` (new classes already compiled in): DafnyTestGeneration.Test 499/499, 70 s; DafnyDriver.Test 256/256, TRX wall 10 m 08 s (08:42:21-08:52:29), 233 campaigns of which 220 compiled C#. Coverage: 5315 of 5754 lines covered.
  - Inventory/mapping: `plan/2026-10-03-contract-test-fixture-merge-mapping.csv` (190 old test methods incl. 18 Recording/LibraryCommand `unchanged`; each migrated row names its new test and bucket/campaign, or `duplicate-of:` its target). Six exact duplicates removed: `RejectsEntryPrecondition`, `InvalidCallDoesNotExecuteCallee`, `ContinuesAfterSampleTimeout`, `DecidesOriginalTwoStateHeapPostcondition`, `AcceptsOriginalTwoStateHeapPostcondition`, `UnvalidatedSpecificationCalleeRemainsUnchecked` (their unique assertions folded into the target). `IgnoresDraftsForAbstractTraitMembers` was planned as a duplicate but the coverage diff showed it alone reaches `ContractRuntimeSourcePreparation.NeedsDraft`'s trait guard, so it is kept (`ModuleBoundaryTests` bucket 9).
  - Result: 19 classes (`PreCompilation`, `ValueEncoding`, `ObligationKinds`, `ModuleBoundary`, `SampleClassification`, `InputValidity`, `CalleeTypeContracts`, `ClosedQueries`, `UndecidedObligations`, `FunctionByMethodGoal`, `Nontermination`, `CliBoundary`, `TwoStateHeap`, `SpecificationDependencies`, `InternalCalls`, `ClauseDependencies`, `HeapProofReuse`, `InitialAdmission`, `HeapConstruction`), 168 methods/232 cases replacing 172 methods/234 cases; 80 campaigns (70 compiled; 10 end before compilation) instead of 233 (220 compiled). Recording/LibraryCommand unchanged.
  - Final checks: `dotnet build Source/DafnyDriver.Test` and `Source/DafnyTestGeneration.Test` ok; `make format` (whitespace only in two new files); DafnyDriver `~Contract` 254/254, TRX wall 77 s (09:18:45-09:20:02), rerun of `~DafnyDriver.Test.ContractRuntime.` 232/232 at load ~17; with coverage: DafnyTestGeneration `~Contract` 499/499 (72 s), DafnyDriver `~Contract` 254/254 (84 s).
  - Coverage diff (scratch `merge/covdiff.py cov-before cov-after ContractTesting/ContractCallableSelector.cs=<pre-edit copy>`; union of both projects, per (file,line) hits and per-condition max coverage): no lost line or condition except in the edited `ContractCallableSelector.cs`, where after line remapping only the deleted dead assignments (`ConcreteTypeArguments = arguments;`, `TypeSubstitution = substitution;`) and the edited constructor call differ. Limitation: union of per-project condition percentages is an approximation (max per condition), not exact branch-outcome union.
  - Deviations: fixture files hold several named sections per class (one request per section) instead of one file per program; generator sections are not standalone Dafny. D7 became `UndecidedObligations` (status "No goal obligation was decided in a valid sample.", absorbing `ReportsClosedQueryBudget` and `ErasedCheckWithoutBudgetIsInconclusive`); `ExecutesGhostPostcondition` moved to `ObligationKinds`. The function-by-method goal uses an unnamed result in every bucket (`contractResult`); no coverage was lost. `TwoStateHeap` Main merges the ghost-amount and plain two-state programs (amount always 2) with nontermination permission and invalid-callee buckets. `Nontermination` holds the rejected-entry and timeout duplicates. Some populations are now pinned more strongly than before (for example the nested-domain bucket is a runtime error "callee implementation invoked a helper outside its precondition"). Harness default campaign timeout 300 s (bucketed campaigns run 16 at a time). 70 compiles instead of ~60: whole-program admission rows (`InitialAdmission` 26 campaigns) and proof-reuse rows (`HeapProofReuse` 13) stay separate by rule.
  - Merge hazards found (also in the wiki): `old(...)` captures are evaluated at entry in every sample (guard inside the capture); a bodyless logical dependency makes the whole request `DraftsRequired`; closed/heap clauses are decided in every bucket; identical samples hit decision caches; `object` is a Dafny keyword.
  - Wiki: [shared-campaign runtime test pattern](../wiki/contract-testing.md#shared-campaign-runtime-test-pattern-2026-10-03-implementation-checks) and `wiki/INDEX.md` entry.
  - Remaining: independent verification by a fresh agent; plan not marked done.

- 2026-10-03 verification findings D1-D4 fixed (test files only):
  - D1 fixed: `TwoStateHeapTests.CapturedGhostHeapDecidesOriginalTransition` pins the shared `Changed(cell, amount)` obligation to `ClosedSmt == 3*4` and `Unchecked == 4`, with `Violations == 8`. These counts come from the actual campaign result: buckets 0-2 decide the clause by closed query; bucket 3 (invalid `Client.Bad` callee) is excluded and records `callee_contract_unvalidated`; only buckets 0 and 2 violate. So holding bucket 1 is decided in all 4 samples.
  - D2 fixed: `CampaignRun.AssertViolated` requires exactly `perSample` (default 1) violations of the clause per ordinal of the bucket. By default (`exclusive`) it also requires no violation of that obligation outside the bucket and `obligation.Violations == 4*perSample`. Only shared clauses opt out with `exclusive: false`: input-validity and callee-type markers, and TwoStateHeap `Changed` (whose exact total is pinned in D1). `ReportsInvariantMaintenance` pins `perSample: 2` (loop heads 2 and 3).
  - D3 fixed: `AssertHolds` requires `ClosedSmt == 0` and `Unchecked == 0` in addition to runtime evaluations, runtime decision and zero violations.
  - D4 fixed: `CapturesOldThroughLocalAlias` asserts that every obligation of its clause is Runtime. The whole Main program is not all-Runtime, because `M.Head` has a `recursive_heap_contract` callee obligation, so the old "all obligations" form does not apply verbatim.
  - Checks: `dotnet build Source/DafnyDriver.Test` ok; `make format` ok; DafnyDriver `~Contract` run twice: 254/254 (77 s) and 254/254 (79 s). Coverage diff not rerun: only assertions changed, with no fixture program, campaign spec or engine code change, so engine coverage is unaffected.
- 2026-10-03 coordinator closure: fresh independent verification (no implementer context): mapping complete (172 old
  methods, 6 duplicate-of), ~70 mappings compared, bucket isolation/status branches/harness safety PASS, coverage diff
  reproduced (nothing lost beyond the deleted dead assignments), DafnyDriver `~Contract` 254/254 in 82 s and 79 s,
  DafnyTestGeneration `~Contract` 499/499. It found weakened assertions D1 (TwoStateHeap holds bucket not pinned as decided),
  D2 (exact violation counts), D3 (AssertHolds), D4 (CapturesOldThroughLocalAlias); fixed by the implementer and rerun
  254/254 twice (77 s, 79 s); the fixes themselves were not re-verified independently. Open follow-up: campaign directories
  under /workspace/tmp are never cleaned (old tests behaved the same).
