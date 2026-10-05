# Remove the agent query-count limit

Status: done — implementation and independent native contract checks passed
Date: 2026-10-04
Owner: Cosyn's embedded Dafny toolchain

## Scope correction — no backward compatibility

The user explicitly directed: ignore backward compatibility, reuse existing code as much as possible, and avoid unnecessary design/code additions. This supersedes all earlier historical-reader/snapshot acceptance criteria and change-table rows. Remove new archived-v6 models/readers and root config_snapshot.py; reporting uses the existing current configuration loader. Do not add legacy parsing, aliases, migrations, compatibility tests or version adapters. Historical raw artifacts stay untouched, but their continued readability is not required. Keep current schema versions coordinated (configuration v6, invocation v11, result v7, PBT request2), and preserve current identity/exit/consumption/artifact validation.

Reuse existing execution, count state, cancellation, process capture, deadlines and scheduling paths. New abstraction/module creation requires a concrete unavoidable need; minimize it and prefer small edits in existing modules. Removing a count ceiling must not silently substitute a default executor count ceiling. All verifier timeouts and shared GC caps remain unchanged. Existing benchmark/evaluator behavior and proof obligations remain unchanged.

| Corrected files / symbols | Work | Validation |
| --- | --- | --- |
| New legacy result models / archival tests in Cosyn, Dafnyutils and Vero | Remove additions; edit current owner models directly | Current result round trips and original runtime acceptance checks |
| Root config_snapshot.py and new historical reporting adaptations | Delete snapshot module and use existing current-config reporting loader | Current configuration/reporting tests |
| New counter/deadline/scheduling helpers | Review necessity, fold into existing code where practical; retain only minimal unavoidable runtime behavior | Existing workflow, timeout/cancel and usage tests |

Vero branch feat/remove-agent-resource-limits was confirmed and created preserving dirty work. Implementations were briefly interrupted for this scope clarification and now resume under this correction. No paid run, dependency, commit or push is authorized.

## Implementation authorization — 2026-10-04

The user approved proceeding with this plan ("OK 진행해"). This authorizes the described code, tests, active configuration, documentation, narrow benchmark-owned result.v7 serialization migration and time-only half-campaign phase reserve. All verifier timeout values, shared GC limits, task contracts, isolation, proof obligations and scoring remain unchanged. Earlier planning-only statements below describe the completed survey stage and do not restrict this authorization. Vero branch confirmation is pending under its owner instructions; Vero code will wait while unaffected work proceeds. No dependency addition, paid provider run, commit or push is authorized.

## Objective, scope and authorization (initial survey, now implemented)

Prepare removal of the runtime campaign's `MaxClosedQueries` ceiling, which
prevents an agent diagnostic from invoking the verifier after a fixed number of
queries. This is the engine prerequisite for the
[Cosyn removal plan](../../plan/2026-10-04-remove-non-timeout-resource-limits.md).
The [integration plan](../../../plan/2026-10-04-remove-cosyn-resource-limit-config.md)
removes corresponding harness configuration.

The user clarified that the shared GC heap limit must stay: the request concerns
agent resource controls such as turn counts and verifier-use counts. This is a
planning-only maintenance task. No C#, generated files, proofs, benchmark inputs,
test expectations, binaries, dependencies, or gitlinks change in this turn.

## Acceptance criteria for implementation

- Runtime campaigns never skip a supported query because a query counter reaches
  a ceiling. Remove the request field, comparisons and
  `closed_query_budget_exhausted` production reason; retain actual query accounting.
- Preserve sample, campaign and query timeouts, cancellation, native dependency
  certification, original assertions, sample validity, caching/provenance and
  conservative unknown/unsupported classifications.
- Preserve finite PBT sample populations, exact replay selection, evidence
  presentation limits and compiler optimization boundaries. They define the
  diagnostic workload or its representation rather than agent call allowances.
- Update Python/C# wire schemas atomically and validate the actual native path.
  Fake Python tests alone cannot establish engine acceptance.

## Inspected evidence and ownership

Read `AGENTS.md`, `CLAUDE.md`, `plan/INDEX.md`, `wiki/INDEX.md`, `Makefile`,
runtime request/runner sources and all `MaxClosedQueries` consumers in source and
tests. No additional scoped instructions/templates were found for the affected
directories. HEAD is `6637a0641f86e6d3b864c957a5307e76365612fb`; the nested working
tree was clean at inspection, while the parent gitlink already differed.

`Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs:12` defines
the default ceiling of 16. `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`
enforces it at lines 334, 630 and 805; line 191 also derives a time reserve from
that count. The ceiling can prevent original dependency certification as well
as direct clause queries. Retain those certifications, and remove only the quota.

Specification/proof/evaluator/dataset/scoring: original contracts, native proof
scope, evaluator and benchmark data stay fixed. Diagnostic reporting changes
only where its former reason depended on quota exhaustion.

## Change table

| File/symbol | Change and method | Necessity / unmet without change | Validation |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs: ContractRuntimeCampaignRequest`; `Source/DafnyDriver/Commands/TestContractsCommand.cs` deserialization boundary | Remove `MaxClosedQueries`, version the request together with Python; retain strict deserialization and reject removed quota data in current-schema requests rather than silently ignoring it; keep timeout/population/replay fields | Python omission alone would still activate engine default16 or stale requests would be silently reinterpreted | Wire serialization and native CLI tests |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs: RunAsync`, query/dependency helpers and request validation | Delete count-based refusal and budget reason; keep query counters as metrics; replace the count-derived reserve with the proposed time-only phase allocation described below, after implementation scope confirmation; actual timeout values stay | Engine still suppresses supported solver work or fails on missing field | Native query/dependency/admission/cancellation tests |
| `Source/DafnyDriver.Test/ContractRuntime/CampaignHarness.cs: CampaignSpec` | Remove query ceiling and constructor forwarding; preserve explicit sample buckets and timeout selection | Every native fixture still sends old quota | Entire ContractRuntime scope |
| `Source/DafnyDriver.Test/ContractRuntime/{ClosedQueriesTests,ClauseDependenciesTests,InitialAdmissionTests,HeapProofReuseTests,TwoStateHeapTests,SpecificationDependenciesTests,InternalCallsTests,HeapConstructionTests,UndecidedObligationsTests}.cs` | Remove ceiling assignments/helper parameters; merge cases distinguished solely by zero/one query allowance; rewrite/delete `ReportsClosedQueryBudget`, `ErasedCheckWithoutBudgetIsUndecided` and shared-fixture expectations; keep invalid/trusted/opaque dependency and genuine undecided/timeout cases | Old tests require removed policy or misleadingly treat a supported proof as unavailable | Relevant classes, then whole runtime scope |
| `Source/DafnyDriver.Test/ContractRuntime/CliBoundaryTests.cs` | Update current wire requests and version/error cases | CLI may accept incompatible request data | CLI boundary tests |
| `plan/2026-10-04-remove-agent-query-count-limit.md`, `plan/INDEX.md` | Record implementation evidence and final handoff when implemented | Owner record otherwise missing | Diff/link review |
| `wiki/contract-testing.md`, `wiki/INDEX.md` (future implementation) | Mark query quota descriptions superseded; retain historical evidence and original experiment populations | Current guidance would still recommend a removed cap | Source-grounded documentation review |

No general compiler rewrite is proposed. Inspection also found
`maximumAttempts=8` and a 20-error presentation cap in the campaign runner;
`ContractReductionBudget` defaults of 100 quantifier instances, inline depth2 and
10000 expression nodes; and sequence proof expansion limits. These bound compiler
diagnostic processing/representation rather than agent turn or verifier-call
allowances, and stay under the clarified scope. Preserve cycle guards and
unsupported-type handling. Do not edit generated C#.

## Compatibility and implementation sequence

1. Reconfirm current source and independent review against the three linked plans.
2. Add runtime campaign request schema version2 in Python and C# in one coordinated
   change, without changing result schema1 or task/proof contracts. New requests
   reject removed quota fields. Keep old saved requests/results unchanged; do not
   present their old workloads as new runs.
3. Delete quota enforcement and adapt query-count-dependent native tests. A
   supported query continues through the unchanged dependency checks until actual
   completion, unknown/error, cancellation or a timeout.
4. Resolve and verify the time-only sampling/proof allocation before engine implementation.
   Current reserve is `min(2 * MaxClosedQueries * query_timeout_ms, campaign_timeout_ms / 2)`.
   Proposed replacement reserves half the campaign time for proof/classification;
   it matches current defaults but can change custom-request sample/proof allocation.
   This is a proposed derived-count policy replacement, not a claim of identical
   phase timing. Confirm this concrete scheduling choice before implementing it;
   if exact custom allocation is required, carry an explicit time-only phase-reserve
   parameter instead of a query-count quota. Sample/campaign/query/verifier timeout
   values are preserved in either design. Record actual sample denominators.
5. Build the owner toolchain, run native tests, then run Cosyn transport/native
   integration and root import/config checks. Review with a fresh agent context.

The finite-population offline API remains supported. Removing the verifier quota
can change diagnostic findings and timing; it is an intentional policy change,
not proof that a historical experiment improved. No provider-backed or historical
benchmark rerun is authorized by this plan-writing task.

## Validation commands (planned; actual outcomes below)

Working directory `/workspace/cosyn/dafny`, prerequisites installed .NET SDK,
restored solution packages, pinned Dafny source and local solver:

- `dotnet build Source/Dafny.sln` — compile engine/schema change; expect success.
- `dotnet test Source/DafnyDriver.Test --filter 'FullyQualifiedName~ContractRuntime'`
  — exercise complete native runtime, dependency admission and cancellation;
  expect pass with explicit unchanged contract/timeout assertions.
- `dotnet test Source/DafnyTestGeneration.Test --filter 'FullyQualifiedName~Contract'`
  — cover runtime model/source/query/encoding contracts; expect pass.
- `make format` — owner-supported C# formatting; inspect all resulting diffs and
  preserve unrelated files. No Dafny source edit is planned, so `make format-dfy`
  and a benchmark proof suite are not required.
- `git diff --check` — whitespace validation.

Working directory `/workspace/cosyn`, after engine implementation/build:

- `make build-dafny` — supported pinned toolchain build.
- `COSYN_CONTRACT_INTEGRATION=1 python3 -m pytest -q tests/test_goal_pbt_integration.py`
  — actual Python/native wire and campaign behavior; expect pass. Use controlled
  sample populations/replays rather than a query cap to keep fixtures finite.

Add meaningful observable coverage for a real supported query/dependency after
more than16 prior queries and for expiration while a further query is pending;
do not add a test that merely checks that a field is absent. Each added test needs
the owner-required intention comment. These are local native checks, not paid
agent experiments, downstream scoring, or whole benchmark proofs.

## Initial planning handoff (historical)

Source investigation and fresh independent plan review (gpt-6-astra/high) are
complete; no substantive planning defects remain after test/phase-allocation
corrections. Implementation and all build/test commands are unrun.
`git diff --check` from `/workspace/cosyn/dafny` passes; affected plan/wiki trees
are Markdown-only and cross-plan links resolve. These are document checks only.
Before implementation the count-derived phase-allocation replacement needs
confirmation, separately from the unchanged verifier timeouts. Only this plan and
its index entry are added. Durable current ownership
findings are summarized in the linked Cosyn plan; no new engine wiki page is
needed for the proposed, unimplemented removal. Existing knowledge stays valid
until implementation updates it. Next action is implementation of the coordinated
engine and Python wire change after the user requests execution.


## Implementation findings

Request schema2 must not be forwarded into internal ContractTestRequest, whose existing independent schema remains1. Extend the change table to Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs: PrepareInitial/Prepare construct that internal DTO using its existing canonical ContractJson.SchemaVersion. No compatibility adapter is added. Validate native heap and full contract tests. CalleeTypeContractsTests and NonterminationTests relied on former zero-query refusal indirectly; retain meaningful native validity/unknown scenarios and update expected native decisions where quota removal permits them.

Initial sandbox build failed without a diagnostic; dotnet build --no-restore -m:1 passed. Official make build-dafny passed through the approved execution path. I initially overlapped its non-incremental rebuild and native tests, causing missing test/driver files; those results are invalid, and stable tests were rerun after completion. Stable test failures revealed the internal request version forwarding above. All generated evidence is in /workspace/tmp/remove-cosyn-resource-limits/native/; no paid providers used.


## Final local verification — 2026-10-04

Code, tests and current wiki are implemented. Official make build-dafny from /workspace/cosyn passed (three existing warnings); corrective incremental dotnet build Source/Dafny.sln --no-restore -m:1 passed with zero warnings/errors. From /workspace/cosyn/dafny, approved socket-capable dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~Contract passed499, and dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~ContractRuntime passed247. Native false erased preconditions now count as rejected, rather than quota-induced unchecked; meaningful rejection, certification, dependency and timeout assertions remain. Request2/internal ContractTestRequest1 are separate current DTOs using the existing canonical constant, not an archival adapter.

make format passed, and final dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes with the owner-generated exclusions passed. git diff --check passed. Cosyn actual-native integration passed2 tests. No benchmark dataset/proof/scoring, dependencies, commits or paid providers changed. Raw build/test/format logs reside in /workspace/tmp/remove-cosyn-resource-limits/native/. An initial overlapping clean build/test run caused missing assemblies and was discarded; final gates ran with stable artifacts.

Initial fresh-review attempts were refused by the runtime thread limit. After implementation agents completed, a new independent verification context started from the requirements and current sources, with no implementation conversation or claims transferred. Its native checks are now running against stable host binaries. Coordinated final image checks remain with the integration plan. Existing wiki contract-testing.md and index document current request2/time-only allocation; earlier quota descriptions are historical.

## Independent native acceptance — 2026-10-04

The fresh requirements-only Cosyn/native verifier independently audited current engine and wire sources, with no implementation conversation or conclusions transferred. Against stable host binaries it ran dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~ContractRuntime:247 passed; DafnyTestGeneration ContractRuntime plus ContractGhostInitialValidity:199 passed; original Python/native PBT integration:2 passed. Parent's broader generation Contract filter499 passing cases is separate local evidence. Existing query/dependency/timeout scenarios now assert actual native decisions rather than quota-refusal outcomes. Native timeout values, proof scope, finite populations, compiler guards and result schema1 remain unchanged; no legacy adapter exists.

Fresh source/quota/version searches, git diff --check and recursive plan/wiki Markdown checks passed. Evidence: /workspace/tmp/remove-cosyn-resource-limits/fresh-review/verification-summary.md and native TRX/JUnit; parent native build/499/247/format logs remain in native/. Current contract-testing wiki and index are updated. Native implementation and independent verification are complete; root image handoff stays in the linked integration plan.
