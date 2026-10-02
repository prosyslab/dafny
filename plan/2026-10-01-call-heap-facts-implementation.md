# Bounded call heaps and exact successful facts

Status: done

Parent: [engine plan](2026-10-01-pbt-call-state-memo-profile.md).
Owner: engine implementation; root registers index and durable wiki findings.

## Objective and acceptance

Extend original method postcondition heap checking to captured internal calls.
Bind receiver, inputs, outputs, call identity and entry/return heaps; old means
that invocation's entry. Reuse exact successful native heap-query facts with
source/query identity and cancellation/budget boundaries. Preserve independent
state admission, original preconditions, types, dependencies, aliases and frames.
Missing or mismatched state, unsupported allocation changes and universal WD
failures remain unchecked. No general sequence solving, h15 specification edits,
paid runs, dependencies, commits or evaluator changes.

## Inspected evidence

Existing transformer only sets EntryHeapPostcondition for goal methods; bridge
captures only goal entry/return. Existing heap preparation accepts campaign Entry,
validates shape and frame, and prepares original-source queries. Campaign runner
already admits initial states and reuses exact native membership certificates.
Existing runtime old and scalar dependency mapping are retained. Parent/root and
engine AGENTS.md, CLAUDE.md, plan/wiki indexes and applicable sources inspected.

| Exact files/symbols | What/how/why; unmet without change | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs: clause metadata, WrapperCore, Check | Method call heap postcondition metadata and invocation captures; internal logical heap checks otherwise unchecked | Native transformer and Driver call transition tests |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeInstrumentation.cs: bridge methods | Begin/end/leave call capture with unique id, current check binding; required original per-call state evidence | Driver nested/repeated call and raw trace tests |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs: heap preparation/classification/QueryHeapAsync | Match captures within prefix, original method mapping and successful exact query reuse; otherwise wrong old/context or repeated proofs | Driver true/false/frame/dependency and memo behavior |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs | Reuse existing preparation through call-specific campaign entry only if needed | Native heap query controls |
| Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs; Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs | Observable call heap regression cases and supported metadata | Focused native suites |
| Source/DafnyTestGeneration/ContractTesting/ContractNativeFactCache.cs: identity, Record, TryReuse | Extract production exact source/query/role identity, successful-outcome admission and current cancellation/deadline boundary; deterministic review controls require this actual reusable boundary | Failed attempt then retry, source/role/polarity identity, expired/cancelled hit controls |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs: MatchCallCaptures | Validate ordered prefix invocation stack and capture field shapes before original heap preparation; malformed/crossed calls otherwise escape conservative handling | Nested, missing, duplicate, crossed, malformed and late-return controls |
| Source/DafnyTestGeneration.Test/ContractRuntimeFactEvidenceTests.cs | Exercise source-bound proof memo and capture matching boundaries with controlled evidence | Focused native tests and existing native heap queries |
| This plan | Record implementation/checks/limits | Diff review |

Root additionally authorized inspecting retained h06 overlapping replacements;
if still present, make only a bounded edit-composition correction and regression
in the already-owned transformer/test files. Preserve the original request.

## Validation

Only after root grants shared native lane, cwd /workspace/cosyn/dafny:
`dotnet build Source/Dafny.sln --no-restore -m:1`; then
`dotnet test Source/DafnyTestGeneration.Test --no-build --filter FullyQualifiedName~ContractRuntime`
and `dotnet test Source/DafnyDriver.Test --no-build --filter FullyQualifiedName~ContractRuntimeHeapTests`.
Run supported `make format` through coordinated lane; independent verifier starts
fresh from requirements/current tree. Original fifteen-case reruns owned by root.
Prerequisites .NET8/restored packages/Z3. Expected: build and affected native
checks pass. No proof/benchmark success inferred from build alone.

Risks: nested calls and finite-prefix termination; old-state confusion; source
mapping; incomplete ghost state; global/WD inconsistency; resource budgets.
No further approval required under explicit parent task authorization.

## Progress

- Initial two solution builds passed. Five new Driver call/memo controls passed
  (nested receiver/alias old state, negative callee, frame, dependency, repeated
  exact heap premise) in 32.3 seconds. Outputs retained under root
  `tmp/experiment/pbt-optimization-20261001/owner-call-checks/`.
- Initial test invocation without single-worker setting hit sandbox local IPC
  denial; authorized escalated `dotnet test --no-restore -m:1` succeeded.
- h15 retained original native result proves remaining scope: message return
  subtype obligations at MvSpec lines 220,225,230 remain unproved, so concrete
  call admission cannot substitute for universal WD certification.

Additional local diagnostic: retained h06 exact original request through
`python /workspace/tmp/experiment/pbt-optimization-20261001/owner-call-checks/check_h06.py`
in tmux `pbt-h06-current`, cwd `/workspace/tmp/experiment`. No providers; request
hash/revision/timestamps/process/artifacts recorded by script. This is an engine
transformation diagnostic, not the final frozen fifteen-case population.

- Native TestGeneration runtime + phase timing scope: 164/164 passed in 25.3591s
  (`native-runtime-1.log`). Broad Driver heap/recording/prefix scope is running.
- Successful fact reuse includes checked clause truth and checked negation (a
  false contract is a successful negative proof); no unknown/timeout/error result
  is newly memoized. Initial-state cache stores affirmative admission only.
  Unknown clause attempts may be retried under the unchanged remaining budget;
  exact query reuse checks cancellation/time before accepting prior evidence.
- Capture occurs only for nongeneric original method wrappers with non-runtime
  heap postconditions, compilable captured inputs/outputs and supported receiver
  naming. Ordinary runtime wrappers preserve prior raw Check record shape.
- Profiling hooks are coordinated with
  [profile child plan](2026-10-01-runtime-profile-sidecars.md); root owns durable
  wiki/index integration. No shared wiki writes from this bounded agent.

## Implementation handoff (2026-10-01)

Bounded implementation complete; parent-owned fresh verification and frozen
fifteen-case results remain pending, so this child remains in-progress for parent
closure. No running owner processes remain. Next action: fresh verifier reviews
current tree, root freezes supported build and runs fifteen original requests.

Validation cwd `/workspace/cosyn/dafny`, SDK 8.0.131, testhost .NET 8.0.31;
engine HEAD `12065bbe85c4e20b9b5f8bb4b159f6394779fdb3` plus this dirty development
state (no commits). Retained logs under root
`tmp/experiment/pbt-optimization-20261001/owner-call-checks/`:

| Command/check | Outcome and evidence |
| --- | --- |
| `dotnet build Source/Dafny.sln --no-restore -m:1` | Twice passed, `build-1.log`, `build-2.log`; subsequent tests rebuilt affected final assemblies |
| `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter 'FullyQualifiedName~ContractRuntime\|FullyQualifiedName~ContractPhaseTimingTests' --logger 'console;verbosity=normal'` | 164/164, 25.3591s, `native-runtime-1.log` |
| `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter 'FullyQualifiedName~ContractRuntimeHeapTests\|FullyQualifiedName~ContractRuntimeRecordingTests\|FullyQualifiedName~ContractRuntimePrefixTests' --logger 'console;verbosity=normal'` | 105/105, 6.8957min, `driver-runtime-1.log` |
| Original fixed h06 diagnostic, tmux `pbt-h06-current` | Exact request hash `08638e59116eea7bead6e943eb0ce8cc87ee84e44cc18d0dafd5552f5d2a5e60`; pre-correction unsupported overlapping edits in 5.93s; `h06-current/run.json`, result/logs retained |
| Generic nested statement-expression regression before correction | Reproduced same unsupported overlap; `nested-statements-before.log` (1 failed as expected) |
| `make format` | Passed; workspace-load warnings recorded in `format.log`; no unexpected files changed |
| `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter 'FullyQualifiedName~ContractRuntimeObligationTests' --logger 'console;verbosity=normal'` | Final 9/9, 2.3562s, `native-final.log`; nested expression regression verifies both surviving branch ASTs |
| `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter 'FullyQualifiedName~InternalHeapCall\|FullyQualifiedName~InternalHeapFact\|FullyQualifiedName~ExactHeapFacts\|FullyQualifiedName~WritesAggregateRuntimeProfileSidecar' --logger 'console;verbosity=normal'` | Final 8/8, 47.2923s, `driver-final.log`; includes missing-return timeout, changed-state negative proof, and profile sidecar assertions |
| `git diff --check` | Passed |

Tests use local fake/drafted programs and native solver only. No paid providers,
benchmark source/specification changes, general sequence solving or commits.
Full upstream tests were not run; affected native checks passed. Root will run
supported integration packaging and independent verification.

Durable findings for parent wiki integration: call old-state requires invocation
identity and prefix-local entry/return captures; initial construction, requires,
observed admission, frame and specification dependencies remain distinct gates.
Exact successful native heap queries can share proof receipts without repeating
premise checks across clauses, but unknown/error/timeout attempts grant nothing.
Nested `StmtExpr` erasure must remove only the proof statement, preserving tail
expressions and their independent instrumentation.

Limits: nongeneric original method callees only; function-by-method call heaps,
changed allocation topology, unavailable ghost outputs, reserved receiver-name
collisions and unsupported shapes stay outside this extension. h15 original
universal string/RawByte return WD remains unchecked; concrete call validity is
not a replacement. Post-correction h06 historical outcome is intentionally left
to root's frozen fifteen-case rerun, not inferred from the generic regression.

## Additional review controls (in progress)

Parent static review requests deterministic generalized-cache and capture-boundary
controls before handoff. Add `ContractNativeFactCache.cs` as the production exact
native identity/success/deadline boundary reused by the runner; add matching and
shape validation to existing `ContractRuntimeHeapChecking` for prefix call
captures. Add `ContractRuntimeFactEvidenceTests.cs` covering failed/nonproof retry,
source/kind/positive/negative-query identity, expired/cancelled cache hits and
malformed/missing/mismatched/nested invocation records. No test-only hooks or
semantic fallback. Validation: focused new native class plus existing
ContractRuntimeHeapQueryTests/ObligationTests and final Driver call/memo controls;
`make format`, affected build and diff review. Prior completed checks retained.


## Final review-control handoff

The additional production-boundary changes are complete and stable. Full solution
`dotnet build Source/Dafny.sln --no-restore -m:1` passed (`build-review.log`), initially
with one CS8601 cache-miss nullability warning. Added the accurate
`MaybeNullWhen(false)` annotation and corresponding nullable runner local;
subsequent affected-project rebuild in Driver tests has no warnings.

- `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter
  'FullyQualifiedName~ContractRuntimeFactEvidenceTests|FullyQualifiedName~ContractRuntimeHeapQueryTests|FullyQualifiedName~ContractRuntimeObligationTests'
  --logger 'console;verbosity=normal'`: 159/159, 19.6923s, `native-review.log`.
  The new class contributes 25 deterministic cases covering failed/nonproof
  retry, premise SAT, query-role/polarity/source/name/path separation,
  cancellation/deadline on cache hit, nested invocation binding, malformed,
  duplicate, crossed and missing captures, and later-return prefix exclusion.
- `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter
  'FullyQualifiedName~InternalHeapCall|FullyQualifiedName~InternalHeapFact|FullyQualifiedName~ExactHeapFacts|FullyQualifiedName~MembershipReuseRejectsUnsuccessfulProof|FullyQualifiedName~MembershipReuseDoesNotCrossCampaignOrSourceView'
  --logger 'console;verbosity=normal'`: 9/9, 1.0530min, `driver-review.log`.
- Final `make format`: passed (`format-final-review.log`), existing workspace
  loading warnings only. Final `git diff --check`: passed.

All owner native processes have finished; no further source edits or checks are
planned before independent review. Root now owns supported packaging/integration,
fresh independent verification and fifteen-case outcomes. No benchmark requests,
budgets, sources or scores were changed. Child remains in-progress solely for
parent-owned acceptance and final closure; current implementation has no known
failing owner checks. The root's wiki integration remains the next documentation
action alongside the final retained-results report.

## Final-verifier cache-hit boundary correction

Fresh verifier found successful campaign memo paths without uniform current
cancellation/deadline checks. Bounded authorized correction after root packaging
stopped: guard reads of `queryCache`, `specificationAttempts`, and
`initialHeapCache` before and after lookup using existing `RequireCampaignTime`;
recheck specification acceptance and memo publication. Preserve caller
cancellation propagation, existing campaign-expiry-to-unchecked behavior, fact
identity/admission and query budgets. No test-only hooks.

| Additional file/symbol | What/why | Validation |
| --- | --- | --- |
| ContractQueryDeadline.cs: TryReadCached | Reuse current boundary before/after production cached-value reads; dictionary lookup itself can be interrupted | Deterministic cancelled/expired-during-hit controls |
| ContractRuntimeCampaignRunner.cs: campaign memo paths | Apply common guard and convert only CampaignDeadlineExpiredException at existing result boundaries | Existing repeated-proof/call controls and cancellation tests |
| ContractRuntimeFactEvidenceTests.cs | Exercise guarded existing fact lookup with controlled lookup completion; unchanged live success/missing behavior | Focused native test class |

Validation cwd `/workspace/cosyn/dafny`: affected native and Driver filters, full
solution build, `make format`, and diff check; exact outcomes appended below.

### Cache-boundary correction results and stable handoff

The correction is complete. All existing campaign successful-proof cache reads
now pass `RequireCampaignTime` before and after lookup; initial admission returns
and specification `Accept` additionally recheck immediately before reuse.
Query publication is checked before memo insertion and before use. Caller
cancellation propagates; only the existing explicit campaign deadline exception
maps to unchecked/unsuccessful admission. Native query charges are unchanged.

Commands below ran in `/workspace/cosyn/dafny`; logs remain under
`/workspace/tmp/experiment/pbt-optimization-20261001/owner-call-checks/`:

- `make format`: passed, `format-boundary.log` (workspace loading warnings only).
- `dotnet build Source/Dafny.sln --no-restore -m:1`: passed, zero warnings/errors,
  35.33s, `build-boundary.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter
  'FullyQualifiedName~ContractRuntimeFactEvidenceTests' --logger
  'console;verbosity=normal'`: 31/31, 1.6079s, `native-boundary.log`. Six new
  controls force cancellation/deadline during successful lookup, reject already
  closed boundaries, preserve live hit/miss behavior, and demonstrate zero new
  query charges when a cache read expires.
- `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter
  'FullyQualifiedName~InternalHeapCallsUseTheirOwnEntryState|FullyQualifiedName~IndependentGlobalProofIsReusedAcrossPureSamples|FullyQualifiedName~ReusesExactNativeInitialCertificateForHeapDecision|FullyQualifiedName~ExactHeapFactsAreReusedAcrossClauses|FullyQualifiedName~HeapQueryBudgetExhaustionRemainsUnchecked|FullyQualifiedName~RespectsSharedClosedQueryBudget'
  --logger 'console;verbosity=normal'`: 8/8, 40.8779s, `driver-boundary.log`.
- `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter
  'FullyQualifiedName~ChecksClosedQuantifier' --logger
  'console;verbosity=normal'`: 1/1, 9.0679s, `closed-hit-boundary.log`; existing
  one-decision-budget/two-sample negative-proof reuse remains correct.
- Final `git diff --check`: passed.

All owner source edits and native processes have finished. Root may now rebuild
supported packaging and run integration/fresh verification. Earlier packaging
was intermediate; use this final current source state for the frozen fifteen
requests. No broader native scope was repeated for this bounded guard correction.

Fresh independent acceptance (requirements-only context/current source): native
49/49, Driver16/16 and artifact13/13 pass. Formal receipt:
`/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/engine-acceptance.json`,
SHA-256 `d58ba07d8bf03a23c0c96611d18bd13e7ce797e4579d06d21e0b952ade88dbbc`.
Supported final package and Cosyn integration4/4 pass. Source is frozen; all15
historical outcomes and replays remain tracked by the root plan. Durable findings:
[invocation-bound heaps, facts and profiles](../wiki/contract-testing.md#invocation-bound-callee-heaps-fact-reuse-and-profiles-2026-10-01).
No pending code or native check remains within this bounded child scope.

## Reopened actual h06 overlap (2026-10-01)

The frozen `optimized-final-01` original h06 request still returns unsupported:
`Overlapping diagnostic source replacements are not supported.` Evidence:
`/workspace/tmp/experiment/pbt-optimization-20261001/cases/h06-fold-zero-width/optimized-final-01/runtime/result.json`;
phase trace reaches `transformation:0` after reachability resolution. The earlier
nested StmtExpr regression addressed one concrete overlap but did not resolve
this retained case. Preserve the failed attempt and original request unchanged.

Parent authorizes current repository edits while the separate frozen toolchain
and all frozen campaign artifacts stay immutable. No native build/test/run until
parent grants the lane after all fifteen frozen campaigns complete.

| Exact files/symbols | Bounded change and reason | Validation |
| --- | --- | --- |
| ContractRuntimeObligationTransformer.cs: Apply overlap exception | Include source path and both edit spans/replacement text so the actual retained failure identifies its conflicting operations; keep rejection unchanged | Reproduce unchanged original h06 using current-source build after lane grant |
| ContractRuntimeObligationTransformer.cs: confirmed overlap producer only | Pending diagnostic evidence; AST identity versus shared source token is a hypothesis, not a confirmed root cause | Real source-shape regression must fail before correction and pass afterward; no broad overlap suppression |
| ContractRuntimeObligationTests.cs | Add exact feasible real h06 shape once confirmed, preserving surviving expressions and original obligations | Focused transformer tests and relevant Driver check after lane grant |
| This plan | Record failure, diagnosis, exact commands and next handoff | Diff review |

Planned commands from engine root after lane grant: `dotnet build Source/Dafny.sln
--no-restore -m:1`; focused TestGeneration transformer test; unchanged h06 through
existing owner diagnostic script with a new output directory/run identity;
`make format`. Parent owns subsequent supported packaging/freeze and acceptance.
No benchmark/specification edits, witness guesses, heuristic fallbacks, or silently
discarded runtime instrumentation. Native obligations retain original source.

Confirmed original h06 diagnostic: build `build-h06-diagnosis.log` passed with
0 warnings/errors (13.04s). Tmux `pbt-h06-overlap-diagnosis`, existing exact
request hash unchanged, completed exit0 in 5.68s; artifacts in
`owner-call-checks/h06-overlap-diagnosis`. It overlapped two distinct wrappers
`StepColumn__pbt_site_104` / `_105` at FoldSpec.dfy byte span [13047,13057),
line475, within ColumnTraceRelation's forall. QuantifierExpr.SubExpressions
includes both its original term and SplitQuantifier verification copies; these
share source tokens but are distinct AST objects. Root cause is source-edit
traversal of verification copies, not a valid competing runtime source site.

Bounded correction: source-only expression traversal in InstrumentCalls and
StmtExpr proof erasure uses QuantifierExpr.PreResolveSubExpressions, retaining
resolved actual expressions but excluding split copies. Leave logical dependency
traversal unchanged. Add real ColumnTraceRelation/StepColumn-shaped regression,
first run before correction, then verify parsed quantifier/source wrapper mapping.
Native diagnostic overlaps frozen01 lane0 by explicit authorization; it is not
a final common-version performance comparison.

Owner checks for reopened h06 (cwd engine root, SDK8.0.131):
- `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter
  FullyQualifiedName~ColumnTraceQuantifierInstrumentsOriginalCallOnce`: first
  test compilation failed on a mistyped enum assertion, removed in favor of
  actual parsed call target assertion (`h06-quantifier-before.log`). Next attempt
  hit testhost loopback sandbox denial (`h06-quantifier-before-2.log`).
- Authorized local IPC `dotnet test Source/DafnyTestGeneration.Test --no-build
  -m:1 --filter FullyQualifiedName~ColumnTraceQuantifierInstrumentsOriginalCallOnce
  --logger 'console;verbosity=normal'` reproduced the same duplicate-wrapper
  overlap in the real source shape (`h06-quantifier-before-3.log`, 1 expected
  failure, 2.1124s).
- After correction, focused obligation suite initially failed a test assertion
  counting resolved quantifier copies; changed the assertion to inspect the
  original predicate conjunction's quantifier and its retained wrapper call,
  matching the source-edit distinction (`h06-quantifier-after.log`).
- `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter
  FullyQualifiedName~ContractRuntimeObligationTests --logger
  'console;verbosity=normal'` passed10/10 in2.3683s
  (`h06-quantifier-after-2.log`).
- Exact unchanged h06 launched in tmux `pbt-h06-quantifier-fixed`, from
  `/workspace/tmp/experiment`, script `owner-call-checks/check_h06_quantifier_fixed.py`;
  separate output `owner-call-checks/h06-quantifier-fixed`. At launch no other
  owner native check active. Parent frozen campaign contention remains recorded.

Final bounded validation after exact h06 finishes: `make format`,
`dotnet build Source/Dafny.sln --no-restore -m:1`, and
`dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter
'FullyQualifiedName~ChecksFunctionCallPrecondition|FullyQualifiedName~ExecutesGhostPostcondition|FullyQualifiedName~ChecksConjunctiveQuantifiedPostcondition|FullyQualifiedName~ChecksConjunctiveQuantifiedCalleePostcondition'
--logger 'console;verbosity=normal'`. These four existing cases check real function
precondition enforcement, ghost predicate execution, and original quantified goal
and callee contracts. No broad suite repeat.

### Reopened h06 stable handoff

Confirmed source-instrumentation fix complete. The source-only walker at
ContractRuntimeObligationTransformer.cs:265 keeps quantifier originals and
excludes verification splits only while creating source edits; logical/native
dependency traversal retains all prior behavior. The regression at
ContractRuntimeObligationTests.cs:92 reproduces the exact ColumnTraceRelation
shape and validates one wrapper plus the surviving quantified call. Arbitrary
competing replacements remain rejected with source/span diagnostics.

Exact original h06 post-fix: `owner-call-checks/h06-quantifier-fixed/run.json`
records request hash unchanged, process exit0, external timeout false, wall
246.75s. Result `violation_found`, generated64/executed64, valid3,
violatingSamples3, preconditionUnchecked47, calleeContractUnchecked14,
runtimeErrors0/timeouts0. All three reported goal-owned violations are original
call-precondition `width > 0` at FoldCore.dfy:221:29, ordinals7,9,12 with width0.
This local diagnostic had authorized possible frozen01 contention and is not a
final common-version timing comparison. Native original contracts/request
budgets were unchanged.

Final checks (commands above, logs in `owner-call-checks`):
- `make format` passed (`format-h06.log`, workspace-load warning only).
- Full solution build passed0warnings/0errors29.23s (`build-h06-final.log`).
- Four focused Driver checks passed4/4 in23.6652s (`driver-h06-final.log`).
- Earlier post-fix transformer suite passed10/10; same production/test source
  thereafter apart from formatting.
- `git diff --check` passed.

All owner native processes and document/source writes stopped at this handoff.
Parent owns independent verification, supported packaging/freeze02, and all
fifteen exact retained request runs for the final common-version table. This
reopened child remains in-progress pending that parent acceptance; no shared
wiki/index changes by this child. Durable addition for parent wiki: source
instrumentation must traverse quantifier originals, while verification split
copies sharing those token spans remain available to logical analysis.

Parent acceptance is complete. Corrective independent native10/Driver5 checks,
supported packaging02 and all15 unchanged frozen02 requests passed their required
gates; h06 remains violation_found with three valid violating samples. All seven
representative replays preserve exact violations, including h06 and the h13
sentinel. [Final report](../../../pbt-draft-exp/optimization-20261001.md) and
[independent final receipt](/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/final-artifact-acceptance.json)
close this bounded child. Shared durable findings and indexes are updated by root.
No child work remains; unsupported/type/unbounded-sequence limits stay explicit.
