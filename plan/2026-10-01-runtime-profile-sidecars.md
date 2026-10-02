# Runtime contract profiling sidecars

Status: done — bounded implementation and fresh independent checks complete

## Objective and authorization

Add bounded diagnostic profiling for the user-authorized PBT optimization and
fifteen fixed historical reruns. Attribute measured time and counts to runtime
contract evaluation, value/heap encoding, record serialization and flushed IO,
sample-process execution, and result classification without changing the raw
observation trace, assertion decisions, ordering, cancellation, or finite-prefix
evidence. Parent scope:
[call-state, fact reuse and profiling](2026-10-01-pbt-call-state-memo-profile.md).

This is engine maintenance for an authorized local retrospective. It does not
authorize a paid provider run, benchmark change, dependency, or statistical
speedup claim.

## Acceptance criteria and non-goals

- Write deterministic schema-versioned aggregate sidecars rather than adding
  timing fields to every observation record.
- Count and time completed actual runtime contract expressions separately from
  value/heap encoding, JSON record serialization, flushed record IO, sample
  process execution, and result classification.
- Preserve exact existing JSONL record contents and order, synchronous flushes,
  exception/cancellation behavior, sample verdicts, and finite-prefix evidence.
- Treat a runtime profile missing because a sample was killed as missing data,
  never as zero work. Parent process timing may still record the cancelled run.
- Use `Stopwatch` monotonic timestamps. Report instrumentation overhead and the
  inability to infer solver speed from these measurements as explicit limits.
- Do not edit the campaign runner or obligation transformer in this child scope;
  give exact integration hooks to their owner. Do not edit shared indexes/wiki.

## Inspected evidence and existing solutions

`ContractPhaseRecorder` already appends cumulative phase boundaries and preserves
terminal cancellation/failure states. `ContractRuntimeInstrumentation` emits one
JSONL record per runtime event under an output lock and flushes every completed
record. `ContractStubRuntime` owns typed observation and heap serialization.
`ContractRuntimeCampaignRunner` runs one process per sample, reads the complete
raw trace, then classifies samples. `ContractRuntimeObligationTransformer.Check`
currently evaluates the predicate and encoded fragments as arguments to
`PbtBridge.Check`, so bridge-only timing cannot separate them without two narrow
predicate boundary calls in the generated expression.

Engine started at revision `12065bbe8` with only the parent plan/index records
present; root and Cosyn have unrelated pre-existing changes. No source change was
present in the files owned by this child when inspected.

## Change table

| File or symbol | Change and necessity | Remaining gap without it | Validation |
| --- | --- | --- | --- |
| `ContractPhaseRecorder.cs`: new `ContractProfileRecorder` and schema records | Thread-safe count/tick aggregation, synchronous and async measurement, deterministic atomic snapshot | Campaign hooks have no shared profile schema or cancellation-safe aggregate | Unit tests for count, elapsed time, failed/cancelled measurement, deterministic replacement |
| `ContractStubRuntime.cs`: generated `ContractRuntimeProfile`; `SerializeNamed`, `Serialize`, `PrepareValues`, `RuntimeHeap` | Aggregate completed value/heap encoding with monotonic timestamps; expose bridge APIs for check/record metrics and sidecar flush | Runtime bridge cannot separate or persist low-overhead in-process costs | Generated-source assertions plus actual recording test if bounded lane permits |
| `ContractPhaseTimingTests.cs` and focused runtime recording test | Bug-triggerable sidecar schema, aggregation, exceptional completion, and raw trace conservation controls | Profile could silently count failed operations or mutate record shape/order | Focused native test filters below |
| Runner/transformer hook instructions to their owner | Add `campaign-profile.json`, measure `sample_process` and per-sample `result_classification`; wrap runtime predicates with begin/evaluated calls; flush `<sample>.jsonl.profile.json` | Process/classification and actual predicate costs remain conflated or absent | Owner tests plus independent verification |

All implementation files belong to the embedded Dafny engine. No specification,
proof, evaluator, dataset, scoring, benchmark, provider, or public wire result is
changed; profiles are diagnostic artifacts beside existing private run artifacts.

## Profile contract and compatibility

Sidecars use `{ schemaVersion: 1, clock: "Stopwatch", metrics: [...] }`. Each
metric is `{ name, count, elapsedMilliseconds }`, sorted ordinally by name.
Campaign names are `sample_process` and `result_classification`. Runtime names
are `actual_contract_check`, `value_encoding`, `record_encoding`, and
`record_io`. Counts include only completed measurements; an in-flight operation
terminated by process kill is absent. Atomic parent snapshots replace a temporary
file in the artifact directory. Runtime final snapshots are written after the
corresponding raw record has been flushed.

## Risks and approvals

Instrumentation adds timestamp, counter, and final JSON serialization overhead;
measured values describe instrumented runs only. `actual_contract_check` includes
the two boundary bridge calls but excludes later value-fragment encoding when the
owner applies the specified wrapper. Runtime `ProcessExit` may execute after an
explicit flush, so snapshot replacement must remain idempotent. Abrupt kill may
prevent a runtime snapshot. No new approval is required. The root coordinator
must grant the single native build/test lane before any compile, format, or test.

## Validation plan

From `/workspace/cosyn/dafny`, after the root grants the native lane:

- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --filter FullyQualifiedName~ContractPhaseTimingTests --logger "console;verbosity=minimal" -m:1`
- `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --filter FullyQualifiedName~ContractRuntimeRecordingTests --logger "console;verbosity=minimal" -m:1` if the actual bridge sidecar test is added
- The root-coordinated solution build and broader Contract filters from the
  parent plan; `make format` only in the same coordinated lane.
- `git diff --check` and a scoped diff review do not require the native lane.

Expected: focused tests preserve raw trace records and decisions while sidecars
contain positive counts and nonnegative elapsed values. These checks do not prove
solver improvement, benchmark performance, or statistical significance.

## Progress and handoff

Implementation is complete in the scoped helper, generated bridge source, and
focused tests. `ContractProfileRecorder` writes sorted atomic aggregate snapshots
and records time ending in normal return, failure, or cancellation. The generated
runtime profile is enabled only for runtime-reference bridges. Its value-encoding
timers surround outer public serialization/heap boundaries, so recursive encoding
does not double count. Actual contract checks count every completed nested check,
while elapsed ticks cover only the outermost active interval. This makes the
elapsed total a non-overlapping amount of instrumented check time rather than the
sum of inclusive nested durations.

The coordinated call-state owner applied the required non-owned hooks:

- runtime checks render `BeginCheck` before the original boolean expression and
  `Evaluated` immediately after it, before encoded value fragments;
- record JSON serialization and locked append/flush use separate profile metrics;
- completed/early-exit/error paths flush `<sample>.jsonl.profile.json` only after
  the corresponding raw record flush;
- records outside an active call retain the exact old JSON shape, while active
  call checks alone add `call_invocation`;
- the runner measures `sample_process` and each sample's
  `result_classification` in `campaign-profile.json` without changing the public
  campaign result model.

Coordinated validation used engine revision
`12065bbe85c4e20b9b5f8bb4b159f6394779fdb3`, .NET SDK `8.0.131`, and the .NET
8.0.31 test runtime. From `/workspace/cosyn/dafny`, the owner ran:

- `dotnet build Source/Dafny.sln --no-restore -m:1` twice; both passed. Logs:
  `/workspace/tmp/experiment/pbt-optimization-20261001/owner-call-checks/build-1.log`
  and `build-2.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter
  'FullyQualifiedName~ContractRuntime|FullyQualifiedName~ContractPhaseTimingTests'
  --logger 'console;verbosity=normal'`; 164/164 passed in 25.3591 seconds,
  including the aggregate profile recorder controls. Log:
  `/workspace/tmp/experiment/pbt-optimization-20261001/owner-call-checks/native-runtime-1.log`.
- The new `WritesAggregateRuntimeProfileSidecar` Driver control passed in 228 ms
  during the still-running combined `ContractRuntimeHeapTests`,
  `ContractRuntimeRecordingTests`, and `ContractRuntimePrefixTests` command. Its
  overall result remains pending in `driver-runtime-1.log`; the root coordinator
  will record the terminal result.
- Five new call controls passed in 32.325 seconds; log `call-controls-2.log` in
  the same owner directory. These call-state controls support the coordinated
  bridge integration but are not independent profiling verification.

`git diff --check` passed for all coordinated profiling/call-state sources,
tests, and this plan after the final profile test edit. The active Driver command,
a focused campaign-sidecar assertion, formatting, broader root-coordinated checks,
fresh independent verification, and the fifteen fixed reruns remain. No durable
finding is written to the wiki here: root owns final knowledge after independent
verification and fixed-run evidence. Profiles measure instrumented wall time and
must not be reported as solver speed or causal performance improvement.

Fresh independent acceptance (requirements-only context/current source): native
49/49, Driver16/16 and artifact13/13 pass. Formal receipt:
`/workspace/tmp/experiment/pbt-optimization-20261001/independent-final/engine-acceptance.json`,
SHA-256 `d58ba07d8bf03a23c0c96611d18bd13e7ce797e4579d06d21e0b952ade88dbbc`.
Supported final package and Cosyn integration4/4 pass. Source is frozen; all15
historical outcomes and replays remain tracked by the root plan. Durable findings:
[invocation-bound heaps, facts and profiles](../wiki/contract-testing.md#invocation-bound-callee-heaps-fact-reuse-and-profiles-2026-10-01).
No pending code or native check remains within this bounded child scope.
