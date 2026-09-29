# Ordered runtime check fragments

Status: done (owner work complete; fresh independent review accepted Driver 22/22 and the raw artifact audit)

Parent: [sequential contract optimization](2026-09-29-sequential-contract-optimization.md).
This is bounded Dafny engine maintenance against retained public h11 artifacts,
not an evaluated or provider-backed run. Root registered this read-only design
in the shared index; registration does not open the implementation gate.
Root owns shared index/wiki updates.

## Objective and observable acceptance

Change only runtime `Check` and `Checkpoint` value transport from a single
concatenated JSON `string` to an ordered `seq<string>` of `SerializeNamed`
fragments. Avoid constructing and decoding the whole values Rune string and
avoid reparsing internally produced fragments, while preserving the exact
ordered JSONL records, checks, termination, newline, and per-record flushes.

Acceptance requires all of the following:

- `ContractRuntimeObligationTransformer.Check` emits `[]` or an ordered sequence
  literal of the existing `SerializeNamed` expressions. Its existing `Encode`
  and `SerializeValues` paths remain unchanged for `InputValues`, receiver/input
  capture, and heap output capture.
- `ContractRuntimeInstrumentation.DafnySource` and `RuntimeSource` expose matching
  `seq<string>` / `ISequence<ISequence<Rune>>` signatures only for `Check` and
  `Checkpoint`; the test and retained h11 executables use that actual route.
- Every `SerializeNamed` result is associated by exact Rune-sequence object
  identity with its complete already encoded object `JsonElement`: the primary
  named value followed by every ordered flat property added by `AddRuntimeFields`.
  The association is weak and is cleared by `Register` alongside the current
  immutable caches. It does not authorize cross-call value reuse.
- The existing `immutableNamedEncodings` remains the sole cross-call fragment
  reuse gate: same value identity, exact label, exact complete shape, and a fully
  established recursively immutable graph. Arrays, heap/class references, and
  externally implemented mutable collections are encoded freshly.
- An ordered-values factory resolves every association before `Write`. If any
  fragment lacks an identity association, the factory reconstructs the complete
  legacy object text (`{` plus all decoded fragments joined by commas plus `}`)
  and parses it with `JsonDocument` before constructing the outer record. The
  converter receives only validated object elements and writes every property in
  fragment and property order, including duplicate labels. This fail-closed
  fallback preserves the legacy parse-before-`Write` exception boundary,
  validation, duplicate-label ordering, and Unicode handling.
- `Check` still writes before testing a failed call-precondition id, then calls
  `Complete` and exits. Nested checks and validity/precondition evaluation are
  never cached or skipped. `Write` still serializes the complete outer record in
  memory before taking its lock, appends one newline, and flushes every record.
- Exact output bytes match the current route for empty, one-property,
  multi-property, Unicode-label/value, and duplicate-label objects. Registration,
  malformed external fragments, mutable values, cancellation, and post-complete
  error behavior remain unchanged.
- A paired retained h11 runtime-only measurement uses the exact original seed
  `3454598619081119827`, ordinals 0 and 1, the original five-second limit, and
  three alternating old/new pairs per ordinal. Every overlapping complete record
  in each pair is byte-identical and ordered. Completion is reported as observed;
  this work makes no promise that h11 completes.

No benchmark source, request, generator, draft, seed, budget, contract, proof,
evaluator, scoring, provider, dependency, or package change is in scope. Do not
cache booleans, suppress records, weaken nested checks, alter `InputValues` or
heap behavior, add a legacy overload and claim it exercises the new route, or
commit changes.

## Inspected evidence and existing mechanisms

The accepted read-only design is
`/workspace/tmp/experiment/pbt-sequential-20260929/runtime-design.md` (SHA-256
`da14c564e57e2e5dd95d71eeccde7042dd5338077c5d5ee6af0ad760c8354544`).
The production baseline manifest is
`/workspace/tmp/experiment/pbt-sequential-20260929/runtime-baseline-production/manifest.json`
(SHA-256 `0ffbe4abdc28145ca7b491e8c58c61244f87758b5ae26ab43ad0bf967a35104d`).
Its two hashes exactly match the inspected current production files:

- `ContractStubRuntime.cs`:
  `4072d3c600d12867e0f95281f3db8e63da1529f89817bc4cc0fa64d539a81842`.
- `ContractRuntimeInstrumentation.cs`:
  `fcc19e03fe89201ada61ba025f1178b0d8771c2fbf4aa75f20bbe7adcdefd4e8`.

Current `ContractRuntimeObligationTransformer.Encode` creates `{`/`,`/`}` Rune
concatenations for checks as well as input/heap captures. Current runtime checks
decode the complete Rune sequence, parse the whole values object, place its root
in an anonymous outer record, serialize, append a newline, and flush. The runtime
already has exact shape parsing, recursive immutability classification,
`immutableNamedEncodings`, registration invalidation, and a concrete/external
Rune conversion boundary. Reuse those mechanisms rather than adding another
value cache.

`Dafny.Sequence<T>.FromElements` copies the element references into its immutable
array representation, so a generated `seq<string>` retains each returned
`SerializeNamed` Rune-sequence identity. Repeated content is not identity and is
not evidence of saved work.

Existing focused controls are in
`ContractRuntimeRecordingTests`, `ContractRuntimeObservationTests`,
`ContractRuntimeCheckTests`, and `ContractRuntimePrefixTests`. They already cover
mutable array/class/external-container observations, generic full-shape changes,
Unicode labels and scalar decoding, registration invalidation, early exit,
per-record cancellation visibility, post-complete errors, nested campaign checks,
and prefix classification. Extend the recording fixture for structured fragments
and exact bytes; reuse the remaining suites without broad unrelated edits.

Prior `bridge-replay-v5` is baseline context only. In five seconds its old/current
arms produced 15,795/48,874 records for ordinal 0 and 15,979/52,111 for ordinal 1,
with exact common prefixes; those arms include earlier optimizations and do not
measure this transport change. The read-only trace analysis counts 48,844 and
52,081 check/checkpoint records, 50,389 and 53,696 properties, and 113 and 89
distinct payload texts. No throughput or completion claim transfers to this work.

The inspected engine revision is
`060d5ad532f67d5367450689225274fb0a0243e7`, with substantial pre-existing dirty
work in all three planned production files and the focused tests. Preserve it;
never reset, replace, or clean another task's edits.

## Design and exact change table

| Owner / exact file or symbol | Planned change and why it is necessary | Validation |
| --- | --- | --- |
| Dafny engine: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs`, `Check`, new `EncodeFragments` | Use `EncodeFragments(encodedValues)` only for generated `Check`/`Checkpoint`, producing `[]` or `[fragment0, ...]` in the existing order. Leave `Encode` and `SerializeValues` byte-for-byte behavior for inputs and heap captures. Without this, generated programs still create whole-object ConcatSequence trees. | Generated campaign compilation plus observation/check tests; diff confirms the two call sites are the only consumers changed. |
| Dafny engine: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeInstrumentation.cs`, `DafnySource`, `RuntimeSource.Bridge.Check/Checkpoint` | Change matching value parameters to ordered fragment sequences. Resolve them through the new parse-before-`Write` ordered-values factory, then pass its converter-backed value at the existing `Write` calls; retain record fields, failed-precondition `Complete`/exit, `Write`, newline, locking, and flush order. | Focused compilation and exact recording bytes/errors; nested failed-precondition and cancellation controls. |
| Dafny engine: `Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs`, `SerializeNamed`, `Register`, new private fragment payload/factory/wrapper/converter | Serialize the complete ordered named-values dictionary once to a detached object `JsonElement`, including the primary property and every flat property produced by `AddRuntimeFields`; derive the returned fragment text from that object and weakly associate the returned Rune object with the entire element. On immutable cache hits, return the same associated Rune object. Before outer serialization, the factory either resolves all associated objects or parses the complete reconstructed legacy object on any miss; the converter only emits validated elements and every property in order. Clear associations at registration. This removes the internal whole-object conversion while retaining strict external semantics and exact malformed-input exception behavior. | Empty/one/many/flat-field/Unicode/duplicate exact bytes; identity/label/shape, mutable, registration, and malformed fallback controls. |
| Dafny tests: `Source/DafnyDriver.Test/ContractRuntimeRecordingTests.cs`, production-bridge fixture and focused cases | Convert direct fixture calls to the structured signature and add observable controls: exact bytes for empty/one/many/Unicode/duplicates; valid unknown fragments; malformed unknown/mixed fragments produce only the same runtime error path; same immutable identity with same label/full shape, different label/shape, mutable array, externally mutable collection, class reference, and registration invalidation; failed call precondition records then `Complete`/exit; existing cancellation and post-complete cases remain. | Focused Driver filter; each test keeps one scenario and its intention comment. |
| Existing tests, no planned edits: `ContractRuntimeObservationTests.cs`, `ContractRuntimeCheckTests.cs`, `ContractRuntimePrefixTests.cs`; `ContractRuntimeObligationTests.cs` | Re-run actual transformed/campaign behavior so structured code generation, nested preconditions, full observation decoding, record order, and finite-prefix semantics remain covered. | Focused Driver and TestGeneration filters below. |
| Measurement artifact only: `/workspace/tmp/experiment/pbt-sequential-20260929/runtime/bridge_replay.py` plus immutable attempt directories under the same `runtime/` collector path | Adapt the retained `/workspace/tmp/experiment/pbt-inconclusive-20260929/runtime/bridge_replay.py`, use the `bridge-replay-v5/new` generated program as the frozen base, and render old/new bridge templates from `runtime-baseline-production`. Build outside timed samples, alternate arms, retain all attempts, and emit manifests/receipts/comparisons. | Hash/diff assertions, successful builds, twelve timed samples, metrics and byte comparisons below. |
| This child plan only | Record implementation hashes, exact commands, outcomes, failures, limitations, and final handoff after `START`. | Plan diff and status review. No shared index/wiki edit by this owner. |

Implementation stays in the runtime code-generation/recording layer. It does not
alter specifications, proof decisions, evaluator behavior, datasets, scoring, or
reports. No generated Dafny runtime file is edited.

## Test controls and semantic risks

The ordered-values factory must resolve every fragment identity before `Write`.
Otherwise discovering an unknown or malformed later fragment inside
`JsonConverter.Write` could change exception wrapping or leave a partially
serialized outer record, unlike the current pre-`Write` parse. On any miss the
factory decodes all fragments and parses the complete reconstructed object before
the outer anonymous object is constructed. The converter only receives validated
object elements. This preserves unusual external fragments containing multiple
or duplicate properties under the legacy comma-join grammar and keeps malformed
external runtime-error messages at the legacy parse-before-serialization boundary.

The weak association may cover freshly encoded mutable fragments because it
describes that already materialized complete fragment object only. It must never
be used to find a later fragment by value/content. The converter must enumerate
all properties in each associated object so `AddRuntimeFields` output is neither
collapsed nor skipped. Only `immutableNamedEncodings` may return a prior fragment
for a later call, under its existing exact identity, label, full-shape,
recursive-immutability, and reference-registration gates.

Exact-byte tests inspect complete JSONL lines, not only parsed JSON. Include an
object with two identical property labels and assert both remain in order. Include
BMP and non-BMP text in names and values. A malformed unknown fragment and a
mixed associated/unknown malformed sequence must fail before a partial check line
is appended. The nested failed-precondition control must retain its check record,
then `complete`, then process exit without the enclosing check or unreachable
body. Existing tests continue to prove a flushed record survives parent kill and
an unhandled error can follow `complete`.

No test may assert an implementation-only cache count as the semantic result.
Identity controls may expose `ReferenceEquals` from the fixture to establish the
precondition for the direct path, but output bytes and process behavior remain the
acceptance evidence.

## Root-coordinated validation after explicit start

All native build/test work requires the root-exclusive lane. Run it in tmux,
launched from `/workspace/tmp/experiment`, with `TMPDIR=/workspace/tmp`; test cwd
is `/workspace/cosyn/dafny`. Record tmux session, exact command, engine revision,
dirty state, source hashes, .NET version, exit status, duration, and complete logs.
Do not run concurrently with stage3a or its independent verifier.

Planned local commands after implementation:

```bash
dotnet build Source/Dafny.sln --no-restore -m:1

dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj \
  --no-build --no-restore -m:1 \
  --filter 'FullyQualifiedName~ContractRuntimeObligationTests' \
  --logger 'console;verbosity=normal'

dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj \
  --no-build --no-restore -m:1 \
  --filter 'FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractRuntimeObservationTests|FullyQualifiedName~ContractRuntimeCheckTests|FullyQualifiedName~ContractRuntimePrefixTests' \
  --logger 'console;verbosity=normal'
```

Expected: build has zero errors; every selected test passes with no skipped case;
the new tests demonstrate exact bytes and strict failures. Run `git diff --check`
and inspect diffs only for the planned files. Root owns final `make format`, the
supported Cosyn `make build-dafny`, transport integration checks, combined source
freeze, and a fresh independent verifier starting from requirements and current
repository state.

## Retained h11 measurement protocol

Measurement begins only after native semantic checks pass and the root grants the
serialized experiment lane. The runner creates a new immutable attempt directory
for every prepare/run failure; it never overwrites `bridge-replay-v5` or a prior
attempt. It records provider/authentication as none.

The old arm uses the two exact files named by
`runtime-baseline-production/manifest.json`. The new arm snapshots the accepted
three production files. Both arms use the same retained
`bridge-replay-v5/new/diagnostic.cs`, project inputs, packages, seed, ordinal, and
timeout except for the necessary executable Check/Checkpoint argument form in the
new arm.

The new generated-program rewrite is fail-closed and auditable:

1. Preserve the complete leading `DafnyAssembly.DafnySourceAttribute` region
   byte-for-byte, including its large quoted historical source. Record its slice
   hash before and after.
2. Scan only the executable C# suffix with balanced delimiter and string-literal
   awareness. Rewrite every and only `DafnyPbtBridgeRuntime.Bridge.Check` fourth
   argument and `Checkpoint` third argument. Accept only the generated empty
   `UnicodeFromString("{}")` form or the exact `{` + ordered `SerializeNamed`
   leaves separated by commas + `}` ConcatSequence form. Convert these to
   `Sequence<ISequence<Rune>>.Empty` or `FromElements(leaves...)`, preserving
   each leaf expression and evaluation order byte-for-byte. Abort on any other
   payload form, unmatched call, or changed non-call suffix span.
3. Assert the frozen base counts (682 actual qualified `Check` invocations and
   268 `Checkpoint` invocations) and record empty, nonempty, fragment, and
   rewritten-call counts. The earlier read-only value 649 counted physical lines;
   33 additional `Check` invocations share those lines (including one line with
   three calls), so it is not the rewrite target count. Emit an executable-only unified
   diff plus a machine-readable span manifest proving that the metadata region and
   every non-argument span are identical. Do not retain a legacy string overload
   in the new bridge.

Preparation requires a fresh nonexisting attempt directory. Execution requires
that prepared directory and exclusively creates its run-start marker before
building; it refuses a previously started or completed directory. This prevents
build/log overwrite and JSONL append contamination. Build old and new projects serially before timed work. The fixed twelve-sample
schedule has three paired repetitions per ordinal and alternates which arm runs
first within successive pairs, with the schedule written into the manifest before
execution. Each sample receives exactly five seconds and runs in its own process
group. Capture wall time with a monotonic clock and child user/system CPU deltas,
plus exit code, timeout/cancellation, output bytes, complete newline-terminated
record count, partial-tail bytes, complete-trace SHA-256, record-kind histogram,
and presence/position of `complete`.

For every old/new pair, compare the first `min(oldCompleteRecords,
newCompleteRecords)` complete records as raw bytes and report the first mismatch
index or exact equality. Also report paired counts and timings without discarding
timeouts, failed builds, partial tails, or slower repetitions. Results establish
only this frozen two-ordinal runtime transport behavior; they do not establish a
campaign verdict, proof result, general speedup, or h11 completion.

## Gate, documentation, and handoff

The root recorded independent stage3a acceptance and sent explicit `START`. This
child now owns the exclusive native/source lane through owner controls and paired
h11 measurement. Preserve the authorized scope and release the lane explicitly
after freezing stable source hashes and artifacts for fresh independent review.

After implementation, keep this plan `in-progress` until owner checks, measurement,
diff review, and independent verification are accurately recorded. Root decides
whether the existing `wiki/contract-testing.md` needs a durable update; this child
does not write shared wiki/index files. If no durable finding survives measurement,
record `No durable findings` here with the reason. No completion claim may be made
from process exit alone or from a larger partial trace.

## Implemented result and source freeze

The implementation follows the design above. `EncodeFragments` now changes only
the generated Check/Checkpoint arguments. `SerializeNamed` materializes the whole
ordered object (including every `AddRuntimeFields` property) and weakly associates
that element with the returned Rune sequence. `PrepareValues` resolves all weak
associations before `Write`; any miss reconstructs and parses the complete legacy
object. The converter writes every property of every validated fragment in order.
The existing immutable cache remains the only cross-call reuse mechanism and
`Register` clears the weak associations along with that cache.

The stable source freeze is
`/workspace/tmp/experiment/pbt-sequential-20260929/runtime/source-freeze.json`.
No source changed after it was announced to the independent reviewer:

- `ContractStubRuntime.cs`:
  `75973b74e0f5c50dbe11e7312061cebae71de3d8a281334f72cee5ac89a50fdf`.
- `ContractRuntimeInstrumentation.cs`:
  `bc01a6e28367156daeb9a57f1354b59acca209f0645233ef9f5034f7872cb563`.
- `ContractRuntimeObligationTransformer.cs`:
  `624bde401281592e6d4f41a903579e3c86f5b42e8aa3e80893c050a0b473d928`.
- `ContractRuntimeRecordingTests.cs`:
  `f4220231143bbaafa4b54173570d93658914a141ad6d0cb500eb81548d8947e7`.

The focused recording fixture covers empty, one-property, many-property,
Unicode, duplicate-name, valid unknown, malformed unknown, mixed known/malformed,
identity/cache boundaries, mutable values, registration, nested failed
preconditions, cancellation, and post-complete behavior. The exact legacy mixed
malformed text is 50 UTF-8 bytes and reports invalid `}` at byte position 49;
the initial expected position 10 belonged only to the standalone malformed text.
The failed broad run is retained rather than hidden.

## Owner validation record

Owner controls ran in the exclusive native lane from
`/workspace/tmp/experiment` with `TMPDIR=/workspace/tmp`, .NET SDK `8.0.419`,
engine revision `060d5ad532f67d5367450689225274fb0a0243e7`, and recorded dirty state.
The first control used tmux `pbt-runtime-owner2-20260929` and artifacts
`runtime/owner-controls-1`; the second used
`pbt-runtime-recording2-20260929` and `runtime/owner-controls-2`.

- `dotnet build Source/Dafny.sln --no-restore -m:1` passed with zero warnings
  and zero errors in 22.64 seconds.
- The planned TestGeneration filter passed 7/7 in 2.4274 seconds.
- The planned broad Driver filter ran all 161 tests in 10.6486 minutes: 160
  passed and the sole failure was the incorrect mixed-fragment expected byte
  position described above. The complete failed log and exit 1 remain retained.
- After correcting only that fixture expectation, the Driver project build
  passed with zero warnings/errors in 7.02 seconds and the complete Recording
  family passed 21/21 in 12.5717 seconds.
- `git diff --check` passed. Source hashes taken after the correction match the
  freeze above.

The root owns broader formatting/integration checks and fresh independent
verification. The owner does not reinterpret the broad run as 161/161; the
affected complete Recording family rerun is the evidence for the fixture-only
correction.

## Paired retained-runtime result

The first fresh preparation directory, `runtime/paired-1`, failed before build
or measurement because the initial scanner treated a comma in a C# generic type
argument as an outer Check argument separator. `paired-1/failure.json` preserves
the exact failure. The fixed scanner uses balanced call boundaries and accepts
only a final exact legacy payload expression. The successful fresh attempt is
`runtime/paired-2`; its POSIX-sh wrapper is `runtime/run-paired-2.sh`, its tmux
session was `pbt-runtime-paired2-20260929`, and `runner.exit` is 0.

Preparation rewrote exactly 682 Check and 268 Checkpoint calls (950 total) into
1,000 ordered fragments. It retained 252 empty and 16 nonempty checkpoints and
682 nonempty checks. The complete leading metadata hash is
`3277fbc33b8678db0c88e495df2db452615200d833fc0fa4e92295e100bf1e8a`
both before and after. The retained diagnostic hash is
`54d3ba8b31264c7b1b203eeaed3dea1babc05733941b2cf2b3e7b76aedbc3dd4`.
The runner hash frozen before execution is
`ac9c281629b845d4c95ab79bc4ea29649e0ba4ac40cd1fb4e3194eba8aa05c9b`.
Old and new project builds passed before the clocked samples in 14.006 and
13.402 seconds respectively.

All twelve exact-seed samples are retained in `paired-2/receipt.json`, including
per-sample wall/user/system time, bytes, complete records, partial-tail bytes,
trace and assembly hashes, kind histograms, exit/timeout state, and `complete`
positions. Their grouped means are:

| Ordinal / arm | Mean wall s | Mean user s | Mean system s | Mean bytes | Mean complete records | Observed termination |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 0 / old | 5.0085 | 5.7191 | 0.2371 | 65,154,074.7 | 48,810.7 | 3/3 timeout, exit -9, no `complete` |
| 0 / new | 3.4748 | 4.0798 | 0.2681 | 73,586,677 | 54,671 | 3/3 exit 0, `complete` at record 54,670 |
| 1 / old | 5.0086 | 5.5966 | 0.2591 | 68,718,581 | 51,783 | 3/3 timeout, exit -9, no `complete` |
| 1 / new | 4.1936 | 4.7608 | 0.3130 | 98,979,345 | 73,915 | 3/3 exit 0, `complete` at record 73,914 |

Every trace ended on a complete newline-terminated record, so all partial-tail
counts were zero. The exact overlapping raw complete-record comparisons were:

| Ordinal | Repetition | Equal records | Equal bytes | First mismatch |
| ---: | ---: | ---: | ---: | --- |
| 0 | 0 | 48,200 | 64,440,434 | none |
| 0 | 1 | 47,520 | 63,362,169 | none |
| 0 | 2 | 50,712 | 67,659,621 | none |
| 1 | 0 | 53,280 | 70,694,017 | none |
| 1 | 1 | 48,729 | 64,671,204 | none |
| 1 | 2 | 53,340 | 70,790,522 | none |

Thus this exact retained program, seed, two ordinals, and six alternating pairs
show byte-identical overlapping record prefixes and observed completion only for
the new arm. These results do not establish a broader h11, proof, campaign, or
general performance verdict. The native lane was explicitly released after the
measurement ended. The reusable transport behavior and bounded measurement are
handed to the root for its existing wiki decision; this child makes no shared
wiki or index edit.

## Independent acceptance and final package check

Fresh review accepted the frozen four-file change. Its predeclared focused Driver
filter passed22/22 in17.9832s; source before/after, diff and overall checks exit0.
The separate raw audit verified950 edits, unchanged source metadata and every
non-argument span, both builds, all12 traces and all6 exact overlapping prefixes.
Evidence: `pbt-sequential-20260929/independent-runtime/decision.md` and
`artifact-audit-01/summary.json`. No unresolved correctness/provenance finding.
The engine reusable findings are in [contract testing](../wiki/contract-testing.md#ordered-runtime-check-fragments-2026-09-29).

Root final `make format` exits0 with a workspace-loading warning and changes
zero of1087 inspected C# sources. `make build-dafny` passes with0warnings/0errors
in28.57s; Cosyn transport integration passes4/4 in23.09s. These checks do not
establish historical campaign outcomes; root's unchanged six-case runs follow.

## Status reconciliation (2026-09-29)

The status line now matches the recorded independent acceptance above and the
engine plan index; no new work was performed.
