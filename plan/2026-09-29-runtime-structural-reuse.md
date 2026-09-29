# Reuse immutable runtime preparation and encoding metadata

Status: done (bounded implementation and validation; broader coverage limits remain)

Parent: [inconclusive optimization](2026-09-29-inconclusive-runtime-optimization.md).
This is engine maintenance against authorized retained h11 artifacts, not a paid
or isolated evaluated run. Preserve all existing dirty changes and original
requests, samples, budgets, obligations, records, dependency checks and flushes.

## Evidence and acceptance

h11 optimized-v2 transformation takes 52.77 seconds before 11.82 seconds of
resolution and 27.27 seconds of compilation. Each unnamed function descriptor
rescans the whole resolved program through ContractBodyNames.Family. Its sources
contain 322 call-site function wrappers and 15 specification wrappers. Samples
emit about 19 MB / 14,500 records in five seconds while evaluating filesystem
membership and the first two IsDirectoryStrict contracts, before backup logic.
Encode repeatedly scans datatype JSON metadata and reflects the same CLR types.

Acceptance: preserve collision-safe descriptor names and check identities; reuse
only immutable metadata, never mutable observed values; preserve exact observation
bytes and generic shape distinctions; demonstrate timings on the unchanged h11
request. Preparation ownership stays local to one transformer and its fixed AST.
No global AST cache, new packages, behavioral heuristics or source contract edits.

## Change table

| Exact files/symbols | Change, reason and unmet behavior without it | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs, DescribeFunction/FunctionResultName | Accept a precomputed collision-safe family for unnamed results | Descriptor/result-clause identity and collision controls |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs, descriptor construction | Compute the family once per transformer; reuse descriptors only where identity/state semantics permit | Transformed source equality, native obligation tests |
| Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs, Encode metadata lookup | Index datatype metadata and cache CLR interface/field reflection by exact closed CLR type; values remain freshly encoded | Datatype/generic/collection/mutable reference observations |
| Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs, Encode/EncodeValue and immutable-graph classification | After measured metadata-only improvement is insufficient, reuse exact serialized structural encodings by object identity and complete shape only for recursively immutable graphs of known concrete Dafny collections/read-only datatype fields; reject graphs containing heap references, arrays or external collection implementations | Same harness/seed/5s replay, exact ordered bytes, changed values and shapes, mutable external sequence/class/array controls |
| Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs, SerializeNamed | After v3 still times out, reuse complete named Rune fragments only for the same proven immutable graph, exact complete shape and exact label; invalidate with explicit reference registration | Existing mutable graph/registration controls plus Unicode label separation and exact replay prefixes |
| Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs, Text; ContractRuntimeInstrumentation.cs, Bridge.Text | Avoid one temporary string per BMP Rune when decoding trusted concrete Dafny strings; retain arbitrary external ISequence fallback and original invalid/non-BMP handling | Existing Unicode/parser controls, exact code point conversion and malformed-scalar errors, faithful dual-production-template replay |
| Source/DafnyTestGeneration.Test/ContractRuntimePreparationReuseTests.cs | Add independent collision/result identity controls | Focused native test filter |
| Source/DafnyDriver.Test/ContractRuntimeRecordingTests.cs | Exercise repeated datatype and map metadata with changing values and generic shapes | Exact bytes plus existing cancellation/flush controls |
| This plan | Record findings, commands, outcomes and next steps | Final diff review |
| /workspace/tmp/experiment/pbt-inconclusive-20260929/runtime/ | Preserve before/after h11 receipts and byte comparisons | Same request hash, seed, limits; serial tmux run |
| /workspace/tmp/experiment/pbt-inconclusive-20260929/runtime/bridge_replay.py | Reproduce old/new production bridge templates over byte-identical retained h11 diagnostic.cs, copy project locally, compile serially and run ordinals 0/1 with five-second limits | Assert baseline template reconstruction, bridge-only patch, ordered complete-record prefix byte equality |
| /workspace/tmp/experiment/pbt-inconclusive-20260929/runtime/h11-campaign-diagnosis.md | Root-authorized read-only analysis of final frozen h11 campaign preparation, all sample frontiers and remaining runtime/classification costs | Read final result, phase receipts, unchanged request and generated source; no new native execution or implementation |

All changes belong to the Dafny engine implementation/testing layer, not evaluator,
dataset, proof contracts or scoring. Parent/root owner updates indexes and wiki.

## Validation commands and risks

Native lane is coordinated by root; no concurrent build/test execution. Cwd
`/workspace/cosyn/dafny`, TMPDIR `/workspace/tmp`:
`dotnet build Source/Dafny.sln --no-restore -m:1`; then
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter
'FullyQualifiedName~ContractRuntimePreparationReuseTests|FullyQualifiedName~ContractRuntimeObligationTests|FullyQualifiedName~ContractEntryTests'`
and `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter
'FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractRuntimeObservationTests'`.
Root coordinates formatting, packaging and fresh independent verification.
After adding the reference-registration regression, rebuild
`dotnet build Source/DafnyDriver.Test --no-restore -m:1` and run the recording
filter again to include that new control.
Historical runtime probes run in tmux from `/workspace/tmp/experiment`, with no
provider/authentication and original h11 seed 3454598619081119827 and request.
Record every attempt, baseline/follow-up hashes, commands and elapsed timings.

Reflection must distinguish closed generic types; metadata sharing must not freeze
array/heap fields or suppress malformed-shape failures. Timings may reveal further
contract-computation cost; no speed or conclusive-result claim before measurement.

## Owner validation and handoff

Implemented local lazy result-family reuse while retaining fresh descriptors and
output variables per call site. Runtime reuse indexes immutable datatype shapes
and caches interface/field reflection by exact closed CLR type. No observed value,
record, snapshot or mutable class/array contents are cached.

2026-09-29 owner checks ran serially from the engine root, TMPDIR
`/workspace/tmp`, in tmux sessions `pbt-runtime-owner-tests-20260929` and
`pbt-runtime-recording-tests-20260929`, against the preceding coordinated native
build. Preparation/obligation/entry filter: 38 passed, zero failures/skips (6 s).
Recording/observation filter: 16 passed, zero failures/skips (29 s). Both exited
zero. Logs and exit receipts are under
`/workspace/tmp/experiment/pbt-inconclusive-20260929/runtime/`. Production-file
`git diff --check` passed. The test runs used `--no-build --no-restore -m:1`.

The concurrent query owner subsequently changed sources; these are local test
receipts, not a claim that the present whole source tree matches those binaries.
Runtime source identities and retained v2 source hashes are in `source-ready.json`
(one later explanatory comment is not reflected in that initial receipt). Full
h11 speed/trace comparison, supported final build, formatting and fresh independent
verification remain pending under root's coordinated combined freeze. Native lane
was returned to the query owner after both test processes exited.

Further read-only finding: concrete Dafny maps/sets use readonly immutable backing
stores and ArraySequence copies arrays; generated datatype fields are readonly.
This alone does not authorize caching arbitrary values because their interface
fields may contain externally implemented mutable containers. Exact concrete
container validation plus complete shape identity and fresh heap expansion would
be required before any future structural-value cache. Root owns durable wiki
updates; no wiki page was written by this slice.

### Measured metadata-only baseline and authorized next step

`bridge-replay-v1` reconstructs the baseline generated bridge exactly from its
frozen production template (asserted), relocates only the legacy output path,
and applies the current production template over byte-identical diagnostic.cs.
Both projects compiled successfully (13.71/12.66 s). In tmux
`pbt-h11-bridge-replay-v1` from `/workspace/tmp/experiment`, seed
3454598619081119827 and original ordinals 0/1 each received five seconds.
Old traces contain 14,915/14,833 complete records; new traces contain
22,654/22,698 (1.52/1.53 times throughput). All overlapping complete-record bytes
match exactly in order. All four executions timed out, none completed. The run
is runtime-only evidence, not a campaign result or preparation speed measurement.
Manifest, bridge-only patch, source/binary hashes and receipts are retained in
`runtime/bridge-replay-v1/`; no baseline artifact was changed.

Root authorized a second bounded optimization because this improvement is
insufficient: exact structural encoding reuse. Reuse excludes arbitrary
ISequence/IMap/ISet implementations and every graph containing a class or array;
known concrete collections and readonly datatype fields must establish recursive
immutability. Cache keys use reference identity plus the entire serialized shape,
entries are installed only after successful encoding, and keys are weakly held.
Reference identity takes priority over structural caches; explicit registration
invalidates structural entries because registration itself changes encoding identity.
Serialized immutable values may be reused, but every check, record, current heap
expansion and flush still executes. This scope supersedes the earlier metadata-only
implementation statement, not its prior validation receipts.

Structural encoding v3 builds succeeded and preserves all overlapping trace bytes.
Old ordinals0/1 emit14,576/13,422 complete records; new emits28,312/29,112 in5s,
still timing out. Owner solution build had0warnings/errors; recording/observation
19/19 and registration-focused13/13 passed. Exact JSON reuse alone leaves
SerializeNamed reserializing immutable JSON and rebuilding Rune arrays on every
record. Extend the same proven immutable graph boundary to named fragments;
key additionally by exact label and still parse/validate supplied shape before
lookup. Repeated composite serialization with changed generic widths and labels
must remain distinct. This does not cache any mutable heap field expansion.

Named fragment v4 recording controls14/14 pass. Runtime emits41,068/41,043records
under5s, all overlapping baseline records byte-identical, but still times out.
It reaches RenameEffect preconditions at records36,459/36,460. The next source-
backed hotspot is Sequence.ToVerbatimString(false): one char.ConvertFromUtf32
string allocation for every Rune, including ASCII JSON. Root explicitly approved
bridge-local Text ownership. Direct StringBuilder.Append(char) for valid BMP
scalars removes those allocations; non-BMP and invalid scalars still use the
original conversion. Restrict the fast path to known concrete runtime string
implementations and fall back to external ISequence.ToVerbatimString unchanged.
No JSON parser, record, flush, obligation or request changes are included.
Text controls include array/concatenation strings containing NUL, controls,
U+D7FF/U+E000/U+FFFF/U+10000/U+10FFFF and a custom ISequence DispatchProxy that
must retain its own conversion. The replay runner now reconstructs both retained
production templates exactly (StubRuntime and Instrumentation), snapshots both
new templates and records its own hash before compilation. Root takes its prefix
red-test lane before this source-ready stage's native checks.

## Final bounded owner result

Owner implementation is stable and handed back to root. Latest targeted Driver
build passed and recording controls16/16 passed (3 s) in
`pbt-runtime-text-tests-20260929`; logs are `text-build.log` and `text-tests.log`.
Native lane is released. Source identities and tested engine revision are in
`runtime/owner-final.json`. Production-file `git diff --check` passes. No commits,
packages, provider calls, request/generator/specification edits or wiki writes
were made by this slice; root owns shared indexes and durable knowledge.

Final runtime-only probe `bridge-replay-v5`, tmux `pbt-h11-bridge-replay-v5`,
retains original diagnostic.cs byte-for-byte, original seed/ordinals0/1 and5s
limits. Old traces contain15,795/15,979 complete records; new traces contain
48,874/52,111 (3.09/3.26 times the paired baseline record counts). The new traces
contain65,220,479/68,999,643 bytes. Every overlapping complete-record byte matches
in order. All four processes still timed out, and neither optimized sample
completed. These are throughput measurements for two fixed samples, not an
aggregate statistical conclusion, complete-trace equality, proof or campaign
verdict. Earlier failed/partial probes and unexecuted source snapshots are kept.

Remaining parent work: fresh independent verification, supported integrated
build/format/package, preparation-time measurement and unchanged six-case
campaigns. The current child record stays in progress because those acceptance
checks are pending. No further generic optimization is authorized for this
slice absent an observed concrete campaign blocker. The next concrete action is
root's independent review/integrated campaign; h11's remaining runtime limit must
remain explicit if it persists. Root may close this record only after accepting
the bounded scope and completing applicable integration checks.

Root subsequently requested a read-only diagnosis of the frozen optimized-v3 h11
campaign. The report is `runtime/h11-campaign-diagnosis.md` under the experiment
directory. Final campaign status remains inconclusive: preparation49.404s,
11 executions and zero complete traces, zero observed false checks, and zero valid
samples. Native query work and post-deadline classification are distinguished
from runtime trace-generation cost. No further implementation/native checks were
performed in this diagnostic follow-up. This is owner analysis, not independent
verification or evidence that all parent acceptance criteria passed.

## Integrated closure, 2026-09-29

Root completed the combined workflow on recorded source hashes at engine
HEAD060d5ad532f67d5367450689225274fb0a0243e7 plus preserved dirty changes.
V3 independent Driver32/Core62/Query83 controls and final v4 independent
Core33/Query21/Driver14 controls passed in fresh contexts. These overlap; they
are not an additive unique-test count. Final makeformat changed no source bytes;
supported `make build-dafny` passed0warnings/0errors and transport4/4 passed.
Frozen v4 manifest1628files SHA256
f7f02a2e14e08e45fb5696da3ad6fbf0d6e1f58ef815a65d6a807db9c34bd402.

All six unchanged historical campaigns finished, preserving original requests,
seeds and budgets. h13 reports two validated finite-prefix violating samples;
representative ordinal1 replays with exact violation equality, exit0 in60.352s.
The other cases retain documented proof/runtime/coverage limits; this bounded
implementation plan does not claim all historical cases or broader M1/M2 solved.
Root orchestration plan tracks next work. Failed attempts, first reviewer quota
interruption, independent replacement review, source patches and native baseline
comparison remain explicit in the [report](../../../pbt-draft-exp/inconclusive-followup.md)
and [root plan](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).
Reusable findings: [contract-testing knowledge](../wiki/contract-testing.md#exact-reduction-and-finite-prefix-counterexamples-2026-09-29).
No package additions, paid runs, original specification edits or commits.
