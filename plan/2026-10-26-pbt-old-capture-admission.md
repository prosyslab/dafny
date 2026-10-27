# Commit PBT old-state captures only when consumed

Status: done (scoped capture repair; external ghost-state/classification limits remain)
Date: 2026-10-26
Parent: [preparation bottleneck](2026-10-26-pbt-preparation-bottleneck.md)

## Objective and observed evidence

The authorized same-input Csplit call4 replay reached64 generated samples after
the compiler/preparation repair, but all64 stopped with a null-reference error
after input records and before any check or Executed record. R02 artifacts live
under `/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r02/`.
Independent source and trace inspection found that Check rewrites old expressions
and renders entry captures before selecting the final decision. Captures survive
a downgrade to unchecked or a fixed-heap query even though those paths do not
consume scalar old locals. Wrappers emit them before validating inputs. The last
generator location therefore misleadingly survives an engine-generated capture.

Fix this general instrumentation defect without constructing missing external
ghost state, changing any benchmark/extern contract or claiming runtime validity.
The public native IO singleton deliberately has no executable ghost initializer.
Whether the subsequent fixed-heap admission can establish a concrete witness is
a separate runtime result; do not silently equate unavailable state with valid
null or synthesize it. Existing trust, obligation and native query checks remain.

## Acceptance and non-goals

- Plan old captures locally for each Check without mutating committed names or
  declarations and without rendering functions during speculative rewriting.
- After final decision/caps, commit and render captures for runtime checks and
  scalar closed queries only. Preserve old evidence required by scalar queries.
- Unchecked and heap-backed closed clauses emit no unused old dereference or
  speculative function wrapper. Their metadata/checkpoints use noncapture original
  expressions (with existing statement-expression normalization) and recomputed
  free variables; heap decisions still use indexed original contracts.
- Retained captures follow entry type/precondition checks and precede invocation
  in method/function wrappers. Existing source mapping and contract authority stay.
- No state fabrication, blanket exception catch, skipped obligation, package, paid
  model trial or benchmark edit. No ghost-field omission policy change in this plan.

## Exact change table

| Owner | Change and necessity | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` Check/RewriteState/CaptureOld and method/function wrapper placement | Defer capture declaration/render side effects until final consuming decision; order entry checks before captures. Prevent discarded checks from executing reads and preserve invalid-input rejection. | Pure snapshot parse/resolve and transformed AST behavior; independent source review. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs` | Cover heap closed clauses, forced unchecked checked-function side effects, scalar closed cap downgrade and input-validation/capture/invocation order. Keep runtime-old behavior. | No temporary directory, file write, native compilation, solver or process from tests; inspect full helper path first. |
| This plan/index, bottleneck/parent records, `wiki/pbt-trusted-sources.md` and index | Preserve R02 actual performance/failure evidence and describe general capture boundary. | Diff and recursive Markdown-only audit. |
| Bounded task scratch build and a new operator replay attempt | Publish changed production with exact current source/products; preserve R02 artifacts and original request bytes. Plan exact helper filenames/pins before creation. | Separate named tmux build/operator run, never native compilation inside tests; dedicated PBT tag/latest preservation and owned cleanup. |

## Validation

From `/workspace/cosyn/dafny`, first review all changed source and test call paths.
After independent review, use the existing bounded serial TG.Test/CLI build pattern
with600-second/256KiB limits and exact input identities, followed by the affected
no-build/no-restore ObligationTests filter. Existing unchanged Driver/preparation
suites need not repeat absent new dependencies/concerns. Actual replay is a distinct
operator measurement, not a unit test. Record source revision/hashes, all commands,
versions, failures and artifact paths. A zero-error build or tool exit alone does
not establish a valid sample or counterexample.

## Results

Implementation is in progress. The transformer now plans old captures per check
and owner, commits only captures referenced by runtime or scalar closed checks,
and emits retained captures after entry checks with their own source location.
Three pure snapshot regressions cover heap-backed discard, unchecked rendering
side effects and scalar decision-cap evidence/order. Independent source and test
call-path review accepted frozen transformer hash
`c435c4ec36f326984fb11a6d351711bd866506b406333541641586117e20910a`
and test hash
`5557ae4e09dfc4ad68dc7a2d7412292b894325864dee8e7d01bb45f2ff8564c9`.
The first bounded focused execution passed42 of44 cases and failed only the two
new discard regressions during generated-source reparse: both declared
`Goal(cell: Cell)` but accidentally used the helper's default `x: int` generator,
leaving two unresolved `cell` identifiers. Both calls now supply the existing
matching in-memory `Cell` generator; production is unchanged. The corrected test
hash is `d06afb26d20a3f4822a4489674867910aacfcb097d4988724fe9c622bb903296`.
A fresh focused execution, wiki reconciliation, publication and any replay remain
pending.

## Exact build and operator preparation scope

Use `/workspace/tmp/pbt-preparation-bottleneck-20261026/native-capture-build-r01.py`
with exclusive same-stem logs/result, derived from the accepted consolidated
`native-final-build-r03.py`. Keep its three serial Driver.Test, TG.Test and CLI
projects,600s/256KiB bounds,20 production/five test input pins and five product
records. Update only attempt identity and settled source/test hashes (including
the already-corrected selected-preparation test). Start in named tmux/socket
`pbt-old-capture-build-20261026-r01` only after source review and pin settlement.
The focused ObligationTests filter is the required fresh test gate; do not repeat
unrelated already-accepted suites solely because their projects were built.

Prepare fresh `/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r03/`
with only `replay.py`, `Pbt.Dockerfile`, `Pbt.Dockerfile.dockerignore`, derived from
the accepted r02. Preserve exact R13 request4/dependency/base image,20+5 input
bindings and all isolation/output/cleanup/latest rules. Update only r03 dedicated
base/output/container identities and the successfully published capture-repair
manifest/source/products. Native request bytes and runtime limits remain unchanged.
Use `pbt-csplit-performance-build-20261026-r03` and
`pbt-csplit-performance-replay-20261026-r03` named tmux/socket sessions for the
separate build and execution. Parent integration plan records these names and
actual results; preserve all earlier artifacts. No model trial is authorized by
this replay. This experiment decides whether the dead-capture crash is removed;
it must expose any remaining heap-admission limitation honestly.

## Publication and focused fixture correction

`native-capture-build-r01.py` completed all three projects successfully with exact
25 source pins, manifest SHA256
`10ff88fd4989ef521b3ffb0fc084aa8107b25b2339ea8c5180d28406ede6ae26`.
The independent focused run passed42/failed2 (44total, no skips). Both failures
are new fixtures supplying the helper's default `x:int` generator to a `cell:Cell`
goal, so transformed PbtMain cannot resolve `cell`. Preserve
`independent-old-capture-r01.log` and its result; this is not a passing run.

Correct only the two Transform calls with the existing Cell generator. Build only
TG.Test using new `/workspace/tmp/pbt-preparation-bottleneck-20261026/
old-capture-test-build-r02.py`, derived from the accepted single-project r04 helper
with this task's current25 input pins, native-capture-r01 production receipt and
exclusive attempt/result/log names. Use named tmux/socket
`pbt-old-capture-test-build-20261026-r02`,600s/256KiB bounds and exact before/after
product checks. It is not another CLI publication. Independent verification then
reruns the corrected44-case owner; r03 operator still binds native-capture-r01's
production manifest/products. No production source change is needed for this
fixture mismatch.

The corrected-generator rerun passed43/failed1 (44total). The remaining test
incorrectly counts CaptureHeap as FunctionCallExpr; the declared runtime API is a
method and resolves to CallStmt. Preserve independent-old-capture-r02 evidence.
Correct that assertion to inspect ordered entry/return CaptureHeap method calls.
Production remains unchanged. Reuse the single-project helper as exclusive
`old-capture-test-build-r03.py` with only attempt/test pin changed, named tmux
`pbt-old-capture-test-build-20261026-r03`. Retain the capture-r01 publication and
all before/after source/product guards; independently rerun the44-case owner.

## Passing focused gate and installed replay

The r03 test-only build passed and retained all five capture-r01 published products.
Independent `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj
--no-build --no-restore --filter FullyQualifiedName~ContractRuntimeObligationTests
-v:minimal` from `/workspace/cosyn/dafny` passed44/0failed/0skipped (VSTest17.8.0,
about1s). Evidence is `independent-old-capture-r03.log` and its result under the
planned scratch directory. Exact source25, testhost dependencies and products5
matched before/after. Final test SHA256 is
`0cf8844d3cbd3924763907fd93297ad770c83761ead9c939c8a4af5521ce5ef9`;
production transformer remains `c435c4ec36f326984fb11a6d351711bd866506b406333541641586117e20910a`.
Earlier failed fixtures remain recorded; none was a passing gate.

Root also ran scoped `dotnet format whitespace Source/Dafny.sln --no-restore
--verify-no-changes --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs
Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs --verbosity quiet`
from `/workspace/cosyn/dafny`: exit0, no diagnostics or source changes.

The independently accepted literal-only r03 operator helper built dedicated image
`sha256:9012e786826d4afcd764f305c1cc108337aa413cbcde56127b915d64c9b70771`
with unchanged latest maps. Root dispatched exact request4 in named tmux/socket
`pbt-csplit-performance-replay-20261026-r03`; runtime outcome remains pending.

## Final observed result and handoff, 2026-10-26

The exact-input r03 replay uses dedicated image
`cosyn-pbt-csplit-performance:20261026-r03` with immutable ID
`9012e786826d4afcd764f305c1cc108337aa413cbcde56127b915d64c9b70771`.
All shared latest IDs remain unchanged and the owned container was removed with
exact name/CID absence verified. No model/provider trial was launched.

The compiler worker measured21.339s versus original51.380s; actual dotnet build
was19.016s and generated C# was5,166,220bytes versus7,466,877. Earlier r02 measured
17.556s compiler worker, demonstrating run variability. These are separate phase
observations, not a pure C# speedup or completed campaign comparison.

All64 retained traces now reach three passed input checks, entry-heap capture and
the Executed marker, followed by a null-reference error. Thus the pre-entry capture
crash is removed. The draft first reads its context from the public external IO
singleton, whose ghost region fields have no executable initialization. The last
location marker is not an exception stack frame. No valid classified sample or
counterexample is established, and no contract or missing ghost state was invented.

Sampling finished by139.279s. Classification subsequently repeated45 failed initial
type checks (29.492s) and45 dependency-scope preparations (32.707s); the original
231782ms deadline expired before a worker result. Native supervisor zero counters
therefore mean unavailable classification, not zero observed execution. The final
campaign phase is unclosed. The complete-phase postprocessor rejected that state,
so there is no summary.json; the raw envelope and all65 artifacts are intact.

The exclusive offline `operator-observation.json` validates all artifact hashes,
64 ordinals and445 phase events, retaining native and observed counts separately
and explicitly recording the unclosed campaign. SHA256:
`aad419b510ebf33ffa5f37d6f14b12262260e39dde22110981b836708518735e`.
It is available under
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r03/`.
The remaining work is a sound external ghost-state execution model and avoiding
repeated classification work without bypassing admission. Neither is completed
by the current repair. No experiment is active; the continuing goal was cleared.

The scoped acceptance criteria pass: independent review,44 affected memory tests,
formatting, exact-source publication and observed removal of the pre-entry crash.
The parent counterexample objective remains unmet. Durable findings are recorded
in `wiki/pbt-trusted-sources.md`; earlier pending paragraphs are historical.

Independent final read-only audit accepted the offline observation hash, all65
artifacts, trace/phase counts, unavailable classification, cleanup and unchanged
latest identities. No discrepancy or overclaim was found.
