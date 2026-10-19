# Native proof-input projection integration

Status: independently accepted replica and consumer interface
Verified: 2026-10-15, native base dce5a96612b6516c5b180bb215d6eb3e3b430d5a plus dirty tree
Origin: [integration plan](../plan/2026-10-15-definition-proof-inputs-integration.md)
Consumer: [Cosyn proof certificates](../../wiki/architecture/definition-proof-reuse.md)

Command-level test availability changed on 2026-10-16: the six-case
`Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs` class was deleted
because its shared helper created and deleted a GUID-named temporary directory.
See the [cleanup plan](../plan/2026-10-16-remove-proof-input-tempdir-tests.md).
The local and independent Driver 6/6 results below are historical receipts from
before that deletion, not current validation; no replacement command-level test
was added. The first independent cleanup review found that four of the five
paths in the historical source manifest remain and match their frozen hashes
at its 2026-10-16 review; the command-test path is absent. This describes path
availability and that review's hash check, not a current five-file source-parity
claim.

Historical transfer and baseline record (2026-10-15): Cosyn's native runtime
received the producer's optional `definition-analysis --include-proof-inputs`
wire extension. Five source and test files were transferred from the frozen
producer, and all five local copies matched its SHA256 manifest at transfer.
The existing two target files had identical clean baselines, and three new
paths were absent. Thirty unrelated dirty-file hashes, including
resource-statistics removal and earlier native repairs, matched their recorded
baseline at that freeze. After the 2026-10-16 cleanup, four manifest paths
remain; the fifth path, the command-test source, is absent. The transfer and
baseline statements above describe the 2026-10-15 state, not current five-file
parity.

The native producer projects the fresh translated global/procedure context plus
target-owned and other nonexcludable implementations, omitting unsupported projections. It uses native
ownership metadata rather than Python source-text heuristics. Ordinary method
body edits can preserve caller inputs; transparent definitions, contracts,
recursion, visibility and configuration changes affect the projection. Unsupported
plugins, custom transformations and unsafe inlining configurations grant no
certificate. The optional command emits JSON alone on stdout and keeps diagnostics
on stderr, includes verifiable owners from included files, and does not start a
solver to discover its version. The host must pin the runtime/solver within a run;
these certificates do not authorize a cache across changed runtimes or runs.

The historical producer and replica source manifest is recorded in
`/workspace/tmp/definition-proof-reuse-20261015/native-cosyn/freeze.json`, alongside
local CLI/Core/Driver/test DLL and PDB hashes, versions, preserved-file hashes and
check logs. This maintenance artifact is available in the current workspace;
it is not a benchmark input. The actual local CLI at the 2026-10-15 freeze was
`dotnet /workspace/cosyn/dafny/Binaries/Dafny.dll`; its copied Core/Driver assemblies
matched those loaded by the native tests and project CLI at local freeze.

Historical local evidence from 2026-10-15: .NET SDK8.0.131; serial no-restore solution build passed with zero
errors and four warnings in untouched TestGeneration test sources. The initial
Core test process could not open its local IPC listener under the sandbox and
aborted before executing tests. Narrow approved reruns passed Core21/21 and
Driver6/6, with no skips. Exact-five-file whitespace verification passed; the
formatter emitted its generic workspace-loading warning. No native source edits
had occurred after those checks at the 2026-10-15 closure. The command-test source
was removed on 2026-10-16, so the prior Driver6/6 receipt is not current
validation. At the original closure, Python's eight frozen source/test hashes
matched their manifest.

Fresh independent acceptance on 2026-10-15 is recorded in
`/workspace/tmp/definition-proof-reuse-20261015/independent-cosyn/native-interface-verification-report.md`
(SHA256 `b04e6cccee621c343c0ca697024db24661442137ab93ce1a3d7b5a547a250fb7`).
It reran Core21/Driver6 without skips, reviewed fail-closed unsupported modes and
host binding, and passed actual CLI/client invalidation, relocation, root-order
and warning controls. The true filtered verifier passed all three mutations on
a tiny caller/callee fixture. At that 2026-10-15 review, all 20 native freeze
identities matched; at the original Markdown closure, all five native and eight
Python source hashes matched their manifests. These are historical results
from before the command-test source was removed.

The native binary/PDB freeze is historical local-build evidence. Parent began
its supported image build at 13:21 UTC, which may regenerate runtime bytes; no
later binary equality is asserted. Image validation, benchmark scoring and paid
performance remain parent-owned. The linked host record preserves the default
typecheck failure (724 discovery errors) and passing canonical Pyright separately.

## Projection boundary and pending optimization

Source review on 2026-10-16, under the [scope-limits plan](../plan/2026-10-16-proof-input-scope-limits.md),
clarifies the original acceptance: `DefinitionAnalysis.ProofInputs.cs` hashes fresh
translation before Boogie resolution and verification preprocessing. Its observed
stability for a particular ordinary callee-body edit is not a proof that every
preprocessing input or the actual solver declaration order is identical.

Removing unreferenced procedures from this hash needs more than a call graph.
Boogie3.5.5's [Checker.Target](https://github.com/boogie-org/boogie/blob/v3.5.5/Source/VCGeneration/Checker.cs#L129)
collects basic types from the whole program except other implementation bodies.
Its setup can shuffle the split's pruned declaration list before selecting solver
declarations. [LambdaHelper.ExpandLambdas](https://github.com/boogie-org/boogie/blob/v3.5.5/Source/Core/LambdaHelper.cs#L128)
adds generated global functions and axioms after the producer's current boundary.
The legacy and modern [ExecutionEngine entry paths](https://github.com/boogie-org/boogie/blob/v3.5.5/Source/ExecutionEngine/ExecutionEngine.cs#L767)
also differ in their handling of effective monomorphism; a future producer must
select and justify the actual supported preparation path.

There is a related open coverage question in the existing implementation exclusion:
`BoogieGenerator.GenerateImplPrelude`/`DefineFrame` creates frame lambdas inside
ordinary method implementations, and Boogie's later expansion can generate global
inputs from them. Those late declarations are not directly fingerprinted today.
Changed generated inputs can be conservative extensions, so this source finding
does not demonstrate invalid proof reuse, a false successful proof, or a C7 failure
cause. It does prevent claiming exact prepared-input identity without further
analysis. No producer, admission or verification behavior changed in this review.

The detailed [design study](/workspace/tmp/central-verification-20261016/procedure-projection-design.md)
specifies exact procedure-name/object matching, own-procedure roots, full contracts,
where clauses and attributes, and the unresolved preprocessing footprint. It is
maintenance evidence available in this workspace, not a benchmark input. Immediate
call-closure-only filtering was not selected. Follow-up requires an owning native
plan, an explicit dependency guarantee and independent validation; the historical
build/test receipts above do not validate that proposed optimization.

## Historical benchmark-native producer record — 2026-10-15

The following original producer record covers the separate benchmark-native
source/binary freeze. Its command-test availability and validation counts are
historical: the command-test class was removed on 2026-10-16 as recorded above.
The current projection limits and later repeatability repairs still apply.

# Optional translated definition proof inputs

Status: frozen native source/binary gate independently accepted
Verified: 2026-10-15, native base `bc427b21461f258fd8de34232e01bb6be03cee39` plus dirty source
Origin: [owner plan](../plan/2026-10-15-definition-proof-inputs.md)

`definition-analysis --include-proof-inputs` optionally adds
`sourceFacts.proofInputs` with `schemaVersion: 1`, `toolchainSha256`,
`optionsSha256`, and `definitions` entries containing `sourcePath`, `fullName`
and `sha256`. The ordinary definition-analysis result remains unchanged by
default. Certificate stdout is one JSON document; existing qualification
diagnostics are preserved on stderr for this opt-in mode. `--spans-only` rejects
proof inputs because they require resolution and translation.

The producer translates every verifiable module using `BoogieGenerator.Translate`
without constructing verification conditions or launching a solver. The CLI skips
the otherwise automatic solver-version subprocess and uses the existing large
stack translation scheduler. It accepts the usual verification options alongside
resolver options. Callers must pass the same input roots, libraries and relevant
verification options as their actual proof command, then separately enforce parse,
type, warning, full-implementation and exact proof-policy admission.

Each fingerprint includes all translated non-Implementation declarations across
all modules, every non-excludable implementation, and every implementation owned
by the target. An ordinary method or exact standard lemma implementation is excludable only when its
`CanVerifyOrigin` maps unambiguously to a source definition and neither it nor its
unique matching procedure carries `inline`. Function implementations, unknown
mappings, generated obligations and nonstandard lemma implementations remain in
the conservative shared context. Extreme, prefix and two-state lemma
implementations remain shared. Visible function bodies, contracts, prelude and recursive-call translation
are therefore retained. This deliberately invalidates more proofs than a minimal
dependency graph would.

Boogie's own lexer removes comments/whitespace from complete canonical emission.
Only complete `id` and `captureState` attributes are discarded: the former labels
diagnostic/unsat-core dependencies, and the latter labels model-view snapshots.
All other semantic attributes and literals remain in the input. Paths identify
entries but do not enter hashes; diagnostic locations and unrelated global
dependency counters cannot invalidate an otherwise identical translated input.

The producer hashes the loaded DafnyCore and relevant Boogie assemblies, plus
declared verifier/resolver settings and relevant supported Boogie settings. Library/prelude
paths are represented by their translated contents. Solver executable discovery
is deliberately absent; callers retain their exact solver/toolchain execution
policy and immutable runtime provenance with the proof evidence.

No certificate is issued for by-method identities, extreme lemmas, bodyless or
verification-disabled definitions, or definitions with no translated owned
implementation. Arbitrary Boogie arguments, external plugins (including both
programmatic configuration lists and the active cached plugin set), nondefault
inlining, inferred modifies, and nondefault loop unrolling/soundness settings omit
the entire optional document because their transformations are outside the
supported projection mode. Missing entries always require fresh verification.
With `--verify-included-files`, verifiable included definitions can receive entries
even though the ordinary analysis envelope lists only the requested root files.

Source: `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`,
`Source/DafnyCore/DefinitionAnalysis.cs`,
`Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs`.
Public controls: `Source/DafnyCore.Test/DefinitionProofInputsTests.cs` and
`Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs`.
The final bounded in-memory Core controls pass21/21 and native CLI controls6/6,
with no skips. Serial no-restore builds and exact five-file format verification
pass. Fresh independent review also passes Core21/21, Driver6/6 and its own API8/8
controls. Its41CLI invocations yield30distinct final assertions after3documented
fixture corrections, with initial receipts preserved. All5source/PDB bindings
pass, all32independently captured files remain unchanged and all16owner-manifest
entries match. The
[independent report](/workspace/tmp/definition-proof-reuse-20261015/independent-native/REVIEW.md)
and [accepted freeze](/workspace/tmp/definition-proof-reuse-20261015/independent-native/accepted-freeze.json)
pin the final result; the owner closure reread those hashes and reconciled the
current source/binaries without editing or rebuilding them. The local source/binary/PDB freeze manifest and logs are available under
`/workspace/tmp/definition-proof-reuse-20261015/native-benchmark/` (maintenance
scratch, not checked into Git); exact receipts belong in the linked plan. No paid
experiments, benchmark grading or solver proof outcomes are established by these
analysis tests. Solver/benchmark validation, consumer/replica integration, image
admission and the paid ten-case run remain parent-owned gates under the
[integration plan](../../../plan/2026-10-15-definition-proof-reuse-and-ten-case-rerun.md).
