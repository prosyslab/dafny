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
