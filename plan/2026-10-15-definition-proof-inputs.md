# Emit optional translated definition proof inputs

Status: done
Date: 2026-10-15
Owner: native benchmark producer
Parent: [integration plan](../../../plan/2026-10-15-definition-proof-reuse-and-ten-case-rerun.md)

## Objective and acceptance

Emit optional, conservative per-definition proof-input certificates without
running a solver. A method A certificate survives an unrelated ordinary method B
implementation or standard lemma proof-body change and relocated source snapshots. Target bodies, contracts,
transparent function bodies, recursive SCCs, visibility and proof configuration
changes invalidate certificates. Ambiguous or unsupported definition mappings
are omitted. Existing analysis JSON is unchanged unless explicitly requested.

This is repository maintenance using current native sources and public generic
fixtures only. No benchmark candidate, private runner/evaluator/oracle records,
paid provider calls, image builds, scoring changes or proof weakening are in scope.
Preserve all existing trigger, exit-code, resource-statistic and source edits.

## Inspected evidence and approach

`DefinitionAnalysis.cs` already enumerates source definitions and offers an
optional document envelope; semantic facts hash source tokens and cannot establish
proof dependency completeness. `BoogieGenerator.Translate` produces all verifiable
modules and full prelude/declarations without invoking a solver. Generated
implementations carry `CanVerifyOrigin` and diagnostic `verboseName`; generated
contracts, function axioms, recursive context and visibility belong in the shared
translation identity. `DafnyCommands.VerificationOptions` provides actual verifier
flags; definition-analysis currently exposes resolver options only.

Certificates hash all non-Implementation translated declarations and all required
target implementations; exclude another ordinary method implementation only when
ownership is unambiguous. Preserve semantic Boogie attributes. Normalize only
proven diagnostic location/tracking noise and comments, with relocation and
body-line-shift controls. Bind loaded toolchain identity and actual accepted
verification/translation options. Unsupported modes fail closed.

## Change table and layer ownership

| Native owner file/symbol | Change, purpose and unmet behavior | Validation |
| --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` | Typed schema and translated proof-input producer; complete conservative dependency identity otherwise unavailable | In-memory public generic semantic-change and relocation controls |
| `Source/DafnyCore/DefinitionAnalysis.cs` / `DefinitionSourceFacts`, `AnalyzeDocument` | Optional proofInputs envelope and opt-in argument; preserve existing defaults | Existing API callers compile; omission/default checks |
| `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` | `--include-proof-inputs`, verifier option support, spans-only rejection and opt-in diagnostics-to-stderr routing so JSON stays independently parseable | Focused Driver command controls and tiny CLI probe |
| `Source/DafnyCore.Test/DefinitionProofInputsTests.cs` | Bounded in-memory normal/invalidation/unsupported fixtures, no solver or bulk disk | Focused Core tests |
| `Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs` | Tiny public CLI option/JSON controls if command boundary requires them | Focused Driver tests |
| This plan and `plan/INDEX.md`; `wiki/definition-proof-inputs.md`, `wiki/INDEX.md` | Record interface, supported proof scope, limitations, validation and handoff | Diff/link and Markdown-only review |

All changes are native analysis implementation/test/documentation. Benchmark
specification, proof scope, evaluator, dataset and scoring layers remain fixed.
Cosyn owns its separate Python consumer and native replica plan; parent owns
fresh independent verification. No dependencies, installs, restores or commits.

## Validation

Working directory `/workspace/dafnyutils/dafny`, cached .NET SDK 8.0.131 and
existing package assets required. Inspect supported Makefile targets; use their
documented `dotnet` command equivalents with `--no-restore` and serial builds.

- `dotnet build Source/DafnyCore.Test --no-restore -m:1` and
  `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsTests`.
- `dotnet build Source/DafnyDriver.Test --no-restore -m:1` and focused Driver
  tests, once implementation settles. Native command probes are final local
  integration validation, not paid experiments or Dafny solver verification.
- Scoped `dotnet format whitespace Source/Dafny.sln --no-restore --include`
  with exact affected C# paths, then `--verify-no-changes`.
- `git diff --check`, exact owned-source review, recursive `plan/`/`wiki/`
  non-Markdown inspection. Record unavailable prerequisites and skipped checks.

Scratch/probes/results: `/workspace/tmp/definition-proof-reuse-20261015/native-benchmark`.
No existing broad benchmark or contract campaigns are authorized by this plan.

## Risks, compatibility and approvals

Unsound reuse takes priority over cache efficiency; omitted certificates force
ordinary re-verification. Source paths identify entries but must not enter semantic
hashes. Boogie diagnostics/tracking IDs may vary with unrelated implementation
size; normalization must use structured AST facts rather than source regexes.
User authorization is recorded in the linked integration plan; no new approval
is required for these bounded reversible source changes.

## Progress and handoff

Ready plan recorded before source changes. API proposal sent directly to Python
owner and parent. Inspection confirms the need for new translated proof facts.

Native Core build initially exposed two API mismatches (enumerable Boogie flags
and VC-generation namespace), then passed. The first affected test run exposed
unset optional CLI collections in programmatic callers; fixed concrete missing
value handling. VSTest requires its localhost socket: sandbox denied it, then the
same focused command received automatic local escalation approval. The Python
owner requires clean certificate stdout and preserved warning diagnostics;
opt-in diagnostics routing is now explicitly included above before that edit.

The first normalization approach used Boogie's StandardVisitor, which expects
resolved implementation blocks and failed on the fresh translator output. Replaced
it with complete emitted Boogie token scanning using the existing native lexer;
only complete diagnostic `id`/`captureState` attributes are omitted. No source
regexes, inferred source contract dependencies or solver checks are used.

Affected in-memory Core11/11 controls pass (3.95s): unrelated ordinary callee body
and line shifts, relocation, target body, callee-only contract, transparent
function, exported visibility, SCC, assertion isolation, by-method omission,
custom Boogie arguments omission and opt-in compatibility. Final command
validation adds included-source projection and solver-unavailable controls. Native
source translation is scheduled on the existing large stack; opt-in command
disables automatic `z3 -version` lookup before resolution. Reusable interface and
limitations: [native wiki](../wiki/definition-proof-inputs.md).

Final CLI controls initially passed3/5. An earlier edit during a long compiler
invocation produced stale output newer than its changed source; refreshed owned
source timestamps and rebuilt serially without source edits. The solver-unavailable
control then passed, while the included-definition control exposed use of
root-only `DefinitionNode.ReportFacts.SourcePath`. Corrected the producer to reuse
`DefinitionAnalysis.SourcePath(INode)` for all sources. Added fail-closed handling
for nondefault global/stratified inlining modes and an opacity control before the
last source freeze. No solver configuration or source contract is weakened.

Fresh independent source review identified programmatic plugin paths beyond the
CLI option: `AdditionalPlugins`, `AdditionalPluginArguments`, and the cached mutable
`Plugins` collection also feed PreVerify hooks. Before freeze, extend the existing
unsupported-plugin guard to all three paths and add bounded public API controls;
then rebuild serially and recheck affected controls/format. This is a concrete
soundness repair within the existing producer/test scope.

Parent clarified that ordinary helper lemmas must also support contract-preserving
reuse. Source inspection shows standard `Lemma` uses the ordinary modular Call
procedure, while Extreme/Prefix/TwoState have special behavior. Whitelist exact
`Method` and exact `Lemma` types for exclusion; retain all other subclasses,
by-methods and generated/unknown owners. Add separate lemma-body preservation and
callee-only lemma-contract invalidation controls before final native rebuild.

Independent vendor-IL review found modern preprocessing can consume all bodies
with `InferModifies`, and loop preprocessing also consumes `SoundLoopUnrolling`.
Root requests conservative omission for inferred-modifies or nondefault loop
unrolling/soundness settings, plus bounded programmatic controls. Add these to
the existing unsupported-mode guard before the final source freeze; normal CLI
verification policy remains supported and unchanged.

## Final owner validation and freeze

Native base revision `bc427b21461f258fd8de34232e01bb6be03cee39`, with all
pre-existing source, trigger, exit-code and resource-statistic edits preserved.
SDK8.0.131, runtime8.0.31, MSBuild17.8.49, VSTest17.8.0, xUnit adapter2.4.3.
All following commands ran serially from `/workspace/dafnyutils/dafny` using cached
assets and without restores, providers, image builds or solver verification.

| Exact validation command/scope | Result and local artifact |
| --- | --- |
| `dotnet build Source/DafnyDriver.Test --no-restore -m:1 -v:q` | exit0,0warnings/errors,1m32.84; `final-frozen-driver-build.log` |
| Refresh only owned CLI source timestamp, then `dotnet build Source/DafnyDriver --no-restore -m:1 -v:q -p:BuildProjectReferences=false` | ensures final Driver compilation from held bytes, exit0,0warnings/errors,5.84s; `final-frozen-driver-refresh.log` |
| `dotnet build Source/DafnyCore.Test --no-restore -m:1 -v:q -p:BuildProjectReferences=false` | exit0,0warnings/errors,4.50s; `final-frozen-core-test-build.log` |
| `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsTests --logger 'console;verbosity=normal'` |21/21 pass,0skips,4.38s; `final-frozen-core-tests.log` |
| `dotnet build Source/DafnyDriver.Test --no-restore -m:1 -v:q -p:BuildProjectReferences=false` | exit0,0warnings/errors,1.73s; refreshes exact test-side binary copies; `final-frozen-driver-test-build.log` |
| `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsCommandTests --logger 'console;verbosity=normal'` |6/6 pass,0skips,3.80s; `final-frozen-driver-tests.log` |
| `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include` the exact five C# files in the change table | exit0; generic workspace-loader warning retained; `final-frozen-format.log` |
| `git diff --check`; recursive native `plan/` and `wiki/` file scan | diff clean; both trees contain0non-Markdown files; frozen five source SHA256s rechecked unchanged |

Artifacts are available locally in
`/workspace/tmp/definition-proof-reuse-20261015/native-benchmark/`; they are
maintenance scratch, not tracked repository documents. `freeze.json` records
exact five source SHA256s, current revisions/dirty state, Core/Driver/test DLL and
PDB SHA256s, commands/log paths and the authoritative project CLI path
`Binaries/net8.0/DafnyDriver.dll`. Core copies and Driver copies are byte-identical.
The pre-existing packaged `Binaries/DafnyDriver.dll` is outside this scoped build;
an initial standalone probe against that older path was discarded as stale.

Native source/binaries were held after these receipts and handed directly to the
Cosyn replica owner and fresh independent native reviewer. The final API is
`--include-proof-inputs` with optional `sourceFacts.proofInputs` schema1. Included
verifiable owners receive entries; ordinary methods and exact standard lemmas
support modular body exclusion. All plugin/inline/inferred-modifies/nondefault
loop modes described in the wiki fail closed. Caller qualification and immutable
solver/runtime policy remain separate mandatory conditions.

## Independent acceptance and closure

The fresh independent native source/binary gate passes. Its
[review report](/workspace/tmp/definition-proof-reuse-20261015/independent-native/REVIEW.md)
and [acceptance metadata](/workspace/tmp/definition-proof-reuse-20261015/independent-native/accepted-freeze.json)
are available as local maintenance artifacts. Acceptance was recorded at
2026-10-15T13:12:11Z and binds report SHA256
`170c9e83c1678ababdcbe1193b24fdad9674e29608df424a5038dbaee985668c`
to owner freeze SHA256
`bade4c12e64bd70cd1725c90d549113efde43682f910a1028f81bdf5ad095038`.

The independent context inspected actual source and modern Boogie3.5.5
preprocessor IL, independently passed Core21/21 and Driver6/6 with zero skips,
and passed its own public API8/8 controls. Its41CLI invocations establish30
distinct final behavioral assertions after3documented fixture corrections; the
initial failed fixtures and corrected receipts remain preserved. All5source/PDB
bindings and DLL/PDB identities pass. All32independently captured source,
binary and tool files stayed unchanged, and all16owner-manifest entries match.
No implementation change was made after the final freeze.

Closure reconciliation independently reread both acceptance hashes and matched
the current5source and11binary/PDB entries against `freeze.json` without any
C# edits, builds or tests. Its local receipt is
[closure-reconciliation.json](/workspace/tmp/definition-proof-reuse-20261015/native-benchmark/closure-reconciliation.json).
The source/binary freeze remains held. Owner formatting/diff checks retain their
separate passing receipts; the fresh reviewer did not rerun formatting because it
changed no repository files. Native plan/wiki closure changes are Markdown only.

Native acceptance criteria are complete and this owner plan is done. Parent-owned
consumer/replica integration, solver and benchmark validation, image/source/runtime
reconciliation, offline normal/forced UID1013 admission and the ten-case paid run
remain pending under the linked integration plan. No solver-proof, benchmark-score,
image or paid-run acceptance is established by this native gate. No native process,
source edit, build or required native check remains to be handed off.
