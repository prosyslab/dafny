# Preserve parseable PBT diagnostic source preambles

Status: done
Date: 2026-10-20

## Objective and acceptance criteria

Repair the public diagnostic-source transformation path that currently inserts a generated runtime
bridge, and for the default module its runtime alias, at byte zero of the first supplied source.
Dafny accepts `include` directives only in the initial file preamble, so this placement can turn an
otherwise valid immutable source snapshot into unparsable diagnostic Dafny when that source begins
with an include. This is a generic source-backed defect and a candidate explanation for separately
observed parser-phase receipts; it is not attributed to any receipt without independently reviewed
parser-error evidence.

Acceptance requires bounded public in-memory parse/transform/reparse cases for a named-module goal,
a default-module goal, cross-file default-module emitted code, and source-order independence when an
include-bearing snapshot appears first.
The exact canonical top-level `PbtRuntime` module, runtime class and generated bridge/alias bindings
must remain declaration-identity based after re-resolution. Original source contents and include
preambles remain in their original order; named modules retain their local runtime alias at the
parser-owned module body boundary. The change must preserve generator selection, proof certificates,
proof coverage, obligation text/IDs/decisions, source mappings, original source hashes/source-set
hashes, trusted runtime/RNG inputs, result schemas, sample accounting and evaluator behavior.

## Non-goals and authorization boundary

This is native repository maintenance, not an evaluated experiment. Do not read candidate/provider/
task/evaluator/reference data, credentials, `/data`, private traces or root experiment reports. Do
not alter a running experiment, its immutable image/package/inputs, retry it, or project development
findings into its results. No candidate/runtime compilation, generated campaign, solver, container,
benchmark, image, paid provider or dependency change is authorized by this plan. After implementation,
the standalone operational C# source build through `make exe` is authorized before the in-memory tests;
the tests themselves must not trigger a restore, source build or native/runtime compilation. Commits
remain parent-owned under the existing authorization and will not be created by the implementation
agent. Parser/build success will not establish generator-proof acceptance or live campaign
effectiveness.

The requested repair is authorized, but implementation begins only after the root owner reads and
announces this ready plan. Extend the change table and obtain any newly required approval before
changing scope or files.

## Ownership and inspected evidence

Owning repository: `/workspace/cosyn/dafny`, current clean revision
`e3cb42691e61369e231f4094d5f3340a1ee535a9`. This change affects only native diagnostic source
transformation and its public in-memory tests/documentation. It does not change the root integration
package, Cosyn harness/protocol, benchmark repositories, specification, proof, dataset, scoring or
reporting layers.

Applicable root, Cosyn and native `AGENTS.md` plus native `CLAUDE.md` were read. No native plan/wiki
`AGENTS.md` or template exists; `plan/INDEX.md`, `wiki/INDEX.md`, the accepted runtime-alias plan and
the generic diagnostic-generator-name knowledge page were inspected. Plans/wiki are development
memory only and are not evaluation inputs.

Current source evidence:

- `ContractRuntimeCampaignRunner.RunAsync` transforms and reparses at lines 163-199. Only parser
  errors leave `ModuleSigs` null and produce `Diagnostic parsing failed`; this occurs before
  compilation and sample population, so zero sample counters do not localize the syntax defect.
- `ContractRuntimeObligationTransformer.Transform` inserts the root runtime bridge into
  `sources[0]` at byte zero and inserts the default-module alias there as well. Named-module aliases
  are found by scanning tokens for the next textual `{`.
- Dafny grammar `Dafny` accepts all `include` directives before its top-declaration loop. A generated
  module/import placed before an existing include is therefore not a valid transformed preamble.
- `ModuleDefinition.BodyStartTok` is the parser-owned public body-opening origin for literal named
  modules. `Program.RawModules` and exact `FullDafnyName == "PbtRuntime"` selection are the existing
  canonical declaration seam; `ContractSourceSnapshot.Find` maps its resolved `Origin.Uri` to the
  immutable supplied snapshot without guessing a file name.
- `ContractRuntimeInstrumentation.DafnySource` is the checked-in synthetic runtime source already
  appended before transformation. It has no user include preamble and supplies the canonical
  top-level `PbtRuntime` and `PbtRandom` modules.
- `ContractRuntimeGeneratorSignatureTests` already provides bounded string-backed source,
  runtime-append and parse/resolve helpers, plus exact canonical runtime declaration-reference
  assertions. It has no directory, process, compiler, solver, synchronization or cleanup path.
- Existing include coverage in `ContractEntryTests` does not run the runtime transformer and does
  not cover bridge placement.

## Design

Resolve the unique canonical top-level runtime module by exact full resolved identity, then locate
its source snapshot through that declaration's `Origin.Uri`. Emit the fresh top-level bridge and a
fresh literal default-runtime façade module at byte zero of that synthetic runtime snapshot rather
than an arbitrary public `sources[0]`. The façade imports `Runtime` from the bridge and exports that
module. In named user modules, the fresh local alias imports the bridge module itself. Set one common
emitted runtime path, `PbtRuntimeAlias.Runtime.PbtChecks`: default/file contexts resolve the global
literal façade, while named contexts resolve the local alias to the bridge. Both `Runtime` members
must dereference to the exact canonical `PbtRuntime`; neither path duplicates or wraps any trusted
runtime implementation. Keep allocating `runtimeBridge` and `runtimeAlias` through
`ContractBodyNames.Family`. Do not identify snapshots by `PbtRuntime.dfy`, source list position,
regex, line scanning or unverified local names.

For each source-backed non-default module, insert its local alias immediately after the resolved
module's `BodyStartTok`. Do not scan the token stream for a brace; module attributes, qualified
modules, refinements/replacements and nested or file-scoped declarations remain governed by the
parser's recorded body origin. Default/file module declarations have no textual body opening and use
the globally visible façade instead. Keep excluding the canonical runtime/random modules from
instrumentation exactly as today.

The generated bridge, façade, local-alias graph and common reference path change as described above.
Their final canonical `PbtRuntime`/`PbtChecks` identity, obligations and trusted implementation remain
unchanged. `Apply` continues to compute transformed hashes from
the resulting bytes. Do not mutate request snapshots, `ContractRuntimeSourceMap`, the prepared
program/source identity, `originalSourceSetHash`, the pinned runtime resource, proof fingerprints or
certificates. No fallback parser recovery or diagnostic suppression is permitted.

## Change table

| Exact owner file/symbol | Planned change, necessity and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan; `plan/INDEX.md` | Register the bounded owner scope, readiness gate, preservation claims and checks before implementation | Markdown links, status and recursive Markdown-only audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs::Transform` bridge/default façade placement and `RuntimeChecks` | Resolve the exact top-level `PbtRuntime` declaration and its authoritative source through `Origin.Uri`; place the bridge and one fresh literal façade there. The façade imports/exports the bridge's `Runtime`; use the uniform `<runtimeAlias>.Runtime.PbtChecks` path without duplicating a declaration or implementation. Without this, arbitrary first-source include preambles can be made unparsable; a runtime-file import is invisible elsewhere and duplicate per-file aliases are rejected | Named/default/cross-file/source-order public memory cases; re-resolved exact bridge/façade `Runtime` imports and every emitted function/method call's canonical ownership |
| Same symbol, named-module alias insertion | Replace the forward textual brace scan with `ModuleDefinition.BodyStartTok`; point the fresh local alias at the bridge module so the common `.Runtime.PbtChecks` path works in named scopes. Without this, insertion location depends on token text rather than the parsed module boundary | Attributed/nested named-module control within the bounded named case; local alias binds the bridge, its `Runtime` binds canonical PbtRuntime, and emitted calls bind canonical members |
| `Source/DafnyTestGeneration.Test/ContractRuntimeGeneratorSignatureTests.cs` | Add four one-scenario facts: include-bearing first source with a named goal, include-bearing first source with a default-module goal, cross-file default-module emitted code in include-linked helper/goal files, and reordered dependency/goal sources. Parse supplied sources, select the exact generator, transform, then parse/resolve transformed sources entirely in memory; assert canonical declaration identity and unchanged public preamble behavior | Exact class filter, no filesystem/temp directory/process/compiler/solver/fsync; inspect every helper call path before execution |
| `wiki/pbt-generator-formal-names.md`; `wiki/INDEX.md` | After independent implementation acceptance, record that bridge/default façade ownership follows the canonical runtime snapshot and named aliases use resolved module-body origins, with include/source-order and evidence limits; link back to this plan | Fresh independent source/documentation review and reciprocal plan/wiki links |

No runner, instrumentation library, parser, grammar, proof, certificate, compiler, evaluator, schema or
benchmark file is planned. A parser-error-code projection being prepared separately may corroborate
or reject this public hypothesis; update this plan before any different repair.

## Public regression designs and test-boundary audit

Each new test uses `ContractSource` values with matching `ContractHarnessBuilder.Hash` values and
relative public names resolved only by `ContractSourceSnapshot`'s `SnapshotFileSystem`. The common
minimal source has `include "Helper.dfy"` as its first token, a goal, and an exact marked generator;
`Helper.dfy` contains a tiny public module, and `ContractRuntimeInstrumentation.DafnySource` supplies
the runtime. No test calls `ContractRuntimeSourcePreparation`, because the target is the transformer
placement seam rather than draft/generator installation.

1. Named module: `Main.dfy` is first, begins with the include, and contains `module M` with the goal
   and generator. Re-resolution must succeed, the include remains the file preamble, `M` imports the
   fresh alias at its resolved body boundary, and generated calls bind the exact canonical
   `PbtRuntime.PbtChecks` declarations.
2. Default module: an include-first source contains top-level goal/generator declarations. It must
   retain its parsed include preamble without receiving a local runtime declaration, and all generated
   calls through the fresh façade must bind the canonical runtime declarations after re-resolution.
3. Cross-file default module: an include-linked helper file and goal file both contain top-level
   methods whose transformed bodies emit runtime references. Neither file receives a local alias;
   both must resolve through the one façade/bridge/runtime identity in the canonical runtime snapshot.
4. Source order: place a harmless include-bearing dependency first and the named goal source later.
   Re-resolution and exact binding must not depend on whichever authorized snapshot occupies index
   zero. This separately protects ordering from target-file assumptions.

Before adding the cases, trace `Source`, `WithRuntime`, `Resolve`, `ContractSourceSnapshot.ParseAsync`,
`ContractCallableSelector.SelectMethod`, `ContractRuntimeGeneratorSignature.Select`, and
`ContractRuntimeObligationTransformer.Transform` through setup/execution/teardown. The accepted
seam uses strings, `StringReader` and in-memory dictionaries only. Do not use `tmp_path`, `tmpdir`,
`TemporaryDirectory`, `mkdtemp`, `Path.GetTempPath`, real files, compilation, subprocesses,
containers, native tools, durable writes or synchronization. Each fact receives a one-line
intention comment immediately above its decorator and covers one observable scenario.

## Compatibility, risks and preservation checks

- Dafny imports remain file-scoped across source roots whose declarations merge into the default
  module, while duplicate same-name imports are rejected. Default and cross-file regressions must
  establish global façade visibility and exact canonical binding, not merely parser success. If the
  façade's exported `Runtime` import produces cloned or wrapper runtime members, reject this design.
- Bridge/façade forward references and export visibility must resolve through ordinary module
  semantics. Tests must assert both generated `Runtime` import signatures point to the exact
  top-level runtime module, each named local alias points to the bridge module, and runtime calls
  point to the exact canonical `PbtChecks` class/members.
- The canonical runtime lookup must reject absence or ambiguity rather than fall back to a path,
  local name or arbitrary module. Preserve the existing unique exact-module expectation used by
  `ShapeExpression`.
- Generated-source placement changes transformed snapshot hashes, as any byte change must. Original
  request snapshots, hashes, source maps, clause `OriginalSourceHash`/`OriginalSourceSetHash`, trusted
  RNG/runtime inputs, generator proof fingerprints/certificates and evaluator inputs must remain
  unchanged. Review these call paths explicitly; do not normalize or relabel hashes.
- Preserve fresh private name allocation, generator/public formal names, selected generator object,
  wrapper/main names, clause ordering/count/IDs, decisions, exclusions, compiled-check discovery and
  all proof/snapshot/evidence semantics. The tests may compare relevant transformation metadata
  across source order where useful, but must not freeze incidental generated byte layout.
- Do not add heuristics, packages, exception swallowing, parser retries, source-order sorting or
  special handling based on private diagnostics.

## Validation plan

After the root owner announces this ready plan, implement the failing memory regression first and
record its generic parser diagnostics without private inputs. Use `/workspace/tmp/pbt-diagnostic-parsing-20261020/`
for non-sensitive logs only; never place artifacts in plan/wiki.

From `/workspace/cosyn/dafny`:

1. `make exe`
   - Expected: `Source/Dafny.sln` builds successfully, including parser generation, with no new
     warnings attributable to this change. This is build evidence only, not a native campaign or
     proof result, candidate compilation or generated-runtime compilation.
2. `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeGeneratorSignatureTests`
   - Prerequisite: step 1 completed successfully with the existing .NET SDK/packages. The test command
     must not restore dependencies, generate build output or compile candidate/runtime sources.
   - Expected: all bounded signature/runtime-binding memory cases pass with no skips, including the
     four new include/default/cross-file/source-order cases.
3. `make format`
   - Expected: scoped C# whitespace is clean; preserve any generic workspace-load warning exactly.
4. `git diff --check`
   - Expected: no whitespace errors.
5. `find plan wiki -type f ! -name '*.md' -print`
   - Expected: no output. Preserve any pre-existing violation unless cleanup is separately authorized.

Run the focused unit class during iteration. Run no integration/native campaign merely for this
memory-only change; if review discovers an affected integration boundary, update this plan before
running it. Known MSBuild/VSTest sandbox socket or restore limits may require the approved execution
path; preserve failed attempts and do not bypass permissions.

Fresh independent verification must start from these requirements and current repository state in
a separate context, inspect canonical declaration/source binding and all stated preservation paths,
and run its own focused checks. Only after that acceptance update the planned wiki/index, rerun
text-appropriate checks, review the complete diff against this table, and mark the plan done. Record
actual commands, SDK/VSTest versions, revision/dirty state, counts, warnings, skips and log locations.

## Progress and handoff

The root owner read and announced the ready plan at 13:52–13:53 UTC. Implementation and fresh
independent native acceptance are complete.
The current generic source evidence establishes a public include-preamble defect but does not
establish the cause of either separately observed receipt. No private data or live experiment input
will be read or changed.

Implementation evidence:

- Revision `e3cb42691e61369e231f4094d5f3340a1ee535a9`, .NET SDK `8.0.131`, MSBuild
  `17.8.49+7806cbf7b` and VSTest `17.8.0`.
- The first sandboxed `make exe` attempt exited 1 after reporting zero warnings and zero errors. The
  approved unrestricted rerun succeeded with four pre-existing warnings: two `CS0162` warnings in
  `ContractRuntimeProfile.cs`, one `CS0618` warning in `PbtObservation.cs`, and one `VSTHRD103`
  warning in `ContractPhaseTimingTests.cs`.
- The initial pre-fix no-build/no-restore class run had 29 passes and three failures. The default
  include-first regression reached the defect and observed a generated bridge before its include.
  The two named fixtures instead failed initial resolution because a contained module cannot see
  outer `PbtRandom`; add explicit fixture-local `import PbtRandom` declarations before repeating the
  pre-fix run. This was a test-input correction, not a production fallback.
- After correcting the public named fixtures and surfacing diagnostic IDs, the three pre-fix cases
  each reported `p_generic_syntax_error: this symbol not expected in Dafny`. This matches the public
  message shape of declassified numeric candidate `[160]`; it does not show that either private
  receipt source begins with an include and does not explain the additional `[89]` candidate on one
  receipt. Receipt attribution therefore remains unproven.
- The first implementation hosted both bridge and default alias in the canonical runtime snapshot.
  Named/source-order cases passed, but the default case resolved with repeated `PbtRuntimeAlias`
  unresolved errors: Dafny imports remain file-scoped across files merged into the default module.
  A second design kept only the bridge in the runtime snapshot and placed the same fresh default
  alias after each relevant file's parsed include preamble. A one-file default case passed, but a
  goal-file-only alias was insufficient for emitted calls in another default-module source.
- The per-file correction then passed a one-file default case but the cross-file case failed with
  `Duplicate name of import: PbtRuntimeAlias`. The final authorized design investigation therefore
  uses one fresh literal façade module in the canonical runtime snapshot. It is acceptable only if
  ordinary parse/resolve proves every emitted `PbtChecks` call still owns the exact original canonical
  class/member; no copied implementation, runtime-library edit or fallback is allowed.
- The bounded façade investigation failed before identity checks. An opened canonical import plus
  `export provides PbtChecks` reports that `PbtChecks` must be a member of the façade; qualified
  `export provides Runtime.PbtChecks` reports that `Runtime` is not a type that can declare members.
  Ordinary Dafny exports therefore cannot preserve `PbtRuntimeAlias.PbtChecks` through this façade.
  The known-invalid façade was removed. The authorized design C instead exports the imported
  `Runtime` module and changes one common emitted path to `PbtRuntimeAlias.Runtime.PbtChecks`; named
  aliases target the bridge module so the same path works in every module header scope.
- One intermediate test edit moved resolved-program assertions before declaring `resolved`, causing
  a C# undefined-local/duplicate-local build failure. The assertions were returned after the single
  re-resolution call before evaluating any Dafny behavior; no production workaround resulted.
- Design C resolves in all four public cases. The bridge imports `Runtime` from the exact canonical
  top-level `PbtRuntime`; the literal façade imports the bridge's `Runtime`, and both resolved import
  signatures refer to that same canonical module object. Each named local alias resolves to the
  generated bridge module object. Every generated runtime function and method call inspected after
  resolution retains the original canonical `PbtRuntime.PbtChecks` class, including exact
  `InstantiateShape` member identity in the existing collision case.
- The production diff changes only generated declaration placement, the named-module parser-owned
  insertion anchor, and the common generated runtime reference path. `Apply` still derives each
  transformed snapshot hash from its resulting content. `ContractPreparedProgram` still retains the
  input `sources`, original goal/source/hash and source map, while clause source/source-set hashes
  still come from the unchanged original location and `originalSourceSetHash` fields. No proof,
  certificate, fingerprint, runtime-library, runner, evaluator or receipt path changed.
- The first post-fix `make exe` succeeded in 24.99 seconds with the four known warnings above. The
  subsequent no-build/no-restore focused run passed 33/33 with no skips in one second. `make format`
  exited zero and reported the repository's generic workspace-load warning; it changed no additional
  files. The final incremental `make exe` succeeded in 9.39 seconds with zero warnings/errors, and
  the final no-build/no-restore focused run again passed 33/33 with no skips in one second.
- `git diff --check` passed. `find plan wiki -type f ! -name '*.md' -print` produced no output.
  No native/runtime candidate compilation, solver, campaign, container, paid provider, private-data
  access or live-input mutation occurred. A fresh independent native verifier accepted the current
  source and public regression behavior; `/workspace/tmp/pbt-diagnostic-parsing-20261020/verify-native.md`
  is the acceptance record.
  The planned wiki/index now record the common two-hop graph and receipt-attribution limitation.
  Commit and parent gitlink publication remain parent-owned.
