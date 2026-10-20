# Diagnostic generator names

Status: formal/local, module-member and private runtime-alias repairs independently accepted,
2026-10-20; this wording awaits fresh documentation review.
Source baseline: `8e5652221199a2ac4414d225266ef92d62965fd5` plus the accepted draft-provenance
and generator-naming working-tree changes.
Originating plans: [formal/local names](../plan/2026-10-20-pbt-generator-formal-collisions.md),
[module members](../plan/2026-10-20-pbt-generator-member-collisions.md), and
[private runtime alias](../plan/2026-10-20-pbt-runtime-alias-capture.md).

The complete `missingGenerator.signature` is authoritative. Copy its generator method name,
random-source formal, implicit receiver output and explicit target outputs exactly. The ordinary
names remain `Generate`, `r` and `receiver` when free. The engine appends `0` until a diagnostic
name is fresh: an existing module/default-class `Generate` produces `Generate0`; an explicit input
named `r` produces random-source formal `r0`; and an instance target with an explicit input named
`receiver` uses implicit receiver output `receiver0`. Explicit target input names, types, order and
tuple arity never change.

Generator member freshening uses the target module/default-class namespace computed before any
draft or generator helper is inserted. Named-class methods such as `C.Generate` occupy a different
namespace and do not cause freshening. The wrapper entry point follows the same deterministic rule
for `PbtMain`, `PbtMain0`, and so on. Existing user members in that exact zero-suffix family retain
ordinary instrumentation and obligations; all other reserved `Pbt` names, `__pbt_` fragments and
`pbtTypeShape` names remain rejected.

Preparation reserves the chosen generator member while installing drafts, so a helper cannot take
the already reported name and silently shift the generator. Strict selection requires one resolved
method in the target module's default class with the expected canonical name, exact
`pbt_generator` target marker and the goal source URI. Canonical reconstruction excludes only that
exact resolved object. The runner carries the same object through missing-draft discovery, proof
construction, diagnostic-construction auditing, transformer reachability, certificate matching and
the emitted invocation. In particular, omitted ghost-field auditing follows `Generate0` rather
than an unrelated original `Generate`.

`ContractRuntimeGeneratorSignature.Names/Format` also chooses the capture-free random-source and
implicit-receiver identifiers. The transformer destructures the validated outputs, dispatches and
captures through the chosen receiver identity, and uses private wrapper RNG/output names from
`ContractBodyNames.Family`. Runner completeness and heap lookup use the same identity. The existing
explicit-`receiver` heap/type-evidence exclusion remains; these changes do not add heap proof
support.

Generated runtime instrumentation has a separate private namespace rule. A valid target formal
named `PbtChecks` remains unchanged; it must not capture generated calls such as `Check`,
`CaptureHeap`, `SerializeNamed` or `InstantiateShape`. The transformer allocates both a local
runtime alias and a top-level bridge name through `ContractBodyNames.Family`, which reserves names
across variables, members, types, constructors and modules. The bridge resolves the canonical
top-level `PbtRuntime` before an instrumented module can shadow it with a nested `PbtRuntime`, then
exports that exact module through its private `Runtime` alias. Each instrumented module imports the
fresh bridge path and all generated runtime calls use the fresh local alias.

String emissions and the static receiver AST for generic shape instantiation share that qualifier.
`ShapeExpression` first selects the unique module whose full resolved name is exactly
`PbtRuntime`, then derives its exact `PbtChecks` class and `InstantiateShape` function declaration.
Re-resolution must bind generated functions and methods to those same declaration objects. Local
name equality is insufficient because user code may contain both `M.PbtChecks` and
`M.PbtRuntime.PbtChecks` competitors.

The bounded controls preserve formals named `PbtChecks`, `PbtRandom`, `PbtRuntime`,
`PbtRuntimeAlias` and `PbtRuntimeBridge`. The preferred private names freshen with the same
zero-suffix rule, and a reachable generic helper exercises `InstantiateShape`. These private names
do not alter the returned generator signature, the public `PbtRandom` API/import, target contracts,
runtime obligations, proof scope or certificate authority. The transformer changes generated
insertions and replacements only; it does not broadly rewrite original user expressions.

Proof statements belong inside whichever marked generator method the response names, and distinct
sibling helpers belong in the same complete declaration file. The proof gate binds the exact
resolved object, default-class/module/source, marker and canonical name while retaining all earlier
signature, type, ghost, termination and authored-requires checks. The raw proof audit, source and
semantic fingerprints, option and solver identity, helper closure, complete native check coverage,
internal certificate authority and pinned random source remain unchanged.

Relevant production sources are `ContractRuntimeSourcePreparation.cs`,
`ContractRuntimeObligationTransformer.cs`, `ContractDiagnosticConstruction.cs`,
`ContractGeneratorProof.cs` and `ContractRuntimeHeapChecking.cs` under
`Source/DafnyTestGeneration/ContractTesting/`, plus
`Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`. Additive prepared-source and
generator-name properties preserve the existing positional constructor/deconstruction shapes, and
legacy overloads remain source-compatible; production uses strict exact selection.

For the module-member work, owner validation built with four unrelated warnings and zero errors and
passed 24 signature plus 122 proof-source memory cases. The original independent 142-case result is
a historical snapshot. A test-only follow-up added four direct `M.Generate`/`M.PbtMain` cases and
independently passed all 146 cases with a zero-warning/error build and unchanged production hashes.
That accepted 146-case member result is also a historical snapshot relative to the later runtime-
alias source; it remains the evidence for the member-only boundary.
Audits: `/workspace/tmp/pbt-generator-member-collisions-20261020/verify.md` and
`verify-selected-target-followup.md`.

The private runtime-alias source was independently accepted after an initial review found that
local module-name checks did not prove canonical ownership. The accepted follow-up includes the
fresh root bridge, exact top-level module/class/function selection and declaration-reference
assertions. A fresh build passed with zero warnings and errors; 29 signature, 122 proof-source and
two runtime-proof memory cases passed, for 153 total with no skips. Targeted nonmutating formatting
passed with one existing workspace-load warning and no changes; diff and Markdown-only audits
passed. Audit: `/workspace/tmp/pbt-runtime-alias-capture-20261020/verify.md`.

No native solver, generated campaign compilation/execution, benchmark or paid provider ran for this
scope. The evidence establishes the reviewed binding and in-memory transformation behavior; it does
not establish generator proof acceptance, live campaign effectiveness or a result for any frozen
evaluation. Active evaluated images/packages remain unchanged. The alias audit had no accepted
pre-alias source artifact matching the earlier supplied hash, so it makes no cryptographic
chronology claim about preserved legacy reachability hunks; its acceptance covers the current
source behavior and exact alias changes described above.
