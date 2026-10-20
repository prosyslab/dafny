# Diagnostic generator names

Status: formal/local, module-member, private runtime-alias and diagnostic-preamble repairs
independently accepted, 2026-10-20.
Current diagnostic-repair baseline: `e3cb42691e61369e231f4094d5f3340a1ee535a9` plus the accepted
working-tree changes. Earlier validation snapshots below remain historical evidence for their
named scopes.
Originating plans: [formal/local names](../plan/2026-10-20-pbt-generator-formal-collisions.md),
[module members](../plan/2026-10-20-pbt-generator-member-collisions.md), and
[private runtime alias](../plan/2026-10-20-pbt-runtime-alias-capture.md), plus
[diagnostic source preambles](../plan/2026-10-20-pbt-diagnostic-parsing.md).

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
across variables, members, types, constructors and modules. It finds the unique resolved top-level
`PbtRuntime` by exact full name and uses that declaration's `Origin.Uri` to place two fresh literal
modules in the authoritative synthetic runtime snapshot. The bridge imports and exports the
canonical runtime as `Runtime`; the global façade imports and exports `Bridge.Runtime`. Default/file
contexts use that façade. Each source-backed named module instead receives a same-spelling local
alias to the bridge at its parser-owned `ModuleDefinition.BodyStartTok`. One common generated path,
`Alias.Runtime.PbtChecks`, therefore works in both scopes without copying or wrapping any trusted
runtime declaration.

String emissions and the static receiver AST for generic shape instantiation share that two-hop
qualifier.
`ShapeExpression` first selects the unique module whose full resolved name is exactly
`PbtRuntime`, then derives its exact `PbtChecks` class and `InstantiateShape` function declaration.
Re-resolution must bind both generated `Runtime` imports to that exact canonical module object,
each named local alias to the generated bridge object, and generated functions and methods to the
original `PbtChecks` declaration objects. Local name equality is insufficient because user code may
contain both `M.PbtChecks` and `M.PbtRuntime.PbtChecks` competitors.

The bounded controls preserve formals named `PbtChecks`, `PbtRandom`, `PbtRuntime`,
`PbtRuntimeAlias` and `PbtRuntimeBridge`. The preferred private names freshen with the same
zero-suffix rule, and a reachable generic helper exercises `InstantiateShape`. These private names
do not alter the returned generator signature, the public `PbtRandom` API/import, target contracts,
runtime obligations, proof scope or certificate authority. The transformer changes generated
insertions and replacements only; it does not broadly rewrite original user expressions.

Generated top-level declarations must not precede a user source's `include` preamble. The canonical
runtime snapshot is synthetic and contains no user include, so it owns the bridge and façade
regardless of supplied source order. Named aliases use the resolved body-opening token rather than
searching text for a brace. Public memory-only controls cover an attributed include-first named
module, an include-first default module, emitted runtime calls in both files of an include-linked
default module, and a named goal after an unrelated include-first source. They parse, transform and
re-resolve without directories, compilation, solver execution or durable writes; the two default
files share the global façade and receive no duplicate file-scoped import.

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

The diagnostic-preamble follow-up was accepted by a fresh independent native review. Owner
validation on revision `e3cb42691e61369e231f4094d5f3340a1ee535a9` used .NET SDK `8.0.131`,
MSBuild `17.8.49+7806cbf7b` and VSTest `17.8.0`. `make exe` passed; its first full affected build
reported the four known unrelated warnings and the final incremental build reported none. The exact
memory command
`dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeGeneratorSignatureTests`
passed 33/33 with no skips. `make format`, `git diff --check` and the recursive Markdown-only audit
also passed; formatting retained the existing generic workspace-load warning.

No native solver, generated campaign compilation/execution, benchmark or paid provider ran for this
scope. The evidence establishes the reviewed binding and in-memory transformation behavior; it does
not establish generator proof acceptance, live campaign effectiveness or a result for any frozen
evaluation. The public pre-fix include cases produced the generic Dafny parser message corresponding
to candidate code `160`; this is consistent with one separately reviewed receipt projection, but
does not prove that either private receipt had a leading include or that this repair changes either
receipt. The other projected candidate code `89` remains unexplained. No private receipt was replayed.
Active evaluated images/packages remain unchanged. The alias audit had no accepted
pre-alias source artifact matching the earlier supplied hash, so it makes no cryptographic
chronology claim about preserved legacy reachability hunks; its acceptance covers the current
source behavior and exact alias changes described above.
