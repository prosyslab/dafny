# Avoid runtime-class capture in diagnostic instrumentation

Status: done
Date: 2026-10-20

## Objective and acceptance

Continued user-requested PBT interface checks found a source-backed capture defect: a valid goal
input named `PbtChecks` becomes a generator output/main local and copied wrapper formal, while
generated instrumentation uses unqualified `PbtChecks.*`. Dafny resolves those variables before
the runtime class. Preserve every original input/name/type/order/contract and resolve generated
checks through a deterministic fresh alias to the canonical runtime module. Do not reject valid
formals or alter target checks to hide the defect. This is not a diagnosis of any frozen trial.

Acceptance: bounded in-memory preparation, transformation and re-resolution succeeds with target
inputs `PbtChecks`, `PbtRandom`, `PbtRuntime` and a name colliding with the preferred private alias;
all emitted runtime calls bind the original canonical `PbtRuntime.PbtChecks` declarations. A reachable
generic helper exercises AST-generated `InstantiateShape` binding as well as string emissions.
Include a competing nested user module `M.PbtRuntime`, not merely a competing class: select the
exact unique top-level runtime module by full resolved name and assert reference identity against
its exact class/function in the transformed program. Matching only local `.Name` fields is insufficient.
Unchanged normal inputs retain observable behavior, generator signatures and required check scope.
All proof/fingerprint/certificate/source/trusted-RNG boundaries remain unchanged.

## Ownership and inspected evidence

Native owner: current `8e5652221199a2ac4414d225266ef92d62965fd5` plus independently accepted
draft provenance and generator formal/member working-tree patches. Preserve those changes.
Read root/Cosyn/native AGENTS and CLAUDE instructions; no plan/wiki scoped instructions or template
were found. Only current public generic source/tests and these current task records are permitted;
no private candidate/model/evaluator/reference/history or benchmark data. Parent experiments retain
all frozen inputs/images/packages/budgets. No live provider/native campaign is authorized here.

Evidence: `ValidateGenerator` preserves explicit input names; transformer wrapper/main/local/check/
location/serialization emissions use PbtChecks; its `ShapeExpression` constructs a static receiver
AST. `PreTypeResolve.Expressions` resolves local/formal scope before static/module members.
`PreTypeResolve.Statements` resolves declaration RHS before installing locals: no equivalent current
PbtRandom capture is established, and PbtRuntime is currently only an import, so those are compatibility
controls. Reuse `Microsoft.Dafny.ContractBodyNames.Family` in `Source/DafnyCore/ContractTesting/`
to freshen across all variable/member/type/constructor/module names. Do not invent naming heuristics.

Related: [accepted member names](2026-10-20-pbt-generator-member-collisions.md),
[Cosyn observation](../../plan/2026-10-20-pbt-observed-interface-refinement.md),
[root experiment](../../../plan/2026-10-20-csplit-pbt-main-experiment.md).

## Change table

| Exact file/symbol | Change, purpose and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan and `plan/INDEX.md` | Register scope before implementation, record checks and acceptance | Markdown/diff audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` runtime qualifier/imports/emissions/ShapeExpression | Allocate one program-fresh runtime module alias; insert explicit alias imports in each instrumented source module; qualify every generated runtime-check reference including the resolved static receiver AST. Keep actual callable/type ownership canonical and preserve original source expressions/strings | Memory-only positive capture regression, canonical resolved-call binding and generic-shape control |
| Same transformer private bridge emission and canonical import target | A nested M.PbtRuntime also captures a textual import inside M. Emit a fresh top-level bridge that resolves the canonical runtime at the root; instrumented modules import through that globally fresh bridge path. Do not change public module/generator/RNG interfaces or insert any trusted proof assumption | Re-resolve nested competitor control and assert emitted import/call references reach the exact canonical runtime declaration, not merely matching names |
| `Source/DafnyTestGeneration.Test/ContractRuntimeGeneratorSignatureTests.cs` | Add bounded exact-formal and preferred-alias collision cases using existing string-backed prepare/parse/transform/resolve helpers; cover reachable generic shape emission | Trace all helpers first; no solver, native compilation, filesystem/tempdirs, subprocess or sync |
| `Source/DafnyTestGeneration.Test/ContractRuntimeGeneratorProofTests.cs` if affected existing assertions need qualification | Preserve meaningful runtime proof/check assertions while adapting only private qualifier expectations; no weaker assertions or test removal | Review helper boundaries before running; only memory-only tests may run |
| `wiki/pbt-generator-formal-names.md`, `wiki/INDEX.md` | Add accepted private-runtime alias behavior and source/binding limits after fresh review | Independent source/docs review; link this plan |

## Constraints, risks and approvals

Replace generated expressions, not user source by broad textual substitution. Centralize the
runtime class qualifier and update every emission path, including deghost fallbacks, location,
capture, contract/domain checks, serialization and generic shape AST printing. A hard-coded
`PbtRuntime.PbtChecks` qualifier would instead be captured by a PbtRuntime formal. The fresh alias
must be absent across source scopes; its AST receiver must print the alias while retaining the
exact resolved canonical class/function. Do not change embedded runtime source, RNG imports or
public generator signatures. Audit unused opened-import dependencies before removing open import.

No benchmark input narrowing, reserved-name expansion to formals, verification skip, trust
assumption, helper-contract change, proof-admission/coverage weakening or name-only certificate
fallback. No changes to active/queued treatment, provider budgets, dependencies, commits or images.
The user authorized repeated generic checks/fixes; no extra paid use or new approval is needed for
this internal compatibility repair. Extend this table before any additional production/test file.

## Validation

From `/workspace/cosyn/dafny`, first add and run the bounded memory regression to confirm the
source-backed failure (catch/report expected resolver diagnostics in test assertions, never private
data). Then run supported `make exe`, exact signature/proof memory class filters and any separately
traced affected runtime-proof class; finish with nonmutating format check and `git diff --check`.
Expected: successful canonical module/class/function binding and no check loss, no skips. Known
MSBuild/VSTest sandbox startup/socket limits may need approved execution; preserve failed attempts.
Artifacts/logs belong in `/workspace/tmp/pbt-runtime-alias-capture-20261020/`, never plan/wiki.

Fresh independent verification starts from requirements/current state in a separate context and
runs its own checks. No live/generated native campaign, solver, benchmark, paid provider, image,
dependency or commit. Parser/build success does not establish generator certification or live
effectiveness. Finish wiki and plan/index only after independent source and documentation acceptance.

## Progress

The bounded `PbtChecks: int` reproduction first failed during transformed-source resolution because
the generated unqualified calls resolved to that formal. Diagnostics included missing `Location`,
`Generated`, `InputValues`, `SerializeNamed`, `Complete`, `Check`, `BeginCheck`, heap-capture and
stop members on `int`; the approved rerun is recorded in
`/workspace/tmp/pbt-runtime-alias-capture-20261020/initial-repro.log`. The first sandboxed build
attempt stopped during restore, so it supplied no behavioral evidence.

The transformer now allocates `PbtRuntimeAlias` through `ContractBodyNames.Family`, imports that
fresh alias to the canonical `PbtRuntime` module in every instrumented source module, and emits all
runtime-check references through one private qualifier. `ShapeExpression` prints the same alias in
its static receiver type while retaining the resolved canonical class and function. Its lookup now
requires the `PbtRuntime` module as well as the `PbtChecks.InstantiateShape` names, so a user class
with the same class/function names cannot become the generated callable. No user text is broadly
rewritten, and public generator/RNG signatures and imports are unchanged.

The four memory-only theory rows cover inputs `PbtChecks`, `PbtRandom`, `PbtRuntime` and
`PbtRuntimeAlias`; the last freshens the private alias to `PbtRuntimeAlias0`. Each uses a reachable
generic helper and a competing user `PbtChecks.InstantiateShape`, re-resolves the transformed
sources, and asserts that emitted runtime methods/functions are owned by canonical module
`PbtRuntime`. The existing `ContractRuntimeGeneratorProofTests` assertion remains meaningful with
the private prefix and needed no source edit.

Owner validation from `/workspace/cosyn/dafny` used the existing .NET SDK and packages:

- `make exe` passed with zero warnings and zero errors; log `make-exe.log`.
- The final serial `ContractRuntimeGeneratorSignatureTests` filter passed 28/28 with no skips; log
  `signature-tests-final.log`.
- The final serial `ContractRuntimeGeneratorProofTests` filter passed 2/2 with no skips; log
  `runtime-proof-tests-final.log`.
- `make format` passed with one generic workspace-load warning and no remaining format diff; log
  `make-format.log`.
- `git diff --check` and the recursive plan/wiki Markdown-only audit passed with no output.

All named logs are under `/workspace/tmp/pbt-runtime-alias-capture-20261020/`. The current production
file SHA-256 is `18fbd3257b190f2042c9c4955e9835561b5606cc06e9b744962247fd5ca43219` for
`ContractRuntimeObligationTransformer.cs`; the bounded signature-test file SHA-256 is
`bf2669d84e0b98e3bdc0d5b44a8bbe39afe7774b8329fdb4477ab82888092cad`. Validation used no solver,
native campaign, generated native compilation, test subprocess, temporary directory, filesystem
synchronization, benchmark/private/history input, dependency, paid provider, image or commit.
Source is ready for fresh independent verification; status remains in-progress and wiki/index
closeout remains deferred until that acceptance.

Initial independent review ran green bounded classes but found the canonical-binding requirement
unmet: ShapeExpression and its tests selected module/class/function by local names, allowing a
nested M.PbtRuntime to compete with the top-level runtime. The scope remains the same production
and signature-test files; strengthen exact module/declaration selection and the nested competitor
regression before independent acceptance. No proof/coverage requirement is relaxed.

The finding fix first selected the unique module whose `FullDafnyName` is exactly `PbtRuntime`, then
derived the exact `PbtChecks` class and `InstantiateShape` function objects from that module. The
nested regression exposed a second part of the same binding defect: a direct `import Alias =
PbtRuntime` inside `M` resolves to the nearer `M.PbtRuntime`. That run failed all four rows during
transformed-source resolution with missing runtime members on the competing class. The redirected
log was inadvertently overwritten by a later passing rerun; a clearly labeled diagnostic excerpt
and this provenance limitation are preserved in
`/workspace/tmp/pbt-runtime-alias-capture-20261020/nested-module-direct-alias-failure.md`.

The authorized private bridge now resolves `PbtRuntime` once at the top level, exports that exact
module through its `Runtime` alias, and lets each instrumented module import a globally fresh bridge
path. Both the emitted qualifier and bridge name use `ContractBodyNames.Family`, preventing any
original variable/member/type/constructor/module scope from shadowing them. The five theory rows
include the four runtime-looking inputs plus a preferred bridge-name collision, a same-named user
class, and nested `M.PbtRuntime.PbtChecks.InstantiateShape`. Re-resolved calls assert reference
identity with the exact canonical top-level module-derived class and function, rather than local
name equality. Original expressions, runtime exclusions, proof policy, legacy reachability, public
generator/RNG interfaces and every runtime check remain unchanged.

Post-fix owner validation:

- The focused five-row nested/alias/bridge theory passed; log `nested-module-finding-fix.log`.
- `make format` passed with the generic workspace-load warning and no remaining formatting diff;
  log `make-format-finding-fix.log`.
- The final `make exe` rerun passed with zero warnings and zero errors; log
  `make-exe-finding-fix-rerun.log`. The preceding successful build had one transient shared-output
  copy retry warning and is retained as `make-exe-finding-fix.log`.
- Final serial signature tests passed 29/29 with no skips; log
  `signature-tests-finding-fix.log`.
- Final serial runtime-generator-proof tests passed 2/2 with no skips; log
  `runtime-proof-tests-finding-fix.log`.
- `git diff --check` and the recursive plan/wiki Markdown-only audit passed with no output.

The post-fix production SHA-256 is
`cfa72ff764598228ab340e2bb9022efe3604342a923538bbfde2aead08def086`; the signature-test SHA-256 is
`ddbc52a2127de8e2c60bf60db6e0d103d1b8734c388053fa0beb84201afb0780`. No solver, native campaign,
generated native compilation, test-spawned process, temporary directory, filesystem synchronization,
dependency, private/model trace, benchmark input, paid provider, image or commit was used. The fix
is pending fresh independent verification; wiki closeout remains deferred.

The strengthened nested-module regression authorized the same-file bridge extension after showing
that, even with exact AST lookup, `import Alias = PbtRuntime` inside `M` resolves to
`M.PbtRuntime`. The completed bridge implementation and checks above address that finding within
the authorization; existing runtime exclusion/proof-scope policies and unrelated legacy
reachability remain unchanged. The nested failure remains evidence rather than an accepted result,
and the fix remains pending fresh independent review.

## Independent source acceptance and documentation handoff

Fresh independent review first requested exact top-level ownership instead of local-name matching,
then accepted the bridge follow-up with no remaining source finding. Its fresh build passed with
zero warnings and errors. The bounded memory filters passed 29 signature, 122 proof-source and two
runtime-proof cases, 153 total with no failures or skips. Targeted nonmutating formatting passed
with the existing unmatched-metadata workspace warning and no changes; `git diff --check` and the
recursive root/Cosyn plan/wiki extension audits passed. Audit:
`/workspace/tmp/pbt-runtime-alias-capture-20261020/verify.md`.

The review establishes the current fresh bridge, exact canonical declaration binding and preserved
runtime/proof boundaries. It ran no solver, native campaign, generated compilation, provider,
benchmark, image or frozen trial. It also records that no accepted-baseline source artifact matched
the supplied pre-alias hash, so it makes no cryptographic chronology claim about legacy transformer
hunks. The current source review confirms the alias work leaves legacy reachability behavior
unchanged.

The planned native wiki page and index now document the accepted behavior, five namespace controls,
historical 146-case member snapshot and current 153-case alias snapshot. This plan remains
in-progress until that documentation receives fresh review; no functional suite was repeated for
the prose-only closeout. Native and parent `git diff --check` passed, and recursive native/parent
plan/wiki extension audits found no non-Markdown files.

Fresh independent documentation review accepted the native plan/index, native wiki/index and
parent plan/index against the accepted source and its own 153 memory checks. It confirmed the
historical 142/146 snapshots, current 153-case evidence, exact canonical binding, frozen-trial
limits and explicitly reconstructed failure excerpt. No source or test changed after acceptance,
and no functional suite was repeated for this prose-only closeout. All acceptance criteria are
complete; the source remains an uncommitted development refinement and is absent from the frozen
three-trial experiment. Audit: `/workspace/tmp/pbt-runtime-alias-capture-20261020/verify.md`.
