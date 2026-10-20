# Avoid capture in diagnostic generator names

Status: done; bounded formal/local-name repair independently accepted, module-member collisions remain separate.
Date: 2026-10-20

## Objective and observable acceptance

Continued source review for the user's PBT interface work found impossible required signatures for
valid targets named `Goal(r: int)` or instance `Goal(receiver: (int, bool))`: fixed diagnostic names
collide with target input names, which Dafny preserves in the same formal scope. Runtime wrapper
locals `pbtRandom`/`pbtOutput0` create another capture point. Make exact reported generator signatures
authorable without changing any target formal, input order/tuple shape, contract or proof scope.

Acceptance: ordinary generators retain `r` and implicit `receiver`; colliding diagnostic formals get
deterministic fresh names. One shared naming/formatting helper drives reported signatures and strict
preparation validation. The runtime wrapper and heap receiver lookup use the same implicit-receiver
identity, and private wrapper locals avoid all program names. A static `r` input retains its exact
original requires/output binding in synthesized generator proof source. Existing fingerprint,
complete-coverage, trusted RNG and internal certificate rules remain intact.

## Boundaries and inspected evidence

Owner: native Dafny. Baseline `8e5652221199a2ac4414d225266ef92d62965fd5` plus the independently
accepted installed-draft attribution patch; preserve that source, plan and wiki work. Root/Cosyn/
native instructions and `CLAUDE.md` apply; no additional scoped instructions/templates were found.
Read only current public generic source/tests and these records, never private candidate/evaluator
data, prior benchmark solutions or historical task records. Active evaluated images/packages/inputs
remain frozen. This is a source-backed generic defect, not an explanation of trial1's agent failure.

Evidence: runner lines around99 builds fixed `r`/`receiver` signatures; preparation ValidateGenerator
around187 insists on the same names; native resolver shares the in/out formal scope; obligation
transformer around502 uses fixed receiver/RNG/output locals; CapturedEntry around490 looks up a
fixed receiver. Existing `ContractBodyNames.Family` is the reusable capture-avoidance helper. Native
proof projection already calls the generator positionally and binds exact output identities/types.

Related: [Cosyn refinement](../../plan/2026-10-20-pbt-observed-interface-refinement.md),
[root experiment](../../../plan/2026-10-20-csplit-pbt-main-experiment.md), and
[accepted draft attribution](2026-10-20-pbt-installed-draft-evidence.md).

## Change table

| Exact owner file/symbol | Change, purpose and unmet behavior | Validation |
| --- | --- | --- |
| This plan; `plan/INDEX.md` | Register scope, state and actual checks | Markdown/diff audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs` new `ContractRuntimeGeneratorNames` and `ContractRuntimeGeneratorSignature.Names/Format`, `ValidateGenerator` | Reserve exact target input names; retain legacy diagnostic names if free, otherwise append `0` deterministically. One formatter supplies the required signature and validation expects that exact shape | Memory-only ordinary/colliding static/instance/tuple preparation controls |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` missing signature and receiver presence | Reuse shared signature formatter and implicit-receiver name; preserve every target/check/request binding | Native build and source/callsite review |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` wrapper construction and instance input capture | Destructure validated generator output names, use capture-avoiding implicit receiver consistently for dispatch/capture and private wrapper RNG/output names from existing name family | Resolve transformed in-memory snapshots for colliding explicit names; preserve noncolliding evidence keys |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs::CapturedEntry` | Look up the same named implicit receiver, avoiding collision with explicit input `receiver` | Source review plus safe pure lookup control if its complete call path is in memory |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs`, `ContractGeneratorProofTests.cs`, new bounded `ContractRuntimeGeneratorSignatureTests.cs` if needed | Cover normal compatibility, static `r`, instance tuple `receiver`, private wrapper-name capture and exact synthesized original-requires binding. Add no generated-campaign fixture | Trace helpers first; snapshot parser/transform/proof-source projection only, no tempdirs/process/native compilation/solver/sync |
| `wiki/pbt-generator-formal-names.md`, `wiki/INDEX.md` | Record response-authoritative naming, compatibility, binding and limits | Fresh independent source/documentation review and links |

## Validation and approvals

From `/workspace/cosyn/dafny`, run supported `make exe`, selected memory-only classes using
`dotnet test Source/DafnyTestGeneration.Test --no-build --filter` with exact class-name terms, then
`make format` and `git diff --check`. Record actual filter/case counts and tool versions. Inspect
complete test helpers/assembly initialization first; do not run any generated-campaign/native-compile
test. Use approved local build/test execution if sandbox MSBuild or VSTest socket restrictions
prevent the supported commands. Add no dependency or cleanup/reset of shared build state. Logs and
synthetic evidence belong in `/workspace/tmp/pbt-generator-formal-collisions-20261020/`.

Fresh independent verification starts from requirements/current state in another context and reviews
canonical capture/lookup/binding plus unchanged fingerprints/checks before running its own bounded
owner checks. No solver success or live efficacy is inferred from parsing/build exits. Preserve
all policy, budgets, request/result schemas, source contracts, RNG pinning and internal omission
authority. No extra paid experiment, image rebuild/retag, commit or publication is requested.

## Progress and next action

Implementation and local validation are complete at native HEAD
`8e5652221199a2ac4414d225266ef92d62965fd5` with the accepted installed-draft changes preserved in
the working tree. `ContractRuntimeGeneratorSignature.Names/Format` now reserves target input names,
strict preparation validates those exact names, the runner advertises the same signature, and runtime
capture/heap lookup share the fresh implicit receiver identity. Transformer-private RNG and result
locals use `ContractBodyNames.Family`; proof support remains static-only and the existing explicit
`receiver` exclusion for native heap evidence remains unchanged.

Validation from `/workspace/cosyn/dafny` with .NET SDK `8.0.131`:

- `make exe` — passed with four pre-existing warnings and no errors after the initial sandboxed
  MSBuild attempt exited 1 with no diagnostic; the approved elevated run passed. Final log:
  `/workspace/tmp/pbt-generator-formal-collisions-20261020/make-exe-final.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter
  'FullyQualifiedName~ContractRuntimeGeneratorSignatureTests'` — 6 passed, no skips. An initial run
  exposed an over-escaped test assertion while showing correct generated source; the corrected final
  run passed. Final log: `/workspace/tmp/pbt-generator-formal-collisions-20261020/signature-tests-final.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter
  'FullyQualifiedName~ContractGeneratorProofTests'` — 117 passed, no skips; log:
  `/workspace/tmp/pbt-generator-formal-collisions-20261020/proof-tests.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter
  'FullyQualifiedName~ContractRuntimeSourcePreparationTests'` — 20 passed, no skips; log:
  `/workspace/tmp/pbt-generator-formal-collisions-20261020/source-preparation-tests.log`.
- `make format`, `git diff --check`, and recursive non-Markdown inspection of `plan/` and `wiki/` —
  passed; no non-Markdown files were present. Format log:
  `/workspace/tmp/pbt-generator-formal-collisions-20261020/make-format-final.log`.

These checks parse, resolve, transform, and fingerprint bounded in-memory sources. They do not invoke
the Dafny solver, native campaign compilation, a generated campaign, an experiment, or a paid
provider, and they do not extend RuntimeTypeEvidence or instance generator-proof support. Native wiki
documentation remains deferred until fresh independent review. Next action: a fresh verifier should
start from the requirements and current repository state, review exact binding and unchanged proof/
evidence exclusions, then run its own bounded checks. Cosyn owns generic guide updates explaining that
exact returned formal names govern; do not edit parent guidance from this native plan.

## Independent acceptance and bounded closure

Fresh independent verification accepted shared ordinal exact-name allocation/formatting, strict signature validation, preserved explicit inputs/tuple shape, matching receiver keys through main/nested capture and heap lookup, and private wrapper-name freshening. Public prepared-source constructor/deconstruction, existing heap/type-evidence exclusion, production proof gates/fingerprints/source bindings/trust/certificates/RNG pins remain unchanged. Approved `make exe` passed with zero warnings/errors; seven selected memory-only regressions passed without skips, nonmutating format verification and diff checks passed. Initial sandbox MSBuild/VSTest socket failures and successful approved reruns are retained in `/workspace/tmp/pbt-generator-formal-collisions-20261020/verify.md`. No solver, generated campaign or benchmark was run or inferred.

Durable findings: [diagnostic generator formal names](../wiki/pbt-generator-formal-names.md). This bounded plan is complete. Separately confirmed fixed module/default-class `Generate` and `PbtMain` collisions are outside its acceptance and require a new plan; named-class members do not share that insertion namespace. Parent observation/refinement work remains in progress and active treatments are frozen. Preserve uncommitted development source and logs; no commit, image change, dependency or paid retry was made.
