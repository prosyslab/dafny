# Preserve generator identity with fresh module member names

Status: done
Date: 2026-10-20

## Objective and acceptance

Continued user-requested PBT checks confirmed two separate namespace defects after the accepted
formal/local-name repair. A target module/default class containing `Generate` cannot accept the
required diagnostic generator, and a module/default-class `PbtMain` conflicts with the runtime
wrapper. Named-class methods such as `C.Generate`/`C.PbtMain` occupy a different namespace and must
not trigger freshening. Choose deterministic module-member names while preserving legacy names
when available, and carry the exact selected generator identity through execution and proof.

Acceptance: original module `Generate` yields diagnostic `Generate0` (then `Generate00` as needed),
the reported signature and strict preparation agree, and the prepared choice is selected only by
exact target marker/module/source URI/expected name with an unambiguous resolved Method. Wrapper
emission and returned MainName use one pre-insertion fresh name. Existing normal names remain
unchanged. Synthesized proof source invokes the actual chosen generator and original requires;
wrong marker/name/source or arbitrary marked methods fail. No target contracts/formals, supported
proof scope, obligation set, certificate authority or fingerprint inputs are weakened.

## Ownership, evidence and boundaries

Owner: native Dafny, baseline `8e5652221199a2ac4414d225266ef92d62965fd5` plus accepted draft
provenance and formal/local-name working-tree patches. Preserve those files and records. Read
root/Cosyn/native instructions and `CLAUDE.md`; no additional scoped instructions/templates were
found. Only current public generic source/tests/these records are allowed; no private candidate,
model, evaluator, historical benchmark or reference data. Fixed live images/packages/inputs and
three-trial budgets remain unchanged. These source defects are not diagnoses of trial1's failure.

Inspected evidence: SourcePreparation formatter/ValidateGenerator/AddHelper; runner generatedMethod
selection; transformer constructor certificate lookup, DiagnosticReachable, wrapper call and MainName;
proof SupportedSelectedGoal and existing dynamic generator.Name admission source; raw proof audit's
URI/name/marker binding and certificate reference/source/semantic/options/solver/coverage matching.
Reuse the exact module/default-class namespace set already used by ModuleNames. Whole-program
ContractBodyNames.Family is appropriate for private locals, but changes names for unrelated scopes
and is not the right compatibility rule for these module members.

Related: [formal/local-name repair](2026-10-20-pbt-generator-formal-collisions.md),
[Cosyn refinement](../../plan/2026-10-20-pbt-observed-interface-refinement.md), and
[root experiment](../../../plan/2026-10-20-csplit-pbt-main-experiment.md).

## Change table

| Exact owner file/symbol | Change and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan; `plan/INDEX.md` | Register scope, states, evidence and checks | Markdown/diff audit |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs` naming helper, prepared metadata, validation | Add canonical fresh module-member selection, method name in generated naming metadata, additive init-only GeneratorMethodName on prepared sources, and strict resolved selector. Compute before insertion, preserve positional constructors/deconstruction where practical and all original input checks | Memory-only legacy/Generate collision/marker/name/source controls |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Replace name-only lookup with strict selector using prepared chosen name; thread the exact resolved Method through proof, missing-helper discovery and transformer | Source identity/callsite review and owner build |
| `Source/DafnyTestGeneration/ContractTesting/ContractDiagnosticConstruction.cs::AuditResolved` | Add a source-compatible overload accepting the exact selected generator; run omitted-ghost-field auditing on that generator closure after strict selection. Otherwise an original Generate shadows the actual Generate0 during this safety audit | Memory-only selected-generator closure/omitted-state regression and production call-path inspection |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` constructor, reachability, wrapper | Accept/thread exact selected generator; use it for reachability, certificate matching and invocation. Generate PbtMain fresh in exact module namespace before insertion and return identical qualified MainName. Preserve source-compatible overloads without a new production fallback | Pure transformed-source resolve for existing/target PbtMain, unrelated named-class members, and bound generator reachability |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs::SupportedSelectedGoal` | Require canonical chosen method name reconstructed while excluding only that exact resolved generator plus marker/module/source identity, preserving every existing proof restriction | Memory-only dynamic Generate0 proof-source projection and negative bindings; raw audit/certificate logic unchanged |
| `Source/DafnyTestGeneration.Test/ContractRuntimeGeneratorSignatureTests.cs`, `ContractGeneratorProofTests.cs` | Cover normal names, repeated namespace collisions, later sibling helper, arbitrary marked name rejection, wrong marker/source, fresh wrapper and exact dynamic admission binding | Trace existing helpers before extending: bounded string-backed parse/prepare/transform/proof-source only, no solver/process/tempdirs/native compilation/fsync |
| Same two memory-test files, exact selected `M.Generate` and `M.PbtMain` scenarios | Close the independently identified acceptance coverage gap: existing cases select M.Goal and exercise only sibling/callee collisions. Select each colliding goal itself through preparation, strict selection, transformation/resolve and proof admission/original-requires projection | Bounded in-memory scenarios for each exact target; no production change or native solver/campaign; independently rerun affected classes |
| `wiki/pbt-generator-formal-names.md`, `wiki/INDEX.md` | Update the existing generic naming page with accepted module-member behavior and remaining limits | Fresh independent source/documentation review and resolving links |

## Design constraints and risk controls

Keep module/default-class namespace scope exact. Do not exclude names by spelling or exclude every
marked method; only the exact selected resolved object may be excluded when reconstructing the
canonical name for proof validation. Earlier names in the deterministic chain must remain occupied,
and successful preparation forbids siblings sharing the chosen name. The chosen name must not be
recomputed after insertion without this exact-object exclusion.

Production must never fall back to an unrelated name-only method. The selector starts from exact
target marker/module/source identity and validates its expected canonical name. Thread that same
Method before constructor-time reachability/certificate decisions, not only at Transform time.
Legacy helper overloads may preserve source compatibility but cannot relax marker/certificate
requirements or grant omission through a name-only fallback. If existing synthetic test fixtures
need exact marker annotations, identify additional files and extend this plan before editing them.

The reserved diagnostic-name guard may exempt only the literal `PbtMain` followed by zero or more
zeroes, so existing source members can coexist with a fresh wrapper. These user members must keep
ordinary instrumentation and obligations; this exception grants no runtime-intrinsic authority.
Preserve rejection of all other reserved `Pbt` names, `__pbt_` fragments and `pbtTypeShape` names.
Review these trust boundaries and exercise negative controls in the bounded signature tests.

Preserve SourceMap, original program/source identities, request/result schemas, native RNG pinning,
internal certificate matching and full check coverage. No change to ContractGeneratorProofAudit
logic is planned; existing dynamic-name raw audit is reused. Parent Cosyn owns guide wording that
the exact reported method/random-source/receiver names govern; native does not edit parent files.

## Validation and approvals

From this root run supported `make exe`, `dotnet test Source/DafnyTestGeneration.Test --no-build`
with the exact selected memory-only signature/proof class filter after tracing all helpers, then
`make format`/`git diff --check`. Record actual filters, counts, tool versions and warnings. Approved
execution may be needed for known sandbox MSBuild/VSTest socket limits. Add no dependency and do
not delete/reset shared work/build state. Logs belong in
`/workspace/tmp/pbt-generator-member-collisions-20261020/`, never plan/wiki.

Fresh independent verification uses requirements/current repository state in a separate context,
reviews all identity/proof boundaries and runs its own bounded checks. No solver, generated native
campaign, paid provider, benchmark, image build/retag, commit or publication is requested. Build and
parse success do not establish native proof acceptance or live effectiveness.

## Progress

Follow-up requirement audit found no source defect for goals themselves named `Generate`/`PbtMain`.
The two bounded theories now select those exact targets through preparation, strict selection,
transformation/resolution and proof admission/original-requires projection. They required no
production change and preserve the accepted implementation and all proof restrictions. The earlier
independent 142-case acceptance remains evidence for its previous 22-signature/120-proof snapshot;
the new owner-tested snapshot is 24 signature and 122 proof cases and still needs fresh review.

Implementation and bounded local validation are complete and independently accepted; status remains
in-progress pending fresh review of the planned native wiki and parent guide closeout. The additional call-path audit found and repaired diagnostic
construction's legacy Generate reachability: the runner now selects first and passes the same exact
Method through an additive audit overload, while the legacy overload remains source-compatible.
The implementation chooses and reserves the canonical
generator member from the original module before draft insertion, carries the exact marked Method
through proof/reachability/certificate/invocation paths, and freshens the wrapper entry point across
the complete `PbtMain`/zero-suffix family. The existing transformer constructor retained its prior
positional shape with one trailing optional exact Method, including source compatibility for an
explicit fourth `null`; production supplies the exact Method and does not use the legacy fallback.

Validation used .NET SDK 8.0.131 and VSTest 17.8.0 from `/workspace/cosyn/dafny`:

- `make format` passed after the final edits; log
  `/workspace/tmp/pbt-generator-member-collisions-20261020/make-format-complete.log`.
- `make exe` passed with zero errors and four pre-existing warnings in unrelated runtime-profile,
  observation and phase-timing files; log
  `/workspace/tmp/pbt-generator-member-collisions-20261020/make-exe-complete.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter FullyQualifiedName~ContractRuntimeGeneratorSignatureTests`
  passed 22/22 with no skips; log
  `/workspace/tmp/pbt-generator-member-collisions-20261020/signature-tests-complete.log`.
- `dotnet test Source/DafnyTestGeneration.Test --no-build --filter FullyQualifiedName~ContractGeneratorProofTests`
  passed 120/120 with no skips; log
  `/workspace/tmp/pbt-generator-member-collisions-20261020/proof-tests-complete.log`.

The first signature-suite run exposed the old broad reserved-name guard rejecting `PbtMain` before
freshening. The final guard exempts only names in the exact generated main family (`PbtMain`
followed only by zeroes), retains every other reserved diagnostic-name rejection, and the repeated
collision case now resolves in memory. `TestContractsCommand.ExecuteAsync` already maps the strict
selector's intentional `NotSupportedException` failures to structured unsupported results in both
worker and supervised modes, so no broader runner catch was added. The first added guard-control run
used an unresolved random-source type before adding the runtime source and expected a redundant
assertion that Dafny eliminated; the corrected controls use a shape-independent marked method and
observe the preserved call-precondition obligation for the user `PbtMain`. Exact-generator omitted
ghost-field auditing now rejects a use reachable only from `Generate0`, while negative controls
retain `PbtChecks`, `PbtRandom`, other `Pbt` prefixes, `__pbt_` fragments and `pbtTypeShape`
rejections. No solver, native campaign,
generated native compilation, process-backed test, temporary-directory test, paid provider,
benchmark, image, dependency or commit was used. No durable wiki finding was published before
independent acceptance. After that acceptance, `wiki/pbt-generator-formal-names.md` and its index were
updated with the durable exact-name contract and limits. Parent observation plans remain in-progress
until their documentation review and authorized three-trial reporting work are complete.

Fresh independent implementation verification reviewed the current requirements and source without
receiving implementation conclusions. It accepted exact member selection, construction auditing,
proof/certificate binding, wrapper freshening, reserved-name guards and preservation of the earlier
draft/formal patches with no findings. Its approved `make exe` rerun completed with zero warnings and
errors; the combined exact signature/proof filter passed 142/142 memory-only cases; nonmutating
formatting passed with one generic workspace-load warning and no changes; `git diff --check` and the
recursive plan/wiki Markdown-only audit passed. It ran no solver, native campaign, generated native
compilation, benchmark, paid provider or image operation. Audit:
`/workspace/tmp/pbt-generator-member-collisions-20261020/verify.md`. The updated documentation is now
ready for a fresh generic guide/source review; this plan is not marked done before that acceptance.

The planned documentation closeout also updated only the three parent-owned generic guides listed in
the parent plan. From `/workspace/cosyn`, `make lint` reported all 205 files formatted and Ruff clean;
root and native `git diff --check` passed; recursive root/native plan/wiki extension audits found no
non-Markdown files. Log:
`/workspace/tmp/pbt-interface-refinement-20261020/exact-generator-name-guide-lint.log`. No functional
or integration suite was repeated for text-only changes, and the concurrent parent I8 lifecycle
implementation/tests were untouched.

The selected-target coverage follow-up used the same bounded in-memory classes after a supported
owner build. `make exe` passed with zero errors and the four known unrelated warnings; the signature
class passed 24/24 and the proof class passed 122/122, both with no skips. `make format` passed with
the known generic workspace-load warning and no formatting changes; `git diff --check` and the
recursive plan/wiki Markdown-only audit passed. Logs are
`/workspace/tmp/pbt-generator-member-collisions-20261020/make-exe-selected-target.log`,
`signature-tests-selected-target.log`, `proof-tests-selected-target.log`, and
`make-format-selected-target.log`. These tests used no solver, native campaign, generated native
compilation, process, temporary directory, synchronization call, dependency, paid provider,
benchmark or image. Fresh review of these four new theory rows is now accepted with no findings.
Independent `make exe` passed with zero warnings/errors; the exact selected-target filter passed4/4
and the complete two-class filter passed146/146 with no skips. The five production hashes match
the earlier accepted snapshot exactly. The reviewer traced original `goal.Req` substitution,
generator ensures and admission assertion through the actual resolved generator name. Audit:
`/workspace/tmp/pbt-generator-member-collisions-20261020/verify-selected-target-followup.md`.
The wiki now records24signature/122proof cases and the independent146case follow-up; final
documentation review remains pending before this plan is marked done.

Final independent documentation/source/usability closeout is accepted with no findings. The native
wiki, indexes and parent exact-name guides reconcile 24 signature + 122 proof cases, all 146 cases,
the four direct selected-target rows and the historical 142-case snapshot. Links resolve; production
hashes are unchanged and no solver/campaign/live-effect claim is made. Audit:
`/workspace/tmp/pbt-interface-refinement-20261020/verify-exact-name-guides.md`. No functional suite
was repeated for this wording review. Acceptance criteria and required bounded checks are complete;
parent three-trial observation/reporting continues under its own in-progress plans. No commit,
dependency, image, benchmark or active treatment was changed by this scope.
