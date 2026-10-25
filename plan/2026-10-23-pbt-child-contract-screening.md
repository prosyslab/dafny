# Draft native child-contract screening owner contract

Status: done — delivered on expecto in `b531cdc0f`/`fff2a462c` via [reviewed main delivery](2026-10-25-pbt-reviewed-main-delivery.md); image/runtime acceptance remains root-owned
Date: 2026-10-23
Owner: native Dafny contract-testing query/service/CLI
Requirements: [Cosyn screening design](../../plan/2026-10-23-pbt-child-contract-screening.md)
Related: native frontend (`2026-10-23-pbt-agent-frontend-native.md`, removed 2026-10-25)

## Implementation release, 2026-10-23 09:25 UTC

The latest user explicitly prioritizes implementing early child-helper contract
screening and continuing the same3serial×90-minute csplit scope. Root releases
source implementation in `/workspace/tmp/pbt-agent-frontend-baseline-20261023-r01/native`,
anchor5fa47c6e949dad736db25e02b5edad95d0b0be1a with preserved current overlays.
The earlier draft sections below are retained as design history; this section
supersedes their no-implementation-release statements. Root owns canonical docs,
actual build operations, fresh independent verification and integration experiments.

### Same-module pure dependency projection increment

The source investigation confirms no existing Boogie pruning or checker API can
establish ambient consistency by itself. Release a small internal two-parse
projection in the already named `ContractScreenSourcePreparation.cs`: resolve a
private contracts-only program for native dependency discovery (never translate/
certify its full ambient declarations), then parse fresh original snapshots and
retain only the selected same-module ordinary target, its supported pure logical
closure and required ordinary module/default-class skeletons before resolution.
Unrelated classes/globals/modules may be removed; required class/global/state or
unsupported import/refinement dependencies remain explicitly unsupported.

Match raw declarations through exact original URI/kind/span identity. Use existing
`Members.RemoveAll` then `SetMembersBeforeResolution`, and prune `SourceDecls`/
`PrefixNamedModules` with `PreResolveSnapshotForFormatter` refresh for affected
module/file views. Both merged DefaultModuleDef and program.Files views require
consistent pruning; keep original raw ownership objects. Re-resolve and verify
every retained logical/type/call binding against the discovered native identity,
and audit the complete final retained ambient set for unexpected declarations.
The same exact projection must apply in checker and every generated query reparse;
retain only native-owned query bodies bound by source/span identity. Bind original
full bytes plus retained identity set/projection-policy digest. This adds no Core
mutation API and does not unfreeze the four current Core leaves.

Ordinary source/parser options remain globally constrained because they can affect
the private parses. Trust/consistency/definedness and termination checks apply to
the complete retained closure; removed declarations supply no axioms or evidence.
The projected result makes no claim about full original-workspace consistency.
General cross-module/import/export/refinement slicing remains outside this slice.

### Independent review corrections, 2026-10-23 10:05 UTC

Independent current-source review requires preserving actual dependency-check
options and exact generated query identities in returned diagnostic evidence.
Release additive `dependencyOptionsIdentities` on the result and `queryIdentities`
on cases, both bounded lists with default-empty compatibility for unexecuted
paths. Native query fingerprints bind actual emitted query bytes/name/source and
effective options, using the existing hash machinery; no user-supplied claims.
Retain each completed dependency module's effective options rather than replacing
them with an unbound aggregate. Coordinate the matching strict Cosyn DTO/validator
fields before packaging. This extends the already named model/service/solver
files and their pure tests; it does not create proof-input certificates.

The old public `ContractQueryBuilder.Build` accepts ContractRealization with
sampled outputs and a generic postcondition assertion. No production caller uses
that kind; explicitly reject it in this old builder and direct callers to the
native-owned screen existential route. Add the exact existing
`Source/DafnyTestGeneration.Test/ContractQueryTests.cs` to the change table for
removing its two obsolete realization InlineData rows; do not run the whole mixed
class or add a test solely asserting feature absence. The new screen controls
establish real realizability semantics. Other old Build behavior is unchanged.

Release screen-local recursive canonical numeric spelling for duplicate finite
map/set input validation before reusing the existing codec, without changing
legacy semantics or original echoed cases. Numeric strings1and+1cannot represent
two distinct map/set keys after native normalization. Add one pure map and one
pure set boundary case. Also correct the Driver's new nullable-context warning
within its already owned TestContractsCommand file. Current compiled outputs
remain historical until the settled correction is compiled and checked.

The exact first vertical service has `inspect` and `screen` actions through
`test-contracts --screen-contract`. Reuse existing snapshot/codec/query/checker/
solver/fingerprint APIs, with additive internal projection/checking overloads.
Do not require completion of the separate four-operation material frontend.

Freeze v1 request fields: schemaVersion, action, sources, target (existing
ContractEntry restricted to static nongeneric/unit), dependencies (identities,
never trust overrides), question, binding, cases and budgets. Inspect has no
binding/cases; screen requires the exact returned binding and unique ordered case
IDs with exact input-formal names. Cases contain no outputs/assertion text.
Questions are input_domain, method_realizability, lemma_implication and explicitly
unsupported caller_sufficiency. Budgets are attemptMilliseconds<=30000 and
queryMilliseconds<=5000; retain32cases/1MiB aggregate request and64KiB diagnostics.

Binding fields are sourceSetHash, targetIdentity, declarationFingerprint,
contractFingerprint, contextIdentity, preparationPolicyVersion, producerIdentity
and optionsIdentity. The result carries schemaVersion/action/question/status,
binding/capability/cases/counts/diagnostics. Capability reports supported,
reasonCodes, supported features and certificationPending. Solver-free inspection
sets certificationPending=true; it does not certify logical premises.

Keep separate attempt/domain/property enums from this design. A stale binding is
invalid_input with stable stale_binding reason. Preserve all ordered cases when
deadlines/cancellation interrupt processing. Finite positive results are local
diagnostics; no sampled bad output or raw failed proof/SAT becomes a violation.

Checkpoint1 implements strict models, precise pre-resolution Method/Lemma body
omission (new Method.ClearBody), scalar ambient/source admission, query/service/
identity/outcome plumbing and separate CLI. Checkpoint2 extends recursive finite
seq/string/set/multiset/map values and supported pure resolved expressions.
Checkpoint3 admits every retained ordinary transparent pure function/predicate
only after complete noncircular logical/termination/definedness certification.
Expression-only functions are the initial logical increment. Proof callees require
the original proof-body closure projection, never erased-body certification;
otherwise return unsupported. Broader paths may be implemented together when
they share the same audited machinery, but scalar success alone is not readiness.

The exact file table below is released, including new strict models/service/source
preparation and selected Core Method/fingerprint/options helpers. Add optional
pure `ContractScreenModelTests`, `ContractScreenServiceTests` and separately
classified native controls only after tracing the complete effects graph. Source
writes are isolated; preserve accepted DTO files and legacy behavior. No new
dependency, trust skip, benchmark change, automatic stability heuristic or commit.
Implementation agents may inspect additional relevant public sources as necessary;
no private trace/evaluator/task solution is an implementation input. Resolve API
details from actual code, not guessed AST fields. If a needed source owner falls
outside the table, report it to root before edit.

Actual Core/TG builds use the related build owner plan; keep Coco/normal generation
enabled and preserve previous outputs before replacement. Final real controls and
fresh independent acceptance remain mandatory. This release is permission to
implement, not evidence that source/query/runtime or csplit coverage works.

## Certified positive proof shortcut and seed release

Matched-default Z34.16.0controls reproduce r02's unresolved identity timeout;
the impossible joint-output negative control passes. Preserve r01/r02/r03as
failed or partial populations, with no inferred individual positive-query outcome.
An independent native source review establishes that an opposite failed proof
adds no mathematical consistency certificate in this restricted path. Root now
releases a narrow classifier change: AFTER the existing complete projection,
logical/termination/definedness certification and constructive input admission,
return immediately on a completed positive UNSAT proof with complete native WD/
coverage/provenance. Do not launch its opposite. A positive Sat still requires
a completed negative Unsat for rejection/violation; Sat alone is never a witness.
Unknown/timeout/error of any actually attempted query remains unchanged and
visible. No already observed timeout is erased or retrospectively reclassified.

Make the case-decision helper's certified-context precondition explicit and keep
it internal to native orchestration/tests if appropriate. Preserve every existing
ambient/input/WD/original-assertion guard. Replace unreachable dual-positive test
expectations with a realistic no-opposite-query positive control; retain actual
negative, missing provenance, timeout/error and certification-failure controls.
Use existing reasonCodes for bounded closed per-query obligation/polarity/outcome
codes so actual outcomes are recorded even when final hashes are unavailable;
do not fabricate unexecuted query evidence. Provenance describes actual queries:
positive domain1, rejected precondition2, admissible positive property2total,
admissible negative property3total. Coordinate strict Cosyn count validation.

The new command currently does not inherit ordinary verification seed42. Release
the narrow existing-pattern typed `--verification-seed` CLI option, default0,
bounded to Int32.MaxValue and bound to DafnyOptions.RandomSeed. This is the same
Boogie RandomSeed used by ordinary `--boogie=/randomSeed:42`, not a new proof
mechanism or SMT seed substitution. Cosyn's native screen adapter supplies its
existing fixed verification-seed constant42 for both inspect and screen. Keep
default legacy runtime behavior unchanged; bind actual effective options through
existing identities. Native controls explicitly pass42 after rebuild. No Core
change or broad arbitrary --boogie option is needed.

The already named Service/Models/Query tests/Driver and Cosyn adapter/model/test
owners cover this change. Rebuild settled TG/Driver and the bounded memory runner;
then fresh independent source/actual positive and strict-negative controls under
the same5squery/30sattempt limits. Broader controls, explicit bad logical-function
admission and ill-defined-clause controls remain required before experiment use.
No benchmark input narrowing, trust assumption, verification skip or time-limit
increase is authorized by this change.

### Fresh r04 native semantic control release

After the frozen new TG/Driver build identities are known, release independent
actual controls in distinct maintenance scratch
`/workspace/tmp/pbt-child-contract-screening/native-controls-r04/` with the same
controls.py/manifest.json/results.json and per-invocation bounded request/result/
log leaves as r01. Existing r01/r02/r03 remain immutable. Use the actual compiled
Driver, maintained packaged Z34.16.0 and explicit --verification-seed=42; bind
Core/TG/Driver/solver before and after. No binary/source writes during population.
All prior12scenario/2case/3KiB/5squery/30sattempt/60sprocess and finite artifact
bounds remain. No generator, runtime compile, provider, task/evaluator input,
filesystem fixture lifecycle or synchronization is part of these checks.

First run bodyless identity and impossible joint outputs. If identity remains
undecided, stop the broader population and report actual closed query outcome
codes without inferring outcomes from hashes. If both expected semantic outcomes
pass, continue the remaining already-required correlated/zero-output/lemma/
requires/definedness/nested-values/pure-closure/body-omission/stale/bad-function/
termination controls within12source scenarios. Use source variants only where
needed to distinguish natural positive and strict-negative cases. Solver-free
inspect seed parsing controls reuse the same tiny source: default0,42,Int32.MaxValue
and overflow, with no extra source population or solver invocation. A process
exit never establishes a semantic or provenance pass by itself.

### Correlated-output quantified solver correction

Actual independent r04controls preserve12source scenarios/29CLI invocations,
62passing assertions and one unmet expected result: the correlated positive
`y == x`, `z == y + 1` at x7remains property-timeout. Identity, impossible joint
outputs, lemma/zero-output/requires, typed nested values, projection, stale binding,
bad logical function, nontermination and original definedness gates pass their
specific controls. These are diagnostic populations, not benchmark scores.

Source inspection confirms the original full joint existential and exact native
reducer witness obligations remain. Positive top-level existential queries use
default MBQI=false, while negated quantified assertions already enable MBQI.
Root releases the smallest static native profile correction in existing
ContractSolver.cs: extend that option gate to positive top-level ExistsExpr ONLY
when screenQuery is nonnull. Keep legacy query behavior, original assertion,
certification, constructive membership, WD/coverage, deadlines and effective
options identities unchanged. This is a hypothesis until actual checks pass;
neither the timeout nor a failed positive proof means unrealizability.

After the one-leaf freeze, rebuild settled TG/Driver with distinct r05artifacts.
Fresh independent controls-r05 must first check correlated positive, then identity,
joint impossible outputs, quantified/nested values, bad logical admission and
ill-defined clauses under seed42and unchanged limits. Preserve all r04outcomes.
No time increase, alternate solver, sampled-output shortcut, source assumption or
query weakening is authorized. Existing pure memory sources remain unchanged;
independent runtime checks focus on the changed quantified solver boundary.

### Witness-guided positive profile refinement

Independent r05records7source scenarios/14CLI calls/10case outcomes. Correlated,
identity, Unicode/empty string and nested seq<string> output realizability pass,
and bad logical admission remains blocked. However impossible outputs and both
original undefined-expression cases now time out on the positive query;32checks
pass and2control groups remain unmet. Preserve every outcome. The all-positive-
existential MBQI profile is too broad for this bounded diagnostic path.

Release one-leaf ContractSolver refinement using existing native reduction
metadata solely as solver guidance. Preserve public void ReduceConcreteAssertion
as a compatibility wrapper; add a private core returning eligibility only when
exactly one processed query method's ORIGINAL assertion is a Dafny ExistsExpr,
reduction.Decision is True, ReducedExpression is literal true, no budget exhausted,
and an explicit ProofWitness expression was actually emitted among Kind.Witness
native assertions. Calculate the flag after the existing final cancellation/AST
publication checks. Apply MBQI AFTER reduction iff the unchanged legacy negated-
quantifier gate, or screenQuery is nonnull and this guidance flag is true.

This exact reduction does not certify semantics or definedness. Every original
assertion, native witness/prerequisite assertion, WD/coverage/certification/input
gate and deadline remains mandatory. No acceptance from reducer booleans, guessed
witnesses, retry, solver/time increase or legacy profile change. Caller audit is
one production call and two existing statement calls; the wrapper preserves API.
No Core/DTO/test or decision-history changes are needed.

After the one-leaf freeze, rebuild TG/Driver into distinct r07artifacts and refresh
the finite actual facade runtime manifest without unnecessary facade rebuild.
Fresh independent controls-r06 repeats only the changed-boundary r05population,
including correlated/collection positive, joint-impossible negative, original
division/index WD and bad logical admission, seed42and unchanged bounds. Native
acceptance is still pending until these expected outcomes pass.

## Bounded native control and memory-check release

Root releases a diagnostic-only first native control population against the
compiled pre-correction Core/TGr02/Driver outputs, preserving their producer
identities and never treating them as current-source acceptance. Exact invocation
is `dotnet exec --additionalprobingpath /home/vscode/.nuget/packages N/Binaries/DafnyDriver.dll test-contracts <request.json> --screen-contract`.
The existing `/usr/bin/z3` is resolved through minimal PATH; record its actual
version and exact executable hash before conclusions. No runtime compilation,
generator, provider or ordinary target execution is allowed. Native snapshots
remain in memory. Existing Binaries may need runtime host probing, not copied
package/toolchain trees. The CLI reads a bounded request file and emits JSON;
solver child communication is stdin/stdout with logging disabled.

Use distinct maintenance scratch
`/workspace/tmp/pbt-child-contract-screening/native-controls-r01/` with exact
`controls.py`, `manifest.json`, `results.json`, `<id>-inspect-request.json`,
`<id>-inspect-result.json`, `<id>-screen-request.json`, `<id>-screen-result.json`
and one bounded raw log per invocation. At most12tiny source scenarios/3KiB each,
at most2cases per scenario,1MiBrequest/response,64KiBdiagnostics,30sattempt/5squery,
60sexternal process,2MiBlog per invocation/16MiBtotal/256entries. Precreate the
one owner scratch directory as maintenance preparation, not a per-test fixture.
No source files, runtime build trees, file/directory fixture lifecycles or sync.
Preserve every failed/unsupported/unknown/timeout process and typed outcome;
do not silently retry or interpret exit0as a semantic pass. Before broadening a
scenario population, record the reason and exact new population separately.

Required first controls are bodyless int identity, impossible joint outputs,
correlated outputs, zero outputs, true/false lemmas, false requires, undefined
division/index, nested strings/collections and retained pure function closure
amid unrelated removed declarations, body-semantic omission and stale binding.
Combine only natural questions within one small source scenario; retain clear
per-case question/expected result labels. Failing native setup is a blocker, not
a semantic failure. These controls may find corrections before the final freeze.

The16current memory facts have an independently inspected bounded pure helper
graph. Root may prepare a distinct ordinary SDK console runner in
`/workspace/tmp/pbt-agent-frontend-native-build-20261023-r01/child-screen-memory-r01/`:
`ChildScreenMemory.csproj`, `Program.cs`, `inputs.json`, restore/build logs/results
and final run logs/results. Compile only the two named new test classes plus the
runner, use the current real TG/Core and existing exact xUnit managed references,
no package/project refs or test-host/fixture hooks. The runner serially invokes
only declared Facts (and explicit InlineData if subsequently planned), preserves
failures, caps diagnostics/output64KiB, and never writes inside test cases.
Normal SDK restore/build is separate maintenance before any test invocation,
under existing offline config/process/tree bounds. Include changed facts and
actual binary/source identities in a fresh manifest; no old pass applies.

## Independent feasibility review and owner choices, 2026-10-23 06:54 UTC

### Preferred contracts-only preparation, source design follow-up

Two bounded AST/API passes confirm a more usable proposed first route: parse a
fresh immutable snapshot with `ContractSourceSnapshot.ParseAsync(resolve:false)`,
capture original declaration/body spans, then omit only exact ordinary Method/
Lemma implementation slots BEFORE ProgramResolver.Resolve. Do not remove
function/predicate bodies, logical proof statements, by-method links, constructors,
iterators or extreme/two-state semantics. Preserve all original headers/logical
declarations and apply the complete raw/resolved ambient/header gate. This is
private diagnostic query preparation, not a changed source submission or proof.

Early removal prevents ordinary bodies' resolution/rewriter/call-graph and
translation artifacts. Clearing bodies only after resolution does not undo them;
dropping Boogie implementations is also too late. The existing
ClonerButDropMethodBodies drops every cloned BlockStmt and is unsuitable unchanged.
Method currently has a nullable private body/Body but a nonnullable SetBody
parameter; propose an explicit narrow ClearBody API. Root spot checks actual
Method.cs, Snapshot.ParseAsync and Cloner.cs (92fa49/5fbe84/b0b29a/bc2743).
No API or query was implemented/executed by these inspections.

Require explicit input/output types (`IsTypeExplicit`/SyntacticType); body-driven
inference remains unsupported. Full original text must parse, but the projected
program resolves contracts only: invalid original body semantics can be omitted,
so success cannot claim full original-source resolution/verification. A fixed
diagnostic options profile must reject source/per-module options and plugins;
parsing can apply source options before body omission. Preserve standard system
declarations introduced during parsing; never exempt user declarations by name.

Before mutation capture native original ranges because EntireRange may be lazily
derived from children. Bind complete original bytes including omitted bodies,
omission policy/version plus exact omitted declarations/spans, projected contract
context, generated query and effective options. Projected facts must be labeled
contracts-only; do not fabricate original resolved body facts or proof inputs.
Every diagnostic reparse must use this route and retain only the exact native-
owned generated query body by snapshot/location and fresh declaration identity,
never a caller-supplied keep-body name. Reject unexpected user declarations or
reintroduced implementation bodies after resolution.

With this audited route, arbitrary ordinary original bodies need not satisfy a
body-statement allowlist: they are parsed and omitted before resolution. If the
route or its safeguards is unavailable, keep such cases unsupported rather than
silently fall back to late body deletion. Original-source dependency certification
must never use erased bodies; the scalar checkpoint still rejects logical calls.
Actual header-preservation, no retained body axioms, definedness, joint existential,
noncircular lemma and native identity/option controls remain required. Status is
draft; general workflow/native readiness is not established.

A fresh requirement/current-source review inspected21public production leaves,
516565bytes, without implementation claims, tests or native execution. It found
that this draft is not ready: snapshot identity, effective context identity,
typed dependency outcomes, independent construction/global admission and ambient
consistency need explicit owner changes. The exact change table below now names
those dependencies. No code or capability is released by this clarification.

Select a deliberately narrow first implementation checkpoint: built-in `int`,
exact system `nat`, `bool`, `char` and `bvN`, ordinary static nongeneric methods
and ordinary lemmas, with empty frames. `real` is not a ContractValue kind.
Collections, datatypes, user refinements/aliases, heap state and source contract
quantifiers remain unsupported in this checkpoint. This conservative checkpoint
does not by itself satisfy general agent-workflow readiness; representative
broader child contracts require a later explicitly reviewed capability expansion.
Keep30s attempt/5s query,32cases,1MiB source/case and64KiB diagnostic ceilings as
the selected design limits, not claims of implemented defaults.

The first ambient policy must cover the complete resolved source closure retained
by translation. Exempt only the exact `program.SystemModuleManager.SystemModule`
object and identify built-in nat by exact `NatDecl` identity. Do not trust names,
paths, generated-origin markers or source attributes. Permit ordinary concrete
nonrefining modules/default classes and ordinary scalar-header methods/lemmas;
reject user functions/predicates, globals/fields/constants, types/classes/traits,
iterators/extreme declarations, imports/exports/refinements and declaration/module
attributes. Restrict source contracts to resolved scalar literals, formal/bound
identifiers, built-in unary/binary operations/conversions and conditionals; reject
calls, source quantifiers, member/heap/state expressions and statement expressions.
The query builder owns its separate output existential. Unrelated method bodies
are not evidence; the proposed pre-resolution projection above prevents their
declaration-producing constructs from reaching translation. Until that path is
audited, reject constructs that could add retained ambient definitions. Confirm
actual AST fields and full retained-declaration coverage before marking this policy ready. A dependency
certificate alone is not proof of arbitrary ambient consistency.

`AnalyzeDocument(includeSemanticFacts:true)` currently reaches a filesystem-based
SourceFingerprint overload despite the existing snapshot overload. Add an
additive snapshot path through SemanticFactsFor. Bodyless proof-input exclusion
remains intact; factor an ordinary native context identity using existing
ProofToolchainIdentity/ProofToolchainHash/ProofOptionsHash, include the actual
TestGeneration query-producer assembly, and bind effective checker/solver options
after per-query MBQI/solver changes. Keep solver-executable provenance distinct;
assembly identity is not a complete solver certificate. Do not fabricate proof
inputs or hash whole installed toolchains in tests.

Add an explicit dependency-check outcome alongside compatible Verified:
Verified/VerificationFailed/Unsupported/Timeout/Unknown/Error, from actual native
counters/coverage rather than prose. Cancellation continues through tokens;
screening distinguishes caller cancellation from its query/attempt deadline.
Initial scalar payload/membership and independent source-bound construction/global
admission precede any input equality or requires assumption. Failed construction
proof is Unknown, not an input counterexample. Remaining blockers are actual AST
coverage confirmation, concrete identity/outcome API review and real native
build/positive/strict-negative validation. Status stays draft.

## Objective, authority and acceptance

Provide an explicitly invoked, body-independent logical screen of a proposed child
contract on supplied concrete typed cases. The minimum slice covers ordinary
value-only method realizability and the existing restricted lemma implication
semantics, with per-case input-domain decisions. Reuse ordinary generated Dafny
queries, native parser/resolver, solver, and certified logical dependency scopes.
This is a maintenance design, not an evaluated turn. This document alone is
authorized here. It releases no code, command execution, dependency, new paid run,
commit, changed N3x90 configuration, proof-scope change or scheduling policy.

Acceptance for a later implementation release:

- A bodyless supported child and explicit concrete cases suffice; no generator,
  placeholder implementation, proof body, compilation or sampling is required.
- Method realizability checks the existence of all legal outputs jointly
  satisfying the complete original ensures for each admissible input.
- Lemma implication retains original clauses and certified logical dependencies,
  with no execution, assumption or dependency certification of the target lemma.
- Invalid cases, rejected requires, inconsistent premises, unsupported features,
  unknown results, deadlines/cancellation and errors cannot become positive evidence.
- Solver-free inspect/preflight and executable runtime campaigns remain distinct.
  Caller sufficiency is explicitly unsupported in this slice.
- Native source/context binding makes stale results distinguishable; evidence is
  diagnostic only and grants no proof, certificate, generator, repair or edit authority.
- Controlled memory checks and separately authorized offline native positive and
  strict-negative journeys pass before release; neither is claimed by this draft.

Non-goals: automatic input generation/distribution inference, arbitrary heap/post-state
semantics, symbolic caller weakest-precondition construction, automatic invocation,
mandatory screening after each patch, a new proof compiler, Python semantic checking,
changes to benchmark contracts/evaluators/scoring, or a universal proof of the child.

## Evidence and existing implementation

Source anchor: `/workspace/tmp/pbt-agent-frontend-baseline-20261023-r01/native`,
native revision `5fa47c6e949dad736db25e02b5edad95d0b0be1a` plus supplied public
overlays. These source observations must be reconciled against the eventual owner
checkout before edits; the draft does not certify checkout equivalence.

`ContractQueryBuilder.Build` fixes supplied inputs and only declares/binds output
formals when concrete outputs are supplied. `ContractRealization` currently falls
through to an ordinary postcondition assertion; it does not quantify outputs.
`BuildClosedClause` and `ContractSolver.CheckAsync` supply reusable ordinary native
query transport. The solver's `Unsat` is a completed proof of its assertion;
`Sat` is an isolated target failure, and proof-only pruning makes such failure
unsuitable as a semantic model. Both-polarity reasoning is already used by the
runtime campaign for closed clauses.

`ContractCallableSelector.SupportsLemmaContract` admits only ordinary static,
nongeneric, value-only lemmas without outputs, reads/modifies, heap state or trust
attributes. The runtime transformer omits the target lemma call and the campaign
restores original clauses, certifies their logical dependencies, and rejects a
scope containing the target lemma. That path still requires a generator. Runtime
method goals require an implementation. `test-contracts` presently accepts only
`--runtime-check`; it has no concrete-case logical screen.

Reuse `ContractSourceSnapshot.ParseAsync`, `ContractHarnessBuilder`,
`ContractModelCodec`, `ContractInitialTypeProof`, `ContractSpecificationChecker`
and its `LogicalScope`, `PendingModules`, `CheckModuleAsync`, `Accept`, and native
source/dependency fingerprints. Do not copy runtime campaign orchestration merely
to bypass its generator requirement. Logical scope acceptance remains distinct
from execution validation. Type/global inhabitance support is reusable but its
current campaign-typed entry overload needs a narrow logical-screen overload or
an internal common preparation routine, not a fabricated runtime campaign result.

## Proposed first wire and service contract

These are concrete draft choices, not registered APIs. Settle the open decisions
below and obtain independent owner review before marking ready.

- Add `ContractScreenSchema` with request/result version `1`, a separate JSON
  family using existing camel-case names and snake-case string enums. Preserve
  legacy/runtime/material versions and behavior exactly.
- `ContractScreenRequest`: schema version, immutable `Sources`, exact `Entry`,
  dependency hashes, `Question`, nonempty ordered `Cases`, and explicit budgets.
  `Entry` must be unit mode, no receiver/reachability/type arguments. Each case
  has a unique caller label and exact formal-name-to-`ContractValue` inputs.
  No outputs, generator, drafts, trusted-source override, caller expression or
  user-authored assertion field is accepted. Unknown fields are rejected.
- Questions: `InputDomain`, `MethodRealizability`, `LemmaImplication`,
  `CallerSufficiency`. The last returns `Unsupported` with
  `native_caller_obligation_unavailable`, before solver execution. InputDomain
  describes the supplied cases only; it does not claim whole-domain emptiness.
- Proposed defaults: 30,000 ms total attempt and 5,000 ms per native query;
  one serial case at a time, at most 32 cases, at most 1 MiB aggregate supplied
  source/case JSON, at most 64 KiB diagnostic text per attempt. Enforce bounds
  before parsing. These budgets are owner decisions, not existing defaults.
- `ContractScreenResult`: schema version, question, binding, capability result,
  attempt state, exact ordered case results, population counts and bounded
  diagnostics. Attempt states are `Completed`, `Partial`, `Unsupported`,
  `InvalidInput`, `Timeout`, `Cancelled`, `Error`; completed means processing
  finished, never that a property is proved. Preserve finished cases on interruption.
- Per-case domain states: `Admissible`, `PreconditionRejected`, `InvalidInput`,
  `PremiseInconsistent`, `Unsupported`, `Unknown`, `Timeout`, `Cancelled`, `Error`.
  Property states: `NotChecked`, `Realizable`, `Unrealizable`, `ImplicationHolds`,
  `ImplicationViolated`, `Unsupported`, `Unknown`, `Timeout`, `Cancelled`, `Error`.
  `NotChecked` requires a non-admissible domain or InputDomain question. There is
  no bare `Passed` and no claimed model/witness field in version 1.
- Population records supplied, admissible, rejected, invalid, inconsistent,
  decided-property and undecided cases; every case belongs to one domain bucket.
  Zero admissible/decided cases cannot support a favorable property summary.
  Preserve individual outcomes rather than collapse partial coverage into success.
- `ContractScreenService.ScreenAsync(request, options, cancellationToken)` owns
  immutable preparation, capability, certification, query sequencing and result
  production. Add an internal injected query boundary for memory tests. Public
  JSON cannot inject proof certificates or select arbitrary solver transformations.
- Extend existing `test-contracts` with mutually exclusive `--screen-contract`
  and `--runtime-check`. Dispatch strict family deserialization to ScreenAsync.
  Keep its existing structured-result convention; consumers inspect the result,
  not exit zero. No sampling/runtime worker is launched for a screen. Native
  service cancellation/deadline behavior must be demonstrated before CLI release.
  Cosyn's injected service/front-end remains owned by the matching Cosyn plan.

## Native semantic sequence and capabilities

First accept only the scalar checkpoint and conservative complete-ambient policy
above, alongside the existing necessary `SupportsLemmaContract` gate. This is a
strict subset of all pure ContractValue types. Reject references, heaps, receiver
state, nonempty frames, old/unchanged/fresh/allocated and unsupported syntax.
Do not treat broader dependency certification as sufficient ambient consistency.

1. Validate shapes, hashes, limits and names; privately parse immutable snapshots,
   capture original spans and apply the precise ordinary-body omission policy,
   then ordinarily resolve the contracts-only program under fixed diagnostic
   options. A bodyless target is allowed. Original source snapshots/contracts
   and all authoritative verification targets stay intact.
2. Compute native identity and capability. Certify original logical dependencies
   of types, requires and ensures, including proof statements and relevant globals.
   Reject target dependency/circularity. Do not certify the target body. Preserve
   original declaration identity, source/trust scope and required native checks.
3. Establish each concrete input's declared type membership and nonvacuous initial
   context using certified construction/global evidence or an explicitly sound
   unpruned consistency path. Existing proof-only SAT is not that path. No valid
   construction or certified consistency means Unknown/Unsupported, never admissible.
   An inconsistent background is not evidence that the child domain is empty.
4. Decide complete requires `P(c)` by native positive/negative assertions under
   the same certified input context. Positive UNSAT establishes admissibility;
   negative UNSAT establishes rejection. Other outcomes remain explicit. Native
   definedness errors cannot be reclassified as false. The admitted context must
   remain consistent when requires are added, since `P(c)` was established first.
5. For a supported method, generate an ordinary Dafny query asserting
   `exists y1:T1, ..., yn:Tn :: Q(c,y1,...,yn)` and its negation, under certified
   inputs/requires. `Q` is the conjunction of every original ensures. Bound-variable
   declared types retain all legal-output constraints. For zero outputs, Q is
   the predicate itself. An empty output type means no legal output; never assume
   an output value merely to form the query. Do not test individual output samples
   or prove separately satisfiable ensures with different witnesses.
6. For a supported lemma, assert the complete original ensures and its negation
   under certified inputs/requires, with the existing noncircular logical closure.
   Do not execute the lemma, assume its ensures, or import its proof result.
7. Positive UNSAT yields Realizable/ImplicationHolds; negative UNSAT yields
   Unrealizable/ImplicationViolated, only after all prior validity and native
   well-definedness gates. A negative proof at a concrete input is a diagnostic
   violation, not an executable witness. Raw SAT in either polarity is a nonproof,
   never a countermodel. Neither polarity proved means Unknown. If both polarities
   are proved, report inconsistent/error evidence, never choose a favorable result.
   Timeout/cancellation/error remains visible. Preserve complete original
   obligations through reduction and dependency validation.

Existence proofs do not synthesize implementations or establish termination.
Deciding finitely many input cases does not prove universal realizability or lemma
validity. Supplied cases do not promise random coverage or inferred distributions.
Whole-domain emptiness and parent sufficiency require distinct native obligations;
they are not inferred from rejected cases or analyzer call-site/control strings.
No caller weakest-precondition engine is added. A later caller slice must bind an
actual native caller VC/context and justified assumptions before its own release.

## Binding and authority

Result binding includes complete source/dependency content digests, selected child
resolved identity and contract/declaration fingerprints, question/cases hash, native
producer identity/version, effective options identity, logical dependency/trust role,
and generated query identity. The target body hash can be reported for provenance
but cannot be used as proof evidence. Recompute binding on changed relevant bytes;
prior results remain historical and cannot authorize a new source revision.

Reuse `DefinitionAnalysis.AnalyzeDocument` semantic facts and `SourceFingerprint`
snapshot overload. Existing `ProofInputsFor` intentionally skips bodyless targets
and returns no certificate under unsupported translation options. Record existing
proof-input evidence only when actually available with its scope. Do not invent
such a certificate, insert a placeholder body, or relax its producer to make a
screen appear certified. The new screen binding is diagnostic provenance, not a
replacement proof-input certificate. Caller sufficiency stays unsupported when
its authoritative native context is unavailable. Public trusted-source fields
cannot expand benchmark trust. Screening cannot grant coordinated repair rights,
retire a caller, verify a goal, or admit generator/runtime execution.

## Exact proposed change table

All production paths below belong to this native repository. New names are draft
owner decisions; generated parser/scanner and benchmark files are untouched.

| File/symbol | Change and reason; unmet without it | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractScreenModels.cs` (new) | Strict v1 request/result/capability/binding enums and DTOs, validation and bounded counts; no logical-screen wire exists | Pure memory JSON round trips, unknown-field/version/limit rejection, legal status combinations |
| `Source/DafnyTestGeneration/ContractTesting/ContractScreenService.cs` (new), `ScreenAsync` | Native orchestration and result producer with injected internal query boundary; runtime runner requires generator/body | Fake boundary order, polarity, stale identity, timeout/cancellation and nonvacuity controls |
| `Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs` (new) | Fresh closed-snapshot parse, raw admission, original span capture, exact ordinary-body omission, ordinary contracts-only resolution and post-gate | Headers/logical declarations unchanged; original body provenance retained; no body-derived axioms; malformed syntax versus omitted body-semantic errors distinguished |
| `Source/DafnyCore/AST/Members/Method.cs`, proposed `ClearBody` | Explicit nullable body-slot operation for privately parsed ordinary Method/Lemma, avoiding null-forgiving call or broad cloner | Only exact eligible slots removed before resolution; unsupported kinds and query ownership preserved |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryBuilder.cs`, `BuildRealizability` and screen clause builder | Ordinary Dafny existential query over all outputs and full ensures; remove `ContractRealization`'s misleading generic fallthrough by explicit routing/rejection of incompatible concrete-output arguments | Native positive/negative multiple-output/type/zero-output/WD controls; source snapshots unchanged |
| `Source/DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs`, `SupportsScalarContractScreen`; new service `ValidateAmbientProgram` | Explicit body-independent scalar capability and whole retained-program ambient gate alongside existing restricted lemma predicate | Bodyless methods; exact built-in identity; unused contradictory/recursive functions, refinements/imports/trust/options and declaration-producing constructs rejected before property queries |
| `Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs`, logical-screen preparation overload | Reuse declared input/global validity without runtime campaign facade or target body | Same existing validity semantics; false refinement/empty type/global circularity controls |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs`, shared initial-binding preparation | Remove runtime-result/attested-heap coupling from the empty-heap logical overload while preserving existing runtime semantics | Exact sources/input binding, empty global construction and malformed scalar controls; no fabricated campaign |
| `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs`, `ContractSpecificationResult`, `CheckModuleAsync` | Add typed native outcome while retaining Verified; bind effective verification options | Timeout/resource unknown/coverage failure/solver exception versus completed failure; cancellation propagated, no diagnostic parsing |
| `Source/DafnyCore/AST/Program.cs` (read-only AST confirmation), actual module/declaration/expression owners TBD | Confirm real AST fields for the conservative whole-closure gate before source release | No guessed field access, built-in identity exemption or omitted retained definitions |
| `Source/DafnyCore/DefinitionAnalysis.cs`, `AnalyzeDocument`; `Source/DafnyCore/DefinitionAnalysis.SemanticFacts.cs`, `SemanticFactsFor` | Add immutable snapshot identity overload and route exact parsed bytes to existing SourceFingerprint.Compute snapshot API | Disk/snapshot disagreement cannot silently bind different source; bodyless selection supported |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` or an explicitly reviewed small shared identity owner | Factor existing producer/options identity without issuing proof inputs or bypassing bodyless exclusion; include query producer and separate solver provenance | Injected memory identity; exact production context source/options producer, no whole-toolchain scans |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs`, `CheckAsync` and dedicated screen preparation route | Surface effective query options identity after existing MBQI/solver processing; screen reparses use precise contracts-only preparation without changing legacy proof semantics | Incoming/effective option difference bound; only exact native-owned query body survives; no late-body-removal fallback |
| `Source/DafnyDriver/Commands/TestContractsCommand.cs`, `Create`/`ExecuteAsync` | Mutually exclusive `--screen-contract`, separate family dispatch and bounded structured result; preserve runtime branch | In-memory dispatch contracts plus offline CLI journeys |
| `Source/DafnyTestGeneration.Test/ContractScreenModelTests.cs`, `ContractScreenServiceTests.cs` (new) | Pure memory schema and fake-query orchestration, no real parser/proof/build/fs boundary | Explicit selected class filters; trace helpers before adding tests |
| `Source/DafnyTestGeneration.Test/ContractScreenNativeTests.cs` (new) | Opt-in separately gated ordinary native parser/solver checks over tiny in-memory source literals | Final offline native positive/strict-negative gate only; no runtime compilation, temp directories or disk-sync |
| This plan and eventual `plan/INDEX.md` entry | Owner scope, unresolved decisions and gates; root coordinator registers index | Markdown checks and bounded metadata inventory; no runtime acceptance |

Existing `ContractSourceSnapshot`, analyzer and fingerprints remain reuse targets;
the listed narrow identity/outcome additions are proposals, not rewrites. If their
interfaces require changes beyond the listed overload/query routing, amend this
table and resolve the semantic impact before implementation. No package addition.

## Validation commands, effects and release gates

No commands below were executed. Working directory for later checks is the
independently selected native checkout, recorded with revision/dirty state. An
implementation plan must audit actual helper/setup/teardown/process paths before
enabling tests. Existing ContractQueryTests was source-inspected only: it mixes
native calls and memory behavior, so do not run the whole class as a cheap unit.

1. Memory tests after build availability:
   `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter 'FullyQualifiedName~ContractScreenModelTests|FullyQualifiedName~ContractScreenServiceTests'`.
   Expected: only the two new memory classes; injected parse/query/identity/storage
   boundaries, no native process, directory creation, synchronization or toolchain
   hashing. Each test has one intention and one scenario. Bound each synthetic
   source to 8 KiB, <=4 cases, <=8 typed values per case and nesting <=4, except
   limit rejection using bounded in-memory strings. No benchmark fixtures.
2. Separately authorized offline build:
   `dotnet build Source/Dafny.sln --no-restore`.
   Requires compatible installed .NET SDK, already restored packages, generated
   source prerequisites and approved build-output location. Missing prerequisites
   block the gate; no automatic restore/download/install. Build writes belong to
   this explicit gate, not test fixtures. A build is not a proof or journey pass.
3. Format gate: use supported `make format` only in the owned implementation
   checkout after auditing scope and preserve unrelated/generated files; inspect
   resulting diff. Do not format the shared checkout during draft work.
4. Final native gate:
   `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter 'FullyQualifiedName~ContractScreenNativeTests'`.
   Requires locally available pinned solver and compiled test binaries. Serial,
   <=12 tiny source scenarios, <=3 KiB each, query deadlines <=5 seconds, no runtime
   compilation/generated build tree. Native process launch is integration work.
   Retain bounded output in the authorized maintenance artifact location only.
5. Final CLI journeys (after implementation and executable path confirmation):
   `dotnet Source/DafnyDriver/bin/Debug/net8.0/DafnyDriver.dll test-contracts <bounded-request.json> --screen-contract` is a command shape, **not a confirmed binary path**.
   Before release, replace it with the actual supported built executable path and
   record exact commands. Use at most two immutable bounded JSON inputs in
   `/workspace/tmp/pbt-child-contract-screening/`, no temp-directory fixtures,
   no compiler/provider, no recursive source/toolchain reads, bounded capture.
   Assert structured result rather than exit status. No journey is releasable
   until executable path and effects are confirmed.

Required native controls: satisfiable bodyless `y == x`; impossible joint ensures
`y > x && y < x`; two outputs with joint correlation; a false sampled output not
misclassified as unrealizability; zero outputs; lemma true/false under admissible
input; requires false/rejected; invalid refinement/type; ill-defined clause;
target-lemma circular dependency; unsupported caller/heap; and unknown/deadline
controls. Combine only where a single observable scenario remains clear. More
than the <=12 real-native scenario cap requires a plan amendment; move routing,
shape/status combinations to memory tests. Ambient inconsistency controls must
demonstrate no vacuous favorable result. Model-capture absence is not counterevidence.

Final release also requires independent context verification of wire/service/CLI
and matching Cosyn positive/strict-negative end-to-end journeys. Parent team owns
that coordination. No paid experiments or changes to a current evaluated run.

## Unresolved material decisions and next action

- Confirm the actual AST fields/full retained-closure coverage for the selected
  scalar ambient policy. General composites/refinements/functions are a later
  capability expansion with complete inhabitance/definedness/consistency controls.
- Confirm a nonvacuity API that exposes existing certified construction/global
  evidence independently of runtime campaign types. Do not treat logical dependency
  verification alone as consistency, and do not label raw failed proof as a model.
- Confirm effective native/toolchain/options identity without whole-runtime hashing
  during tests; establish an injected identity boundary and production producer.
- Confirm v1 APIs, selected resource-limit enforcement, cancellation lifecycle and
  exact built CLI executable before ready. Existing inspect/preflight capability DTO
  integration is owned by the native frontend plan and must be coordinated, not
  inferred from schema names.

Next action: resolve these owner choices, reconcile the exact checkout, register
this draft in INDEX via the coordinator, then obtain independent requirement/source
review. Do not start implementation on this draft. No acceptance, readiness,
native runtime result or durable empirical finding is claimed. No wiki update is
authorized in this assignment; reusable source findings remain in this record.

## Read ledger and current closeout

Initial 16 public production leaves (<=768 KiB): ContractTestModels,
ContractHarnessBuilder, ContractCallableSelector, ContractQueryBuilder,
ContractSpecificationChecker, ContractSolver, TestContractsCommand,
ContractRuntimeCampaignRunner, ContractRuntimeModels, ContractDiagnosticConstruction,
ContractRuntimeObligationTransformer, SourceFingerprintCommand, SourceFingerprint,
DefinitionAnalysis, DefinitionAnalysisCommand, ContractRuntimePreparationModels
(all `.cs` under the isolated native `Source/` directories).

Additional six exact public production/config leaves total 46,306 bytes:
`Makefile` (6,414), `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` (10,904),
`Source/DafnyTestGeneration/ContractTesting/ContractSourceSnapshot.cs` (5,878),
`ContractInitialTypeProof.cs` (12,021), `ContractGlobalAssumptions.cs` (2,354),
`ContractModelCodec.cs` (8,735). One existing test leaf:
`Source/DafnyTestGeneration.Test/ContractQueryTests.cs` (36,326 bytes), inspected
selectively, not executed. Instructions and the normative design were read;
prior implementation/verifier conclusions and private/evaluated artifacts were
not used as evidence. No source/native/parser/proof/build/test/import/provider
execution, copy, package or Git changes occurred. Only this Markdown owner draft
was created; index registration and final cross-owner review remain with root.
Draft-only checks: `rg -n '[[:blank:]]+$'` on this document reported no trailing
whitespace. Metadata-only `rg --files --hidden` over native `plan/` and `wiki/`,
filtered for non-`.md` names, reported none. These checks establish documentation
hygiene only; all implementation/build/proof/journey gates above remain unrun.

## Typed relative-path native controls, 2026-10-23

The installed frontend check authenticates500image leaves and restricted UID,
then correctly rejects archived raw-native r06requests because their source paths
are absolute. Actual Cosyn requests require workspace-relative paths. Keep that
validation and all prior source/image/control records unchanged; do not transfer
old native bindings to renamed sources. Root owns the linked image/check update.

Release bounded independent actual controls under
`/workspace/tmp/pbt-child-contract-screening/native-relative-r07/` only:
`controls.py`, manifest/results/provenance JSON and at most64bounded public
request/result/log leaves (aggregate<=16MiB, each<=1MiB, no subdirectories).
Use the same seven public r06source/case scenarios, unchanged query5s/attempt30s/
process60s/seed42 and final native binaries. Convert only each source path to
`virtual-input.dfy`, validate every INSPECT and newly bound SCREEN through the
actual normal r04Cosyn DTOs, run them sequentially from one fixed workspace and
validate every native reply with the actual validator. Use the maintained Dafny
facade directly with the complete finite runtime closure; no SDK/cache walks,
builds, directories inside tests, synchronization, Docker or provider calls.

This is separately authorized bounded native maintenance, outside development
tests. Check at least the original seven scenario outcomes/10inputs, strict
source/target/question/ordered-input echoes, actual native binding/options/paired
query evidence, before/after four binary/source hashes, and one trivial ordinary
facade verification. Preserve any failure without automatic retries or altered
limits. Fresh results can establish typed relative API compatibility, not
installed native confinement or model behavior. Source-only review of the script
and effects precedes actual execution; the existing source freeze remains held.

Independent source review of the initial r07script (SHA
1211a10bb4506813fc1b521effa44c98b1dfe1701eddd82ba842dc727eefc9a4)
clears typed relative requests, all7source/10ordered cases and19query pairs, but
withholds execution for four harness issues. Release changes to that script only:
always bound/kill/reap its owned process group on capture/wait failure, including
closed pipes; reject nonzero exit or any timeout/output boundary before accepting
a reply; require completed for the five positive/negative scenarios (retain exact
partial statuses for ambient/definedness); and charge existing script/other leaves
plus reserved external capture headroom to the16MiB total. Keep command/budget/
fixtures/source hashes fixed and preserve evidence of the rejected source. Recheck
the narrow delta independently before actual CLI execution; no native source edits.

Fresh independent delta review clears final r07controls.py SHA
66b02634013e947f3e42aa70cb178809b7900860c692a81efe6e0df266360f65:
all four harness findings are resolved; commands/fixtures/budgets remain unchanged.
Release its exact normal /usr/bin/python3 -B -P invocation from the fixed r07
directory with PYTHONPATH pointing only to the normal r04import-root,
PYTHONDONTWRITEBYTECODE=1, PYDANTIC_DISABLE_PLUGINS=__all__, LOGURU_AUTOINIT=0
and PATH=/usr/bin:/bin. No external artifact capture is needed beyond the tool's
bounded result; any later external capture must fit the reserved2MiB/two leaves
and1MiBindividual cap. This release is native/public synthetic maintenance only.

Actual r07exits1 before any native process: its operator assertion compares the
DTO's pathlib.Path source.path with a str. The DTO correctly parsed the relative
path. Preserve r07controls.py and its2597Bmanifest as the failed population;
no native result exists. Release a new native-relative-r08/controls.py, copied
from the reviewed r07script with only that assertion changed to compare
Path('virtual-input.dfy'). Same flat64/16MiB/individual1MiB/reserve limits and
normal native commands apply to the new namespace. Independently inspect the
one-line change and construct one actual DTO in memory before releasing r08CLI
execution. No runtime/schema/specification change is needed.

Source-only r08copy exposes the same Path type at independent source-hash JSON
construction. Before execution, also convert that `Path` to str in the existing
native-matching `{'Path':..., 'ContentHash':...}` document; preserve its current
actual-content hash calculation and all key names. Inspect remaining path uses for this
specific type mismatch without broad changes. Release a normal pure DTO smoke
check (no native/file writes) of the exact assertion and source-hash serialization
on the seven relative fixtures, then fresh narrow independent review. Keep r07
unchanged and record both pre-run r08source hashes/diff; no further namespace is
needed for a source correction before any r08output or process exists.

Independent r08delta review clears final controls.py SHA
cd3cd3f6afcc53a68e70ba6fd0c77854ae7b9321372f4a9afd40a128d3e852d5.
The exact two Path fixes pass actual normal DTO construction/hash checks across
seven scenarios and fourteen memory INSPECT/SCREEN round-trips; no native
execution in review. Release the identical approved command/environment from
native-relative-r08, pointing to its controls.py. Commands, fixture source/cases,
statuses, hashes and all budgets/caps remain unchanged. Preserve r07 as failed.

Actual r08now completes exit0:53checks pass,0fail; seven typed relative-source
INSPECT/SCREEN pairs cover ten ordered cases, plus ordinary verification. All15
processes exit0 without timeout/output/parse/typed boundaries. Fresh independent
read-only result review recomputes the seven source-set hashes, fresh binding
equality, ordered input echoes, seed42/options profiles and19unique query pairs;
all12pinned binary/facade/solver-source/Python inputs still match. The five normal
screens complete; bad-function remains partial unknown/not_checked and both
undefined cases remain partial admissible/error. No false decision is inferred.
Results.json is77569B, SHA
c27ddafb8acd258bd4043b3d2366cc35be60714e90fa6a93fa541d77cbcf6b04;
controls.py remains cd3cd3f6afcc53a68e70ba6fd0c77854ae7b9321372f4a9afd40a128d3e852d5.
There is no separate provenance-manifest.json; the script's existing input
manifest and results contain provenance. This establishes the public synthetic
typed bridge only. Independent installed controls also pass under the separate
[root image plan](../../../plan/2026-10-23-pbt-child-screen-image.md); model behavior
and new official csplit outcomes are still pending.
