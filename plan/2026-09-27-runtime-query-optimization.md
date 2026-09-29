# Optimize runtime contract decisions without weakening validity

Status: done (closed by user decision 2026-09-29; broader historical/full-population acceptance remains follow-up)
Date: 2026-09-27
Owner: embedded Dafny engine
Integration plan: [M2 detection optimization](../../../plan/2026-09-27-pbt-m2-detection-optimization.md)
Predecessor: [entry heap checking](2026-09-27-runtime-entry-heap-checking.md)
Knowledge: [contract testing](../wiki/contract-testing.md)

## Objective and acceptance

This is authorized development maintenance, with local public-input probes, not
an evaluated provider run. Preserve every original contract and the current
64-sample, 5-second sample, 240-second campaign, 16-query, 10-second query limits.
Obtain positive-valid runtime samples and actual detection of all four public M2
mutants; retain no spurious reports on four proof gaps and existing M1 behavior.
Engine unit success alone does not complete this integration acceptance.

No benchmark changes, public DTO changes, packages, commits, hidden inputs,
task-name branches, unproved witnesses, trust assumptions or skipped meaningful
checks are authorized. Existing dirty changes are the accepted predecessor and
must remain intact. Root owns probes, snapshots, reports and population runs.

## Inspected evidence and approach

`ContractSolver.CheckAsync` reparses/resolves the original source closure for
every polarity before reducing a scalar assertion; reduction conjoins the
original expression and cannot remove this frontend cost. Probe06 scalar queries
are closed `InputsFromOperands` results and `Utf8ByteWidth` equalities. Its
original and diagnostic ASTs are already available to the runtime runner.
`ContractExpressionReducer` supplies a detached resolved concrete reduction used
by existing input refinement checking. Inlining alone does not validate callee
preconditions or postconditions, so its literal output is not an unconditional
runtime validity certificate.

`CheckInitialTypes` recursively rejects omitted structured refined types even
where empty containers or one datatype constructor provide a witness. A total
arrow can be inhabited by a pure constant function when its codomain has a
validated witness; its domain need not be separately inhabited. A declared
subset witness is a candidate, never evidence until its original constraint and
dependencies are checked. Generic substitutions and constructor identity matter.

The runner admits a completed sample only after original input types and every
observed callee contract are validated. Its entry heap postcondition additionally
rejects any transitive specification callee with an unchecked contract. This gate
must be replaced only by explicit evidence for the exact dependency obligations,
never deleted. Scalar and heap optimizations must remain source-bound and keep
unsupported, partial, ill-defined and exhausted decisions unchecked.

## Staged changes

| Exact engine files / symbols | Change, necessity and unmet behavior without it | Validation |
| --- | --- | --- |
| `ContractHeapFactory.ContractHeapPlan.QuerySourceEdits`, `BuildConstructorInsertions`; `ContractHarnessBuilder.DiagnosticSourceSnapshots` / `Insert`; `ContractRuntimeHeapQueryTests` | Separate native query visibility edits from executable allocation helpers. Preserve original initialized readonly equations and exact captured equality without injecting illegal, unused constructor assignments; leave executable constructor semantics intact | Imported revealed-class matching/mismatching readonly native queries; initialized-constant Driver positive/rejection controls; full Contract suites |
| `Source/DafnyTestGeneration/ContractTesting/ContractGlobalAssumptions.cs`; `ContractSpecificationChecker.cs`, `ContractRuntimeHeapChecking.cs`, `ContractInitialTypeProof.cs`, `ContractRuntimeObligationTransformer.cs`, `ContractSolver.cs`; `Source/DafnyTestGeneration.Test/ContractRuntimeHeapQueryTests.cs`, `ContractQueryTests.cs`; `Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs` | Cover unconditional static constant assumptions in constructive admission; remove abstract-global-dependent axioms only from proof premises; retain full consistency/model theory and conservative fallback for unsupported global equations/types. Needed to prevent vacuous own-witness proofs and primitive-heap bypass | Native direct/transitive witness failures; exact imported reference carrier identity; closed constructor values; unsupported refinement/function/cycle fallback; actual inconsistent-global population rejection; all Contract suites |
| `Source/DafnyTestGeneration.Test/ContractPhaseTimingTests.cs` (root-owned timing slice) | Verify retained phase records from successful, invalid-source and cancelled native query processing; prevent unavailable phase evidence at deadlines | Deterministic query scenarios and structured persisted event checks; no live provider |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`; `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs`, `ContractSourceSnapshot.cs`; new `ContractPhaseRecorder.cs` beside solver if needed | Retain internal phase start/completion/cancellation artifacts for preparation, reduction and query frontend/translation/solver; preserve DTOs. Optional internal observer on source parsing separates parser and resolver costs. Needed to distinguish frontend deadline from actual solver cost | Phase records for success, failure and cancellation; unchanged result contracts |
| New `Source/DafnyTestGeneration/ContractTesting/ContractConcreteChecking.cs`; `ContractRuntimeCampaignRunner.DecideClosedAsync`; existing `ContractModelCodec.cs` / `ContractTypeShapeGenerator.cs` only for reusable typed-value conversion | Build resolved concrete values against exact original variable types; use detached original AST to decide supported scalar clauses before source reparse. Validate refined carriers, definedness and function dependencies; residual uses existing solver. Reuse existing reducer with explicit existing refinement reduction limits | Both truth polarities, imported declarations, equal-spelled constructors, generic/bitvector types, invalid refinements, bad callees, partial operations, residual/budget cases, original AST unchanged |
| `ContractRuntimeHeapChecking.CheckInitialTypes` / `PrepareInitial`; new `ContractTypeInhabitation.cs` if separation helps; `ContractHeapFactory.cs` only if witness query plumbing needs it | Construct generic inhabitants with empty containers, one datatype constructor, primitive literals, pure constant arrows, and checked declared subset/newtype witnesses. Do not infer inhabitance from generic SMT typing. Original full initial-state consistency remains required where any carrier constraint is residual | Empty type alone remains rejected/unchecked; `seq<Empty>` inhabited; `Box<Empty>` not; alternate constructor works; recursive constructor cycle terminates; arrow codomain witness valid/invalid; false declared witness and bad witness callee do not admit sample |
| `ContractSolver.cs` and existing `ContractQueryTests.cs` (root-owned translation slice) | Use native `BoogieGenerator.DoTranslation` only for the exact diagnostic query owner module(s), with native scope reset and the complete original resolved program/imported visible declarations. Measured redundant translation of every module takes 13–14s and expires before solver; existing verification scope already selects only the diagnostic query. No pruning of its dependencies, original assertion or definedness checks | Imported definitions in both truth polarities, imported false preconditions, observed module-phase scope, existing complete query tests |
| `ContractRuntimeObligationTransformer.cs`, `ContractConcreteChecking.cs`, `ContractRuntimeHeapChecking.cs`, `ContractRuntimeCampaignRunner.cs` | Where required for entry detection, discharge actual specification dependency preconditions and postconditions using concrete/solver evidence keyed by exact calls or a separately verified dependency closure. Retain unsupported heap/higher-order/recursive cases. Original `CoreSummary` and every other postcondition remain tested as written | Existing unvalidated-callee regressions plus valid/invalid direct/transitive specification dependencies, both goal polarities, by-method result mismatch and precondition failure |
| `Source/DafnyTestGeneration.Test/ContractRuntimeHeapQueryTests.cs`, `ContractQueryTests.cs`, new `ContractConcreteCheckingTests.cs` if needed; `Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs`, `ContractRuntimeCheckTests.cs` | Add observable generic regressions for the preceding mechanisms; reuse native fixtures and controlled artifacts | Focused tests first, then complete Contract suites and fresh independent verification |
| `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs`, `ContractReductionResult.cs`, `Rewriters/PartialEvaluatorEngine.cs`, `PartialEvaluatorVisitor.cs`, corresponding Core tests only if a measured unsupported exact operation is required | Targeted exact-evaluation support or explicit evidence metadata; preserve default rewriter profile and original contract semantics. Update this plan with concrete operation before editing these files | Affected Core reducer/default-profile/unrolling suites, invalid/partial counterparts |
| New `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs`; `ContractSymbolicChecker.TrustDependencies`; `ContractRuntimeObligationTransformer.ExecutionReachable`; heap checker and runtime runner; new `Source/DafnyTestGeneration.Test/ContractSpecificationCheckerTests.cs` | Build source-bound native certificates for exact original specification closures, including reached refined type constraints/witnesses and by-method bodies. Expose reached types from existing closure traversal; reuse trust audit. Translate owning modules and retain only exact selected native implementation bodies, leaving all declarations/procedures intact. Each module consumes one existing 10s/count16 query; cache covered declarations per immutable source program. Release validity gates only after the whole requested closure is proved | Valid/invalid transitive requires/ensures, false declared witnesses, invalid by-method equality, bodyless/assume/verify-false rejection, imported same-name declarations, zero-obligation and exact complete emitted-implementation coverage; unchanged full premise SAT checking |
| New `Source/DafnyTestGeneration/ContractTesting/ContractQueryDeadline.cs`; `ContractSolver.CheckAsync`; `ContractSpecificationChecker.CheckModuleAsync`; runtime query callers; `ContractPhaseTimingTests.cs` and `ContractSpecificationCheckerTests.cs` | Enforce absolute monotonic query deadlines independently of delayed cancellation callbacks, from before source construction through frontend/native solve and before cache/result publication. Preserve actual phase timings and report expired work as timeout. Required because probe04 mathematically detects a mutant but initial premise verdict arrives at11.76s under10s configured timeout | Deadline already expired; native proof completing after explicit deadline with uncancelled token; no certificate/cache acceptance after expiry; unchanged timely results and current phase tests |
| `ContractRuntimeHeapChecking.PrepareInitial`; `ContractRuntimeHeapCheck`; runtime initial consistency handling; `ContractRuntimeHeapQueryTests.cs` and `ContractRuntimeHeapTests.cs` | Restrict initial existential model search using explicit original subset/newtype witness definitions only after native certification. Insert private diagnostic helper predicates in original type scope, retain full typed heap premises, and never use these choices in final property polarities. Narrowed UNSAT is unknown, not evidence the broader state is empty. Unsupported generic/export views retain existing unrestricted query | Imported higher-order witness SAT; invalid captured refinement remains inadmissible; no witness choice in final Q; invalid/uncertified declared witness not used; narrowed UNSAT does not reject a potentially broader state |
| `ContractSpecificationChecker.Scope` / `CheckModuleAsync`; `ContractSpecificationCheckerTests.cs` | Permit declarations carrying only a source verification skip to earn a new native certificate: remove false verify attributes solely in the checker's detached parsed AST, then prove every original body, WD, ensures and by-method implementation with strict native coverage. Filter only `verify_false` audit entries; retain axiom/extern/bodyless/assume/facade and unsupported source failures. Exclude uninitialized non-static immutable fields from callable proof obligations while retaining their reached types and heap checks; native translator emits no WF procedure for these slots | Valid/invalid skipped module/member/class bodies; positive native implementation coverage; original AST attributes unchanged; skipped assumption still rejected; typed immutable field dependencies retained; bodyless static constant rejected |
| `ContractQueryBuilder.Build` / `BuildClosedClause`; `ContractQueryTests.cs` | Emit existing native source-qualified reveal statements for reachable original accessible opaque function definitions using `AutoRevealFunctionDependencies`, without assumptions or contract edits. Definitions must be available in the query import view; inaccessible opaque exports remain unsupported. Needed for original final predicates whose existential relations call explicit opaque definitions | Imported nested opaque definitions in both polarities; false callee precondition remains Error in both polarities; source bytes unchanged; inaccessible exports not revealed |
| `ContractSolver.CheckAsync`; `ContractQueryTests.cs` | Before native Boogie preprocessing, retain only exact diagnostic-owner Implementation nodes selected by original FullDafnyName/VerboseName, preserving all procedures, definitions, axioms and type checks. Existing ProcsToCheck selection occurs after expensive whole-module CFG processing; reuse certificate selection semantics to remove that unused work | Existing both-polarity and invalid-precondition queries; unrelated implementation contracts cannot affect target; retained target WF coverage and scoped phase profile |
| `ContractSolver.CheckAsync`; `ContractQueryTests.cs` | Disable axiom pruning for decisions that can publish SAT/model evidence, following native test generation counterexample setup. Verification pruning is not documented to preserve input satisfiability; retain every original meaningful typed premise axiom. Pure native dependency certificates still use ordinary proof settings | Actual PrepareInitial explicit omitted-type inhabitance for satisfiable/empty refinements; current query/heap native regressions |
| New `Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs`; `ContractRuntimeHeapChecking` private validation core and proof planning; `ContractQueryBuilder` exact source type rendering and zero-input construction query; `ContractRuntimeCampaignRunner` initial admission; existing heap/query/certificate tests and `ContractRuntimeHeapTests.cs` | Replace expensive global SAT only for a fully covered compositional state: validate all original heap fields AND entry input/receiver carriers, with a mandatory native original type/function WD closure. Host checks preserve exact references/aliases/classes/array shape; existing certified structural rules inhabit omitted fields. Candidate pure values are constructed as locals of their exact declared types in a zero-formal, zero-requires native query. Only complete UNSAT proves membership and allows admission. Reuse a successful initial certificate only by the identical serialized full request/source/input/heap key in later heap decisions; host-only type success is not a cache certificate. Unsupported reference/arrow/coinductive/generic/opaque cases or initializer-bearing immutable fields retain original full SAT; failed proofs stay unchecked | Valid/invalid root inputs with valid heap; nested/imported/generic refinements; original plain-function WD failure without Req/Ens; opaque constraints; empty/false omitted witness; aliases/references/cycles/initializer fallback; source identity and exact query budgets; public strict-budget probe |
| `Source/DafnyCore/DafnyMain.cs` (`BoogieOnce`, `BoogiePipelineWithRerun`); `ContractSolver.cs`; `ContractSpecificationChecker.cs`; `ContractPhaseTimingTests.cs` / cancellation cases in `ContractSpecificationCheckerTests.cs` (root-owned cancellation slice) | Thread CancellationToken through a native wrapper overload into the actual supported ExecutionEngine.InferAndVerify overload. Preserve the existing eight-argument BoogieOnce binary signature as a forwarding overload with CancellationToken.None, native diagnostics/statistics/model handling, and strict monotonic admission checks. Needed to prevent physical native overruns from exhausting the enclosing240s campaign | Native successful query unchanged; actual long-running query/module cancellation terminates without verdict/cache publication; existing focused suites; full campaign timing |
| `ContractRuntimeObligationTransformer.cs` / internal `ContractRuntimeClause`; new `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeTypeEvidence.cs`; `ContractInitialTypeProof.cs`; `ContractRuntimeCampaignRunner.cs`; existing `ContractRuntimeHeapQueryTests.cs`, `ContractRuntimeCheckTests.cs` and `ContractRuntimeHeapTests.cs` | Reuse actual existing compiled formal type checks as source-bound pure-value membership evidence. Mark type-check clauses internally (no public DTO/schema change); bind their one formal to its unchanged original callable signature and original declared type. Accept only actual Runtime check records whose exact original pure type and serialized value match a planned carrier, after full native original type/function WD certification. Exclude draft/helper owners and any drafted type dependency; missing, malformed, conflicting or unchecked evidence never admits. Keep native construction for uncovered carriers, root input/receiver, original structure/reference/omission/initializer gates, original P/Q and query budgets | Actual recursive finite set/path carrier check admits a valid heap; false/refined carrier fails; exact type/value/source/owner mismatch and malformed/conflicting records cannot authorize; native-WD failure and draft predicate remain unchecked; same public DTO and method classification; public frozen probe |
| `ContractInitialTypeProof.cs`; `ContractRuntimeHeapChecking.cs`; `ContractRuntimeCampaignRunner.cs`; `ContractRuntimeTypeEvidence.cs`; `ContractRuntimeHeapQueryTests.cs`; `ContractRuntimeHeapTests.cs`; `ContractRuntimeCheckTests.cs` | Compose observed-state consistency from an explicit exact constructive initial certificate, unchanged original P proof, checked shape/frame/immutables and native or source-bound Runtime final-field/output memberships. Preserve fallback global SAT on unsupported states and every original Q/callee validity check. Measure evidence collection and pre-query scope phases; bound collection by cancellation and the unchanged campaign deadline. Index original binding only after phase evidence identifies repeated traversal | Native final/output refinement negatives, invalid P, immutable/reference/array/omitted/frame regressions, real both-polarity original Q; cancellation cannot publish partial evidence; public frozen probe and unchanged budgets |
| This plan, `plan/INDEX.md`, `wiki/contract-testing.md`, `wiki/INDEX.md` | Retain failed attempts, actual phase costs, soundness boundaries and integration acceptance | Diff/link review and evidence-backed owner/root handoff |

## Soundness obligations

### Measured-source refinement before the second implementation slice

Probe06 `transformed-sources-0.json` already contains executable scalar checks,
but its runtime renderer loses declaration scope: `EncodeChar__pbt_site_25` calls
`_default.Utf8ByteWidth__pbt_spec_477`, and `InputsFromOperands__pbt_definition`
prints unqualified `Input.Stdin` / `Input.File`. The next transformation lowers
these checks to closed queries. First fix this existing generic renderer rather
than introduce an interpreter. `ContractQueryBuilder` already has source-aware
qualification for these exact resolved declarations.

The next edits are `ContractQueryBuilder.QualifyExpression` (shared existing
substituter), `ContractRuntimeObligationTransformer.Render` and every insertion
scope caller, native regressions in `ContractRuntimeCheckTests.cs`, and retained
`transformed-diagnostics-<attempt>.txt` in the campaign runner. This restores
original compiled checks and preserves actual runtime classifications. Deferred
original-clause interpreter metadata from the timing slice is unnecessary and
will be removed. If a later exact interpreter is needed, classify its actual
decisions as runtime, record host evaluation separately from compiled execution,
and never claim an SMT invocation that did not occur.

For omitted inhabitance, a supplied direct subset/newtype field can serve as a
conditional leaf witness for another omitted value of that exact instantiated
type. Every supplied field still undergoes original type checking; a residual
requires the complete original initial SAT premise. No sample is admitted merely
because a field is declared at that type. Empty containers, one valid datatype
constructor and a pure constant arrow provide structural witness composition;
unknown/refined/cyclic cases keep existing query/unsupported behavior. Add
normal and invalid conditional-witness cases and empty-domain/container/arrow
cases in `ContractRuntimeHeapQueryTests.cs` and `ContractRuntimeHeapTests.cs`.

1. Concrete substitutions preserve exact resolved variable, constructor, type,
   generic and source identity. Every input value belongs to its original type.
2. Reduction does not erase required definedness, call preconditions or an invalid
   contract-bearing implementation. Unknown dependencies force residual/unchecked.
3. Omitted witnesses prove existence only for genuinely irrelevant ghost fields;
   existing reachability/omission rules still forbid omitted observed state.
4. A failed constructive search means unknown, not emptiness. Recursive type
   search uses instantiated identities and terminates. A subset's declared witness
   is checked in its declaring scope without assuming membership or its ensures.
5. No original tested postcondition becomes an assumption. A partial witness can
   prove an existential true when checked, but failure of one witness cannot prove
   it false. Universal/negative decisions retain complete original quantification.
6. Reuse cannot mutate the authoritative AST or leak bindings, requires, reveals,
   contracts, observations or solver assumptions between samples or variants.

## Validation and coordination

Prerequisites: installed supported .NET SDK/restore and local solver; no paid calls.
From `/workspace/cosyn/dafny`, use `dotnet build Source/Dafny.sln --no-restore -m:1`
and focused `dotnet test ... --no-build --no-restore -m:1 --filter ... -v:minimal`
for touched classes. Run `make format`, then the complete TestGeneration and Driver
`FullyQualifiedName~Contract` suites sequentially. If Core changes, run affected
`ContractExpressionReducerTests`, `PartialEvaluator` and quantifier cases.
Root performs supported `make build-dafny` packaging from `/workspace/cosyn`,
four local transport cases, frozen public one-sample probes and eventual full
M1/M2 populations. Do not build concurrently with any probe or independent check.

Start with instrumentation and original-AST scalar checking; use retained phase
evidence to select the next minimal correction. Then establish original initial
state inhabitance and all callee validity. Only after positive-valid probes address
remaining entry postcondition dependency and existential cost. Announce any scope
change before editing additional files. Fresh verification starts independently
from requirements and repository state, without implementation conclusions.

## Progress and handoff

- Instrumented baseline probe01 (2026-09-28, root-owned immutable artifact)
  establishes that scalar partial reduction completes in milliseconds, while
  whole-program translation takes 12.8–14.5s and no Boogie solver phase starts
  before query cancellation. Replace redundant per-module translation using the
  existing native module API before considering any new exact interpreter or
  resolved-template cache. Root owns solver/query tests for this slice; owner
  retains runtime qualification and conditional type-inhabitance implementation.

- Read root/submodule instructions, original engine code and permitted public
  contracts, predecessor owner records and probe06 artifacts. No hidden files,
  source edits, builds or experiment runs performed during this design phase.
- Parent owns profiling/probe/freeze/evaluation work; engine source writes and
  builds have one owner. Initial implementation begins after ready-plan handoff.
- Remaining acceptance is all implementation, tests, independent verification and
  positive-valid/detection population evidence. No passing or completion claim.
- Timing slice: initial build exposed one local pattern-variable name collision,
  corrected before passing build. Root timing/query focus passed 28/28 (10s),
  supported packaging passed 37.84s with zero warnings/errors. Frozen baseline
  has 893 files and SHA-256
  `c9091a020255220ebc547b1095bca327157908c2320ce82e1ca426de963173de` at
  `/workspace/tmp/experiment/pbt-m2-optimization-toolchain-20260928-01`.
  Root owns the frozen baseline probe; source work may continue, but builds and
  native checks wait for the profiling execution lane to be released.
- The frozen timing baseline completed in 241.09s with no valid sample. Every
  scalar query completed reduction but took about 13–14s translating before
  cancellation; none entered a Boogie solver phase. Native scoped translation
  now uses `DoTranslation` only for exact diagnostic owner modules while retaining
  all original visible declarations. Root contributed that change and six native
  imported-dependency/polarity/definedness cases.
- Restored runtime source qualification in all insertion contexts, after unsplit
  quantifier reconstruction so native `Substituter` cannot erase compilable bounds.
  Added constructor/arrow inhabitance composition from empty containers and exact
  captured type witnesses, conditional on the unchanged original initial SAT check.
- Merged `dotnet build Source/Dafny.sln --no-restore -m:1 -v:minimal` passed in
  35.91s, then 14.25s after a test-only fixture correction, both zero warnings/errors.
  Initial VSTest invocation was sandbox-blocked before execution by its required
  localhost socket. Approved local escalation ran the tests. First focused run
  passed 55/56; the remaining new test lacked Dafny's required constructor for an
  uninitializable field. Its explicit impossible constructor corrected the fixture.
  The repeated TestGeneration filter
  `FullyQualifiedName~ContractRuntimeHeapQueryTests|FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ContractPhaseTimingTests`
  passed 56/56 in 10s. Driver filter
  `FullyQualifiedName~ImportedSpecificationWrapperKeepsCompiledCheck|FullyQualifiedName~ImportedRecursiveDefinition|FullyQualifiedName~RunsWithConstructibleRefinedArrowOmission`
  passed 4/4 in 10s. Commands used `--no-build --no-restore -m:1 -v:minimal` from
  `/workspace/cosyn/dafny`; logs preserve all attempts under
  `/workspace/tmp/pbt-m2-optimization-checks-20260928/qualification-*`.
  These focused tests are implementation evidence, not independent acceptance or
  M2 detection. Full suites and final source/requirement review remain pending.
- Probe02 completed in 54.53s with one transformation, no scalar closed queries,
  and zero unchecked scalar callees. The initial state now reaches a previously
  masked constraint-dependency guard; it remains invalid/unvalidated, with no
  positive-valid sample. Next expose the exact generic dependency names in
  `ContractRuntimeHeapChecking.CheckConstraintDependencies` diagnostics and inspect
  those original declarations before choosing their validation strategy. Typed
  subset premise SAT does not itself validate calls inside a refinement definition;
  keep this guard until explicit membership/definedness evidence exists.

- Next native-certificate slice (2026-09-28): parent cost probe verifies all
  28 selected BenchWorld implementations without errors in 4.38s solver plus
  0.64s translation. A combined two-module 10s process expires in IOContract;
  this motivates natural per-owner-module queries under the unchanged per-query
  and total query budgets, not larger deadlines. Production must not rely on
  substring routine filters: select exact native implementation VerboseName
  identities, retain complete procedure/declaration semantics, and require every
  emitted selected implementation to be accounted for. Native omission of a
  zero-assertion implementation is recorded explicitly. Closure certificates
  include type well-formedness/witness obligations and reject arbitrary source
  assumptions; a successful prefix never clears a dependency gate. Initial and
  later entry-Q requests share only certificates of unchanged original source
  declarations, with no benchmark-specific names. Broad closure checks may still
  time out or fail; such outcomes remain unchecked and consume their real budget.

- Native certificate implementation now discovers exact original callable/type/
  constant dependencies, rejects source trust and skipped module/member owners,
  verifies every selected native implementation with full procedure/declaration
  retention, and records genuinely assertion-free native procedures. Successful
  module prefixes are cached but cannot authorize a closure before every member
  succeeds. Each module consumes one existing closed query. Native BoogieOnce has
  no cancellation argument; an explicit post-await deadline check prevents late
  proofs from entering the certificate cache, but native execution may finish
  after cancellation before returning. No increased deadline is claimed.
- Initial-state retry validates the exact original field-type closure only when
  the prior conservative check is unsupported. Validated explicit type witnesses
  can then supply omitted inhabitants; every captured residual constraint still
  needs its original SAT premise. Entry heap clauses request certificates only
  for otherwise valid samples; invalid executed callees still exclude samples.
  Scope rejection and module evidence persist as internal specification artifacts.
- Certificate build attempts 1/2/4 failed on ordinary C# type/API errors (module
  node versus declaration, ambiguous LiteralExpr, declaration traversal helper),
  corrected before build5 passed with zero warnings/errors in37.56s. Focused
  TestGeneration filter adds ContractSpecificationCheckerTests to the prior
  heap/query/timing filter and passes72/72 in14s. After four Driver integration
  cases and formatting, build6 passes zero warnings/errors in19.31s. Driver filter
  `FullyQualifiedName~CertifiesOriginalOmittedWitness|FullyQualifiedName~CertifiedSpecificationDecidesBothHeapPolarities|FullyQualifiedName~UnvalidatedSpecificationCalleeRemainsUnchecked|FullyQualifiedName~InitialFieldConstraintCalleeRemainsUnchecked`
  passes6/6 in29s. All commands use the documented engine working directory and
  --no-build/--no-restore -m:1 flags where applicable. Local VSTest socket requires
  the already approved sandbox escalation. Logs are specification-* under
  /workspace/tmp/pbt-m2-optimization-checks-20260928. make format and
  git diff --check pass. Full suites and independent review remain pending.
- Freeze03 handoff: source/tests stable; root packages and probes initial validity.
  Public BenchIO declares module-level {:verify false}, so CoreSummary's observer
  dependencies remain conservatively blocked. A later planned slice may remove
  that skip only in a detached certificate AST and actually verify the original
  bodies, with exact coverage and valid/invalid skipped-declaration regressions;
  no benchmark source or evaluator scope change. Original opaque definitions may
  also need native reveals. Neither step is included in freeze03.

- Probe03 (55.62s, no valid sample) fails before Boogie because native coverage
  incorrectly demands WF procedures for pure aliases Path/Bytes/RawBytes/
  FileSystem. The resolved ConcreteTypeSynonymDecl inherits RedirectingTypeDecl
  through TypeSynonymDeclBase; earlier direct-class inspection missed that base
  interface. Fix the exact declaration selection to SubsetTypeDecl/NewtypeDecl
  only, and explicitly traverse ordinary TypeSynonymDecl RHS in the existing type
  dependency visitor. Add alias-chain/underlying-refinement regressions to
  ContractSpecificationCheckerTests before freeze04. Do not change input validity
  or accept aliases as proofs: they have no native WF obligation, while reached
  refinements/witnesses still do. Skip re-verification and reveals remain deferred.

- Alias fix is validated by a regression that first confirms the raw reachable
  set actually contains concrete aliases, then confirms certificate selection
  excludes them while retaining the underlying subset. Both true and false
  underlying witnesses behave correctly. Alias build passes17.19s with zero
  warnings/errors; focused ContractSpecificationCheckerTests plus
  ContractRuntimeHeapQueryTests pass40/40 in5s. make format and diff --check pass.
  Logs alias-* under the same retained check directory. Source is stable for
  root freeze04; broad suites remain pending integration acceptance.

- Probe04 proves the initial full source closure: World42 implementations plus16
  assertion-free declarations (6.754s including frontend), IOContract12 plus4
  assertion-free declarations (4.496s). Original initial premise is SAT and the
  drop-stdin mutant has one valid violating sample. However the premise query
  finishes at11.761s despite its configured10s timer; this is mathematical
  detection, not strict-budget acceptance. Delayed cancellation callbacks are
  insufficient for admission. Prioritize absolute Stopwatch deadlines on every
  runtime query/certificate before proceeding to CoreSummary. Parent profiles
  exact initial premise with MBQI off/on; no deadline increase is authorized.

- Independent exact-query replay by root repeats late SAT at12.048s with its
  cancellation token already cancelled. Thus delayed timer scheduling was only
  an initial inference; the direct demonstrated bug is absence of a post-native
  token/deadline gate in the existing solver. New checks enforce both, preserve
  timeout result artifacts, and reject expired certificate-cache publication.

- Deadline slice passes solution build35.28s with zero warnings/errors and focused
  phase/certificate/query/heap77/77 tests in15s; make format passes. Logs deadline-*
  under the retained check directory. The native task can still overrun physically,
  but expired work cannot publish a verdict or certificate.
- Root exact-premise MBQI profile is negative evidence: off SAT12.048s, on
  SAT14.003s, both token-cancelled and outside the10s deadline. No MBQI change.
  Trace03 isolates53 well-formedness obligations at0.143s versus actual SAT model
  construction7.456s (total11.609s). Therefore membership-only checking is not a
  substitute for the original full consistency query. Next bounded optimization
  uses only certified explicit source witnesses as additional initial existential
  choice constraints; root first measures the exact query with one such helper.
  Any narrower UNSAT remains unknown; full-state/property queries retain their
  original unrestricted domain. This is constructive existential search, not a
  change to benchmark inputs or an assumption that a declared witness is valid.

- While the root measures the witness-constrained initial query, proceed with the
  independent final-entry prerequisite already authorized: native re-verification
  of source-skipped declarations. Removing a source skip in a private certificate
  copy strengthens checking and does not change source/evaluator scope. No source
  axiom, assumption, absent body or extern becomes trusted. Every emitted native
  obligation remains mandatory and original AST attributes remain untouched.
  Constructor-initialized immutable instance fields are modeled heap slots; they
  have no native WF procedure, so retain their type dependencies and all concrete
  immutable/reference constraints rather than demand a nonexistent body proof.

- Witness04 could not access an omitted ghost field through the explicit original
  export view. Diagnostic witness05 preserves the exact broad query plus one
  original certified witness restriction, but remains SAT12.177s (WF0.268s,
  correctness7.626s), with no elapsed gain. No production witness-choice code was
  added. Keep this negative result; the previously listed choice slice is deferred.
- Native options already enable pruning. The remaining generic overhead candidate
  is unselected implementation CFG preprocessing: legacy BoogieOnce resolves and
  preprocesses every translated implementation before its routine filter. Apply
  the existing certificate implementation-only selection to exact diagnostic
  methods before native processing; declarations/procedures/axioms remain intact.
- Native original reveals cover queried clauses and original premise type/entry
  requirements. A consistency query cannot count SAT over an inaccessible opaque
  refinement body as exact source existence; such an import view remains unsupported.

- Query implementation selection clears inherited ProcsToIgnore and requires exact
  native coverage: one correctness implementation; all selected implementations
  verified for UNSAT; or all other implementations verified and every error an
  original diagnostic target counterexample for SAT. Multiple target errors in
  one correctness implementation do not falsely count as multiple implementations.
  Inherited ignore-filter valid/invalid-WD regressions are mandatory.
- Read-only initial/precondition diagnostics have no assignments and therefore
  need no diagnostic modifies frame. Omit that generated frame only when observed
  heap assignments are absent; retain original method frames and all observed
  transition query frames. Existing initial-state and old/new heap polarity tests
  validate both query shapes. This removes unnecessary frame-lambda preprocessing.

- Root found an existing correctness concern: UserGuide lines739–750 warns
  --force-prune can produce tests violating preconditions, and native
  ProgramModification.SetupForCounterexamples disables Prune unless explicitly
  forced. ContractSolver inherited verification-default Prune=true while using
  SAT as original-state evidence. Explicitly disable it for contract queries;
  certificate UNSAT proofs retain ordinary verifier settings. This is a soundness
  correction, not a performance claim, and the next frozen probe must measure it.

- The first unpruned regression incorrectly expected a bare non-null class argument
  to entail inhabitance of every unmentioned field. Native encoding still returns
  SAT for that artificial query; this is why the real PrepareInitial already emits
  explicit exists-value constraints for uncertified omitted refinements. Preserve
  the failed test log (definition-testgen2:103pass/1fail), replace the mistaken
  expectation with actual generated initial queries for inhabited/empty omitted
  fields, and retain the existing omission gate. No axiom is invented to satisfy
  the test. This regression validates the real safeguard, not a claim that it
  uniquely distinguishes the pruning option.

- Definition/selection slice now passes solution builds1/2/3/4 with zero warnings
  and errors (34.49s/34.76s/16.47s/14.20s). Initial focused99/99 passed19s before
  exact coverage, unpruned SAT and extra premise regressions. Corrected final focus
  passes104/104 in26s: ContractPhaseTimingTests, ContractSpecificationCheckerTests,
  ContractQueryTests and ContractRuntimeHeapQueryTests. All use --no-build
  --no-restore -m:1 and the already approved VSTest socket escalation. Retained
  logs definition-* under the same check directory include the artificial failed
  expectation separately. Driver focus and final formatting precede freeze05.

- Corrected final native focus104/104 passed26s; Driver focus6/6 passed25s
  (same four integration method filters as certificate slice). Final formatting
  runs before stable freeze05 handoff. Native unsupported opaque-premise failures
  persist as Unknown internal query artifacts; they do not escape the campaign.
  Full suites, all-four strict-budget integration and independent review remain
  outstanding. No witness-choice production feature was added.

- Frozen05 completes77.25s but admits no valid sample: World/IO certificates pass
  within10s, while initial unpruned SAT returns after15.772s and is correctly
  rejected by the new deadline. Continue with native typed construction rather
  than global higher-order model search. Root holds the native lane briefly for
  Arguments/Predicates encoding comparison and cancellation API inspection.
- Compositional proof design is approved in principle before implementation:
  refactor initial validation into a private core that can collect candidate pure
  value obligations during planning, never admit on those candidates alone. The
  plan exists only if all other reference/shape/omitted-inhabitant checks succeed.
  Construct each exact literal as a local of its declared type with no formals,
  requires or heap assumptions; native assignment WD proves nested type membership.
  Require all original type and function WD certificates, including functions
  lacking explicit requires/ensures. Native UNSAT is the only success outcome.
- Coverage includes original entry input formals and the actual receiver, because
  the replaced global SAT query bound and typed those too. A valid heap with an
  invalid refined argument must not pass. Initializer-bearing immutable fields
  remain outside the compositional domain: type membership alone does not prove
  their original defining equation. Unsupported types/views and unresolved omitted
  inhabitants retain the existing full typed SAT path. Plans/proofs/caches are bound
  to the original source program and exact captured values. No DTO changes, larger
  budgets, trust assumptions, task-specific names or new packages are permitted.

- Encoding06 is negative evidence: Arguments cancelled16.335s and Predicates
  cancelled16.683s on the exact frozen05 initial query. Keep original encoding.
  Root reflection found native InferAndVerify already accepts CancellationToken;
  the existing DafnyMain wrapper drops it. Root now exclusively owns the bounded
  optional-token propagation through DafnyMain, ContractSolver and
  ContractSpecificationChecker plus cancellation tests while owner implements
  compositional membership. Existing native logging and outcome logic remain.

- First compositional solution build passes with zero warnings/errors (11m05.30s). Native focus116 cases:112 passed,4 failed in1m07s; both actual-running cancellation tests passed. Three new fixtures need explicit constructors for witness-* fields; one imported-carrier regression exposes diagnostic static/module syntax and constructor import-alias qualification. Correct these without changing admission semantics, then rerun affected focus.

- Second merged solution build passes zero warnings/errors (6m32.68s), including the binary-compatible native cancellation overload bridge. Before final focus, tighten compositional omissions to affirmative structural/certified inhabitants; legacy OmittedNeedsQuery=false is not a constructive certificate. Add opaque omitted-type fallback and both-polarity newtype construction regressions. Initial-cache reuse is exact full-request/source identity; observed-state consistency remains unchanged.

- Final construction-build3 passes16.62s, zero warnings/errors. From the owning
  Dafny root, `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore
  --filter 'FullyQualifiedName~NativeInitialConstruction|FullyQualifiedName~NativeCancellationStopsQueryAndCertificate'`
  passes15/15 in5s. Driver focus with NativeConstruction,
  ReusesExactNativeInitialCertificateForHeapDecision,
  ValidatesResidualInitialFieldConstraint, CertifiesOriginalOmittedWitness,
  CertifiedSpecificationDecidesBothHeapPolarities and
  InitialFieldConstraintCalleeRemainsUnchecked passes12/12 in57s. No skipped tests.
  Logs: construction-testgen2.log and construction-driver1.log under the existing
  checks directory. `make format` exits0 with the existing workspace-load warning;
  `git diff --check` passes. Owner wiki/index records the bounded soundness evidence
  and failed approaches without claiming integration acceptance. Hand source and
  native execution to root for supported packaging/freeze06/public probes.


### Ready next slice: reuse compiled original type checks (2026-09-28)

Frozen06 initial construction reaches native verification in9.404s but cannot
prove the InodeFileSystem membership. Diagnostic profiles07–09 isolate recursive
set/path extensional facts: ordinary proof-only pruning still reports the same
failure in6.208s, and six asserted equalities time out. Preserve all profiles and
do not introduce unhelpful pruning/fuel/encoding options. The same frozen sample
already executes original compiled type checks over the exact filesystem value:
for example the original IO.fs return-type check, not a draft-owned arbitrary
clause. This supports a smaller extension than new heap snapshot hooks.

The approved design keeps native WD certificates mandatory and treats only
actual compiled membership execution as Runtime evidence. Add an internal
TypeConstraint marker to generated clause metadata. Recover the authoritative
type from the original callable's matching single input/output formal; a passed
arbitrary predicate containing the value is not membership evidence. Require
actual check records, Runtime declared/compiled classification, exact serialized
value and original constrained type identity. Restrict reuse to reference-free
pure carriers whose membership cannot depend on a changing heap. Exclude draft
owners, synthetic owners and any reachable drafted type dependency. Duplicate
identical observations may repeat during execution; conflicting outcomes for an
identical type/value invalidate reuse. Malformed or missing evidence cannot admit.

The existing construction planner still checks all root inputs and the receiver,
references/aliases/classes/arrays, immutable initializer exclusions and affirmative
omitted inhabitants. Runtime evidence covers only matching pure carriers; all
remaining values retain native typed construction. Admission requires the full
original type/function WD scope plus complete construction or runtime evidence
for every carrier. A failed original callee check still invalidates the sample
through the existing campaign gates. Record reused evidence in internal artifacts,
never as an SMT verdict and never by changing public campaign DTOs or budgets.
No new reflection hooks, capture schema, interpreter, benchmark change, packages
or paid calls are needed. Status: in-progress; exact scope announced to root before edits.

- Provenance tightening before acceptance: internal clause metadata binds the entire original source set (sorted paths and content hashes), including imported type/function definitions. Collected evidence also binds the exact original resolved Program and source fingerprint. Add same-path imported subset changed from a weaker to stronger constraint with an unchanged owner file; both stale clause metadata and cross-program evidence reuse retain native proof. The actual Driver recursive getter fixture must exercise synthetic function output/contractResult rebinding. First slice build runtime-evidence-build1 passed34.80s, zero warnings/errors; tests pending.

- Current membership slice validation (owning Dafny root): build2 passed34.26s,
  build3 passed14.06s, each zero warnings/errors. `dotnet test
  Source/DafnyTestGeneration.Test --no-build --no-restore --filter
  'FullyQualifiedName~RuntimeTypeEvidence|FullyQualifiedName~NativeInitialConstruction'`
  passed29/29 in7s. Driver filter `ReusesCompiledRecursiveTypeCheckForCapturedHeap|
  NativeConstruction|ReusesExactNativeInitialCertificateForHeapDecision|
  InitialFieldConstraintCalleeRemainsUnchecked` passed8/8 in21s, no skipped tests.
  Its valid recursive fixture excludes constructor membership evidence and
  explicitly requires reused original M.Read contractResult membership; invalid
  carrier and invalid callee cases stay inconclusive. Same-path imported
  stronger-type cases reject stale metadata and cross-program evidence reuse.
  Logs: runtime-evidence-build1/2/3, runtime-evidence-testgen1 and
  runtime-evidence-driver1 under the existing checks directory. Owner wiki/index
  records the bounded extension; frozen acceptance and independent review remain
  outstanding. `make format` exits0 (existing workspace-load warning), and
  `git diff --check` passes. Source/native lane handed to root for supported
  packaging, frozen07 and public probes; no further source edits during freeze.


### Ready next slice: observed construction and evidence timing (2026-09-28)

Frozen07 probe08 detects the stdin mutant: valid1, violating1, no population
unchecked/timeouts/runtime errors,99.946s. Exact IO.fs/stdin/stdout/stderr runtime
type checks cover carriers; residual native construction passes. Probe09 has
valid1 but no violation because original PadLeft by-method proof remains
unvalidated. Both are one-sample development probes, not full64/all-four acceptance.
After sample completion, file timestamps expose30.633s before the first native
scope artifact; native query phases account for23.33s of56.45s total classification.
Add actual collection/preparation phase boundaries before attributing that gap.

The next generic route requires an explicitly constructive (not merely SAT)
initial cache entry bound to the exact request. Existing Prepare validates equal
object identities/types/array lengths/captured fields, unchanged immutable cells,
references, actual root inputs/outputs and frame. Check full original native WD for
all final field and output types. Reuse source-bound exact pure Runtime memberships
or prove remaining final carriers with zero-input native typed assignments. Keep
unsupported/initialized immutable/unknown omitted cases on the existing full SAT
path. Every omitted field must retain the same affirmative inhabitant across both
states; pure type constraints cannot observe changing heap state. Native original
P remains mandatory before accepting the composed observation. Final positive and
negative original Q queries and callee validity are unchanged. No postcondition is
assumed to establish consistency, no new allocation or hidden state is invented.
Internal artifacts record initial provenance, exact observed material and every
Runtime/native component; public DTOs, inputs, source bytes and budgets unchanged.

Evidence collection must check external cancellation and monotonic campaign
remaining time. Cancellation discards all partial evidence, since a later false
observation could contradict an earlier true one. Missing evidence retains native
fallback; expired campaign cannot publish a new certificate. Root approved generic identity
indexing after source evidence identified DescribeFunction body clones and repeated
whole-program result-name traversal; telemetry will measure its benefit. It must retain
source/type/value/draft/malformed/conflicting checks. No arbitrary fuel/pruning,
proof-scope bypass or benchmark-specific behavior. Root separately profiles native
proof assistance; no production helper hints included in this slice.

Status: in-progress. Parent authorized this bounded scope after probe09; ready
plan announced before edits. Native execution
is reserved for root final11; edits may begin, builds/tests wait for release.
Validation from owning Dafny root: solution build; TestGeneration observed and
initial construction/evidence tests; Driver observed-composition admission and
both-polarity tests plus existing heap integrity regressions; make format and diff
check, followed by root supported package/frozen probes. Record failures, queries,
phase outcomes and unchanged query/campaign deadlines separately.

- Observed-build1 passed35.26s zero warnings/errors. Full
  ContractRuntimeHeapQueryTests plus ContractPhaseTimingTests focus passed69/69 in16s,
  including native final/output constraints, omitted inhabitance, frame, shape,
  immutable/reference checks and collection/native cancellation. Driver focus is
  running. Parent requests full owner Contract regressions before stable handoff:
  `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter
  'FullyQualifiedName~Contract'` and the same command for `Source/DafnyDriver.Test`,
  from the Dafny root; expected all pass with no skipped tests. Retain failures
  and repair only concrete regressions before packaging. Independent review is
  still unavailable due runtime thread limit.

- Observed Driver focus passed12/12 in41s, no skips. New both-polarity case
  uses an actual Runtime output membership to cover final carriers with no native
  observed carrier query; explicit initial Constructive provenance and original
  Q verdicts are asserted. Original invalid P remains rejected. The M.Read result
  fixture now includes an original contractResult name collision. `make format`
  exits0 with the existing workspace-load warning; diff check passes. Full Contract
  TestGeneration suite is running (observed-testgen-full1.log), then Driver full
  suite. No original proof scope or native helper-hint changes were introduced.

- Full Contract TestGeneration passes418/418 in2m53s. Driver full1 exposes
  ScalarClosedCalleeUsesOriginalSources(valid case): exact result==4 existential
  positive target error235ms, negative native phase cancellation3106ms under the
  existing3s fixture limit. Artifacts retained at
  /workspace/tmp/contract-runtime-heap-db86fc97bf274d32b2307e6358c4a769. Parent
  authorizes exact positive-query default versus existing MBQI-option profile,
  preserving query bytes/unpruned semantics/3s limit. New temporary Profile.csproj,
  Program.cs and run.sh under /workspace/tmp/experiment/pbt-m2-scalar-mbqi-profile-20260928-01
  reference only frozen07 assemblies, no packages; build/run in tmux after the
  active suite, preserve each outcome/phase/elapsed/hash. No production MBQI toggle
  or budget increase without concrete native evidence and further plan amendment.

- Driver full1 finishes183/186 pass,3 fail in10min: two original scalar
  quantified proof failures and one nested generic runtime-helper qualification
  exception. Preserve the full log and raw artifacts. Extend the approved temporary
  profile to exact exists-positive and forall-positive/negative queries, default,
  MBQI, proof-only Prune and both. Temporary PrunedContractSolver.cs is an exact
  current solver copy except class name and Prune=true, diagnostic only. Native
  proof-only pruning may be adopted only after measured benefit/caller audit:
  weaker assumptions preserve UNSAT proofs, but pruned SAT cannot admit any state
  or model. Production query kind/capture direction must enforce that boundary.
  Fix runtime generated helper qualification using owned synthetic receiver
  identity before full original-source qualification, with the existing nested
  generic failure and cross-module recursive wrapper regressions. No broad
  qualification fallback or benchmark branch. New exact source scope if needed:
  ContractSolver.cs, ContractQueryTests.cs and existing Transformer.cs/test rows.

- Exact scalar profile01 completed in tmux, helper build5.63s zero warnings/errors.
  Exists-positive: default SAT1645ms, MBQI UNSAT757ms, pruned UNSAT246ms.
  Forall-negative: default/MBQI timeout3103/3104ms, pruned UNSAT138ms.
  Positive forall: default SAT380ms, pruned SAT191ms, MBQI times out3110ms.
  Preserve all12 raw results and query hashes. Adopt only native proof pruning
  for ClosedClause/ObservedPostcondition with captureModel=false; keep existing
  MBQI polarity detection unchanged. Caller audit: ClosedClause feeds runtime
  proof or native carrier admission requiring UNSAT; ObservedPostcondition feeds
  runtime or ContractTestRunner, both retaining original consistent state and
  opposite UNSAT before violation. Generators/realizers use PremiseConsistency,
  ContractRealization, CallPrecondition or captureModel and remain unpruned.
  SAT in proof-only results remains only native target nonproof, explicitly marked
  in diagnostics, never state/model/violation admission by itself. Add tests for
  original positive exists, false forall opposite, nonlinear false/undefined
  checks, and inherited Prune=true unable to erase an unused inconsistent global
  declaration for premise/model queries. Qualification fix orders original AST
  qualification before inserting owned runtime shape-helper calls, so source
  visibility checking never treats generated helpers as original declarations.
  Parent authorized this measured, direction-aware scope; implementation resumes.

- Observed-build2 passes18.74s with one synchronous StringWriter analyzer warning;
  changed logging to StringBuilder.AppendLine (no behavior change). Query/cancellation
  focus passes49/55; six new unused-global fixture cases fail at resolution because
  witness-* makes a static bodyless constant potentially empty. Preserve log;
  correct fixture to explicit invalid witness0 so native consistency, rather than
  resolver rejection, tests the pruning boundary. Audit whether constructive
  admission also needs original global constant assumptions beyond reached types.

- Native unused-static-constant boundary confirmed6/6 after fixture correction.
  BoogieGenerator.Methods.cs445 emits unconditional static constant type/allocation
  axioms; Fields.cs134 adds RHS equality,168 verifies RHS WD. Extend exact scope
  to `ContractSpecificationChecker.Scope` and `ExecutionReachable` optional constant
  roots, plus initial/observed RequiredScope and heap inhabitance helpers. Include
  every original static constant type/witness and native WD/definition dependencies
  for constants with RHS. Bodyless constants have no implementation to trust:
  require affirmative type inhabitance, including a same-typed captured reference
  whose complete heap will be certified. Existing structural/native witnesses cover
  pure cases; absent witnesses defer to full consistency. Do not discharge called
  extern behavior, remove original constraints or branch on a benchmark name.
  Public ProcessHandle is an example of abstract typed reference requiring a real
  captured inhabitant, not a special case. Tests cover invalid typed RHS/witness,
  valid constrained global, abstract reference with/without matching capture and
  unchanged frame/immutability. Mark all fixture/setup failures explicitly.

- Global own-WD circularity refinement (parent approved): constructive eligibility
  requires structural inhabitance for global types, independently of native type
  certificates. Explicit RHS equations must be closed acyclic literal, conversion,
  constructor or collection values with exact recursive type compatibility, plus
  original native RHS WD. Refined/opaque globals or unsupported function/cyclic
  equations fall back to the unchanged full consistency query. Tests distinguish
  fallback from successful construction, including invalid RHS, false witness,
  valid refined global, and abstract exact reference with/without capture.

- Parent-approved proof-context strengthening: add internal
  `Source/DafnyTestGeneration/ContractTesting/ContractGlobalAssumptions.cs`.
  Match resolved Boogie functions by original bodyless static constant
  FullSanitizedName, remove every axiom referencing those exact function objects
  and its OtherDefinitionAxioms metadata reference in detached specification and
  proof-only query translations. Retain declarations, assertions and procedures;
  SAT/model queries remain unchanged. Record removed axiom identities/counts in
  internal diagnostics. Test original/import identity, direct and transitive
  false-witness vacuity, captured global references and unchanged model theory.
  This weakening of proof premises makes a proved result stronger and closes
  circular justification by global type/allocation axioms; it may reduce support.

- Complete campaign global regression exposes the legacy primitive-field shortcut:
  CheckInitialTypes returned true before construction/global gates, admitting an
  inconsistent unused global as population.Valid=1 (no Q decision). Tighten the
  public host-only CheckInitialTypes result to unknown whenever static global
  assumptions exist; the internal construction planner still validates carriers
  independently. This routes even empty/primitive captures through native global
  WD plus structural eligibility or unchanged full consistency. The new Driver
  tests deliberately use ordinary int fields; preserve the failed run evidence.

- Global patch local evidence: build1 failed IList.RemoveAll API use; corrected
  explicit metadata removal. Build2/3 passed (build3 13.24s, zero warnings/errors).
  Focus129/130 passed; remaining fixture rejected before verification because a
  non-extern bodyless nonnull constant is potentially empty. Corrected the fixture
  to an abstract extern reference (matching the supported native source form),
  then10/10 global cases passed4.28s, including a valid transitive refined omission.
  All three previously failing Driver names pass4/4 in13.84s. Added complete
  primitive-heap global campaigns; first run2/2 failed Valid=1, revealing the host
  shortcut above. Build6 passed13.36s zero warnings/errors after gating it; corrected
  campaigns pass2/2 in14.45s. Full Contract suites now running on that state.
  New sound global gating may cause empty-heap M1 sources with uncaptured abstract
  reference globals to use full SAT; no performance/completeness claim until root's
  frozen diagnostic. No static-global source assumptions are silently ignored.

- Full native regression after the bounded fixes: from the Dafny owner root,
  `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj
  --no-build --no-restore --filter 'FullyQualifiedName~Contract'
  --logger 'console;verbosity=normal'` passed439/439 in2.7742min
  (`observed-testgen-full2.log`). Driver counterpart is running against the same
  build6 source; no full-suite/frozen acceptance claim until its actual result.

- Full Driver2 reveals one compatibility failure so far:
  `IsolatesUnrelatedNativeHostState` requires zero-query pure-goal isolation with
  an unused abstract Handle -> Region -> int global. Parent authorizes a bounded
  structural extension in ContractRuntimeHeapChecking (same test files): finite
  acyclic nonnull class inhabitants from all instance fields, including ghost and
  immutable fields, with primitive/finite-datatype/nullable-reference inhabitants.
  Reject generic/inherited/array/cyclic/reference-trait cases, unsupported
  refinements/arrows and any initialized immutable fields. No constructor is
  executed or trusted; this is an existential logical heap witness. The host gate
  bypasses global queries only for bodyless globals whose entire inhabitants are
  independently structural. Initialized globals retain native RHS WD gates.
  Preserve original zero-query fixture and failed full2 log. Add direct positive
  finite-ref and negative empty/refined/cycle/generic/inherited/initializer cases;
  rerun focused global/isolation, then full affected suites before handoff.

- Datatype member-constant guard (parent confirmed): ordinary constructor fields
  are not the entire logical shape when a datatype has readonly member constants.
  Conservatively reject these shapes in independent structural inhabitants,
  existing global/omitted inhabitants, pure carrier planning and host datatype
  checks. Original native checks remain; unsupported cases use full consistency.
  Add a source-backed member-constant fixture for both host and native construction
  paths, then lock source for full checks. No expanded datatype support is added.

- Driver full2 completed187/188 in9.9180min; sole failure is the original zero-query
  native-host isolation case, preserved in observed-driver-full2.log. Bounded
  structural implementation build7 passed34.55s zero warnings/errors, global
  focus20/20 passed4.35s, and original isolation plus inconsistent-global campaigns
  passed3/3 in14.15s without changing fixture budgets. Datatype member-constant
  exclusion now covers all structural, host and pure-construction paths. Build9
  passed16.58s zero warnings/errors and final focused guard tests12/12 pass2.21s.
  Production source locked; full TestGeneration3 and Driver3 follow on this state.

- Final structural-state native suite:451/451 Contract TestGeneration tests pass
  in2.7703min (`observed-testgen-full3.log`) on build9. Same command as full2;
  additional coverage is the finite global heap and datatype member-constant
  boundary. Driver full3 now runs with original fixture budgets and no production
  edits during execution. Earlier failed full1/full2 runs remain distinct evidence.

- Complete pre-final-guard state build9 passed both owner suites: TestGeneration
  451/451 in2.7703min and Driver188/188 in9.8336min (full3 logs). Final source audit
  identifies two concrete admission boundaries; parent authorizes bounded guards,
  not new support. (1) Every original datatype member constant can impose type/RHS
  equations on an inherently inhabited constructor, even if unused and no heap is
  captured: force host unknown and explicit unsupported global-shape scope failure.
  Do not certify that shape with its own axioms; retain every model/SAT translation.
  (2) Captured initialized constants, including omitted primitive/nat ghost slots,
  need original RHS WD/dependencies and full consistency; host field types alone
  are insufficient. Force unknown for these slots while preserving known false;
  constructive plans remain excluded. Existing RequiredScope follows root class
  constant RHS/function edges, and only original unpruned consistency can admit
  after that WD gate. Add scalar empty-heap datatype/global controls, raw native
  consistency evidence, omitted nat=-1, invalid-RHS-call and valid initializer
  controls. Preserve original budgets; no benchmark changes. Exact files remain
  ContractRuntimeHeapChecking/InitialTypeProof, ContractRuntimeHeapQueryTests,
  ContractQueryTests, ContractRuntimeHeapTests and ContractRuntimeCheckTests.

- Parent confirms the initialized-constant capture fixture correction: keep its
  original Seed()/Box/Goal source and zero-query configuration, preserve actual
  execution/captured tag=7 and RuntimeErrors0, but require valid0/unchecked because
  readonly equations now need validation. Add the identical source under an
  existing normal native-query budget retaining ViolationFound, valid samples and
  violation tag=7. This documents stricter validity rather than dropping capture
  or detection coverage; production/public benchmark budgets are unchanged.

- Final-guard native preflight3/4 passes; the raw unused datatype member query
  returns target SAT, not expected UNSAT. Preserve exact source in
  unused-datatype-global-raw1.dfy and failed observed-finalguard-testgen1.log.
  Do not interpret that native target counterexample as proof of full datatype
  consistency. Keep explicit unsupported global-shape rejection. Replace the
  incorrect native expectation with a separate activated-original-fact test:
  assert the original Item().bad == 0 before assert false, adding no assumptions.
  Complete campaign tests separately require admission rejection for the unused
  contradictory shape. This is explicit native incompleteness evidence, not a
  passed original consistency proof.

- Final guard build11 passes17.32s with zero warnings/errors; focused native
  guard tests4/4 pass2.8221s. Driver guard focus5/7 passes27.4057s: both positive
  initialized-constant controls fail before native verification with `LHS of
  assignment must denote a mutable field`. Saved query injects an unused heap
  allocation constructor assigning `this.tag := tag` despite original tag RHS.
  Preserve observed-finalguard-driver1.log and its exact diagnostic directories.
  Executable generator constructors share ConstructorDeclaration, so dropping
  assignments there risks silently substituting original initialized values for
  supplied ones. Bounded correction, ready before edits: add internal query-only
  source edits to ContractHeapPlan/ContractHeapFactory, retaining identical field
  export and additional premise edits but excluding allocation constructors and
  their exports. ContractPreparedProgram.DiagnosticSourceSnapshots and
  ContractHarnessBuilder.Insert use those edits; executable harness SourceEdits,
  allocation statements and ConstructorDeclaration remain unchanged. Native
  queries never allocate these objects and keep original readonly RHS plus exact
  captured equality constraints. ContractRuntimeHeapQueryTests will verify native
  matching/mismatching readonly values across a revealed module export. Rerun
  final guard native and Driver controls, then format/diff and hand off stable
  source for parent's frozen M1 probes before the mandatory final full suites.
  This changes no constructor protocol, benchmark, native/public budget or DTO.

- Query-only projection build12 passes34.95s, zero warnings/errors. Native focus
  observed-finalguard-testgen3 passes5/6: imported matching readonly value works,
  but mismatching value returns target SAT. Existing export edit only `provides`
  an otherwise hidden constant, hiding its original RHS from the query. Extend
  the same bounded query-only visibility edit to `reveals` initialized constant
  definitions for originally revealed heap classes, including provided-but-opaque
  fields; retain original RHS byte-for-byte. Executable edits remain unchanged.
  This restores original equations rather than injecting any assumed fact.
  Add same-module and cross-module value controls; preserve failed attempt.

- Native readonly visibility controls now cover same-module, imported hidden field
  and imported provided-but-opaque field, each matching7/SAT and mismatching8/UNSAT
  against original const7. Query-only export reveal preserves original definition;
  executable constructor and export behavior are unchanged. Build13 passes34.89s,
  then build14 including expanded cases passes14.44s, both zero warnings/errors.
  `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj
  --no-build --no-restore --filter 'FullyQualifiedName~InitialQueriesCheckImportedInitializedConstant|FullyQualifiedName~DatatypeMemberConstantsBlockConstructiveAdmission|FullyQualifiedName~InitializedConstantsCannotUseHostMembershipAlone|FullyQualifiedName~UnprunedReadonlyFactsExposeInconsistentDatatype'`
  passes10/10 (~3s), observed-finalguard-testgen4.log. Driver controls rerun next.

- Final Driver guard control rerun7/7 passes (~19s),
  observed-finalguard-driver2.log, with exact command
  `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore
  --filter 'FullyQualifiedName~CapturesObjectWithConstantInitializer|FullyQualifiedName~InitialConstantEquationsRequireValidation|FullyQualifiedName~ScalarAdmissionChecksUnusedDatatypeConstants'`.
  Both original positive initialized-constant controls now admit and detect;
  zero-query tag capture, invalid nat initializer, invalid initializer precondition,
  unused datatype constant rejection and ordinary datatype control all pass.
  Earlier native5/6 and Driver5/7 failures remain preserved. Final full suites are
  not yet rerun: parent schedules supported packaging/frozen M1 probes first to
  measure the global gate performance boundary on immutable binaries.

- `make format` exits0 with the existing workspace-loading warning only
  (observed-finalguard-format.log); `git diff --check` passes. Stable source/native
  lane handoff to parent after build14 and focused native10/10, Driver7/7.
  No full4 launched. Parent owns supported package/freeze/M1 diagnostic probes;
  owner holds all source writes/builds/tests until coordinated release. Full final
  Contract suites, all-four/full64 evidence and fresh independent review remain
  required and unclaimed. No commits or benchmark edits.

## Bounded M1 compatibility and reusable independent global proof (ready)

Parent authorizes this follow-up after immutable frozen08 probes: digit-order
probe12 detects with valid1 but consumes two source WD queries and one per-input
initial SAT; distinct64 inputs would exceed16 queries. Blankstreak probe13 fails
initial preparation because an irrelevant ghost output is rejected. M2 probes10
and11 retain valid1 (stdin detected, exit original CoreSummary still unchecked).
No budget, DTO, benchmark, trust or evaluator change is authorized.

| Exact files/symbols | Change and necessity | Validation |
| --- | --- | --- |
| `ContractHarnessBuilder.Prepare`/`ValidateSignature`, `ContractRuntimeHeapChecking.PrepareInitial` | Internal initial-only mode checks inputs/receiver, not unused outputs; executable/full-query mode keeps original signature restrictions | Ghost-output actual campaign succeeds; ghost input still rejected; original initialized-constant controls |
| `ContractSpecificationChecker`, `ContractInitialTypeProof`, `ContractRuntimeHeapChecking.AbstractGlobalsInhabited`/`HasStructuralInhabitant` | Publish/cache independent global inhabitance only under exact original Program/source identity and complete native type/RHS WD closure whose abstract-global axioms were removed. Construct finite acyclic fresh reference heaps and certified leaf/pure-arrow inhabitants without captured/input witnesses. Keep initialized-static values on independent structural closed acyclic RHS/type gate. Old conditional captured proof stays separate; no failed-independent certificate published | Valid/false/optout/circular witnesses, direct/transitive vacuity, imported changed source, no captured witness promoted, empty/inhabited arrow codomain, readonly/datatype guards |
| `ContractRuntimeHeapChecking.CheckInitialTypesCore`, `ContractInitialTypeProof` | Decisive exact host membership runs before residual native planning; unknown constraints still need exact runtime evidence/native proof, and false carrier never becomes accepted via planned proof | More than16 distinct inputs with max3 queries; later invalid refined input; original nested refinements, root inputs and observed construction |
| `ContractRuntimeCampaignRunner` internal initial/observed certificate artifacts | Record independent global source/scope/native-context provenance plus host/runtime/native carrier counts; keep full-request cache/deadlines and per-input P | Actual Driver artifact and budget assertions; no public schema change |
| `ContractRuntimeHeapQueryTests`, `ContractRuntimeHeapTests`; existing `ContractSpecificationCheckerTests` if needed | Behavioral regression coverage for the above boundaries | Focused TestGeneration/Driver, supported build, format/diff; full Contract suites after successor frozen probes |
| Owner wiki/index | Record failure provenance, exact bounded support and validation | Links, no all-four/full64/independent-review acceptance claim |

Implementation uses existing stripped native checker and structural/value helpers;
no new general heap solver. Independent certificate never takes a captured heap,
input value, runtime membership record or draft as evidence. Source identity checks
are mandatory even when an empty native scope trivially accepts. Closed initialized
globals remain structurally eligible before their own native WD may support any
certificate. Unsupported source shapes retain original consistency/fail-closed
paths. Native lane is owner-exclusive until focused stable handoff; final complete
suite reruns remain mandatory after immutable successor diagnostics.

Status: in-progress (ready scope announced before implementation).

- M1 follow-up build1 passes35.21s with zero warnings/errors. First focused
  heap/specification suite126/131 passes (~19s); all five failures are invalid new
  fixture declarations missing constructors for opt-out/non-null fields, before
  any native verdict. Preserve m1-global-testgen1.log. Add ordinary constructors
  initializing those fields; constructors remain unexecuted/untrusted by the
  logical inhabitance proof. Existing original/rejection cases and valid new
  certificates pass in that run. No production logic changed for these failures.

- Build2 passes14.46s, zero warnings/errors. Corrected bounded native focus10/10
  passes (~1s): `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj
  --no-build --no-restore --filter 'FullyQualifiedName~IndependentGlobals|FullyQualifiedName~ConstructiveAdmissionRequiresExactGlobalReference|FullyQualifiedName~InitialPreparationStillRejectsGhostInputs'`.
  First broader command selected `ContractRuntimeHeapQueryTests|ContractSpecificationCheckerTests`
  and passed126/131 before the fixture-only corrections; no production failures.
  Logs m1-global-testgen1/2 retain both attempts separately.

- Driver focus13/13 passes49s (`m1-global-driver1.log`), exact command:
  `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore
  --filter 'FullyQualifiedName~IndependentGlobalProofIsReusedAcrossPureSamples|FullyQualifiedName~InitialConstantEquationsRequireValidation|FullyQualifiedName~CapturesObjectWithConstantInitializer|FullyQualifiedName~ScalarAdmissionChecksUnusedDatatypeConstants|FullyQualifiedName~RejectsOrdinalInput|FullyQualifiedName~IsolatesUnrelatedNativeHostState|FullyQualifiedName~ObservedConstructionDecidesBothOriginalPolarities|FullyQualifiedName~ObservedConstructionKeepsInvalidEntryRejected'`.
  The actual20-distinct-input/ghost-output campaign admits20/20 with only one native
  source verification query under max3; no heap or carrier query. All20 certificate
  artifacts contain host-membership counts and independent source/scope/context
  provenance. Artifact directory:
  `/workspace/tmp/contract-global-reuse-5d5bb4b86b5941dfb38f711307f4134f`.
  Original readonly/global rejection and zero-query isolation behavior pass.
  This is a local bounded fixture, not public full64/all-four acceptance.

- `make format` exits0 (existing workspace-loading warning only), log
  m1-global-format.log; `git diff --check` passes. Owner source/native lane is
  stable and handed to parent for supported package/frozen09 probes14–17. No
  additional suite/probe is running, no full4 launched. After immutable diagnostics,
  mandatory final TestGeneration/Driver `--filter 'FullyQualifiedName~Contract'`
  suites remain, on final source, plus independent review when runtime permits.
  No benchmark/DTO/budget/package change and no commits.

## Final measured preparation reuse and initializer visibility follow-up (ready)

Frozen09 proves M1 populations again (digit64valid/63violating,168.630s; blank64valid/
33violating,131.105s; both2queries/no unchecked/errors/timeouts), but runtime remains
above r6 (25.468s/52.254s). M2stdin66.776s detects valid1; exit68.006s remains original
CoreSummary-unchecked. These are development diagnostics, not acceptance or parity.
Measured duplicate initial preparation/scope inside TryPrepare costs about0.86s per
sample; remove that exact repetition without a cross-sample shape cache.

| Exact files/symbols | Bounded change | Validation |
| --- | --- | --- |
| `ContractRuntimeHeapChecking.ContractRuntimeHeapCheck`/`PrepareInitial` | Internal original initial-request fingerprint, never a DTO; attest provenance for a same-sample reusable preparation | Wrong request/source/heap mutation rejected |
| `ContractInitialTypeProof` | Opaque preparation handle owns exact initial check, scope and checker identity; factory computes scope from resolved prepared method once. Fast overload validates binding and exact owned scope, then shared membership/global planning. Existing public raw wrapper retains full validation order | Same proof behavior; wrong checker/source/request/heap regressions; per-input exact membership, global proof and initializer gates |
| `ContractRuntimeCampaignRunner` | Reuse handle.Scope after native validation and handle.Initial for planning/fallback; preserve original full-request cache, phases, query counts/deadlines/P/Q | Existing20input query-budget/ghost-output control; public64 timing probes after handoff |
| `ContractRuntimeHeapQueryTests` | First preserve native hidden-Seed and hidden-constant-chain initialized readonly repro, with same-module/revealed controls | Record actual SAT/error/unknown before any guard; no claimed unmeasured result |
| `ContractQueryBuilder` only if native repro confirms gap | For initial SAT involving initialized fields, reject unavailable transitive original initializer definitions (functions and constants), including transparent functions hidden by export. Explicit unsupported; no broad export expansion | Hidden states fail closed, visible matching SAT/mismatching UNSAT, original native WD remains mandatory |
| `ContractRuntimeHeapQueryTests`, `ContractRuntimeHeapTests`; owner wiki/index | Behavioral regression checks and measured limitations | Focused native/Driver, format/diff, supported build; successor public probes before mandatory final full suites |

Parent releases source/native lane after all frozen09 diagnostics. Ready scope
announced before edits. No budgets, packages, benchmark definitions or DTO changes.
Independent review remains unavailable due runtime thread limit. Full Contract
suites and full r7-dev populations follow stable successor probes, not this slice.

Status: in-progress.

- Native baseline CONFIRMS initializer visibility gap before production edits.
  Build1 passes14.48s/zero warnings/errors; reproduction8/8 passes3s with observed
  hidden function and hidden constant tag8 both SAT after full original WD; their
  revealed versions reject8 UNSAT and accept7 SAT. Exact command uses
  DafnyTestGeneration.Test --no-build --no-restore --filter
  'FullyQualifiedName~InitialQueriesRequireTransitiveInitializedDefinitions'.
  Log reuse-visibility-baseline.log. Eight immutable source/query/result triples
  are retained in /workspace/tmp/contract-readonly-dependency-*; hidden mismatch
  function23f5fc2256d64e9d96b296305c677c47 and constant796016537c494fe78990341c590a5cb0.
  Apply the authorized bounded visibility guard; these SAT results are evidence of
  incomplete original definition context, not valid-state acceptance.

- Reuse/visibility production build2 passes34.67s/zero warnings/errors. Bounded
  heap/specification focus145/145 passes19s (`reuse-visibility-testgen1.log`),
  including exact wrong-checker/source/input/heap/prepared handle rejection and all
  previous global/readonly/type checks. Command selects
  `FullyQualifiedName~ContractRuntimeHeapQueryTests|FullyQualifiedName~ContractSpecificationCheckerTests`.
  Add only remaining planned private/opaque/transitive visibility controls, then
  build3 passes13.94s/zero warnings/errors; those four tests pass4/4 in140ms
  (`reuse-visibility-testgen2.log`, filter InitialQueriesRejectHiddenInitializerChains).
  All eight original visibility baseline artifacts remain unchanged. No observed
  native failure prompted a broader export or capability change.

- Final bounded Driver controls13/13 pass49s (`reuse-visibility-driver1.log`),
  using the same exact selected command as m1-global-driver1 above. This includes
 20distinct inputs/max3queries with ghost output, all original readonly/global
  rejection and positive controls, unsupported ghost input, zero-query isolation,
  both observed polarities and invalid entry P. No production change follows this
  pass; format/source identity and stable parent handoff follow. Full suites,
  frozen10 timing/populations and original exit-contract detection remain pending.

- `make format` exits0 (existing workspace-loading warning only),
  reuse-visibility-format.log; `git diff --check` passes. Source identity recorded
  in reuse-visibility-source-manifest.json:32 changed/untracked Source files on
  baseline060d5ad532f67d5367450689225274fb0a0243e7,
  manifest SHA2567a4b74645564ec3c468f49352a033db8b653199de0dc8a09bf59e81717fcbc46.
  Source/native lane handed to parent for supported packaging/frozen10 probes18–21,
  mandatory full4 Contract suites and actual r7-dev populations. No other process
  running, no full4 launched by owner, no further edits/probes while root validates.
  Owner may inspect remaining original CoreSummary/by-method proof scope read-only;
  this does not close the all-four/exit-contract objective.

## Final stable-source local validation and pending population acceptance

2026-09-28 owner-record update only; no source changes or native execution by the
owner. Root ran the final checks sequentially on the handed-off source/binaries:

| Check | Command/scope | Result and retained log |
| --- | --- | --- |
| Supported packaging | `/workspace/cosyn`: `make build-dafny` | Pass, 28.91s, zero warnings/errors; `package10.log` |
| TestGeneration Contract suite | Dafny root: `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~Contract -v:minimal` | 486/486 pass, no skips, 2m50s; `observed-testgen-full4.log` |
| Driver Contract suite | Same command with `Source/DafnyDriver.Test` | 195/195 pass, no skips, 9m53s; `observed-driver-full4.log` |
| Cosyn transport | Root integration transport selection recorded in the linked integration plan | 4/4 pass, 8.64s; `cosyn-transport10.log` |

Logs are under `/workspace/tmp/pbt-m2-optimization-checks-20260928`; their terminal
results were read for this record. Root confirms the exact 32-file Source set and
content hashes still match the handoff manifest. Frozen10 has 2205 files, manifest
SHA256 `5f982bdfd41842d53474b3eba0bae8773c5beb31a5fa6c14c742b5495c19122b`.

Frozen development probes18–21 retain the original budgets:

| Probe | Samples | Valid | Violating | Elapsed |
| --- | ---: | ---: | ---: | ---: |
| 18 M1 digit-order | 64 | 64 | 63 | 103.047s |
| 19 M1 blankstreak | 64 | 64 | 33 | 109.927s |
| 20 M2 drop-stdin | 1 | 1 | 1 | 64.705s |
| 21 M2 invert-exit | 1 | 1 | 0 | 65.808s |

Probe18 retains zero unchecked/errors/timeouts and improves over frozen09's
168.630s; probe19 improves over131.105s. Both remain slower than retained r6
25.468s/52.254s: no performance-parity claim. Probe21 still leaves original
CoreSummary unchecked. Artifacts are the corresponding
`/workspace/tmp/experiment/pbt-m2-optimization-20260928-{18,19,20,21}` directories.
These diagnostics and passing local suites do not establish full-population or
all-four acceptance. Root has started actual r7-dev M1 in tmux
`pbt-r7-dev-m1-20260928`; M2 follows. Status remains in-progress pending those
results and fresh independent review, still unavailable due runtime thread limit.

### Unimplemented logical-definition certificate design and blocker

Read-only implementation design (not independent verification) found native
function well-formedness and by-method correctness are separate obligations, but
the current contract certificate combines them. `ExecutionReachable` adds every
reachable by-method; checker selection also includes correctness for the shared
function/by-method source name. Therefore removing one reachability edge would
not establish a sound role distinction. A possible later logical-only certificate
would need explicit role-aware closure, exact native coverage and role-specific
cache identities; retain every original body/type/ensures/termination obligation,
proof-method dependency, override, visibility, source identity and trust gate.
It must not populate stronger runtime/construction `IsValidated` certificates.
Actual runtime callee preconditions, output types, ensures and original-definition
equality checks remain mandatory, as do original state consistency/P/Q checks.

The current PadLeft failure is original `CatCore.dfy:112:24`: the by-method loop
invariant passes inferred `seq<char>` to a `seq<RawByte>` parameter. PadLeft is not
unused: probe17 records six passed original result-type checks and six passed
definition-equality checks. Those concrete executions do not prove its universal
by-method obligation. Earlier final10 separately fails HelpTextSpec's original
Bytes result membership at `CatSpec.dfy:49:4`, a long ASCII literal concatenation.
The whole CoreSummary logical closure includes help/version branches even in a
run-mode sample. Existing reducer literal folding is not a certificate of the
original result-type obligation; native per-character checks use the expression's
inferred element type, here char. Prior native typed-prefix/display/equality hints
did not solve this under the unchanged query deadline. No existing inspected
generic reduction/native switch establishes that missing proof. A new generic
sequence-refinement proof decomposition would require a separate approved plan
and validation; no role split, helper, benchmark edit or assumed proof was added.
Current post-gate Q performance is unknown because certification stops first;
old frozen06 Q timeouts do not establish current downstream behavior.

## Frozen10 full r7-dev M1 population result (2026-09-28)

Root completed 36 rows covering12 variants in1441.191832s. Mutant detection is
6/6; spurious reports are0/5. The one verifying original variant is excluded from
those denominators. Across11 PBT campaigns,704 samples were generated, executed
and valid;282 samples violated contracts, with zero errors, unchecked samples or
timeouts. There are36 violation records and277294 runtime clause evaluations,
with zero closed-SMT clause evaluations. The latter counts clause decisions,
not the separate native validity-certificate work.

PBT campaigns take97.537–117.985s each,1200.807s total. Full M1 wall time materially
regresses from retained r6's670.248s; preserved detection/validity does not imply
performance parity. Root's mechanical audit passes2754 checks and117 summary-field
comparisons, retained at
`/workspace/tmp/pbt-r7-dev-mechanical-audit-20260928/m1-evidence.json`. Its explicit
scope is mechanical cross-checking, not fresh independent source/artifact review.
The owner read its audit metadata for this documentation update; no source or
native execution occurred.

Full M2 is now running in root-owned tmux `pbt-r7-dev-m2-20260928`, output
`/workspace/tmp/experiment/pbt-offline-20260928-m2-r7-dev`. This plan remains
in-progress: full M2 results, all-four detection and fresh independent review are
pending. The logical-definition certificate proposal remains unimplemented and
the original CoreSummary proof gate remains a known limitation.

## Measured recording overhead follow-up (in-progress, 2026-09-28)

Root authorizes only two generic reuse changes while the immutable frozen10 M2
population continues. Sample0 retains9663 check records/12.33MB; sample17 retains
10869/13.90MB. Source inspection finds a file open/append/close plus argv scan per
record and repeated base64/JSON shape decoding per serialized value. Their
individual timing shares are unmeasured. Sample18's cancellation reflects only
about2.124s remaining before the existing120s execution-reserve boundary, not an
observed5s sample overrun or parent240s deadline. No scheduling change is included.

| Exact owner files/symbols | Change, reason and required preservation | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeInstrumentation.cs`, generated `Bridge.Write`/path lifecycle | Lazy process-local output path and append writer; serialize every record in original order, write explicit LF and flush each completed record with existing UTF-8 behavior. Dispose at process exit; retain exception reporting, explicit early exits and partial traces. A fresh child process remains mandatory per sample. | Generated bridge fixture observes complete lines while child remains alive, abrupt termination, normal/explicit exits, repeated/changing values and separate process paths |
| `Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs`, generated `Shape` | Cache only immutable cloned parsed shape metadata by complete encoded token with ordinal string identity; generic argument distinctions remain part of the key. Dispose each temporary parsed shape document. Never cache values, verdicts or reference field snapshots. | Repeated shape reuse, bv7/bv8 generic instantiation, Unicode, mutable arrays/reference identity, malformed base64/JSON and unsupported parameter shape still reject |
| `Source/DafnyDriver.Test/ContractRuntimeRecordingTests.cs` (new); existing `ContractRuntimeObservationTests.cs` only if fixture extension is needed | Exercise actual generated bridge source in isolated child processes using existing `ContractCompilerWorker.CompileRuntimeAsync`: a tiny Dafny Main calls a controlled C# fixture dependency. No replacement production helper bodies; retain existing full campaign observation fixtures. Driver's in-process Roslyn3.7 is unsuitable for the newer syntax already emitted, so use the actual supported compiler lifecycle instead | Per-record byte/JSON conservation, visible flush before child exit, explicit stop/error paths, separate process files; existing generic/reference/cyclic/Unicode observation controls |
| Owner plan/index and `wiki/contract-testing.md`, `wiki/INDEX.md` | Record exact scope, failed attempts, final local checks and measured successor outcomes | Documentation diff review; do not relabel frozen10's486/195/4 as checks of changed source |

Lifecycle inspection: production `CompileRuntimeAsync` emits one assembly and
`ContractRuntimeCampaignRunner` launches a new `dotnet` process for every ordinal,
passing a fixed `--pbt-out` path. No supported caller changes the observation path
inside a process. Retain lazy opening so an invalid first record does not create
a file before serialization succeeds. Keep the writer open after `Complete`:
early-stop code may call Complete before process exit, and error reporting must
remain able to append. Each successful Write flushes immediately; no buffered
records may be lost merely because cancellation kills the child. No new catch or
I/O fallback is introduced.

After root releases the native lane, run the supported solution build, focused
`ContractRuntimeRecordingTests|ContractRuntimeObservationTests` plus applicable
existing timeout/error/isolation tests, `make format` and diff checks. Root then
packages a new toolchain/output identity and measures one/64 sample timings with
record count/content conservation, before final required suites and populations.
All original budgets, query reserve, contracts, inputs and per-sample isolation
remain. No process reuse, record dropping, verdict/value memoization, reflection
framework, role-certificate redesign, packages, DTO or benchmark edits. Source
edits are allowed now; builds/tests/profilers remain blocked by root's exclusive
native lane until the entire frozen10 M2 population finishes. This ready scope is
announced before implementation; overall objective remains in-progress.

- Drafted the two production changes and nine generated-runtime behavioral cases.
  The writer is assigned only after successful opening, so opening failures are
  not memoized; its fixed process path is cached separately. The live-trace test
  opens its reader with explicit read/write sharing while the child remains
  alive, then verifies identical retained bytes after killing the child. The
  complete-token shape cache clones before disposing its temporary document.
  Only these two production files and the planned new test file changed in this
  slice; static documentation/source diff checks pass. No build, test, format or
  native profiling has run: root retains the native lane for immutable full M2.
  Frozen10's486/195/4 results do not validate this new source.

## Original sequence-refinement proof steps (in-progress; native checks gated on recording baseline)

The matching root-plan section authorizes this separate slice. Recording-only
package11 and four transport cases now pass; frozen11 contains2212 files with
manifest SHA256 `5b8e7d65e9cdc21e5179d81dd7fa09960aab079109b9c87680948dc143571f62`.
Root explicitly releases LIVE SOURCE drafting now while its four unchanged-budget
diagnostics run exclusively from immutable copies. No proof helper or role split
may enter that baseline. No build/test/format/profile may run until all four
recording diagnostics and complete-record comparison finish and root releases the
native lane. Later final
suites/populations require a fresh final frozen identity; an intermediate recording
population is not required merely because an unrun r8 launcher exists.

Native source evidence: string literals become original `Seq#Build` terms in
`BoogieGenerator.ExpressionTranslator.cs`; `TranslateBinaryExpr` uses Seq#Append.
`DafnyPrelude.bpl:276–280` defines pointwise membership,1318–1319 supplies Build
preservation, and1164–1173 supplies Append length/index facts. `CheckSubrange`
currently asserts whole-result membership. Expose intermediate terms using only
checked assertions; no body rewrite, resolved-type retagging, replacement final
assertion, assumed equality, added axiom, arbitrary fuel or benchmark change.

| Exact owner files/symbols | Change / unmet need | Validation |
| --- | --- | --- |
| New `Source/DafnyTestGeneration/ContractTesting/ContractSequenceRefinementProof.cs` | Recognize original native sequence-membership assertions using actual prelude declaration identities; bounded postorder visits original empty/build/append terms and boxed elements. Insert checked element/prefix/build/append memberships using the same target element type, preserving native Lit/coercion wrappers and original terms | Native long valid/invalid concatenations, empty/escaped/verbatim/supplementary literals, unknown elements, arbitrary/false refinements; unsupported shapes retain original query |
| `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs`, `CheckModuleAsync` and internal `ContractSpecificationResult` | Apply only after exact implementation selection. Retain every original command, assertion and metadata; preserve original module/source/trust/deadline/native coverage gates. Record assertion inventories and insertion status as internal evidence, no public campaign DTO | Exact before/after command/assertion identity and order; added/original failure, missing coverage, cancellation or late results prevent certificate publication |
| New `Source/DafnyTestGeneration.Test/ContractSequenceRefinementProofTests.cs`; existing `ContractSpecificationCheckerTests.cs` when native fixture reuse suffices | Test actual native obligations plus structural proof preservation; meaningful negatives, not text-fragment tests | Focused helper/checker tests, same ten-second original result-refinement reproduction, final full Contract/transport validation only on final source |
| Owner plan/index and `wiki/contract-testing.md`, `wiki/INDEX.md` | Preserve measured results and unsupported/proof limits | No unrun proof or performance claim; link root's immutable diagnostics |
| Temporary `/workspace/tmp/experiment/pbt-m2-optimization-heap-profile-20260928/sequence15/{Profile.csproj,Program.cs,request.json,identity.json,scope.json,proof-CatSpec.json,proof-CatSpec.phases.jsonl,accepted.json,run.sh,run.log,run.exit}` | Fresh original-source diagnostic reading frozen11 probe22 request, referencing current built assemblies/prelude; no augmented historical hint sources | Run in tmux with the unchanged ten-second token and monotonic deadline; preserve source/DLL/prelude hashes, solver/version, actual selected assertion inventory, result and whole-scope nonacceptance |
| Fresh sibling `sequence16/` with the same artifact names plus `structural-inventory.json` | Isolate the original `CatSpec.HelpTextSpec` scope under the same ten-second native check; afterward separately translate/apply the helper to its exact original native implementation for command inventory even on timeout | Untimed inspection is not native proof or campaign acceptance; no original source edits, observer API, role change or broader warmup. Bind all source/DLL/prelude identities and keep sequence15 untouched |
| Fresh sibling `sequence17/`, same diagnostic artifacts plus `initial-heap.json`, `initial-scopes.json`, `initial-*.json`/phases | Reproduce the original runner's genuine initial dependency scope and required construction scope from probe22 sample0 on one checker, compare the74 original symbols with its saved scope0, then check original entry-scope CatSpec with that warm checker | Each genuine module check retains its own10s token/deadline; no fabricated warmup, no input/state/campaign admission claim, no role/source changes, preserve all costs and stop on failed prior certification |

Use the existing internal `ContractReductionBudget.DefaultExpressionNodeLimit`
as the traversal/addition work bound, with the existing monotonic deadline and
cancellation checks. Do not add configuration or a new tuning policy. Compute a
candidate insertion list before applying it to each assertion, so exhaustion can
leave that original assertion unchanged. Unsupported/exhausted traversal is not a
certificate: success still requires the complete original native proof. No new
query allocation, time allowance or budget is introduced.

### Assertion-level preservation and native acceptance evidence

Before insertion, retain each selected implementation's ordered block/command
inventory and original AssertCmd identities, original predicates/attributes and
source tokens. After insertion, require all original command objects (including
each final AssertCmd) remain in their original relative order with unchanged
contents, and count exactly the new assertion objects separately. Internal evidence
records per-implementation original/retained/added assertions, deterministic
original block/command IDs, source locations, unsupported/exhausted status and
the implementation/procedure inventory. Counts alone do not prove a result; the
native zero-error/timeout/inconclusive gate and exact verified-implementation
coverage still must pass before checked/accepted caches change.

Assertion-free evidence is allowed only for an actual native zero-assertion
declaration with its expected procedure present. It cannot arise from traversal
failure, removed obligations, skipped selected implementations or a failed added
assertion. Tests must include source declarations whose implicit result-refinement
WD produces native assertions despite no explicit source `assert`, as well as
negative native cases showing added/original failure blocks Accept. Distinguish
this pre-verification native assertion inventory from a solver-reported VC/PO
count; do not mislabel one as the other. Preserve diagnostic source locations and
record any compiler/pipeline optimization limitations discovered during validation.

### Role separation prerequisite (design only; not authorized implementation here)

The proof steps alone do not remove the existing PadLeft by-method gate. A later
role-specific slice needs its own ready root/owner approval and would affect:

| Potential exact files/symbols | Separate design requirement | Required negative/compatibility cases |
| --- | --- | --- |
| `ContractRuntimeObligationTransformer.cs`, new logical dependency collector alongside unchanged `ExecutionReachable` | Traverse original function body/Req/Ens/Reads/Decreases, types/witnesses/constants and proof statements. Logical use does not automatically add a by-method; invoked proof methods and overrides still require their relevant full correctness obligations | False logical ensures/result refinement, hidden imports, failing proof lemma, false precondition and trust escapes remain rejected |
| `ContractSpecificationChecker.cs`, scope/role inventory, PendingModules/CheckModuleAsync/Accept and caches | Exact declaration-plus-role identities, role-specific expected native procedures/assertions and source/Program/proof-context-bound caches; shared function/by-method names must not accidentally select both or satisfy the wrong role | Logical success cannot populate `IsValidated` for stronger runtime/construction scopes; changed import/source, wrong Program, missing role and same-name by-method coverage controls |
| `ContractRuntimeCampaignRunner.cs`, entry heap-postcondition dependency gate | Request logical-only certificate solely for native original-Q evaluation; preserve initial/observed validity, P, both polarities and actual runtime callee failure/unchecked gates | Good logical definition with wrong executed by-method return still invalidates the sample; good by-method with invalid pure definition cannot certify Q |
| `ContractSpecificationCheckerTests.cs`, `ContractRuntimeHeapQueryTests.cs`, `ContractRuntimeCheckTests.cs` or `ContractRuntimeObservationTests.cs` | Native role/identity coverage plus actual compiled execution fixtures | Original six-call-style definition equality/type evidence remains concrete only; no blanket universal by-method correctness claim from runtime samples |

Implementation detail: native translation initially leaves some FunctionCall.Func
references unresolved. Match a bound call by exact declaration identity; for an
unbound call, resolve only through the unique same-program declaration of that
native symbol, requiring the prelude's AlwaysRevealed marker set by the original
BoogieGenerator before source translation. Ambiguous/non-prelude identities leave
the original assertion unchanged. Newly inserted calls bind to those exact native
declarations. No original call is rebound or mutated. Original assertion/source
inventories and added-step counts are internal result properties, preserving the
existing positional result constructor and public campaign DTOs.

No role change is included in the sequence helper slice. Existing execution,
runtime type-evidence and construction certificates retain all current obligations.
HelpTextSpec proof-step success and performance are unknown; PadLeft remains a
separate gate. This plan extension changes records only while frozen10 M2 runs;
the recording baseline is frozen before any live proof-helper drafting begins.

## Frozen10 full M2 result and recording-only checks

Root completed full r7-dev M2 with exit0 and immutable post-check:24 rows/eight
variants,2082.009492s wall. Detection is3/4 mutants with0/4 spurious reports;
invert-exit remains undetected. There are167 generated/executed samples,159 valid,
54 violating and eight sample timeouts (one per campaign), with no other population
errors or unchecked-precondition/callee counters. Valid counts in catalog order
are18,18,18,18,18,19,32,18. Clause-level results separately retain159 unchecked
CoreSummary evaluations (`callee_contract_unvalidated`),1563246 runtime evaluations,
zero closed-SMT decisions and nine loop-maintenance violation records. PBT campaign
times are181.446–194.539s. Do not conflate unchecked clause evidence with population
admission counters or treat the undetected exit mutant as correct.

Root mechanical audit passes2582 checks/117 summary-field comparisons in
`/workspace/tmp/pbt-r7-dev-mechanical-audit-20260928/m2-evidence.json`; owner read
the population/evaluation fields and empty failed-check list. This is mechanical
cross-checking, not fresh independent verification. All-four acceptance remains
unmet. Root released the native lane only after this immutable population ended.

Recording-only validation now underway, with fresh `recording-*` logs in the
existing check directory. Solution build1 passes16.33s with zero warnings/errors;
the nine generated-runtime cases pass9/9 (2s) and existing runtime observation,
timeout, early-precondition exit, isolation and generic serialization controls
pass13/13 (29s). Actual successful process statuses are retained separately in
`recording-build1.exit`, `recording-driver1.exit`, `recording-driver2.exit` without
rerunning. The shared shape helper's four non-runtime `ContractExternExecutionTests`
run next, followed by format/diff and source manifest. Exact commands and final
results will be recorded in the recording-only handoff manifest. No sequence
proof helper or role-source implementation has begun; frozen11 diagnostics and
final-source complete suites/populations remain required in their planned order.

- Recording-only focused validation completes: shared non-runtime bridge
  `ContractExternExecutionTests` passes4/4, no skips,23s (`recording-driver3.log`,
  exit0 retained). Together with9/9 new and13/13 existing runtime cases,26 focused
  cases pass on build1, without a failed attempt or budget change. Generated
  runtime fixture source/assembly and all normal/partial/error traces remain at
  `/workspace/tmp/contract-runtime-recording-e6d0b86ddd5c42649100ec49746554b3`.
  `make format` exits0 with the existing workspace-load warning only
  (`recording-format.log`/`.exit`); `git diff --check` passes.

- Final recording-only source identity and exact commands/cwds/logs/exit statuses
  are in `recording-source-manifest.json` under the check directory. It records33
  changed/untracked Source files on baseline060d5ad532f67d5367450689225274fb0a0243e7;
  manifest SHA256 `700770318bfdc8c2c77f9955e10d59ecda391efe3a6d27979f181fbb3ca66c2a`.
  Comparison against the frozen10 handoff source identity confirms exactly two
  modified production files (Instrumentation and StubRuntime) and one added
  RecordingTests file, with every other source hash unchanged and no removals.
  Source/native lane is stable and handed back to root for supported packaging,
  four transport checks, frozen11 diagnostics and complete-record comparison.
  No sequence proof-step or role implementation has started. Full suites and
  actual successor populations await the final-source sequence in the root plan;
  no speedup or all-four detection claim follows from these focused checks.

## Sequence draft checks and original diagnostic (2026-09-28)

Root completed all four frozen11 recording diagnostics and released the native
lane before these checks. Sequence build1 fails only on the ambiguous imported
`Action` name; qualifying `System.Action` fixes that compilation error. Build2
passes with one test-only synchronous-cancellation analyzer warning. Replacing
it with `await CancelAsync()` yields build3 (14.42s), build4 (14.40s) and build5
(14.29s), all zero warnings/errors. Logs are preserved as `sequence-build1` through
`sequence-build5.log` in the existing check directory; no failed attempt was
overwritten.

Focused helper/checker run1 is51/52: the empty sequence of an opt-out empty subset
correctly has actual native assertion-free declarations, but the test wrongly
required a nonempty implementation inventory. The corrected fixture explicitly
requires zero implementations/verified count and the original `Model.Root`
assertion-free declaration; production acceptance is unchanged. Run2 passes52/52
(13.71s). Added original import-view controls (`provides` rejects unknown result
refinement; `reveals` allows its original definition) plus phase/deadline controls
pass61/61 in run3 (18.07s). The extra global-test class filter in run3 matches no
class and contributes no coverage. False inserted assertions, false/non-byte
original memberships, unknown elements, exhaustion, declaration lookalikes,
duplicate identities, original token/attribute preservation and original by-method
equality checks are included; this is implementation-owned verification.

Fresh original-source `sequence15` runs in tmux `pbt-m2-sequence15-20260928`, cwd
`/workspace/tmp/experiment`, against the exact probe22 request (18 source hashes).
Its helper build passes3.82s with zero warnings/errors. Identity manifest SHA256
is `9d679afbe689fba8015067574ed8a2ddcf89594f007fed0c8f04247c656cc83f` and binds104
files including copied executable dependencies/prelude, helper and current engine
source, plus `/usr/bin/z3`4.8.12 and SDK8.0.131. Original entry-scope CatSpec-only
verification cancels at10.060s, process exit0; whole-scope Accept isfalse. Native
parse/resolve completes1.513s, translation completes3.741s, sequence insertion
takes54.50ms, Boogie runs3.886s→10.052s and iscancelled. This does not establish
the original HelpTextSpec proof or final Q; the cold module check's frontend cost
and exact selected obligations need separate diagnosis. No role change is made.

`sequence16` then isolates `Scope([original CatSpec.HelpTextSpec])` under the same
ten-second deadline, preserving the complete original source and native module
declarations. Its helper build passes3.93s; tmux `pbt-m2-sequence16-20260928` exits0.
The timed native check still cancels10.135s (Boogie4.034s→10.133s); Accept remains
false. A separately labeled, untimed translation/apply inspection afterward
records one original `CheckWellformed$$CatSpec.__default.HelpTextSpec`
implementation,15/15 original commands and1/1 original assertion retained,
2668 added assertions, zero unsupported/exhausted roots. This inspection is not
the timed proof's result and cannot authorize any certificate. It rules out
unrelated selected CatSpec implementations or traversal exhaustion as the sole
cause of this timeout. Identity manifest SHA256
`87f59afcaac760f9c4ee1fb7183adc23c874f96508f6ffe52d5055a619f3dbd6`
binds the fresh source/binaries/prelude/request; old artifacts remain untouched.

Global witness/vacuity and source identity controls additionally pass9/9 in
`sequence-testgen4.log` (4.13s). Actual runtime by-method, original type evidence
and independent-global-cache controls are the next focused Driver check; full
suites remain deferred until final source, as root requested.

Driver focus passes7/7 (34.49s), covering original compiled by-method execution,
malformed recursive implementation rejection, concrete type evidence and the
multi-input independent-global certificate cache. Format exits0 with only the
existing workspace-load warning; diff check is clean. Post-format solution build6
passes13.58s, zero warnings/errors. Actual statuses for all six builds, four
native-focused attempts, Driver and format are retained in matching `.exit`
files; the51/52 failed fixture attempt remains explicit.

The separately authorized `sequence17` reproduces the original runner's precise
initial route on original probe22 sample0. Both dependency and construction scopes
match all74 saved scope0 symbols exactly; the initial unsupported-callee outcome
also matches. On one checker, original BenchWorld verifies6.874s and IOContract
4.474s, each with its own unchanged10s deadline. The resulting warm original
entry-scope CatSpec check then verifies2/2 implementations with zero errors in
7.128s and no cancellation. Its phases are translation2.008s, sequence insertion
57.57ms and native Boogie5.039s. The Boogie phase includes native pipeline work;
it is not a separately measured pure Z3 interval.

The timed successful result inventories original HelpTextSpec15/15 commands and
1/1 original assertion retained, with2668 additional checked assertions. Original
ErrorMessageSpec retains31/31 commands and1/1 assertion, with one unsupported root
and no added steps, yet still passes its unchanged native proof. No exhausted
roots occur. `ErrnoText` and `VersionTextSpec` remain native assertion-free
declarations. This establishes the selected original CatSpec obligations under
the campaign's actual cached-frontend route; it does not certify unchecked modules,
root inputs, the whole CoreSummary closure or any campaign. Whole-scope Accept
remainsfalse. PadLeft's separate execution-role gate remains unchanged.

`sequence17` helper build passes4.07s, tmux `pbt-m2-sequence17-20260928` exits0,
identity manifest SHA256
`21dd16c59cfcae981d09d57a13e9fd1aa648f69826911c1cd8816deb08b1fc3d`.
Cold sequence15/16 timeouts remain valid limitations; no extra allowance, heuristic
cut batching, role change or source amendment was used to obtain warm success.

Sequence source handoff is stable: `sequence-source-manifest.json` under the check
directory binds35 changed/untracked Source files, exact commands/logs/statuses and
all three diagnostic identities. SHA256
`4d2a14eb271a26a61ae935d0c02132710cb68b13d2a7a2847e39beeaf8a4a53e`.
Mechanical comparison with the recording-only33-file manifest finds exactly the
new proof helper, checker integration and new proof tests; all other source hashes
are unchanged with no removals. No native process remains active from this owner.
Root receives the source/native lane; further role implementation, final complete
suites and successor population require their coordinated next gate. Overall
plan remains in-progress and all-four detection is not claimed.

## Separate logical and execution native certificates (in-progress, 2026-09-28)

Root's matching ready section authorizes this next bounded slice. Only the original
entry heap-postcondition dependency gate requests logical proof. All construction,
runtime-callee/type evidence, initial/observed validity, original P and both Q
polarities retain their existing routes and requirements. No sequence, recording,
benchmark, budget, solver-context, assumption or body change is included.

| Exact owner paths/symbols | Change and reason | Required checks |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs`, new `LogicalReachable`/logical-node traversal beside unchanged `ExecutionReachable` | Traverse original logical Function children excluding only ByMethodBody; retain signature/defaults/Req/Ens/Reads/Decreases/Body, resolved function/member/constant references, type constraints/witnesses, proof-statement method calls and overrides. Do not use the unfiltered native call graph, whose edges may include compiled execution | Distinct by-method-only dependency excluded from logical scope but retained in execution; false logical contract/type/precondition, invoked failing lemma, overrides and hidden definitions still block proof |
| `ContractSpecificationChecker.cs`, scope role/owner/native obligations, `Scope`, `PendingModules`, `CheckModuleAsync`, `Accept`, `IsValidated` | Bind each scope to this exact checker (original Program/source/proof context), key checked evidence by original declaration plus native well-formedness/correctness/override role, and select required exact native procedure/implementation roles. Preserve required procedure checks even when native emits no assertion body. Only accepted execution scopes populate existing runtime/construction IsValidated; logical acceptance never promotes a by-method proof | Logical function WF may reuse an already proved identical role; absent/failed correctness cannot be supplied by it. Wrong checker/Program/source, same-name by-method, trust, missing roles, failed proof and late cache controls |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`, entry-Q dependency gate and `ValidateSpecificationsAsync` key/artifacts | Request logical role solely at original entry postcondition; include role/source/context in attempt key and retain exact scope identity on cache hits. All existing bad/unchecked callee and input gates remain | Actual good logical definition with bad executed by-method invalidates sample; bad pure definition cannot certify Q even when executed result is otherwise plausible |
| `Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs`, sole construction of rejected scope in `ConstructionScope` | Replace direct unsupported-scope construction with the checker's bound rejection factory after scope ownership becomes mandatory; preserve exact rejection reason and execution role | Existing datatype member-constant rejection and failed construction-scope tests; no change to supported admission |
| Existing `ContractSpecificationCheckerTests.cs`, `ContractRuntimeHeapQueryTests.cs`, Driver `ContractRuntimeCheckTests.cs` / `ContractRuntimeObservationTests.cs` as needed | Native role/dependency/import/trust and compiled runtime regressions, with original source obligations and actual native errors | Good/bad logical and by-method combinations, proof methods, false ensures/refinement/precondition, overrides, role/cache/source identity, actual runtime definition equality; no replacement evaluator |
| Existing `Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs`, two-state entry-Q fixtures | Reuse actual heap-query fixtures for logical versus executed by-method roles; split the old mixed dependency theory's unexecuted wrong-by-method row into a positive logical-use test while preserving executed mismatch and bad logical-definition rejection | True logical function with universally wrong but concretely matching by-method can certify only Q; executed mismatch invalidates input; false original logical ensures still block both Q polarities |
| Owner plan/index/wiki | Record exact source-backed roles, failed attempts, commands, outcomes and remaining Q limits | No all-four, unused-body correctness or independent review claim |

Native source evidence: `Function.Children` includes ByMethodBody while its logical
SubExpressions exclude that body; StmtExpr.Children includes its proof statement.
`BoogieGenerator.AddFunction_Top` emits function WD and applicable override checks
separately from `AddMethod_Top(byMethod,true)`, whose native correctness procedure
shares the function's source name. Regular proof methods retain specification WD,
correctness and applicable overrides. Exact declaration+native-role keys prevent
same-name or previously accepted logical evidence from satisfying a missing role.
The original execution traversal remains behaviorally unchanged.

Logical trust auditing must inspect logical nodes rather than calling Function's
recursive Assumptions over ByMethodBody; declaration/owner/module trust attributes,
missing logical body, proof-statement assumptions and nontermination remain
rejected. Invoked methods retain full existing trust audits and correctness. Any
unsupported native coverage fails closed, never an assertion-free success.

Validation from `/workspace/cosyn/dafny`: `TMPDIR=/workspace/tmp dotnet build
Source/Dafny.sln --no-restore -m:1`, focused actual TestGeneration/Driver csprojs
using `--no-build --no-restore -m:1` and relevant filters, then `make format` and
diff/source manifest. Native lane is exclusive to this owner. Preserve fresh
`role-*` logs; stable handoff precedes root packaging/diagnostics and final full
suites/populations. No heap-Q partial-evaluation expansion is included here.

### Role-focused implementation and local validation

The logical role is now implemented only at the original entry heap-Q dependency
gate. Existing execution reachability and runtime/construction acceptance retain
their previous role. Native evidence is keyed by original declaration plus exact
well-formedness/correctness/override role; logical acceptance never populates
execution IsValidated. Scope ownership and full source fingerprint prevent foreign
Program/checker or changed-source promotion. Direct expression-root proof methods
and constants, formal defaults, type witnesses, imports and overrides are covered.

Preserved failed attempts: `role-build1.log` reports four compile errors in the
new bound-scope constructor and resolved AST type casts; build2 fixes them and
passes34.08s with zero warnings/errors. `role-testgen1.log` passes48/51; three
failures were expected test labels `Method` versus actual resolved `Lemma`, before
the native assertions. Corrected labels and additional role controls are retained.
Build3 passes17.42s with zero warnings/errors.

`role-testgen2.log` passes98/98 in23.3463s with no skips. It covers the checker,
sequence proof, native cancellation, independent global witnesses/vacuity and
source/input identity. New role cases include good/bad logical definitions versus
good/bad by-method bodies; both direct and witness proof statements; false types,
ensures and call preconditions; hidden/imported same-name definitions; invoked
lemma overrides; and an unused contradictory function contract that must not
certify an invalid result refinement.

`role-driver1.log` passes14/14 in1.1420 minutes with no skips. Actual two-state
campaigns establish that an unexecuted invalid by-method body does not block a
valid logical definition, an executed mismatching body still invalidates the
sample, and a bad logical definition cannot certify Q even when the by-method
return would satisfy its declared result contract. Existing both-polarity, bad
callee, imported recursive definition and multi-input global-cache controls pass.

All logs are under `/workspace/tmp/pbt-m2-optimization-checks-20260928`; exact
commands and source hashes will accompany the stable role handoff manifest.
These focused checks are not an original CoreSummary campaign result. Root's
next frozen12 one-sample stdin/exit probes precede final full suites; all-four
detection and fresh independent review remain pending. No heap-Q reducer change
was made in this slice.

Role source is stable for root handoff. `role-format2.log`/`.exit` records a
completed formatting pass (exit0; existing workspace-load warning only). The
first formatting log is retained; its terminal status was lost across context
recovery, so the fresh pass provides explicit status. Post-format `role-build4`
passes14.10s with zero warnings/errors and captured exit0. Diffcheck exits0.

`role-source-manifest.json` binds the exact35-file Source set, commands, logs,
failed attempts and completion evidence; SHA256
`e4e5867508e2c674eb46feab3f1f5312b056d2d30c6bfd05d56413d80fbdb94c`.
Exactly six authorized role files differ from the sequence manifest, with no
added/removed paths and all other hashes unchanged. The test logs retain their
`Test Run Successful` terminal summaries; separate process-exit files were not
captured for those pre-compaction runs, as the manifest states explicitly.
Source/native lane is released to root for package12/transport/freeze and original
stdin/exit probes26/27. No final full-suite or actual-Q acceptance is claimed.

## First state-aware reduction slice (ready then in-progress, 2026-09-28)

Root authorizes the matching ready table after explicit user steering toward
partial evaluation. MBQI diagnostic never ran and solver options remain unchanged.
Frozen12 admits the original logical/observed state but both stdin/exit negative Q
proofs time out10.108s. This slice supplies checked bounded state projection, not
a claim to complete final Q. Root releases the native lane exclusively to owner.

| Exact files | Change / necessity | Validation |
| --- | --- | --- |
| New `Source/DafnyCore/ContractTesting/ContractHeapReductionContext.cs` | Immutable entry/current typed field facts, exact reference aliases and reveal identities; residualize unknown state | Epoch, readonly, aliases, missing cells and invalid contexts |
| `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs`, `ContractReductionResult.cs` | Optional context entry point preserving existing API; projection/residual statistics | Detached original preservation, scalar compatibility and shared exhaustion |
| `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs`, `PartialEvaluatorVisitor.cs` | Opt-in reads/twostate unfolding, OldExpr and member projection; caller-valued arguments, epoch-sensitive replacements, disable heap literal cache | old(local), old(r.f)/old(r).f, hidden/revealed, unknown label and actual-argument capture |
| New `Source/DafnyTestGeneration/ContractTesting/ContractQueryHeapReduction.cs` | Parse resolved requires and supported field assignment/reveal prefix, conservative may-alias invalidation; checked iff before original target and retained identity inventory | Unknown effects/labels, alias conflict, original command/token/attribute preservation |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs` | Apply recognized heap reduction and log counts/residuals; keep target and native coverage | Separate non-target iff failure is Error; both polarities and WD preserved |
| Existing `Source/DafnyCore.Test/ContractExpressionReducerTests.cs`; new `Source/DafnyTestGeneration.Test/ContractHeapReductionTests.cs`; existing `Source/DafnyDriver.Test/ContractRuntimeHeapTests.cs` | Actual generic reducer/native/compiled two-state tests | All semantic controls above, invalid preconditions, time/node/depth limits and actual sample admission |
| Owner plan/index/wiki | Preserve commands, failures, exact source identity and limitations | Diff/source manifest and no independent-review claim |

No query builder, runner, benchmark, public DTO, solver option or scheduling change.
Preserve shared depth2/100 quantifier/10000 node limits; no resetting per subtree,
ADT payload enumeration, guessed witnesses or trusted reduction verdict. Inline
stateful calls only after actual arguments reduce to heap-independent terms or
canonical references; otherwise leave the call intact. Old rolls back heap lookup,
never a local/formal value. Explicit reveals use resolved OffsetMembers and actual
visibility. A distinct non-target checked iff must pass with original target and
all native WD; helper failure cannot become a bug verdict.

Validation cwd `/workspace/cosyn/dafny`: solution build with TMPDIR=/workspace/tmp
and --no-restore -m:1; Core tests filter
`FullyQualifiedName~ContractExpressionReducerTests|FullyQualifiedName~PartialEvaluatorTest`,
new TestGeneration heap tests plus query/phase/role controls, applicable Driver heap
controls, make format, post-format build and diff/source manifest. Capture fresh
heap-pe-* logs with explicit exit files and retain every failed attempt. Frozen12
and prior artifacts remain unchanged. Status in-progress; source edits begin only
after this ready scope and announcement.

First-slice clarification during root review: alias union/disequality and may-alias
write invalidation belong to the query extractor; the Core context receives only
immutable canonical facts. Existing reducer exhaustion preserves original/residual
terms, so a bounded partial result may still receive a checked equivalence without
resetting any limit. Log exhausted/residual work explicitly; the unchanged original
target and native helper proof remain mandatory. Unknown executable effects still
leave the original query without applying a context.

Final bounded guard clarification: heap-context StmtExpr proof expressions,
ApplyExpr higher-order calls, and labeled member selections remain untouched;
related Core controls cover proof/higher-order/labeled-old contexts. Native import
fixtures explicitly export Cell.value; testgen2's two frontend export failures
are retained (139/141 pass). No visibility or native gate is relaxed.

### First state-aware PE validation and limitations

The implementation preserves original target/commands and detached source bodies.
Canonical reference aliases and explicit disequalities are extracted from original
requires; a write invalidates all possibly aliasing cells of that exact field.
Old changes only heap selection. Actual call arguments must first become
heap-independent caller values; heap-context literal caches and helper-interpreter
execution are disabled. Unknown heap cells, labeled contexts, proof statements,
higher-order application, unsupported control flow and hidden definitions remain
residual. The native language rejects `old(Delta(c))` for a two-state function
before reduction; this is now an explicit rejection control, not claimed support.
Function bodies are cloned before the mutable visitor because native Substituter
may share unchanged original subtrees. Snapshot tests retain every original body.

All logs and actual exit files are under
`/workspace/tmp/pbt-m2-optimization-checks-20260928/heap-pe-*`. Build1 passed with
two nullable warnings; build2 passed with one remaining test nullable warning;
build3/4/5/6 pass with zero warnings/errors. Core1 failed one of9 on illegal
old/twostate syntax; core2 passes94/94, core3 passes95/95. Core4 passes97/98 with
a new labeled-old fixture incorrectly naming a requires label; core5 passes98/98
after using a real body label. Native testgen1 passes14/16 (illegal old/twostate
fixture plus labeled-prefix diagnostic expectation); testgen2 and3 each pass139/141
with import fixture export mistakes (missing field, then mutable-field reveals).
The corrected fixture explicitly provides the mutable field and varies only the
function body visibility. Final testgen4 passes141/141 in27.2935s; core5 passes
98/98 in5.0899s; build6 passes15.96s. Failures are retained, not relabeled.

Exact commands use engine cwd and `TMPDIR=/workspace/tmp`:
- `dotnet build Source/Dafny.sln --no-restore -m:1`
- `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractExpressionReducerTests|FullyQualifiedName~PartialEvaluatorTest' --logger 'console;verbosity=normal'`
- `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ContractHeapReductionTests|FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ContractPhaseTimingTests|FullyQualifiedName~ContractSpecificationCheckerTests' --logger 'console;verbosity=normal'`
- `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~HeapProjectionKeepsOriginalRuntimeTransition|FullyQualifiedName~ObservedConstructionDecidesBothOriginalPolarities|FullyQualifiedName~ObservedConstructionKeepsInvalidEntryRejected|FullyQualifiedName~LogicalHeapCertificate|FullyQualifiedName~InvalidCalleeExcludesHeapDecision|FullyQualifiedName~DirectSpecificationContractBlocksBothPolarities|FullyQualifiedName~HeapQueryBudgetExhaustionRemainsUnchecked|FullyQualifiedName~ScalarClosedCalleeUsesOriginalSources' --logger 'console;verbosity=normal'`

Driver focus, final format/build and source handoff are being completed. Actual
frozen13 Q/projection/residual evidence is unrun, final full suites are deferred by
root until source settles, and fresh independent review remains unavailable. The
existing depth2 bound will leave deeper definitions and general witness/payload
existentials residual; no all-four detection or timing improvement is claimed.

Driver1 completes15/15 in1.5082 minutes, exit0. `make format` exits0 with the
known workspace-load warning; diff-check exits0. Final post-format build7 and
`heap-pe-source-manifest.json` preserve the stable handoff identity. There are43
changed/untracked Source files overall, exactly10 added/changed paths relative to
the35-file role manifest; all other role source hashes remain unchanged. These
checks are implementation-owner validation, not fresh independent review. Root
will own supported package13, transport, frozen13 and actual Q probes28/29 before
any further scope decision or final suites. Status remains in-progress.

Stable handoff completed: post-format build7 passes29.74s with zero warnings/errors;
final diff-check exits0. `heap-pe-source-manifest.json` SHA256
`80df2456ba420072bc3acb02045e0ece32764164178a5cfd4c1022e2826ed5b3` records43
Source hashes, the exact10-path role-baseline delta, validation commands and log
hashes/exit statuses. Source is unchanged after build7. Native lane and source
freeze ownership explicitly transferred to root for package13 and diagnostics.

## Checked heap-equivalence repair (in-progress, 2026-09-29)

Authorization: root [historical follow-up](../../../plan/2026-09-29-pbt-m2-historical-followup.md)
explicitly supersedes deferral for this bounded implementation diagnosis. Retained
public probes28/29 report a non-target checked equivalence failure with zero heap
reads and two stateful inlines. This may be proof incompleteness; no reduction is
trusted, and original target/WD/equivalence gates remain fixed.

| Exact files | Change, purpose and otherwise unmet behavior | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryHeapReduction.cs` | Supply resolved owner signature visibility to reducer if controls establish missed imported unfolding; diagnose iff independently | Imported revealed projection counts, hidden negative, DisableScopes actual diagnostic route |
| `Source/DafnyTestGeneration.Test/ContractHeapReductionTests.cs` | Add native controls and retained original identities for resolved scope and any independently reproduced equivalence defect | Focused heap tests, positive/negative outcomes and projection evidence |
| Owner plan/index/wiki `contract-testing.md` | Preserve baseline hashes, diagnosis, commands/failures and handoff | source manifest, diff review |
| `/workspace/tmp/experiment/pbt-m2-pe-equivalence-20260929/` | New immutable retained-query diagnosis driver/logs, no old output writes | tmux, TMPDIR workspace, exact source/options/budgets and output |

No settings, limits, match expansion, contract/export/generator changes, provider
calls or packages. Source scope expands only through a revised table before edits.
Current solution is already dirty; capture all changed Source hashes before edits.
Native lane exclusively held by this owner until explicit release. Validation cwd
`/workspace/cosyn/dafny`: `TMPDIR=/workspace/tmp dotnet build Source/Dafny.sln
--no-restore -m:1`; `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1
--filter 'FullyQualifiedName~ContractExpressionReducerTests|FullyQualifiedName~PartialEvaluatorTest'`;
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter
'FullyQualifiedName~ContractHeapReductionTests|FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ContractSpecificationCheckerTests'`;
Driver existing heap controls as first-slice filter above; `make format`, postformat
build and `git diff --check`. Tests require existing restored .NET packages and Z3.
No benchmark proof or complete population acceptance is inferred from local tests.

### Evidenced residual boundary revision (ready then in-progress)

Native generic source isolates the failure to rewriting inside an unbounded
existential. Removing let/match or replacing getters by fields still fails the
auxiliary iff; removing the quantifier passes. Native CLI also cannot establish
its existential target. A checked pointwise equivalence succeeds but does not
prove outer body equivalence; native one-level `Summary <==> exists trace ::
Relation(...)` succeeds. Thus no unsound substitution is established; this is an
unsupported symbolic quantified rewrite/proof path. The earlier canCall/trigger
explanation is a hypothesis, not a proved backend root cause. No proof scaffolding
or solver setting change follows that unsuccessful experiment.

Parent authorization accepts a conservative, general finite-domain boundary:

| Exact additional files/symbols | Change / necessity | Validation |
| --- | --- | --- |
| `Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs`, `SimplifyQuantifierExpr` | Heap-aware profile attempts existing finite-domain unrolling first with unchanged shared expansion/instance/depth budgets; if unavailable preserves original quantified body/range/triggers and records `unbounded_quantifier`. Scalar profile unchanged | Finite positive/negative native controls; unbounded quantified/no-quantifier controls; immutable original AST; existing scalar/Core suites |
| `Source/DafnyCore.Test/ContractExpressionReducerTests.cs` | Verify bounded heap quantifiers share cap and keep a residual/original source when exhausted | Core reducer and PartialEvaluator filters |

Outer checked iff, original target and every native WD assertion remain. This
resolves unsupported helper rewriting, not general ADT existential inference or
all-four detection. Actual retained Q28 must be measured under unchanged10s; old
probe artifacts remain immutable. Root/ghost own separate new source changes;
combined-source hashes will distinguish their paths from this owner's3 planned
production/test paths plus Core regression. Native lane is released after focused
validation and retained-Q diagnosis; root coordinates final format/build/packages.

### Validation progress and explicit finite-negative limitation

Build1/2 pass; focused imported scope baseline fails3/4 (all exposed bodies miss
projection), corrected full heap focus passes23/23. The first test invocation is
aborted by sandbox localhost socket restrictions; approved local test-runner
execution succeeds afterward. No network/provider call is made. Small fixture
attempt1 fails to parse reserved identifier `witness`; subsequent quantified
attempts2/3/4 reproduce native iff failures and isolate them from let/match/getter
behavior. Failed experimental outputs are retained, not relabeled.

Combined build7 includes independent root type-qualification and ghost source
changes and passes zero warnings/errors. Core `core-final1` passes100/100 in5.013s;
TestGeneration `testgen-final1` passes156/157 in26.843s. Root's8 closed-clause and
8 ghost controls pass; unbounded original positive and negative target controls
now both return `Sat` **native nonproof**, never a validated runtime violation.
The no-quantifier and finite-positive controls pass. The newly probed finite-negative
case (`forall i:int | 0<=i<2 :: a.value==4` under current a.value3) reduces false but
its original native iff cannot establish the bounded witness, so the auxiliary
marker correctly yields Error. Parent explicitly accepts this as a documented
negative rejection test; it is not claimed supported, and no gate is weakened.

Existing unroller cap/node exhaustion paths return a residual with recorded
exhaustion. False returns after exhaustion are not additionally labeled unbounded;
resolved split quantifiers receive their distinct residual reason. Core's new
sibling-domain cap3 test verifies cumulative accounting and residual preservation.
Build8 and narrow final checks follow this reason-only refinement. Root owns final
format/package, combined Driver validation and fresh review after lane handoff.

### Stable PE handoff (2026-09-29)

Build8 passes29.99s with zero warnings/errors; final owner Core100/100 passes5.300s
and combined TestGeneration157/157 passes30.9437s, all captured exit0. The latter
filter is `FullyQualifiedName~ContractHeapReductionTests|FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ContractSpecificationCheckerTests|FullyQualifiedName~ContractClosedClauseTypeTests|FullyQualifiedName~ContractGhostInitialValidityTests`.
Other flags are `--no-build --no-restore -m:1 --logger 'console;verbosity=normal'`;
Core uses the previously specified reducer/PartialEvaluator filter. The final
reason refinement preserves cap/node exhaustion, distinguishes split quantifiers,
and tests cap3 sibling accounting. `git diff --check` passes before lane release.

Retained public Q28 now completes8.214s with **Sat native nonproof**, reporting only
`contract_query_target`; its checked auxiliary iff no longer fails. The residual
has1 stateful inline,60 nodes,532 expansion nodes,0 heap reads and explicit
`unbounded_quantifier`. All9 original statements, original target metadata and
original function bodies remain unchanged. Q29 hits the unchanged10s deadline
(10.113s measured) and remains unchecked; no iff pass or detection is claimed.
Direct replay uses retained query text and original request snapshots, with a
separate detached reduction/immutability warmup outside its timed check. It is not
a full campaign, source-preparation replay or a latency comparison. Frozen13 and
old outputs are unchanged.

Exact commands, per-query phases, returned outcomes, diagnostic source driver,
all earlier failures and baseline/final hashes are under
`/workspace/tmp/experiment/pbt-m2-pe-equivalence-20260929`. `final-checks.sh` records
the serial sequence in tmux `pbt-pe-boundary-20260929`, with experiment cwd and
TMPDIR inside workspace. .NET8.0.131 and Z3 4.8.12, no provider/authentication.
`owner-source-manifest.json` SHA256
`8051016fe29f865dafc076527920ab8b3d6a1092f819769538159850c86f7472` binds45 changed
Source files,4 PE-owned path deltas and5 concurrent root/ghost path deltas, zero
removed baseline paths, exact artifact hashes and exit statuses. Owner changes are
only QueryHeapReduction, PartialEvaluatorVisitor, and their two existing test
files. Broader source work and all prior dirty changes remain preserved.

Native/source lane explicitly released to root after final2 completion. Root owns
final formatting/build/package, Driver regression checks and independent review;
these have not been run or claimed by this implementation owner. Plans/wiki remain
in-progress because broader historical/full-population acceptance is separate.
Next action: root's final-source validation/freeze and unchanged h11/h13 reruns.
Knowledge updated at [checked equivalence boundary](../wiki/contract-testing.md#checked-heap-equivalence-boundary-2026-09-29-development).

Root handoff completed2026-09-29: final supported format/build/transport checks
pass; fresh independent review passes44 affected native,42 Core,7 Driver and12
final cross-context type controls. The unchanged h11/h13 reruns are complete and
neither yields a valid sample or new counterexample. The bounded parent follow-up
is done, but this broader optimization plan remains in-progress. Final outcomes,
all failed attempts and independent review are recorded in the
[root follow-up](../../../plan/2026-09-29-pbt-m2-historical-followup.md).

## Closure (2026-09-29)

User decision 2026-09-29 before the core PBT commit ([commit preparation](../../../plan/2026-09-29-pbt-core-commit-preparation.md)): closed as done. All implemented stages and
validations above are final records; broader historical and full-population
acceptance was not performed and remains follow-up work.
