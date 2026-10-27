# PBT trusted source snapshots

## Binary feasibility before authoring, 2026-10-26

Status: implemented and independently verified2026-10-26; validation is recorded in the
[shared Cosyn plan](../../plan/2026-10-26-pbt-binary-feasibility.md).

`--runtime-feasibility` exposes a separate schema1 source-only analysis. Its sole
support verdict is `possible`: false carries concrete blocking reason codes;
true allows draft/generator authoring under the selected execution policy.
Parsing, transport, cancellation and timeouts remain operational errors. This
analysis runs no compiler or solver and does not certify later authored bodies,
generator proofs, linkage, valid samples or counterexamples.

`ContractRuntimeFeasibility` shares resolved callable, runtime reachability,
input-type, reserved-name and required heap-field checks with the runtime paths.
Only state and declarations relevant to the selected target cause rejection.
Supported missing bodies yield canonical draft prerequisites; false yields none.
Campaign and source-authoring preparation use the same early gate before exposing
templates. An explicitly supplied bounded contract-model policy is analyzed
structurally; the analysis never selects synthetic extern semantics implicitly.

The result binds exact source contents, entry, dependencies, trusted sources,
extern policy, native producer and resolver options. Cosyn checks this binding
and runs fresh analysis before assigned-goal PBT guidance and each tool dispatch.
Newly declared children are analyzed on their first PBT call. A negative result
suppresses that target's PBT authoring while ordinary synthesis/proof and other
targets remain available. Authored source still passes the existing subsequent
extraction, transformation and execution checks.

Final r03 builds of Driver tests, generation tests and CLI passed with41 exact
input pins. Independent prebuilt-only memory validation passed109 cases across
feasibility, bounded models, source authoring and runtime obligations, with no
failures/skips. Test bodies use snapshots and pure transforms, with no compiler,
solver, temporary-directory or synchronization workload. Scoped formatting and
diff checks pass. The plan records initial syntax and fixture corrections and
the VSTest loopback permission prerequisite. Evidence remains under
`/workspace/tmp/pbt-binary-feasibility-20261026/`; this is source support and tool
validation, not sampled benchmark evidence or installed-image adoption.

## Trusted-source acceptance, 2026-10-19

Status: independently accepted on the combined integration base, 2026-10-19.
The owning plan is
[2026-10-19-pbt-trusted-sources](../plan/2026-10-19-pbt-trusted-sources.md).

## Contract

Schema-v2 runtime campaign requests can carry an optional `TrustedSources` list
of `ContractDependency` identities (`Path`, `Sha256`). The default is null and
retains strict checking. Validation requires each identity to match one unique
source snapshot exactly; source content hashes and canonical path uniqueness use
the existing `ContractSourceSnapshot.Validate` checks.

The specification checker binds the list to canonical source origin URIs only
after validating path and digest membership. A trusted source's original
declarations remain in dependency closure and scope symbols, but their own
declaration trust audits and native declaration proof obligations are omitted.
The checker still verifies ownership against the original resolved program, and
declarations reached transitively from a trusted declaration remain checked
unless their own source identity is explicitly trusted. Scope/cache identity
contains both source-set and trust-set hashes. Trust is source-granular and is an
explicit host assumption.

Runtime value admission remains separate. Campaign input validation, concrete
predicate reduction, runtime type evidence, heap field membership, frame checks,
and candidate/helper obligations retain their existing code paths. Internal
initial and observed heap checks carry a defensive trust-set copy; initial
preparation attestation hashes that copy with its request, and checker binding
checks it before carrier or observed construction work. The legacy
`ContractTestRequest` has no trust field.

## Verification and limits

The focused test class uses the in-memory `ContractSourceSnapshot.ParseAsync`
path and a pure expression reducer. It covers exact path/digest membership,
same-path foreign AST ownership, default/untrusted `assume` and `extern` rejection,
trusted axiom audit omission, retained candidate and transitive helper checks,
module-name lookalikes, trust-separated scope identity, concrete false predicate
reduction, and initial/observed checker-context mismatch.

On the original native tree at `bef89d2244ddd9a3bc898ad97252d82049ff5cdd`,
`.NET SDK 8.0.131` test-project and driver builds passed. The first
test restore attempt stopped during MSBuild's restore-project-reference walk
without an emitted error diagnostic; a serial scratch-isolated restore then
passed. The initial Java runtime build could not use the incomplete default
Gradle wrapper cache in the read-only home directory; preparing the official
Gradle 8.14 distribution under task scratch resolved that prerequisite without
repository changes. The test-project build had zero errors and four existing
warnings outside the changed code; the driver build had zero warnings/errors.
The focused filter `FullyQualifiedName~ContractTrustedSourcesTests` passed 15/15
with no skips. VSTest's ordinary sandbox attempt failed before executing tests
with `SocketException (13): Permission denied`; the authorized local-socket run
first found an incorrect expected label (`Function` instead of Dafny's
`Predicate`), which was corrected before the passing rerun. A fresh independent
review accepted that native source and independently passed the 15 focused tests.
No solver was invoked by the focused tests. Final logs and the test assembly are
under `/workspace/tmp/pbt-trusted-core-20261019/`. These results make no Dafny
proof, benchmark or performance claim.

Integration follow-up: the native patch is now at
`0e5338b75e4094be20e005d79abcc750cf69a44e` on base
`29da48b6c47e9c8484c8a2818e2be2032ad14206`, which adds separate
DefinitionAnalysis visibility changes. On 2026-10-19, the serial test-project and
Driver builds were rerun against this HEAD using the prepared Gradle cache and
scratch output paths; the focused in-memory filter passed 15/15 with no skips.
The test-project build had four unrelated existing warnings and no errors; the
Driver build had zero warnings/errors. VSTest used the approved local-socket path.
Logs are under `/workspace/tmp/pbt-trusted-core-20261019/` as
`build-test-integration.log`, `build-driver-integration.log`, and
`test-focused-integration.log`. The plan/wiki diff passes `git diff --check`, and
the plan/wiki trees contain Markdown files only. Fresh independent review accepted the
combined source and independently passed all 15 focused tests (zero failures/skips).

Source of record: native Dafny changes in `Source/DafnyTestGeneration` and
`Source/DafnyDriver`; implementation plan above. Independent verification
accepted both the original and combined native source, and independently passed
all 15 focused tests on the combined assembly.

## Ambient integer constants, 2026-10-26

Source/local status: independently accepted; CLI publication and installed-image
adoption remain separate. [Arithmetic admission plan](../plan/2026-10-26-pbt-constant-arithmetic-admission.md).

Trusted declarations still undergo the existing ambient global inhabitance and
closed-value gates. A missing arithmetic case in `ClosedConstantValue` formerly
sent an ordinary `nat` multiplication to the full-premise SMT fallback. The
runtime now reuses `ConstantFolder` through
`ContractExpressionReducer.TryFoldTotalIntegerArithmetic`: only integer literal
leaves and recursively closed Add/Sub/Mul trees reach folding. This helper
computes values; the admission boundary still rejects negative nat and all
other constrained subsets/newtypes. Undefined, residual, conversion, function,
string and noninteger syntax gains no new admission route.

Full global declaration/dependency scope, native obligations, source ownership,
trust hashes and concrete receiver/input/heap checks are unchanged. Trust never
turns the ambient gate into an unconditional success. Independent matching-source
memory validation passed 28 cases (new admission plus existing trusted-source
owners), scoped formatting and diff checks; no solver/compiler is invoked by
those tests. Logs are under `/workspace/tmp/pbt-constant-arithmetic-20261026/`.
These checks do not establish Csplit sampling or counterexample discovery.

## Immutable field identity aliases, 2026-10-26

Source/local status: independently reviewed; 40 selected in-memory admission
and trusted-source cases pass with zero skips. Full-public construction and
installed-image adoption remain separate. [Alias admission plan](../plan/2026-10-26-pbt-immutable-alias-admission.md).

`ContractRuntimeHeapChecking.HasStructuralInhabitant` can construct a fresh
non-null class containing a single-hop immutable identity alias. The resolved
initializer must be an unlabeled selection on this, naming a distinct own
nonstatic bodyless constant. Alias, selection and target types must match with
constraints preserved. The ordinary field traversal still independently
constructs the target value; the alias denotes that same value. Existing generic,
trait, inheritance and recursive-class exclusions remain. Other receivers,
mutable/static targets, calls, conversions, chains and mismatched types gain
no new route. Concrete captured heaps and abstract empty-heap checks are unchanged.

This exact construction also applies to the existing checker-free structural
fast path; it introduces no trusted fact or assumed witness. Scoped admission
still retains the defined alias's original well-formedness obligation when its
source is untrusted. Bodyless instance fields remain intentionally absent from
that declaration scope, while their types remain structurally checked.

Evidence: source SHA256 `0f936f59ba21f56f5910fbe484534201cf66c80280ea2fc019b6ca7093013117`,
test SHA256 `427bb2adf58bd38c03d6ef5aef9a9f3f308c49f7f6cf3f51c92087742bf87d1b`,
independent memory and scoped-format logs under
`/workspace/tmp/pbt-immutable-alias-20261026/`. The tests use SnapshotFileSystem
and direct construction APIs; no solver, compiler campaign or temporary directory.
These results do not establish a valid full-support sample or Csplit counterexample.

The separate current-public diagnostic is also independently accepted: the old
CLI fails independent global construction, while the repaired testhost succeeds
with the identical public snapshots and requires no native proof. Both accept
the unchanged complete scope, and abstract empty-heap admission remains false.
This uses current IO/IOContract bytes, which differ from frozen R11, and is not
a byte-identical R11 replay. Before/after r02 records are in the same scratch.
Installed-image sampling and live benchmark results remain separate.

## Post-preparation sampling budget, 2026-10-26

Source/local status: independently accepted; CLI publication, image adoption and
campaign evidence remain separate. [Sampling-budget plan](../plan/2026-10-26-pbt-post-preparation-budget.md).

Runtime campaigns compute one fixed sampling deadline after successful
compilation. If `elapsed` milliseconds of a `total` campaign budget have already
been consumed, the deadline is `elapsed + floor(max(0, total - elapsed) / 2)`.
Every sample uses the remaining time to that same fixed deadline, additionally
bounded by the existing per-sample timeout. Preparation that consumes more than
half the original total can therefore still leave sampling time, while an expired
campaign cannot start a sample. Result classification retains the original
absolute campaign deadline.

The change does not alter request/result schemas, proof or trust policy,
admission checks, sample classification, cancellation, or evidence validity. It
does not force a sample after expiry or enlarge the campaign budget.

Independent review accepted the source and audited the complete pure test path.
The bounded Driver test-project build matched every declared source pin. The
source-bound `SamplingBudgetTests` run passed 9/9 with zero failures or skips,
and scoped formatting and diff checks passed. Evidence is under
`/workspace/tmp/pbt-post-preparation-budget-20261026/`; runner SHA-256 is
`90fb1858e2c20cb7e17275d7714a965d0bb8c1f1702f5244273691b511834826`
and test SHA-256 is
`78ba1c5a4b186b69113a50293fb8675b8097ac8e02dd406e57334728424e130f`.
These local checks establish the budget arithmetic and fixed-cutoff behavior,
not CLI publication, installed-image behavior, a valid sample, or a benchmark
counterexample.

## Preparation and compilation reuse, 2026-10-26

Status: source independently accepted, published CLI built,111 affected memory
cases pass; exact-input operator observations below establish reduced compiler
work and remaining execution/classification limits. Owning
[preparation bottleneck plan](../plan/2026-10-26-pbt-preparation-bottleneck.md).

`ContractRuntimeSelectedDraftPreparation` retains the accepted sources, resolved
program, options and deferred diagnostics together. Proof expansion commits or
rolls back the whole bundle. `ContractRuntimeCampaignRunner` reuses that bundle
and supplies compilation options before resolving each transformed attempt.
`ContractCompilerWorker` compiles the final accepted program directly, preserving
the same backend/reporter and compiled-check discovery rather than resolving again.
The shared options receive their existing compile-boundary updates so downstream
classification retains its prior semantics. There is no cross-campaign AST cache.

The obligation transformer caches source encodings/offsets and renders accepted
text edits in one forward pass, retaining overlap, insertion-order and Unicode
semantics. Wrappers preserve authored arguments/defaults, lexical context,
name-only parameters and evaluation count. Reachable declaration and constructor
defaults are instrumented once; unavailable generic datatype runtime shapes
produce an explicit unsupported result. Resolution retries remain semantically
necessary when checks move from compiled expressions to closed queries.

The PBT-only `ContractCsharpBackend` references the pinned installed
`DafnyRuntime.dll`, omits serialized source/output translation records and
redundant framework package references, and avoids a duplicate source write.
Ordinary C# backend defaults and input translation-record merging remain intact.
Separate optional phases measure code generation, rendering, source/project
writes and actual `dotnet build`. A compiler-worker duration includes more than
C# compilation and must not be reported as a C# timer.

Request7/result4 add typed terminal stages and zero-valid-sample reasons; legacy
pairings remain accepted with their original result shapes. Supervision failure
means the worker result is unavailable, not that the worker executed zero samples.
Generator proof remains independent of runtime sampling evidence. Sampling uses
one cutoff calculated from the remaining post-compilation budget without extending
the original campaign deadline or weakening admission.

Verification: .NET SDK8.0.131; independent no-build/no-restore Driver38, obligation41
and selected-preparation32 cases passed with no skips. Exact current production20
source pins are bound to r03 CLI publication; the selected-preparation r04 rebuild
corrected only a test fixture and left all five published products unchanged.
Evidence is retained under `/workspace/tmp/pbt-preparation-bottleneck-20261026/`.
These memory tests use no solver or native compilation. Native publication and
the separate operator experiment are not development test workloads. Direct
unsupervised cancellation of an active `dotnet build` is observed after its return;
the supervised path still terminates the owned process tree. These checks alone
do not establish sampling throughput, a valid Csplit sample or a counterexample.

### Same-input operator observation

On2026-10-26 the r02 dedicated offline replay retained the exact original Csplit
request4 bytes, seed and limits. Source preparation17.094→7.011s and compiler
worker51.380→17.556s; new `dotnet build` phase15.813s. Generated C# decreased
7,466,877→5,184,348bytes. The first sample began at76.697s, and the104.700s campaign
now included64 sample attempts (27.642s), versus154.369s previously with none.
These are one-run phase observations; the prior C# file timestamp interval is
not a directly comparable instrumented compiler duration. Exact evidence is under
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r02/`.

All64 attempts failed before target execution, so valid samples and counterexamples
remain0. Dead old-state captures executed before entry checks after the contract
was assigned a fixed-heap decision. The public native object's erased ghost state
is not populated by its CLR constructor. The [capture follow-up](../plan/2026-10-26-pbt-old-capture-admission.md)
repairs unused-capture execution and ordering without inventing this state. Do
not infer benchmark success from the timing improvement or successful tool exit.

## Old-state capture admission, 2026-10-26

The [capture repair](../plan/2026-10-26-pbt-old-capture-admission.md) separates
speculative expression rewriting from executable capture emission. Each Check
plans captures without rendering calls; only after final decision/caps does it
commit referenced captures for runtime checks and scalar closed queries.
Fixed-heap queries use the original indexed contract and snapshots, while
unchecked clauses execute no scalar capture. Both discard speculative locals
and retain normalized original expressions/free variables for metadata.

Capture names are isolated per owner so nested specification wrappers cannot
reset an outer owner's state. Partial unchanged-expression rewrites commit only
locals actually referenced by the final expression. Method/function wrappers
validate inputs/preconditions before committed captures and invoke the target
afterward. Captures carry their own source location. This fixes unnecessary
pre-entry reads without fabricating unavailable external ghost state or changing
original contracts, scalar closed-query evidence, heap admission or trust.

Independent source review and44 memory cases pass, including scalar closed-cap
downgrade, heap-backed discard, unchecked checked-function side effects and
existing runtime-old semantics. Scoped formatting passes. Production publication
and image build are complete; exact-input r03 observation below confirms removal
of the pre-entry capture crash, with subsequent body errors and incomplete classification.
Initial42/44 and43/44 runs exposed two fixture issues, corrected before the passing
run; artifacts are preserved in `/workspace/tmp/pbt-preparation-bottleneck-20261026/`.

## Final observed result and handoff, 2026-10-26

The exact-input r03 replay uses dedicated image
`cosyn-pbt-csplit-performance:20261026-r03` with immutable ID
`9012e786826d4afcd764f305c1cc108337aa413cbcde56127b915d64c9b70771`.
All shared latest IDs remain unchanged and the owned container was removed with
exact name/CID absence verified. No model/provider trial was launched.

The compiler worker measured21.339s versus original51.380s; actual dotnet build
was19.016s and generated C# was5,166,220bytes versus7,466,877. Earlier r02 measured
17.556s compiler worker, demonstrating run variability. These are separate phase
observations, not a pure C# speedup or completed campaign comparison.

All64 retained traces now reach three passed input checks, entry-heap capture and
the Executed marker, followed by a null-reference error. Thus the pre-entry capture
crash is removed. The draft first reads its context from the public external IO
singleton, whose ghost region fields have no executable initialization. The last
location marker is not an exception stack frame. No valid classified sample or
counterexample is established, and no contract or missing ghost state was invented.

Sampling finished by139.279s. Classification subsequently repeated45 failed initial
type checks (29.492s) and45 dependency-scope preparations (32.707s); the original
231782ms deadline expired before a worker result. Native supervisor zero counters
therefore mean unavailable classification, not zero observed execution. The final
campaign phase is unclosed. The complete-phase postprocessor rejected that state,
so there is no summary.json; the raw envelope and all65 artifacts are intact.

The exclusive offline `operator-observation.json` validates all artifact hashes,
64 ordinals and445 phase events, retaining native and observed counts separately
and explicitly recording the unclosed campaign. SHA256:
`aad419b510ebf33ffa5f37d6f14b12262260e39dde22110981b836708518735e`.
It is available under
`/workspace/tmp/experiment/pbt-csplit-performance-replay-20261026-r03/`.
The remaining work is a sound external ghost-state execution model and avoiding
repeated classification work without bypassing admission. Neither is completed
by the current repair. No experiment is active; the continuing goal was cleared.

## Bounded contract models, 2026-10-26

Status: independently verified2026-10-26 on native
`3eeedd010d05c9bcc556c79bc6f62447380b58ad` plus the preserved working tree. Origin:
[Cosyn bounded-model plan](../../plan/2026-10-26-pbt-bounded-contract-models.md).
This supersedes the absence of any automatic model above only for the restricted
fragment below. It does not make the original Csplit IO executable.

`ContractRuntimeContractModels.ReadPolicyAsync` parses exactly one empty
module-level helper from the supplied generator packet:
`{:pbt_contract_models "Full.Goal", lo, hi, cap}`. Bounds are literal integers;
cap is1..4096. The parsed policy is passed into the transformer explicitly, so
task-source annotations cannot grant model authority. Source preparation rejects
drafts for the same modeled extern and retains existing constructor/heap audits.

`ContractRuntimeContractModelPlan` accepts one nonnull flat nongeneric receiver
with bool/int fields, mutable ghost state and scalar bool/int formals. It unfolds
only transparent acyclic scalar definitions with no requires and supports boolean
operators, comparisons, addition/subtraction/multiplication, conditionals and old
scalar state. Every conjunct is checked; unsupported expressions and excessive
Cartesian domains fail before compilation. References/aliases, nested state,
function values, quantifiers, collections, recursive definitions and division or
modulo are outside this first fragment. Target calls must be selected-receiver
bodyless externs. Diagnostic constructors still supply explicit placeholder
fields; generator execution cannot access modeled state before initialization.

Expansion also enforces4096 visited expression nodes and64KiB of UTF-8 text for
each rendered expression and the complete predicate. This bounds duplication
through acyclic helper argument substitution before generating compiler input.

Initialization occurs after Generate, before Generated/input capture and original
entry checks. Transition search snapshots old scalar fields, varies only ghost
fields allowed by the frame plus outputs, and applies assignments only after the
entire predicate succeeds. Nonghost fields and fields outside the frame stay fixed.
Target ensures are never selection constraints, and the target body remains the
executed implementation. The model policy disables generator-proof entry omission;
it grants neither trusted-source status nor proof admission.

`Library/PbtContractModels.cs` enumerates the complete bool/int Cartesian domain
with BigInteger cardinality checks. `FindModel` uses the existing seeded random
stream to rotate the starting index, preserving reproducibility without claiming
uniform sampling of satisfying states. Choice records identify phase, symbol,
domain and typed values. Exhaustion exits the sample without complete/runtime-error
evidence. The campaign records precondition/callee-contract unchecked counts and
continues later ordinals, but skips prefix and heap classification for that sample.
Even earlier failed checks in an exhausted sample do not become counterexamples.
An exhausted campaign cannot report `no_violation_found`; an independently accepted
violation from another sample remains a violation.

Final reasons explicitly identify synthetic extern behavior. Model observations
establish only behavior under the chosen contract environment, not agreement with
native C# IO. Runtime library embedding includes the pure search engine; normalized
`PbtRuntime.dfy` pin is
`8965d7933db0ad93747efd23d8286b1b8d6335f7f1300ec5070b90da44116c15`.
Source owners are under `Source/DafnyTestGeneration/ContractTesting/` and
`Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`.

Fresh r03 Driver/generation/CLI builds passed with36 explicit source pins retained
through testing. Independent33 model/runtime,7 feedback and105 related regression
checks passed (145 distinct cases); standalone runtime resolution also passed.
Scoped format/diff checks and recursive Markdown-only audits passed. Exact commands,
source/assembly identities and failed r01/r02 corrections are recorded in the plan.
No transformed-program native campaign, solver, Docker, live provider or benchmark
was run. This acceptance concerns source semantics, in-memory generated-code
resolution, pure runtime search and feedback behavior, not Csplit efficacy or a
new observed counterexample.
