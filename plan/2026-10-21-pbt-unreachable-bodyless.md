# Compile selected PBT helpers in unfinished workspaces

Status: done (fresh independent source/local acceptance; operational validation parent-owned)
Date: 2026-10-21
Parent: [/workspace/plan/2026-10-21-pbt-stabilization-loop.md](/workspace/plan/2026-10-21-pbt-stabilization-loop.md)

## Objective and observable acceptance

This is public repository maintenance, not an evaluated candidate turn. Permit
the selected helper's diagnostic program to be parsed/resolved and have complete
executable bodies even when unrelated concrete methods or functions in the same
workspace remain bodyless. Reuse diagnostic-only unreachable traps. No unrelated
implementation is fabricated for proof or submitted workspace source.

Acceptance requires an actual pre-fix in-memory regression; a source correction;
regressions for method/function insertion, lexical boundaries and relevant
abstract/native/ghost/constructor/override distinctions; preserved selected and
execution-reachable bodies; unchanged original contracts, immutable source
snapshots and ordinary proof/admission/fingerprint boundary; affected cached
builds, memory-only tests, scoped formatting/diff checks; and a fresh independent
review that starts from requirements/current source and runs its own checks.

The parent owns later canonical packaging, new public operational controls,
image acceptance and live cohorts under separate ready plans. A parse/resolve
test or successful library build is not native sample execution, solver proof,
Docker acceptance, benchmark efficacy or full stabilization evidence.

## Evidence, existing implementation and ownership

Read root/Cosyn/native AGENTS.md and native CLAUDE.md. No narrower source,
plan/wiki instructions or templates were found. The live native base is
b4f683fd85c9764c032346e0367df325f73dd4be, with accepted13-product PBT changes,
existing preparation changes and concurrent nested-match planning. Preserve all
pre-existing/unrelated work. The accepted isolated tree at
/workspace/tmp/pbt-worker-failure-20261021/native and every frozen experiment
capsule/image/gate/report are immutable and must not be edited or rebuilt.

Public source paths establish the specific mismatch:

- Driver ContractRuntimeCampaignRunner checks missing drafts using selected-goal
  reachability, then selected-goal/generator reachability after insertion.
- ContractRuntimeSourcePreparation installs only explicitly supplied drafts;
  its existing ReplaceBody uses the parser-owned final token plus UTF-8 byte
  length as the missing-body insertion anchor.
- ContractRuntimeObligationTransformer computes executable/type/dispatch closure
  and EraseUnreachableBody already replaces unrelated existing bodies with
  RuntimeChecks.UnreachableBody/UnreachableValue traps, but leaves null bodies.
- ContractCompilerWorker reparses and ordinarily compiles the whole diagnostic.
  SinglePassCodeGenerator rejects nonvirtual, nonextern executable declarations
  whose bodies remain null (c_method_has_no_body/c_function_has_no_body).
- Existing ContractRuntimeObligationTests use bounded dictionary-snapshot source
  parsing/transformation/reparse. The prior public nine-control run covered a
  missing selected executable body, not an unrelated plain bodyless declaration.

The native repository owns runtime diagnostic implementation and regressions.
Do not change authored specification/proof sources, benchmark/task contracts,
datasets, evaluator/oracle/scoring, reports, Cosyn APIs, selected reachability,
generator-body/all-ensures verification, implication verification, analyzer
fingerprints, source/scope/toolchain binding or fallback admission. Do not add
assumptions, extern/axiom/verification skips or behavioral heuristics.

## Exact change table

| File/symbol | What, how and why; unmet behavior without it | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs::EraseUnreachableBody, InsertUnreachableBody and UnreachableConstructorBody | Extend the existing diagnostic-only trap treatment to missing concrete executable bodies outside the computed closure, preserving parser token/UTF-8 boundaries and abstract/native/ghost exclusions. Preserve bodyless methods with the compiler's existing synthesize attribute path. Reuse divided constructor initialization/trap text for null constructors, but never assign an already initialized ConstantField; handle null concrete overrides before preserving the existing-body override exclusion. Without it unrelated null bodies still block whole-program compilation. | Pre-fix memory reproducer; original/transformed AST/source invariants; constructor initialized/uninitialized constants; affected build and scoped style; independent review |
| Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs (new) | Small independent normal/error scenarios for selected helper beside unrelated bodyless declarations, safe token placement, preserved clauses and snapshot identity, preserved reachable/virtual/native/ghost behavior, applicable constructors/overrides. Every test has an intention comment. | Dictionary-only ParseAsync, Transform and reparse; no compiler/solver/process/directory/staging/sync/toolchain-tree reads; fresh test-helper audit |
| plan/2026-10-21-pbt-unreachable-bodyless.md and plan/INDEX.md | Register, track exact scope/commands/results/limits and close only after independent checks. | Diff, source hashes, reciprocal links, Markdown-only audit |
| /workspace/tmp/pbt-unreachable-bodyless-20261021/verification.{json,md} | Fresh independent reviewer records its own source hashes, helper/I/O audit, commands/outcomes and limited source/local conclusion. Keep reports distinct from all older native reviews. | Exclusive bounded public report creation, immutable final report hashes; no private/runtime/image claim |
| wiki/pbt-unreachable-bodyless.md (new) and wiki/INDEX.md | Record the reusable compilation boundary, exact supported/excluded cases and limited evidence after verification. No benchmark-specific material. | Source/review links, date/revision/status and parent plan |

## Validation commands and I/O boundaries

Working directory for all native commands: /workspace/cosyn/dafny. Existing
dotnet SDK/NuGet/generated core outputs are prerequisites. Do not restore,
install packages, copy whole trees, reset caches or rebuild immutable packages.
Cached library/test builds are operational build validation outside development
test bodies; each command is serial, bounded to120seconds initially, with
bounded public scratch logs under /workspace/tmp/pbt-unreachable-bodyless-20261021.
If a legitimate existing build exceeds120seconds, stop/record it and update this
plan before extending the bound. No automatic retry after source/process errors.

1. Add only the first in-memory regression, build the test project and run it
   against unchanged product source. Expected: new assertion fails because an
   unrelated body's parsed AST remains null, with no environmental failure.
2. After the source settles, sequentially run:

   ```sh
   dotnet build Source/DafnyTestGeneration --no-restore --no-dependencies -m:1 /nr:false
   dotnet build Source/DafnyTestGeneration.Test --no-restore --no-dependencies -m:1 /nr:false
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeUnreachableBodyTests -m:1
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeObligationTests -m:1
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeSourcePreparationTests -m:1
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractGeneratorProofTests -m:1
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractGeneratorProofHelperTests -m:1
   dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter FullyQualifiedName~ContractGeneratorVerificationTests -m:1
   dotnet format whitespace . --folder --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs --verify-no-changes
   git diff --check
   ```

   The normal dotnet/VSTest host may need its already-authorized execution path
   for local socket/runtime-cache access. Do not treat a sandbox/host failure
   before test execution as a regression result. The tests themselves must not
   open sockets, spawn native tools, compile/stage sources, create directories,
   synchronize disk or read/hash installed trees. Trace every helper and fixture
   before adding or running the selection. Existing Driver CampaignFixture tests
   are not selected because they reach real runtime staging/compilation.
3. A fresh native verification agent independently inspects current requirements,
   sources and test helper boundaries and runs the same settled affected checks.
   ROOT does not supply implementation-agent claims/conclusions to it.
4. Inspect plan/wiki recursively for non-Markdown leaves/symlinks and inspect
   final diffs, preserving other work and historical accepted records.

## Implementation and owner-local validation, 2026-10-21

The bounded implementation is complete in the two source/test leaves from the
change table. Unreachable plain concrete methods and functions with null bodies
now receive diagnostic traps at the established UTF-8 end-token insertion
anchor. Null concrete overrides receive the same treatment before the existing
override guard. Unreachable null concrete constructors reuse the existing field
initialization, `new;` and trap body. Reachable goal/generator callees and
ghost, virtual, abstract, extern and valid `{:synthesize}` declarations remain
bodyless. The tests also retain and reparse the complete selected helper and
assert that the immutable input snapshot, contracts and attributes are unchanged.

The initial one-case reproducer used `{:axiom}` on the unrelated declarations;
it is distinct from the settled regression, which uses plain concrete bodyless
declarations without trust attributes. Against the unchanged transformer, the
test-project build passed with four pre-existing warnings. The first sandboxed
VSTest attempt stopped before test execution with `SocketException(13)` because
the host could not open its localhost control socket. The approved host rerun
then executed the test and failed at the expected non-null-body assertion. The
expanded pre-fix suite had three product failures (plain callables, concrete
overrides and a constructor) and three passing preservation controls. This
pre-fix output exists only in the tool transcript; no persistent log or timing
artifact was created.

The first independent review found that the shared constructor helper also
assigned authored initialized constants. A separate dictionary-only regression
against that unsettled product reparsed the transformed source and failed with
`LHS of assignment must denote a mutable field`. After the plan was amended,
the initializer selection was restricted to mutable fields and uninitialized
constants. A two-case theory now covers both insertion for a bodyless constructor
and replacement of an existing unreachable constructor body. In each case it
preserves `const initialized: int := 7`, initializes an uninitialized constant
and a mutable field, and reparses the diagnostic trap body. This follow-up output
also exists only in the tool transcript; the first sandboxed host attempt stopped
before execution and the approved VSTest rerun supplied the product failure.

The reconstructed pre-edit transformer SHA-256, including the preserved earlier
`requiredProofChecks` change, was
`77d2eb68f4c153664bdfafaaa86d55d91b5129395a0792199d934e9eff581547`.
The final settled transformer SHA-256 is
`37beb75be2f5040791fcd5aae57887c734ab38c50544fd91a15092dd0eecc784`,
and the settled regression-file SHA-256 is
`565eb1a811dab6b5bc71d50ae33375826e8c7398d5a4af0e443346b0acc81a65`.
The first product build exposed three `CS7036` errors from calling a non-public
convenience `IsExtern` overload. The implementation was corrected to the public
`IsExtern(program.Options, out _, out _)` form before the settled validation.

With `timeout 120s` applied to each command, both planned `dotnet build`
commands passed; the test-project build retained the same four unrelated
warnings. Every `dotnet test` command used `--no-build --no-restore -m:1` and
the approved VSTest host path. The final settled selections passed with no skips:
8 unreachable-body cases, 14 obligation cases, 24 source-preparation cases,
48 generator-proof cases, 15 proof-helper cases and 10 generator-verification
cases, for 119 tests total. Scoped `dotnet format whitespace --verify-no-changes`
passed. The eight new cases use dictionary snapshots plus parse, transform and
reparse only; they invoke no native compiler, solver, process, staging, temporary
directory, synchronization or toolchain-tree hashing. Reusable behavior and
limits are recorded in [the corresponding wiki page](../wiki/pbt-unreachable-bodyless.md).

These are owner-local results. At that handoff the plan remained in-progress
until the fresh independent reviewer inspected the settled hashes and recorded
its own acceptance below.

## Fresh independent acceptance and handoff

The fresh verification context inspected requirements/current code without
implementation conversations, outcomes or wiki conclusions. It independently
found the initialized-constant error before acceptance; ROOT amended the plan
and the implementation was corrected. The final source/test inputs stayed at
37beb75be2f5040791fcd5aae57887c734ab38c50544fd91a15092dd0eecc784
and565eb1a811dab6b5bc71d50ae33375826e8c7398d5a4af0e443346b0acc81a65.
Its own two cached builds passed with0warnings/0errors; all six serial memory
selections passed119/119,0failed/0skipped. Scoped whitespace/diff and Markdown-
only audits passed. The earlier VSTest socket denial was before any test and
the earlier builds are explicitly superseded. No operational native program,
solver, canonical launcher, image, provider or paid run occurred.

Readonly independent reports, rehashed by ROOT:

- /workspace/tmp/pbt-unreachable-bodyless-20261021/verification.json,
  21497bytes0444, SHA256
  a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be.
- /workspace/tmp/pbt-unreachable-bodyless-20261021/verification.md,
  7588bytes0444, SHA256
  3bbe6468c053dd6f7ed3999d82ef593aa4fdd8a51070c493df8800afab4d7ffc.

The tested native base remainsb4, with concurrent Substituter.cs and nested-match
test/doc work preserved and explicitly outside this repair. Cached dependency
outputs were not freshly rebuilt or claimed as validation of that concurrent
work. Root advanced concurrently tod7567b1; Cosyn remainsf919f65. Acceptance
closes this bounded source/local plan, not the parent stabilization goal.
Reusable findings are indexed in [the native wiki](../wiki/pbt-unreachable-bodyless.md).
Next action belongs to the separately ready
[isolated overlay build](2026-10-21-pbt-isolated-overlay-build.md) and later new
public operational controls. Original accepted inputs/image40d remain immutable.

## Risks, compatibility, approvals and handoff

Design review before source edits,13:38UTC: bodyless concrete class overrides
and constructors share the compiler barrier. Handle null overrides before the
existing-body override exclusion. For null constructors reuse the existing field
assignment/divided-body/new/trap text. Retain ghost, instance trait/virtual and
native extern null declarations. Reuse the established parser end-token UTF-8
anchor. No file scope expansion or source-preparation/reachability/compiler
change is needed. This authorizes the bounded design, not its correctness or
actual runtime acceptance.

Additional source-backed compatibility check,13:40UTC: the ordinary compiler
has a separate bodyless static-method-with-output synthesize path before its
missing-body rejection. Keep a null Method with that existing semantic attribute
unchanged; otherwise inserting a trap body creates c_invalid_synthesize_method.
Add a small in-memory exclusion regression. This is a compiler-defined exception,
not a behavioral heuristic or new synthesis feature.

Fresh independent source finding before acceptance: the shared constructor trap
initializer iterates all source fields, including ConstantField with an authored
Rhs. Dafny resolution prohibits assigning such initialized constants again. Add
a separate dictionary-only regression against the unsettled product, preserve
the original initialized constant expression, continue initializing mutable and
uninitialized-constant fields, and correct only the existing helper's semantic
field selection. The common helper also fixes that same invalid assignment in
the older existing-body constructor-erasure path; preserve its other behavior.
After this new relevant correction, rerun the affected build/new-test selection
and final affected checks, with independent hash-bound reinspection. Do not label
the earlier six-case local state as accepted. No private or operational scope
expansion is needed.

The trap is runtime diagnostic-only and must fail if executed unexpectedly;
never use it to establish an authored generator proof or omit requires. Existing
reachability includes executable, dispatch and type/constraint dependencies;
do not narrow it to make a test pass. Preserve bodyless abstract/native/ghost
meaning. Constructors have initialization constraints and overrides have inherited
contracts; inspect them before choosing the smallest safe same-boundary treatment
and update this plan before any wider file/symbol change.

The user's stabilization instruction authorizes this reversible local repair and
checks. No new approval is needed. No packages, commits, image/tag operations,
private reads, provider calls, native campaigns or paid experiments are part of
this plan. Shared task-tag restoration still awaits its separate user decision;
even approval there would not authorize launching the old image with this known
gap. ROOT announced the ready plan before implementation at13:35UTC and set it
in-progress. The fresh review and its correction are now complete as recorded
above. No native/runtime operational success is claimed; the next isolated
package/control gate remains open under its separate plan.
