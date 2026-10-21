# Verify generator bodies and an ordinary implication lemma

Status: in-progress
Date: 2026-10-21
Parent: [integration plan](/workspace/plan/2026-10-21-pbt-authored-generator-proofs.md)
Related: [existing worker repair](2026-10-21-pbt-worker-failure.md)

## Objective and observable acceptance

Preserve agent-authored Generate body and ensures. Verify the body establishes
all those ensures and all required helper proofs. Automatically synthesize a
normal lemma from authored ensures to all original selected target requires.
Require both complete successful ordinary Dafny proofs and current analyzer
source/input identities before issuing internal omission evidence. Never inject
target requires as new generator ensures. Wrong generator ensures and a weak
contract must fail at their respective proof stages. Bodyless helpers, missing
parts, unsupported semantics and proof-local timeouts keep runtime entry checks;
caller cancellation stops the campaign. A buggy ordinary target body remains
outside admission proof obligations and can produce a PBT witness.

## Evidence, owner and existing solutions

Work only in this isolated native checkout, detached at
b4f683fd85c9764c032346e0367df325f73dd4be plus the existing six-file source/test
repair. Preserve preparation and null-draft fixes and the recorded historical
fingerprint guard until its mechanism is deliberately replaced. Live
/workspace/cosyn/dafny, frozen images and evaluated run inputs remain untouched.
No private/candidate/evaluator/provider material is an implementation input.

ContractGeneratorProof currently strengthens Generate and synthesizes an
executable admission method. The ordinary IProgramVerifier task backend already
used by Compilation.VerifyCanVerify supports exact resolved owners and all task
parts; Driver references DafnyProgramVerifier. Inject the existing Core
interface rather than adding a compiler command or a dependency from
TestGeneration to Driver/LanguageServer. Reuse
DefinitionAnalysis.AnalyzeDocument(includeSemanticFacts:false,
includeProofInputs:true), SourceFingerprint.Compute's existing snapshot overload,
existing immutable ContractSourceSnapshot and resolved
closure utilities. Preserve all retained ambient logical obligations and the
exact embedded random API trust exception. Do not use the specialized
ContractSpecificationChecker Boogie filtering/refinement path for this new
generator proof; preserve its other consumers.

## Change table

| Files/symbols | Change, reason and behavior otherwise unmet | Validation |
| --- | --- | --- |
| This plan, plan/INDEX.md; existing worker-repair plan | Record source ownership, preserve earlier repair history and capture current patch before edits | Diff, hash, Markdown-only audit |
| ContractTesting/ContractGeneratorProof.cs::PrepareProofSources, TryProveAsync, certificate and obsolete private fingerprint/verifier helpers | Keep authored contracts, generate implication lemma, orchestrate standard tasks and require complete bound evidence; remove obsolete custom generator-specific machinery when superseded | Memory source/scope/coverage/identity cases and build |
| ContractTesting/ContractGeneratorProofAudit.cs; optional ContractTesting/ContractGeneratorVerification.cs | Audit actual generated proof context and implement a small ordinary-backend adapter if needed; preserve trust rejection and exact task owner/part accounting | Memory fake-task outcomes including missing/failed/timeout parts, bodyless/assume/ambient cases |
| ContractTesting/ContractSpecificationChecker.cs existing assembly friend declaration | Grant DafnyDriver access to an internal host proof entry; arbitrary public verifier injection must not issue omission evidence. Preserve all existing specification-checker behavior for other consumers | Public/internal API review and build |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs | Supply host-owned standard verifier through existing interface; retain ordinary failed-proof runtime fallback, deadline reservation and cancellation | Direct early-boundary/result tests, source review |
| ContractTesting/ContractRuntimeObligationTransformer.cs | Adapt internal evidence binding if needed; preserve selected-entry-only omission and all remaining runtime/type/heap/callee/postcondition checks | Forged/missing/stale evidence cases |
| Source/DafnyTestGeneration.Test/ContractGeneratorProofTests.cs, ContractGeneratorProofHelperTests.cs; Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs; optional focused ContractGeneratorVerificationTests.cs | Replace obsolete mechanism tests with realistic in-memory behavior checks; generator false ensures vs failed implication, helper closure, target exclusion, source drift, complete parts and cancellation | Trace full helper paths before edits; fake fingerprint IO/normal verifier; no real solver/build/tempdir/sync in tests |
| wiki/pbt-generator-proof-integrity.md, wiki/pbt-generator-proof-helpers.md, wiki/INDEX.md | Document verified authored-contract/implication boundary, helper placement and conservative ambient scope; remove stale strengthened-contract guidance | Source-backed independent review and reciprocal links |
| /workspace/tmp/pbt-worker-failure-20261021/inherited-before-authored-proofs.patch | Preserve exact six tracked source/test diffs from before this refactor, bounded bytes and0444 | git diff explicit six paths, SHA256/size recorded here |
| /workspace/tmp/pbt-authored-generator-proofs-20261021/independent-native-review.md and independent-native-review.json; bounded native verification command logs alongside them | Independent verifier records outside the Markdown-only plan/wiki trees; root coordinates execution after implementation builds/tests finish | Fresh independent source review and separately traced local checks |
| /workspace/tmp/pbt-authored-generator-proofs-20261021/owner-validation.log | Bounded transcript of implementation-owned commands, outcomes and unchanged build warnings, copied from tool outputs; no private data | Compare recorded commands/results with executed tools |

## Proof and compatibility policy

Standard verification selection must use exact resolved declarations, not CLI
substring matching. Every required task/part must finish successfully; require
positive generator correctness and generated-lemma correctness in addition to
dependency well-formedness. Empty selection, failed/partial/unsupported task
results and public JSON counters are not proof. Retain the complete
generator/helper closure and all ambient logical definitions that contribute
axioms; unrelated ordinary method bodies including the target stay excluded.
No unchecked bodyless lemma, assume, verification skip or arbitrary axiom may
establish a certificate. Keep host-controlled options/verifier and exact RNG
library identity. Use analyzer fingerprints and recheck immutable source/scope
binding immediately before omission; no ad hoc fallback identity.

The implication lemma is pure over supported value outputs (and supported
immutable inputs), not an executable ghost call to Generate. Use resolved
capture-free substitution and preserve target requirement order/well-formedness.
Unsupported heap/old/receiver/RNG dependencies return unsupported and retain
checks. Do not add a general source slicer or new compiler feature. Bodyless
proof-helper fallback does not authorize executing a missing non-ghost body.

## Validation commands and boundaries

Cwd is this native root. Read AGENTS.md, CLAUDE.md, Makefile and affected source
instructions. Existing SDK/assets permit:

`dotnet build Source/Dafny.sln --no-restore -m:1 /nr:false`

Expected: matching binaries build without errors. Development tests are only
traced in-memory source/schema/task logic; no real compilation, solver, process,
directory creation, file synchronization or installed-toolchain hashing.
Use fake IO identities/verification boundary for analyzer tests. After build:

AnalyzeDocument's default semantic-facts path reads source files; do not use it
for detached snapshots. Its proof-input path hashes six compiler/Boogie
assemblies on first use. Fake the entire proof-input provider in development
tests; cache warming does not make the real path compliant.

`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter 'FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractGeneratorProofHelperTests|FullyQualifiedName~ContractGeneratorVerificationTests'`

`dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~GeneratorProofResultTests`

Run only included methods whose complete paths pass the I/O audit; update this
plan before widening/changing test classes. Expected: normal and negative proof
workflow cases pass without native solver execution. Record actual counts and
skips. Run scoped `dotnet format whitespace Source/Dafny.sln --no-restore
--verify-no-changes --include <changed C# files>` and `git diff --check`.

A fresh independent verification agent starts from requirements/current code,
not this implementation conversation. Real public Dafny verification/runtime
controls are later operational tasks under their own ready plan, not tests.
No paid run, package, commit or edit of benchmark specifications/scoring here.

## Risks, approvals and knowledge

Existing generators without sufficiently strong ensures retain runtime checks.
Conservative ambient obligations can prevent the optimization. Do not weaken
any proof/trust/scope/fingerprint checks to obtain a pass. Do not hide programming
exceptions with a workflow-wide fallback. The user expressly requests the
architecture and generator-own-postcondition proof; maintenance is authorized.
Relevant durable findings will update the two existing proof wiki topics after
verification. Build/test success alone cannot close the parent stabilization
goal or establish that the old private failure's exact cause was fixed.

## Progress

Ready plan announced; implementation is starting. Bounded inherited patch
capture precedes replacement. Actual operational results and independent
verification pending.


### Implementation boundary decisions

The inherited six-file patch was frozen before edits at
`/workspace/tmp/pbt-worker-failure-20261021/inherited-before-authored-proofs.patch`
(20,521 bytes; SHA256
`3b2f7ede711ae66e0b1573f7311e250765fb97baf665440302cb3daf2b5b98ce`).
The ordinary backend enumerates all native tasks per selected module. A role
with no emitted assertions can be accounted for from that trusted complete
enumeration, but an enumerated part with no successful completion cannot be
reclassified as assertion-free. Generate and the bridge each require positive
actual correctness tasks; zero-task roots retain runtime checking. The adapter
uses IProgramVerifier directly, with ObservableErrorReporter and the existing
normal task lifecycle. Its injected backend entry is internal and accessible to
DafnyDriver, never supplied by request JSON. The legacy custom semantic/options
fingerprint and solver-probe mechanism is deliberately replaced by analyzer
proof-input identities plus snapshot scanner fingerprints; the prior parentless
reference repair remains preserved in the frozen patch.

Development tests will replace obsolete custom-fingerprint/strengthening cases
with bounded in-memory source/audit/binding/coverage cases. The complete analyzer
proof-input provider is faked in tests; no real toolchain identity hashing is
called. Complete task results are tested through an internal pure accounting
boundary; no executable verifier task is started by unit tests.

Raw audit traversal will use PreResolveChildren rather than resolved Children,
including nested concrete-syntax expressions; this is a completeness correction
inside the planned source audit, not a claim about the historical private crash.
The first build uses the exact planned no-restore, single-worker solution command;
only the listed traced memory test classes will then be selected.


### Build scope adjustment

The planned solution build started but the unchanged DafnyRuntime Java target
failed repeatedly because Gradle could not create its lock under the read-only
`/home/vscode/.gradle`. The command was interrupted (exit 130) after recording
that prerequisite failure. No passing full-solution build is claimed.

Every affected C# project references the unchanged runtime indirectly.
`dotnet build --help` documents `--no-dependencies`; existing DafnyCore,
DafnyPipeline, DafnyRuntime and DafnyLanguageServer binaries are available.
Use these sequential builds to compile all changed source/test files against
those existing unchanged dependencies, without regenerating Java or restoring:

- `dotnet build Source/DafnyTestGeneration --no-restore --no-dependencies -m:1 /nr:false`
- `dotnet build Source/DafnyDriver --no-restore --no-dependencies -m:1 /nr:false`
- `dotnet build Source/DafnyTestGeneration.Test --no-restore --no-dependencies -m:1 /nr:false`
- `dotnet build Source/DafnyDriver.Test --no-restore --no-dependencies -m:1 /nr:false`

This is affected-C# compilation validation, not a full toolchain rebuild.

The first affected-project build found CanVerifyOrigin is internal to DafnyCore.
Use the existing public OriginWrapper.WrappedOrigin to identify task ownership
by exact unwrapped origin reference plus owner module and native role name;
reject ambiguous or unknown parts. Do not expose compiler internals or select by
substring. This API correction stays inside the planned ordinary adapter.

The corrected TestGeneration and Driver project builds passed with zero warnings
and errors. Production edits are settled for independent source inspection;
implementation-owned tests and documentation are still being finalized. The
first TestGeneration.Test build passed with four pre-existing warnings plus one
new assertion-style warning, which is corrected before rerunning that build.

The parent source precheck found required task names could be ignored if origin
mapping failed. The adapter now rejects a required descriptor with an unknown,
ambiguous or null owner before accounting for assertion-free roles. Its small
internal selection helper is exercised with bounded parser fixtures and no
native tasks, including both wrong-owner and null-origin cases. Production
builds must be repeated for this correction; independent reviewers are notified.

### Final implementation-owned checks

All four affected C# builds passed after the task-owner correction. TestGeneration,
Driver and Driver.Test had zero warnings/errors. TestGeneration.Test had four
pre-existing warnings: ContractRuntimeProfile.cs lines 44/55 (CS0162),
PbtObservation.cs line 287 (CS0618), and ContractPhaseTimingTests.cs line 211
(VSTHRD103). The approved TestGeneration filter passed 37/37 and Driver filter
passed 9/9, zero skips. The first test runner invocation aborted before executing
tests because its local TCP communication socket was sandbox-blocked. The exact
command succeeded with auto-reviewed escalation for that local socket.

The solution-scoped whitespace verifier produced no output for several minutes
and was interrupted. `dotnet format whitespace --help` documents `--folder`;
use `dotnet format whitespace . --folder --no-restore --verify-no-changes
--include <same nine changed C# paths>` to check only those files without loading
the solution. This changes workspace loading only, not the formatter or scope.
The bounded transcript is the owner-validation.log path above. Independent
source review is underway; native proofs/runtime controls remain unrun here.

Independent review identified that nonempty analyzer output alone does not bind
every required body: schema 1 deliberately omits unsupported definition rows
and excludes other modular method implementations from each row. Capture will
therefore require exact source-path/full-name identities for every audited
callable, validate schema/digests/unique identities and reject missing rows.
After ordinary scopes are known, strengthen the original binding to all those
callables except the generated bridge and compare it with the fresh source
resolve. The private proof binding includes the bridge. Non-callable type and
constant obligations remain in each analyzer row's ambient translation. Tests
fake whole valid-shaped analyzer output and remove generator/bridge/helper rows
while retaining an unrelated row, plus malformed schema/digest/duplicate cases.
Affected builds and only the changed TestGeneration memory filter will repeat.

Folder whitespace formatting rejects the `--no-restore` combination at argument
validation; omit that flag in folder mode, which loads no project and performs
no restore. The exact corrected command is `dotnet format whitespace . --folder
--verify-no-changes --include <same nine changed C# paths>`.

### Authored helper and deferred-AST correction

Independent review traced the real Runner seam: MakeGeneratorVisible blanks
ghost method bodies before runtime reachability. Proof must instead receive
sourcePreparation.Sources before that erasure. Extend the internal proof entry
and Driver call to supply these authored snapshots. Reuse MakeGeneratorVisible
on a raw parse of those snapshots, append the exact runtime resource, and
require equality with the supplied executable snapshots. Normally parse both
contexts before analyzer use. Never translate the diagnostic resolver's AST.
The certificate owns the normally resolved runtime program and selected
declarations; only a verified result switches Runner to these identical-source
objects for transformation. Failure leaves the existing runtime path unchanged.
The generated bridge and all helper verification use the authored context.

The independent reviewer traced ContractRuntimeSourcePreparationTests through
bounded strings, dictionary parsing and source maps with no native tool/IO
boundary. Add that exact unchanged class to the final TestGeneration filter:
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter
'FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractGeneratorProofHelperTests|FullyQualifiedName~ContractGeneratorVerificationTests|FullyQualifiedName~ContractRuntimeSourcePreparationTests'`.

Memory controls will cross PrepareAsync and the actual visibility seam, retain
nontrivial valid and false helper bodies in proof sources, and check invalid
ghost proof resolution returns unsupported before a verifier is touched. Add
forged-report runtime transformation and bounded quantified binder collision
controls in the existing authorized proof test classes. Extend the internal
pure cancellation outcome seam only if needed; no real task/solver/IO test.

The whole analyzer provider seam is also passed internally through TryProveAsync
for a cancellation-only control: its fake throws before real hashing or native
tasks, and the public outcome is timeout with runtime checks retained. Caller
cancellation is tested separately before all external boundaries. Certificate
rechecks always use the real analyzer provider; no test provider is retained as
omission authority. A first 77-case memory run found one test expectation error:
resolved quantifiers expose split descendants as well as the root, so the binder
test now inspects the actual root quantifier rather than requiring a unique
descendant. The other 76 cases passed; this run is not final acceptance.

Independent recheck required Runner to adopt the certified runtime options along
with its program and declarations. It now assigns options = program.Options on
successful handoff, so subsequent transformed-source resolve, runtime compilation
and queries share the bound detached options. No public schema changes. The
corrected expanded memory selection passed 78/78 and Driver 9/9 before this
one-line Driver correction; rebuild Driver/Driver.Test and rerun its filter.
Folder formatting found one helper-test whitespace change and applied it;
rebuild the formatted test binary and rerun the affected helper class only.

### Settled implementation handoff

Final Driver/Driver.Test builds passed with zero warnings/errors; its selected
filter passed 9/9. The formatted TestGeneration.Test rebuild passed with exactly
the four pre-existing warnings recorded above, and affected HelperTests passed
15/15. The expanded 78/78 run remains the final semantic TestGeneration selection;
only helper whitespace changed afterward. Final folder whitespace verification
passed. All commands finished before independent executable checks were released.
The bounded command receipt is
`/workspace/tmp/pbt-authored-generator-proofs-20261021/owner-validation.log`.

Durable findings updated [proof boundary](../wiki/pbt-generator-proof-integrity.md)
and [helper guidance](../wiki/pbt-generator-proof-helpers.md), with current
authored/runtime source ownership and exact analyzer row completeness. Earlier
2026-10-20 native acceptance is explicitly historical. The inherited custom
fingerprint repair remains frozen in its patch, and unrelated preparation and
null-draft fixes remain intact. Source-only root review and fresh independent
native verification are separate records; this owner plan stays in-progress
until independent acceptance and the parent-owned public controls settle.

Remaining work: independent current-source review/checks; actual ordinary proof
and runtime controls, especially the common tautological bridge/zero-task
boundary; parent integration and stabilization. No compiler/solver or experiment
control was executed by this implementation task, and no commit was created.

Final `git diff --check` passed. Recursive hidden/ignored-inclusive
`rg --files --hidden --no-ignore plan wiki -g '!*.md'` found no non-Markdown
files. The implementation handoff has no pending code, test, documentation or
artifact writes and no running validation process.

## Binding diagnostics follow-up, 2026-10-21

Status: ready, then in-progress on announcement. Parent scope is
[binding diagnostics](/workspace/plan/2026-10-21-pbt-verifier-binding-diagnostics.md).
Public r02 retained runtime checks and executed three valid samples, but its
compound final binding diagnostic did not identify the rejected component.
This follow-up changes diagnostic precision only; repeat-translation state is
a source-backed hypothesis, not an established r02 cause.

| Exact files/symbols | Change and necessity | Validation |
| --- | --- | --- |
| ContractGeneratorProof.cs::TryProveAsync final gate, ContractGeneratorInputBinding::Capture/Matches and small internal ordered diagnostic helper | Preserve exact equality/complete identities and capture each comparison once; attribute proof/runtime/caller-policy failure and bounded source/analyzer/toolchain/options/definition mismatch | Whole-analyzer fake cases for unchanged inputs, each drift, missing/malformed rows, output bounds and short-circuit order |
| ContractGeneratorProofTests.cs | Extend existing memory fixtures with meaningful mismatch diagnostics and ordered final-gate checks | Same dictionary parsing/fake entire provider; no real analyzer hashing, solver, process, temporary directories or sync |
| This plan, plan/INDEX.md, wiki/pbt-generator-proof-integrity.md, wiki/INDEX.md | Record actual limited r02 result, diagnostic semantics and unestablished cause | Diff and Markdown-only checks |
| /workspace/tmp/pbt-verifier-binding-diagnostics-20261021/owner-validation.log and independent source-review.md/source-review.json | Bounded command receipts and fresh independent current-source review outside documentation trees | Exact commands/results/hashes and no runtime acceptance claim |

No analyzer/translator/ID-counter/clone reset changes, baseline replacement,
weakened hash/source/scope/certificate checks, CLI/schema additions or changed
proof semantics. Tests retain full serialized analyzer equality, including
definition order and unrelated rows; output truncation never limits validation.
Use sequential builds of Source/DafnyTestGeneration, Source/DafnyDriver,
Source/DafnyTestGeneration.Test and Source/DafnyDriver.Test with
`dotnet build <project> --no-restore --no-dependencies -m:1 /nr:false`.
Then run the audited proof/helper/verification classes only:
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter
'FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractGeneratorProofHelperTests|FullyQualifiedName~ContractGeneratorVerificationTests'`
and `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter
FullyQualifiedName~GeneratorProofResultTests`. Scoped folder whitespace verification
includes the two changed C# files; run git diff --check and recursive
hidden-inclusive Markdown-only audit. No actual public campaign, packaging,
native CLI, paid run, private input, package or commit is authorized here.

### Diagnostic implementation and local verification

Implemented ordered proof/runtime/caller-policy reporting and bounded component
mismatches. Exact serialized equality still decides acceptance; component
decoding happens only after rejection. Missing required identities retain the
original Any-based guard, and malformed null identity text is displayed safely
without converting a prior bounded rejection into an exception. Self-review
checked each old Capture predicate, certificate gate and final short-circuit
order against the revised code. No analyzer, translator, verifier or proof-source
generation behavior changed.

Initial diagnostic tests passed 71/71 and Driver 9/9. Final self-review added
two null-identity regression cases and repeated the four sequential builds:
all passed, with only the four existing TestGeneration.Test warnings. Final
approved selection passed 73/73, Driver 9/9, zero skips. The full-source hash
handoff below supersedes the earlier provisional hashes sent before null-safe
formatting. No independent executable review overlapped those builds.

- ContractGeneratorProof.cs: `c89723ae57375485c946bcdef11961b7fff7f153eeebc5585d1bc21890c5537a`
- ContractGeneratorProofTests.cs: `3d5cbaed546905d67b7858435a2d2b8629f5d56bf7dd796c4fcefaa5bba76f74`

Command receipts and existing warning locations are transcribed in
`/workspace/tmp/pbt-verifier-binding-diagnostics-20261021/owner-validation.log`.
Independent current-source review and actual diagnostic attribution remain
pending; r01/r02 artifacts and their source-only frozen reviews were untouched.

Final scoped folder whitespace verification and `git diff --check` passed.
Recursive `rg --files --hidden --no-ignore plan wiki -g '!*.md'` found no
non-Markdown files. All implementation self-review, builds, tests and records
are complete; no writes or validation processes remain pending. The next step
is the fresh independent current-source review; actual diagnostic operation
requires its separate ready plan.
