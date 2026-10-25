# Diagnostic treatment of unrelated bodyless declarations

Status: independently accepted source/local method/constructor, iterator transformation and execution-only draft-discovery repairs. Actual R07 false Valid draft is preserved; full new iterator workflow remains root-owned and unaccepted.
Verified: method/constructor scope2026-10-21 on base `b4f683fd85c9764c032346e0367df325f73dd4be`; iterator transformation2026-10-23 on `5fa47c6e949dad736db25e02b5edad95d0b0be1a` plus the predecessor four-file delta. The later accepted discovery correction retains five source leaves218055B on that same base, reviewa60e53f9... below.
Originating plan: [compile selected PBT helpers in unfinished workspaces](../plan/2026-10-21-pbt-unreachable-bodyless.md).

## Compilation boundary

Runtime-diagnostic source preparation requests drafts only for executable callables
reachable from the selected goal and generator. The later diagnostic transformer
still emits the whole supplied workspace, so an unrelated non-ghost, nonvirtual,
nonextern method, function or constructor without a body would otherwise reach
the backend's `c_method_has_no_body` or `c_function_has_no_body` error.

`ContractRuntimeObligationTransformer.EraseUnreachableBody` now gives those
unreachable concrete declarations the same fail-fast diagnostic implementation
used for unrelated declarations that already have bodies. Methods call
`PbtChecks.UnreachableBody`; functions return `PbtChecks.UnreachableValue`; and
constructors initialize their source fields, cross `new;`, then call the body
trap. Constructor initialization assigns mutable fields and constants without an
authored initializer; a constant whose declaration already has an expression
retains that expression and is not assigned again. Missing bodies are inserted
after the parser-owned final declaration token
using its UTF-8 byte length, matching the established draft-body insertion
boundary. Original clauses, attributes and immutable source snapshots remain
unchanged.

This is a runtime-diagnostic repair. The ordinary generator-proof raw audit still
rejects an authored bodyless logical function, even if it is unrelated to the
selected runtime closure. That conservative proof boundary is unchanged: report
unsupported proof and retain requires checks rather than certify the inserted
diagnostic trap as an authored implementation.

The transformation preserves null bodies that already have defined language or
backend meaning: reachable goal/generator callees, ghost callables, instance
trait members, declarations in abstract modules, imported `{:extern}` members,
and valid bodyless `{:synthesize}` methods. Concrete class overrides are not
virtual declarations; when unreachable and bodyless, they receive traps so they
do not block whole-program compilation. Existing-body override handling is
unchanged.

## Evidence and limits

Sources: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs`.
Memory regressions: `Source/DafnyTestGeneration.Test/ContractRuntimeUnreachableBodyTests.cs`.

The first regression built against the unchanged transformer and failed because
the unrelated method body remained null. The final eight-case selection covers a
complete selected helper beside plain bodyless method/function declarations,
UTF-8 final contract tokens, adjacent/module-end insertion, constructor field
initialization for inserted and replaced constructor bodies, initialized and
uninitialized constants, concrete overrides, and every preserved null-body category above.
It also checks a bodyless method reached from the selected entry, and method/
function callees reached from the generator. The original source snapshots and clauses remain intact, and the
inserted ASTs resolve to the diagnostic trap calls.

Local cached product and test-project builds passed. The new eight cases and the
affected obligation, source-preparation, generator-proof, proof-helper and
generator-verification selections passed (119 tests total), with no skipped
tests. The test bodies use only in-memory snapshots, parsing, transformation and
reparse; they do not invoke a compiler, solver, process, staging, temporary
directory, synchronization or toolchain hashing. VSTest itself used its approved
localhost control socket. Scoped whitespace verification passed.

Fresh independent review found the initialized-constant problem before
acceptance and rechecked its correction. Its own two cached builds passed with
zero warnings/errors; all119affected memory cases passed with zero failures or
skips. Source/test identities are respectively
37beb75be2f5040791fcd5aae57887c734ab38c50544fd91a15092dd0eecc784
and565eb1a811dab6b5bc71d50ae33375826e8c7398d5a4af0e443346b0acc81a65.
The readonly [independent report](../../../tmp/pbt-unreachable-bodyless-20261021/verification.md)
is7588bytes, SHA256
3bbe6468c053dd6f7ed3999d82ef593aa4fdd8a51070c493df8800afab4d7ffc;
its JSON is21497bytes, SHA256
a8c4fbf515bedd8f3b59357055a70a00b3d517fd9a4116d01ced150e41d811be.
Both are public scratch evidence and may not be available outside this checkout.
Concurrent nested-match source/test work is preserved and outside this repair;
the cached dependency build does not verify that work.

This evidence does not establish native generated-program compilation, sample
execution, solver proof, Docker/image acceptance, benchmark efficacy or public
cohort stability. Those operational claims belong to parent plans after fresh
source/package/operational gates. The next package step is the separate
[isolated overlay build](../plan/2026-10-21-pbt-isolated-overlay-build.md).

## Iterator declarations and execution boundary (2026-10-23)

An IteratorDecl owns its body separately from MemberDecl. Its generated _ctor,
Valid and MoveNext members share iterator-wide source ranges. Generic missing
method-body insertion therefore corrupted detached source beside an unrelated
bodyless iterator; an actual pre-fix memory regression failed with rbrace expected.
Separately, wrapping a reached MoveNext like a source method generated a member
that iterator syntax cannot declare and failed ordinary re-resolution.

The transformer now handles source-owned unrelated concrete iterators directly
and excludes their generated members from generic body insertion. Existing
bodies become fail-fast traps; missing bodies are inserted after parser tokens
and trailing trivia using UTF-8 byte lengths, including actual EOF comments.
Abstract, compile-disabled and omitted-signature semantics remain preserved.
Iterator extern attributes do not independently grant bodyless code-generation
support; ordinary iterator backend semantics determine that treatment.

Directly type-referenced iterators retain their bodies. Genuinely unexecuted
nested helper/iterator bodies may still receive traps; preserving every authored
nested body is unnecessary and could retain another unimplemented declaration.
Original snapshots, authored contracts and selected bodies remain unchanged.

Actual iterator-member execution is explicitly unsupported: existing runtime
instrumentation does not cover IteratorDecl.Body, nested calls or yield contracts.
The runner rejects selected-goal execution before missing-draft/generator requests,
then checks the exact resolved generator closure before construction audit,
further drafts, proof or transformation. Transform also rejects before edits.
The reply identifies the iterator and advises selecting a goal/generator without
iterator-member execution. It never requests drafts for generated MoveNext or
silently omits those checks to accept samples.

The resolver represents iterator TYPE dependencies as pseudo-callable IteratorDecl
graph nodes. The private capability-only closure excludes those graph targets;
direct generated members, function values, dynamic dispatch, constraints and
constant initializers remain traversed. Public execution/diagnostic closures and
proof/fingerprint behavior retain their previous conservative mode. A type-only
nullable local therefore passes that capability/transformer seam; this did not
establish full campaign preparation, as the later R07 failure below demonstrates.

Source: ContractRuntimeObligationTransformer.cs and ContractRuntimeCampaignRunner.cs.
The unchanged embedded runtime's normalized digest is
adcd11f333a7086255e3736b212dbd613737f7b6af084f64f86545cf76d5425e;
the stale Driver command-test constant now matches its existing memory-test pin.

Fresh independent review accepts71memory tests, four isolated cached project
builds, exact formatting/diff and source/reference/output audits. Test helpers use
snapshot dictionaries and in-memory C# syntax emission, with fake/no verifier
paths; no target C# compilation, Z3, native campaign or Driver command execution
occurs. The one sandbox testhost-socket abort is preserved before the exact
authorized replacement; it executed zero tests. Native SDK8.0.131 and final
source hashes are recorded in the
[owning plan](../plan/2026-10-23-pbt-iterator-diagnostic-isolation.md).

Public independent reports are
[source-review.md](../../../tmp/pbt-iterator-diagnostic-isolation-20261023-r01/verification/source-review.md)
and its JSON companion, exclusive0444, SHA2563be1d3e7.../a54657d0....
They are local scratch evidence. Actual runtime/image acceptance is the separate
[root image/control plan](../../../plan/2026-10-23-pbt-iterator-isolation-image.md),
in-progress with actual failed attempts preserved. These source findings do not
identify any private cohort failure.

## Iterator types and implementation draft discovery (2026-10-23)

Status: actual defect independently established; source/local correction
independently accepted2026-10-23 on5fa47c6e...plus5source delta218055B.
Applicability: a selected method
or prepared generator mentions an iterator type without constructing/advancing it.
Originating plan: [draft-discovery correction](../plan/2026-10-23-pbt-iterator-draft-discovery.md).

R07's [actual execution review](../../../tmp/experiment/pbt-iterator-isolation-image-20261023-r07/verification/execution-review.md)
accepts preserved failure/resources/accounting/cleanup and rejects success.
Rootba6503 authenticates JSON88c2c721.../MDcb2b437b.... The first receipt binds
selected Isolation.Scalar and the exact415B public source55c6ab086a...; it returns
drafts_required for Isolation.Typed.Valid at Main.dfy:5, with an iterator-header
signature. Typed already has a body; Scalar has only an unused Typed? local.
This is one returned/bound call,0accepted/generated/proofs and seven calls unrun.
It establishes no private cohort cause. Evidence is local public scratch and may
not remain available after cleanup outside this task.

The resolver adds a type dependency edge to IteratorDecl. Default broad
ExecutionReachable follows it and scans generated contracts referencing the
bodyless Member_Valid. MissingDrafts classified that ghost Function as an authored
missing implementation, using its shared iterator origin for OriginalSignature.
The earlier private capability mode omitted the pseudo-edge, but discovery used
the broad default and returned before transformation. Transformer-only emission
tests could not detect this response.

The frozen correction adds internal RuntimeExecutionReachable around that same
false-type-edge mode and uses it for MissingDrafts and the existing capability
query. It keeps public broad ExecutionReachable/DiagnosticReachable, proof/trust/
fingerprints and type-preserving transformation unchanged. No name-based Valid
filter or new assumption is introduced. Actual callable/spec/helper/type-
constraint/dispatch edges remain; an unused iterator's yield-only helper no
longer becomes an implementation request. The owner-based Unsupported guard
remains conservative for directly reached generated iterator members, including
explicit Valid references; finer ghost-validity support is not claimed.

New Driver.Test regressions call production discovery after real snapshot
parsing/resolution/selection. The prepared-generator case also uses actual source
preparation, visibility rewriting and deferred resolution. They preserve genuine
body/spec/generator helper requirements and the constructor/advance boundary.
The initial red selection retains two actual product failures and two corrected
fixture defects. Fresh independent review accepts its own3isolated builds and
4memory cases,0warnings/errors/skips, complete five-source/asset/reference/effect
audits. Root558a59/c98011 authenticates JSONa60e53f9.../MDaeba37c2...; rootd49093
fully binds four output/intermediate pairs1692148B and unchanged product deps/
runtimeconfig. Exact accepted prefix is the independent verification/out,
not implementation/out; future packaging must use that prefix and hashes.
[Review evidence](../../../tmp/pbt-iterator-draft-discovery-20261023-r01/verification/source-review.md)
is public local scratch. New registered sampling/compiler/solver/image results
remain separate root requirements. Do not implement generated Valid or weaken
the public fixture to make R07 disappear.
