# Diagnostic treatment of unrelated bodyless declarations

Status: independently accepted source/local repair; actual generated-program and image validation remain pending under parent plans.
Verified: 2026-10-21 on native base `b4f683fd85c9764c032346e0367df325f73dd4be` plus the preserved reviewed PBT changes and this repair.
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
