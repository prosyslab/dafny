# Repeatable analyzer inputs across ordinary translations

Status: in-progress
Date: 2026-10-21
Owner: isolated native checkout, base b4f683fd85c9764c032346e0367df325f73dd4be plus preserved existing changes.
Parent: [root repair plan](/workspace/plan/2026-10-21-pbt-repeatable-proof-inputs.md).
Related: [authored generator proofs](2026-10-21-pbt-authored-generator-proofs.md), [proof integrity](../wiki/pbt-generator-proof-integrity.md).

## Objective and acceptance

This is public repository maintenance. Reproduce the quantified helper's changed
analyzer input using real in-memory translation before changing naming. Then make
ordinary translation naming local to a translation, preserving every existing
source/options/toolchain/definition/scope/certificate equality gate. Unchanged
once-resolved programs must have identical fingerprints before and after ordinary
translation; actual resolved-body, contract, options and toolchain changes must
still change their identities. No proof acceptance or operational stabilization
is inferred from these source checks.

Inspected evidence: the accepted public binding diagnostic identifies
QuantifiedControl.GeneratorRange; SetupBoundVarsAsLocals allocates fresh locals
through persistent declaration generators, original variables cache names, and
forall Push/Pop advances child scope counters. Existing Program resolved cloning
is unsupported; resetting counters alone can collide with cached names. Existing
DefinitionProofInputsTests currently reach prelude disk reads and six assembly
hashes and must be adapted before execution. Preserve all previous source work,
review artifacts and public operation slots. No private data or provider inputs.

## Exact changes and validation

| Files/symbols | Change and necessity | Validation |
| --- | --- | --- |
| Source/DafnyCore/Verifier/BoogieGenerator.cs | Internal prelude factory seam, shared production define computation; disposable naming scope inside ordinary DoTranslation | Embedded fresh prelude; consecutive and intervening ordinary translations |
| Source/DafnyCore/Verifier/FreshIdGenerator.cs | Small internal translation naming context, scoped declaration generators and variable names | Nested scopes, cleanup, consistent names and unchanged outside behavior |
| Source/DafnyCore/AST/TypeDeclarations/Declaration.cs | Route verification generator through active translation context, retain outside generator | Code-generation generator remains unchanged |
| Source/DafnyCore/AST/Expressions/Variables/NonglobalVariable.cs and AST/Statements/Assignment/LocalVariable.cs | Route verification name assignment/read/assigned-state through active context | Collision, trigger name consistency, outside-state controls |
| Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs | Internal environment overload of actual analyzer with supplied translator and toolchain identity; production defaults unchanged | Real projection/serialization/lexer/hashing; synthetic toolchain boundary |
| Source/DafnyCore.Test/ProofInputRepeatabilityTests.cs, DefinitionProofInputsTests.cs, DafnyCore.Test.csproj | Strict memory filesystem, embedded unchanged prelude, actual pre-fix regression and adapted analyzer tests | No solver/process/staging/directories/disk sync/installed assembly hashing |
| This plan, plan/INDEX.md, wiki/pbt-generator-proof-integrity.md, wiki/INDEX.md | Record exact source evidence, checks and limits | Diff and Markdown-only audit |

## Boundaries and implementation decisions

No public API/CLI/schema/package/compiler feature changes. Test injection is
internal and cannot authorize candidate certificates. Keep actual analyzer hash
algorithm and exclusions unchanged. Naming context must cover both declaration
generators and variable caches, restore an enclosing context on exception, and
leave compiler names untouched. Audit all UniqueName/HasBeenAssignedUniqueName
consumers, including TriggerExtensions, before production edits. Use a scoped
context rather than AST traversal or semantic cloning. Stop and update this plan
before expanding scope or changing approach.

Test setup: parse bounded source through a strict IFileSystem dictionary that
throws for unknown paths (the existing InMemoryFileSystem has disk fallback).
Resolve with no includes, plugins, print files or external libraries. Translate
using the original embedded DafnyPrelude.bpl parsed freshly in memory with the
same arithmetic/Unicode defines. Hash via the actual analyzer with a supplied
synthetic toolchain digest. Never call ExecutionEngine.GetVerificationTasks or
the real ProofToolchainHash. All teardown is managed-object disposal. Test
resources are embedded at build time, not read from disk by tests.

## Commands and artifacts

Working directory: /workspace/tmp/pbt-worker-failure-20261021/native.
All commands sequential, no restore/download, no full solution, launcher/image,
actual control or paid run. Build only minimum needed prerequisites, in order:
`dotnet build Source/<project> --no-restore --no-dependencies -m:1 /nr:false`
for DafnyCore, DafnyPipeline, DafnyLanguageServer, DafnyTestGeneration, DafnyDriver,
DafnyCore.Test, DafnyTestGeneration.Test, DafnyDriver.Test. Initially only Core
and Core.Test are required for the pre-fix regression. Existing generated parser
inputs are unchanged; do not force regeneration.

Before naming correction: `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~ProofInputRepeatabilityTests`.
Preserve the actual failure, then implement naming. After correction, run Core
filters `FullyQualifiedName~ProofInputRepeatabilityTests` and
`FullyQualifiedName~DefinitionProofInputsTests` in separate invocations;
TestGeneration filter `FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractGeneratorVerificationTests|FullyQualifiedName~ContractGeneratorProofHelperTests|FullyQualifiedName~ContractRuntimeSourcePreparationTests`;
Driver filter `FullyQualifiedName~GeneratorProofResultTests`, each with
`dotnet test Source/<project> --no-build --no-restore --filter '<filter>'`.
Test-runner local TCP permission, if required by sandbox, is distinct from the
memory-only test bodies. Audit all direct/indirect paths before each new class.

Scoped `dotnet format whitespace <project> --no-restore --include <touched files> --verify-no-changes`,
`git diff --check`, exact changed-source hashes and recursive plan/wiki
non-Markdown audit finish local validation. Root owns fresh independent review.
Logs <=8MiB each live only at /workspace/tmp/pbt-repeatable-proof-inputs-20261021/
build-before.log, checks-before.log, build-after.log, checks-after.log;
before.patch and before-state.json pin the exact pre-fix Core/test source state;
source-review.json, source-review.md, independent-checks.log are reserved for
root's fresh verifier. No overwrite of prior artifacts. Record actual outcomes
below; unrun checks are not passing results.

For C# whitespace only, the equivalent folder form is
`dotnet format whitespace . --folder --include <exact touched C# paths>` and then
the same command with `--verify-no-changes`; this avoids project loading while
using the repository .editorconfig. The first folder-format pass targeted Core;
the final pass and verification include Core and both changed test files.

## Progress

- Ready: instructions, current source, public diagnostic and root plan inspected.
  No naming changes or new test executions yet. No additional approval required
  within the announced root scope. Independent source review and subsequent
  operational acceptance remain parent-owned.
- Implementation started with test-environment seams only. A bounded read-only
  gpt-6-astra/high support audit checks variable-name consumers and outside-state
  compatibility; it is not independent verification. Ordinary IVariable's
  HasBeenAssignedUniqueName contract must remain meaningful after translation.
- Prelude seam uses existing SourcePreprocessor.ProcessDirectives on the embedded
  resource and Boogie's string parser; the existing prelude contains only the
  supported #if/#else/#endif directives. Two initial test builds failed while
  resolving the Boogie API (no text+defines overload or Boogie.Preprocessor type);
  those results remain in build-before.log. Core seam build passed, 0 warnings.
- Consumer audit found only TriggerExtensions.SameBoundVar outside verifier code;
  all operational AssignUniqueName callers pass declaration generators. Preserve
  legacy names and their generator counters separately: scoped assignment also
  initializes a previously absent legacy name using its legacy generator. Outside
  assigned-state/pre-existing names and future uniqueness remain intact. Newly
  initialized outside names can differ from emitted scoped identifiers; no
  inspected consumer requires equality. Scope begins after plugin PreVerify and
  restores the prior context before DoTranslation returns or throws. It does not
  span the yielding Translate iterator. Compiler naming is unchanged.
- Actual pre-fix checks: Core and Core.Test seam builds passed with 0 warnings;
  first test-runner attempt was aborted by the sandbox's local TCP restriction.
  The authorized socket-only escalation then ran both real memory regressions:
  0 passed, 2 failed, 0 skipped, with changed GeneratorRange definition hashes.
  This reproduces consecutive-analysis and analysis/ordinary-translation/analysis
  drift. Naming files remain unchanged until the exact pre-fix patch/hash capture.
- Pre-fix patch SHA256 b7fda3e51269c3527a77876d8056a99a11a5b7f5a9909f686a983f4e403b4296;
  before-state.json lists all nine Core/test hashes. Naming implementation uses
  thread-local context because DoTranslation is synchronous, with using-disposal
  restoring its enclosing context. Legacy names are allocated using mapped legacy
  generators; code-generation names are untouched.
- Initial corrected Core check passed 32/32, zero skips (11 new repeatability/
  mutation/scope cases plus 21 adapted analyzer cases). It used a combined filter,
  already started before root requested separate final invocations; both classes
  belong to one explicit nonparallel collection, so the run remained serial.
  Final validation will use separate class invocations as requested. One initial
  corrected test build failed on xUnit's throw-only lambda overload ambiguity;
  explicit Action resolved it, and the subsequent build had zero warnings.
- Added a direct trigger-equivalence control for scoped versus legacy binder
  names. Both new and adapted analyzer classes share a nonparallel collection.
  Embedded prelude is the unchanged existing 67,083-byte resource; all reads in
  its test parser use managed resource/string streams and the production defines.

## Settled local handoff

All planned local implementation and self-review are complete. Final production
changes are the five naming files and DefinitionAnalysis.ProofInputs.cs; test
changes are DefinitionProofInputsTests.cs, new ProofInputRepeatabilityTests.cs,
and DafnyCore.Test.csproj. Documentation changes are this plan, plan/INDEX.md,
wiki/pbt-generator-proof-integrity.md and wiki/INDEX.md. All earlier inherited
and authored-proof changes remain preserved. No commits or operational runs.

Final sequential builds passed for all eight listed projects. The five production
libraries and Core.Test/Driver.Test had zero warnings/errors. TestGeneration.Test
retains exactly four pre-existing warnings: ContractRuntimeProfile.cs:44 and :55
(CS0162), PbtObservation.cs:287 (CS0618), ContractPhaseTimingTests.cs:211
(VSTHRD103). Their complete paths and diagnostics are in build-after.log.
The earlier new trigger test build failed due to an incorrect internal class
identifier; the corrected ExprExtensions alias then built with zero Core-test
warnings. Earlier API/overload compile failures are preserved, not passing builds.

Final serial test invocations passed 12/12 ProofInputRepeatabilityTests,
21/21 DefinitionProofInputsTests, 97/97 selected TestGeneration classes and
9/9 GeneratorProofResultTests, all zero failed/skipped (139 unique final cases).
Scoped folder whitespace verification passed. The final diff/Markdown-only
audit and source/library hash manifest are recorded with exit results in the
external logs. Build outputs to hand off explicitly are
Binaries/net8.0/{DafnyCore,DafnyPipeline,DafnyLanguageServer,DafnyTestGeneration,DafnyDriver}.dll;
their exact hashes and all current-task source/document hashes are appended to
build-after.log after documentation settles. Canonical flat packaging is root-owned.

This plan remains in-progress for fresh independent verification and parent-owned
operational acceptance. No further source/test/document writes are planned after
the settled hash handoff; coordinate any correction before changing the reviewed
state. Root owns source-review.md/.json and independent-checks.log. Source-level
repeatability is established for the covered quantified/nested cases; the public
operation's sole cause and actual generator proof acceptance are not claimed.
