# Resolved verification target facts

Status: current; locally and independently verified
Verified: 2026-10-18 at `bc427b21461f258fd8de34232e01bb6be03cee39` plus scoped implementation diff
Originating plan: [resolved verification target facts](../plan/2026-10-18-verification-target-facts.md)

`definition-analysis --include-verification-facts` returns the document wrapper
and adds `sourceFacts.verificationTargets`. Each record has `fullName`,
`sourcePath`, and `attributes` (existing `name`, `arguments`, `start`, `end` records).
The property is absent without this opt-in; existing array and source-facts
consumers retain their previous shape. Combining the flag with `--spans-only`
is rejected because native targets require resolution.

The driver takes targets directly from `ResolutionResult.CanVerifies`, built by
`TextDocumentLoader.ResolveInternal` with native verification eligibility checks.
The analyzer restricts this inventory to requested analysis sources and orders it
by source path/native full name. It does not infer verification targets from source
declaration kinds or derive names. In particular constructor names retain their
native `#` prefix, and function by-method proof ownership stays with the native
function target. Subset/newtype, constants and iterator-generated targets follow
the actual compiler inventory.

Attributes describe authored target declarations. Legacy brace attributes reuse
`DefinitionAnalysis.AttributesFor`; authored `@TimeLimit` and
`@TimeLimitMultiplier` are reported under their resolved legacy names `timeLimit`
and `timeLimitMultiplier`, with authored arguments/spans. Synthesized multiplier
expansions are omitted. Compiler policy and proof behavior are unchanged; callers
apply their own policy. Statement/module attributes are outside this metadata scope.

Sources: `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs`,
`Source/DafnyCore/DefinitionAnalysis.VerificationFacts.cs`,
`Source/DafnyCore/Pipeline/TextDocumentLoader.cs`, and
`Source/DafnyCore/AST/Attributes.cs`. Evidence: focused in-memory native tests
7/7 and native driver build passed; see plan for commands and prerequisites.
These tests establish analyzer behavior, not benchmark proof acceptance.

CLI symbol filters ending in `.` still use suffix matching. Native full names
are authoritative but do not change that selector behavior; callers must account
for same-file suffix collisions when requiring single-target selection.
## Independent verification

Fresh independent review accepted 2026-10-18: driver/core-test builds, seven focused
tests, native generic proof/attribute controls and legacy wire compatibility.
Whole-file style verification retains four IDE0048 diagnostics already present
at the baseline; touched-file whitespace checks pass. See the originating plan
for exact commands, evidence and limits.
