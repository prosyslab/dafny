# Substitute nested statement matches in proof expressions

Status: done (focused source repair independently accepted)
Date: 2026-10-21
Parent: [compiler repair and weekly restart](../../../plan/2026-10-21-native-match-crash-weekly-restart.md).

## Objective and acceptance

Fix the native `Substituter` abort on legal nested statement-match syntax inside
a function-body proof statement. Preserve constructor-pattern variable binding,
scope restoration, resolved statement semantics and ordinary proof checking.
Keep unsupported/malformed states explicit; no assertion removal, proof skip,
assumption, source rewrite heuristic or benchmark change.

## Evidence and change table

The current weekly paste-r04 `ShapeParallelEntriesFromLines` process exits-6
while translating a function axiom. `SubstStmt` lacks `NestedMatchStmt` although
ordinary verifier translation consumes its resolved flattened form. Baseline is
native `b4f683fd8`; unrelated dirty PBT source is preserved.

| Files / symbols | Change / necessity | Validation |
| --- | --- | --- |
| `Source/DafnyCore/AST/Substituter.cs::SubstStmt` | Support resolved nested statement matches at this existing substitution boundary | Tiny reproducer; constructor-only, bound-variable/shadowing and failing-proof controls |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/patterns/nested-statement-substitution.dfy` and its expected output | Reproduce function-body forall proof plus nested constructor statement-match, with a case binder shadowing an enclosing let variable | Actual before/after native proof; reject deliberately invalid proof; no fixture staging/temp/sync tests |
| `Source/DafnyCore.Test/NestedMatchSubstitutionTests.cs` | In-memory resolved AST substitution controls for flattened form, attributes, nested constructor/binder metadata, type substitution and outer-map restoration | Focused native unit test; no file fixture, subprocess, sync or generated output inside the test |
| This plan, `plan/INDEX.md`, `wiki/INDEX.md`, `wiki/nested-match-substitution.md` | Record semantics, verification and limits | Fresh independent review, diff and Markdown-only audits |

## Validation and isolation

Implement in an isolated native worktree under
`/workspace/tmp/native-match-crash-20261021/`. Follow native AGENTS/CLAUDE.md,
Makefile and .editorconfig. Use `dotnet build Source/Dafny.sln`, relevant native
tests, `make format` and `make format-dfy` as applicable; record exact scope and
prerequisites. Keep runtime/build outputs outside plan/wiki. Inspect tests before
extending them, and retain meaningful proof obligations and strict negative
controls. Fresh independent verification must inspect current source and run its
own checks; implementation claims are not verification.

User authorized the compiler repair and the active commit/restart workflow.
Parent owns focused commits/pins, images, cancellation and one paid restart.
Native work must not touch current evaluator inputs or any candidate workspace.

## Results

Baseline isolated `dotnet build Source/Dafny.sln -p:NuGetAudit=false --nologo`
passes with four existing warnings and zero errors. Existing Gradle-cache access
needed the approved escalated execution path. The exact new LIT source reproduces
SIGABRT before the fix using canonical Z3-4.12.1: function-axiom translation
reaches `SubstBlockStmt -> ForallStmt -> StmtExpr -> LetExpr`, matching the weekly
stack. Source includes nested constructors and a shadowed `outer` binder.
No private candidate source or oracle was needed.

Implementation is frozen in the isolated worktree. `SubstStmt` rebuilds nested
matches, substitutes the resolved flattened statement and attributes, clones
constructor-pattern bindings, and restores the complete prior substitution map
after each case. The in-memory regression checks generic type replacement,
shadowed pattern mappings and case-local declarations; the public proof has a
reachable nested constructor branch and an ordinary false-assertion control.

Implementation-side final `dotnet build Source/Dafny.sln -p:NuGetAudit=false
--no-restore --nologo` passes with four existing warnings and zero errors.
Focused Core and LIT checks each pass one case without skips. Direct checks
with canonical Z3-4.16.0, one core, assertion isolation, seed42 and exact symbol
filtering give positive4verified/0errors (exit0) and negative2verified/1error
(ordinary assertion, exit4). These are local native checks, not benchmark scores.

The implementation's broad/scoped formatter attempts did not terminate and were
interrupted without source edits. Fresh independent project-scoped C# format
checks pass (`--verify-no-changes`, zero formatted files) for both changed C#
files. Direct `dotnet Binaries/Dafny.dll format --check` passes for the new Dafny
source. The earlier attempts are not used as successful formatting evidence.

## Fresh independent acceptance and transfer

The fresh reviewer independently inspected all four files and accepted the
frozen `b4f683fd8` delta. From the isolated native root:

- `dotnet build Source/Dafny.sln -p:NuGetAudit=false --nologo`: exit0, zero
  warnings/errors on the cached independent run. Initial sandbox failure was
  cache access; the approved identical execution passed.
- `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore
  --filter FullyQualifiedName=DafnyCore.Test.NestedMatchSubstitutionTests.SubstitutesResolvedNestedStatementMatchWithScopedPatternVariables`:
  one passed, zero skipped. Initial VSTest local-socket denial was an environment
  failure; the same approved command passed.
- `dotnet format whitespace Source/DafnyCore/DafnyCore.csproj --no-restore
  --verify-no-changes --include Source/DafnyCore/AST/Substituter.cs --verbosity
  diagnostic` and the matching test-project/new-test-file command: exit0,
  zero formatted files.
- Direct LIT-equivalent proof commands use canonical
  `/workspace/cosyn/dafny/Binaries/z3/bin/z3-4.16.0` (version4.16.0,
  SHA256 `bf8484ec7c3c76ba5f221245e396748f9632cf6af05d219e10cd669a3913d373`),
  `--cores 1 --isolate-assertions --boogie /randomSeed:42` and exact filters
  `NestedProof.` / `NestedProofRejectsFalse.`: positive4verified/0errors,
  exit0; strict negative2verified/1error, exit4. Negative output matches
  `.dfy.expect` byte for byte. The fresh review did not run the LIT xUnit
  harness because its helper creates an Output directory; the direct native
  equivalent establishes proof/output behavior without that fixture workload.
- `git diff --check` and recursive plan/wiki Markdown-only audit: clean.

Canonical transfer checked the tracked source against committed baseline and
new paths for absence before copying. All four canonical SHA256 values match
the independent review: `Substituter.cs` `fa79dcbf...`, unit `0435ec34...`,
Dafny `454c3ba2...`, expected output `1c198471...`. Raw proof output remains
under `/workspace/tmp/native-match-crash-20261021/`. No benchmark solution,
provider call or evaluator change was used. Durable finding:
[nested statement substitution](../wiki/nested-match-substitution.md).

The user subsequently requested delivery of all latest native changes on
`expecto`; [the delivery plan](2026-10-21-expecto-native-latest.md) records the
same-tree branch migration and the separate combined-tree review. This focused
acceptance does not imply acceptance of other pending compiler changes, runtime
images, live recovery or statistical improvement.
