# Deliver the latest compiler changes on expecto

Status: done (latest compiler source delivered on expecto)
Date: 2026-10-21
Parent: [compiler repair and weekly restart](../../../plan/2026-10-21-native-match-crash-weekly-restart.md).

## Objective and observable acceptance

The user explicitly requested that compiler changes be committed and the latest
changes moved onto `expecto`. Preserve existing source and historical records.
Fast-forward local `expecto` from `10dca3ba4` to current `main` at `b4f683fd8`,
then switch the canonical native checkout to it with identical working-tree
bytes. Retain the five existing commits without cherry-pick duplication or
history rewriting. Leave `main` unchanged. Inspect and independently verify all
pending native compiler changes before focused commits on `expecto`.

The nested-match fix has already passed a fresh independent clean-base review.
Its exact four product/test files were copied to the canonical native tree only
after proving the tracked source matched baseline and the new paths were absent.
The combined latest tree requires a separate fresh review before delivery.
Do not claim repeated operational stability, private-worker causation or weekly
performance from local source/tests. No push, dependency change, benchmark
specification/evaluator/compiler-policy change or extra paid run is requested.

## Inspected evidence and changes

This is repository maintenance. Root, Cosyn and native AGENTS/CLAUDE instructions
apply; no narrower plan/wiki instructions or template exist. Current native
`expecto` is an ancestor of `main`; existing worktrees do not use `expecto`.
The five latest committed PBT changes are reachable from `main` and will remain
reachable from `expecto`. Pending PBT source and historical records were already
transferred by the [native integration plan](2026-10-21-integrate-reviewed-pbt-native.md).
Its historical imported plans/wiki remain unchanged except additive index entries.

| Exact paths / symbols | Change and necessity | Validation |
| --- | --- | --- |
| `refs/heads/expecto`, canonical native checkout | Fast-forward to `main`, switch with unchanged source; retain all committed work on requested branch | Ancestry, branch/worktree inventory, before/after pending source hashes; no reset/rebase |
| `Source/DafnyCore/AST/Substituter.cs`, `Source/DafnyCore.Test/NestedMatchSubstitutionTests.cs`, `Source/IntegrationTests/TestFiles/LitTests/LitTest/patterns/nested-statement-substitution.dfy` and `.dfy.expect` | Commit the independently accepted compiler crash fix | Owner [focused plan](2026-10-21-nested-match-substitution.md), combined build and exact positive/negative proof |
| `Source/DafnyCore/AST/Expressions/Variables/NonglobalVariable.cs`, `Source/DafnyCore/AST/Statements/Assignment/LocalVariable.cs`, `Source/DafnyCore/AST/TypeDeclarations/Declaration.cs`, `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`, `Source/DafnyCore/Verifier/BoogieGenerator.cs`, `Source/DafnyCore/Verifier/FreshIdGenerator.cs`, `Source/DafnyCore.Test/DafnyCore.Test.csproj`, `Source/DafnyCore.Test/DefinitionProofInputsTests.cs`, `Source/DafnyCore.Test/ProofInputRepeatabilityTests.cs` | Commit existing repeatable verification names and bounded proof-input tests without modifying their reviewed bytes | Full build; inspected in-memory Core selections, exact hashes/CRLF preservation |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`, `Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs` | Commit existing pre-artifact request validation and proof result reporting | Inspected pure/memory Driver selection, full build |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs`, `ContractGeneratorProofAudit.cs`, `ContractGeneratorVerification.cs`, `ContractRuntimeObligationTransformer.cs`, `ContractRuntimeSourcePreparation.cs`, `ContractSpecificationChecker.cs` | Commit current authored-body proof, complete verifier-task accounting, preparation and audited helper handling as a coherent boundary | Independent source/contract review, build; inspected bounded TestGeneration selections |
| `Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs`, `ContractGeneratorProofTests.cs`, `ContractGeneratorVerificationTests.cs`, `ContractRuntimeSourcePreparationTests.cs`, `ContractRuntimeUnreachableBodyTests.cs` | Commit current regression/adaptation tests with implementation | Trace helpers through teardown; no temp-directory, runtime build, toolchain hash or sync workloads |
| `plan/2026-10-21-integrate-reviewed-pbt-native.md`, `2026-10-21-pbt-authored-generator-proofs.md`, `2026-10-21-pbt-preparation-preambles.md`, `2026-10-21-pbt-unreachable-bodyless.md`, `2026-10-21-pbt-worker-failure.md`, `2026-10-21-repeatable-proof-inputs.md`, existing modified `wiki/pbt-generator-proof-helpers.md`, `wiki/pbt-generator-proof-integrity.md`, new `wiki/pbt-unreachable-bodyless.md`, plan/wiki indexes and this plan | Commit source-associated historical records, preserving their explicit incomplete operational claims; add current delivery provenance | Exact inventory/diff, independent review, Markdown-only audit; no historical status relabeling |

All code belongs to native Dafny. Parent Cosyn only updates its native gitlink
and records; root owns image composition and the already authorized one restart.
Python PBT work remains outside this native delivery. Benchmark-owned Dafny stays
at its previous evaluator-policy pin; changing it is outside this branch repair.

## Actual validation and prerequisites

From `/workspace/cosyn/dafny`, fresh independent review runs supported
`dotnet build Source/Dafny.sln -p:NuGetAudit=false --nologo`, affected in-memory
`dotnet test <project> --no-build --no-restore --filter <inspected classes>`, and
scoped `dotnet format whitespace <project> --no-restore --verify-no-changes
--include <changed C# files>`. Existing Gradle/NuGet caches and VSTest IPC may
use the approved execution path; do not add/download dependencies. Tests must
not stage source/build trees or create temporary directories. Treat builds as
separate maintenance operations rather than test fixture activity.

Run direct positive and strict-negative nested-match verification with existing
Z3-4.16.0, one core, isolated assertions, seed42 and exact declaration filters.
Check Dafny formatting and expected negative output. The LIT harness creates an
Output directory and is not repeated; use its direct command equivalent.
Record exact commands, tested hashes, warnings and environment failures. Review
staged diffs against logical groups and preserve all non-native work. Inspect
plan/wiki recursively for non-Markdown files. No image or paid call is validation.

## Progress and remaining work

Branch migration completed without history rewriting: `expecto` fast-forwarded
over the five existing commits, `main` remains `b4f683fd8`, and all41pending
file hashes matched before/after switching. Inventory:
`/workspace/tmp/native-match-crash-20261021/expecto-before.json`.
The focused match repair is commit `edc216e65` on `expecto`.

Fresh independent combined-tree review accepts the frozen compiler at
`edc216e6502ca05939863f8df729fe2367a65a0a` plus the remaining PBT changes.
Evidence: `/workspace/tmp/native-match-crash-20261021/expecto-latest-independent-review.json`,
SHA256 `3df039776d32fa185569c75735860d218f61d35c5f0fdce6af6a63b736ed4069`.
All reviewed source/LIT hashes are stable across the branch/commit changes.

From the canonical native root, the independent reviewer ran:

- `dotnet build Source/Dafny.sln -p:NuGetAudit=false --no-restore --nologo
  -m:1 /nr:false`: success, four existing warnings, zero errors.
- Core `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter
  'FullyQualifiedName~ProofInputRepeatabilityTests|FullyQualifiedName~DefinitionProofInputsTests|FullyQualifiedName~NestedMatchSubstitutionTests' -m:1`:
  34passed, zero skipped. First sandbox invocation failed before tests on
  VSTest socket access; identical approved invocation passed.
- Driver `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter
  FullyQualifiedName~GeneratorProofResultTests -m:1`:9passed, zero skipped.
- TestGeneration `dotnet test Source/DafnyTestGeneration.Test --no-build
  --no-restore --filter <seven inspected memory classes> -m:1`:152passed,
  zero skipped. Exact class filters are in the evidence JSON and include
  generator proof/helper/verification, source preparation, unreachable body,
  obligation and generator signature controls. Helpers were traced through
  teardown; no temporary directories, toolchain-tree hashing or native build
  occurs inside these tests.
- `dotnet format whitespace . --folder --verify-no-changes --include
  <23 changed C# files>`:success; `./Scripts/dafny format --check
  Source/IntegrationTests/TestFiles/LitTests/LitTest/patterns/nested-statement-substitution.dfy`:
  correctly formatted.
- Direct `./Scripts/dafny verify --solver-path
  /workspace/tmp/native-match-crash-20261021/runtime/dafnyutils/dafny/Binaries/z3/bin/z3-4.16.0
  --cores 1 --isolate-assertions --boogie /randomSeed:42 --filter-symbol
  NestedProof. <new regression>`:4verified/0errors, exit0. Same policy,
  `--filter-symbol NestedProofRejectsFalse.` and `--show-snippets false`:
  2verified/1expected assertion error, exit4; output matches `.expect`.
- Diff and Markdown-only/symlink audits:clean. No image, provider or benchmark
  run was part of these native checks.

When historical untracked records were staged for the generator-proof commit,
full staged `git diff --check` additionally detected an inherited blank line at
EOF in `plan/2026-10-21-pbt-worker-failure.md:331`. The ordinary unstaged check
does not include untracked files, so the earlier clean result did not cover
this record. Preserve its previously reviewed raw bytes rather than rewrite the
historical plan: SHA256
`5c2b14daabedd4ce8690a5d4613fc674cad997c3a5b02e97048209a1c82a21d8`.
All other staged paths pass the whitespace check. This documentation-only
inherited exception is explicit and does not affect source/build/test acceptance.

Delivered source commits on `expecto`:

| Commit | Change |
| --- | --- |
| `edc216e65` | Nested statement-match substitution and strict regression controls |
| `7910ad1a8` | Repeatable translation names and proof-input analysis |
| `fda6af291` | Authored generator proof boundary, complete task accounting and preparation |
| `12485e5bd` | Unreachable bodyless diagnostic declarations and constructor handling |

The transformer certificate-match hunk was staged separately from body-erasure
changes; its intermediate reviewed-transfer SHA256 is
`77d2eb68f4c153664bdfafaaa86d55d91b5129395a0792199d934e9eff581547`.
Imported historical records and their incomplete operational claims are
preserved. A record-only closure adds this plan and reconciles index ordering.
The concurrently created `plan/2026-10-21-pbt-isolated-overlay-build.md` and
its index entry belong to another active task and are excluded.

All26reviewed source/LIT hashes still match after the source commits. Their
committed checkout-filtered bytes also match the review; no product source or test remains
uncommitted. Existing `main` remains at `b4f683fd8`; only `expecto` advanced.
The remaining concurrent operational plan/index change is preserved in the
canonical working tree, excluded from runtime snapshots. No remote push occurred.

The existing `.gitattributes` sets `*.csproj` to `text eol=crlf`; Git stores a
normalized LF blob and recreates the reviewed CRLF working bytes at checkout.
`git cat-file --filters HEAD:Source/DafnyCore.Test/DafnyCore.Test.csproj`
matches reviewed SHA256 `c5df8e8d...` exactly. No attributes or raw working bytes
were changed to force blob identity.

Parent then pins the final native revision, builds once through the standard
launch path and observes the authorized replacement weekly run. Native local
acceptance does not establish generated-runtime recovery, provider behavior,
weekly stability, efficacy or performance.
