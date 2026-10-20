# Validate generator-local proof helpers

Status: done

## Objective and acceptance

Document and validate sibling proof declarations authored in `.top-down-pbt/generators/<TargetFullDafnyName>.dfy`. Statements and proofs inside `Generate` may call sibling lemmas and functions from that file. Preparation must retain those declarations and the original target contract; the admitted proof closure must require the actual lemma correctness and transitive function checks. Unsupported/trust-bearing helper bodies and incomplete or failed proof evidence must remain non-certifying. Authored `Generate` requires clauses cannot restrict the generated input proof.

This is repository maintenance. It changes no target specification, benchmark dataset, evaluator or score. No dependencies, paid experiments, runtime compiler/solver tests, or additional helper merge implementation are needed. Existing `ContractRuntimeSourcePreparation.AddHelper` already accepts callable and datatype declarations. Parent-owned promotion plan: [exact generator admission proofs](2026-10-20-pbt-generator-proof-promotion.md).

## Inspected evidence and existing solutions

- Read root/Cosyn instructions and native `AGENTS.md`, `CLAUDE.md`, plan/wiki indexes, `Makefile`, preparation implementation/tests, source snapshot parser, proof/audit code and checker.
- No descendant `AGENTS.md` files govern the changed paths. Source snapshots parse from an in-memory dictionary; preparation slices/merges strings without real file operations.
- `ContractGeneratorProofAudit` rejects authored generator requires and trust attributes. Audited execution scopes discover transitive bodies and require method well-formedness/correctness and function well-formedness checks; the exact embedded RNG is the sole module exception.
- Existing coverage acceptance requires exact expected check coverage, no failures and positive admission implementation evidence. New tests use actual discovered helper checks as controlled fake evidence rather than claiming solver validation.

## Change table and ownership

All changes belong to native Dafny; affected layers are source preparation contracts, proof-closure checks and developer guidance. Root/Cosyn prompt and README changes are parent-owned.

| Exact file | Change, purpose and unmet behavior without it | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs` | Add isolated bounded in-memory preparation/AST/closure/audit/coverage tests for sibling lemmas and transitive functions, preserving the original goal requirement. Existing tests do not tie authored sibling declarations to required helper proof checks. | Focused xUnit filter; source tracing and format check |
| `wiki/pbt-generator-proof-helpers.md` | Explain exact generator file and supported authored proof placement, checked helper closure and trust restrictions. | Review against current source and test evidence |
| `plan/2026-10-20-pbt-generator-proof-helpers.md` | Record scope, validation and handoff. Parent registers plan/wiki indexes to avoid concurrent edits. | Diff and Markdown-only audit |

## Compatibility, risks and approvals

No production behavior change is planned: helper merging already exists. Parsing/resolution and scope checks establish source/AST behavior, not proof validity. Actual true/false helper proof probes remain parent-owned manual tiny public runs in `tmux`. Keep this test/documentation change separate from the proof engine promotion. No new approvals are required.

## Validation plan and I/O trace

From `/workspace/tmp/pbt-main-hardening-20261020/native`, after coordinating shared build directories with the proof implementation agent:

1. Manually build the affected existing test project using `dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -m:1`; installed .NET and existing package cache are prerequisites. This build is outside test execution and creates normal bounded build outputs.
2. Run `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractGeneratorProofHelperTests -m:1`; expect all new focused cases to pass. Tests instantiate options with null writers, parse/resolve bounded strings through snapshot filesystem, read one embedded runtime resource, inspect ASTs, discover scopes and use fake sets. No fixture instances are used; the assembly attribute disables test parallelism. No tests call native proof/compiler, processes, solver version probes, durable writes or cleanup.
3. Run targeted `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs --verify-no-changes`; expect formatting clean. Coordinate this solution read with shared builds.
4. Review own file diffs and recursively inspect plan/wiki for non-Markdown files; preserve pre-existing violations.

## Execution record and handoff

Implemented the dedicated nine-case helper test class and [generator-local helper guidance](../wiki/pbt-generator-proof-helpers.md), with no production changes. Native base is `10dca3ba4a2909c11299176440401fc31413b53d` plus concurrent parent-authorized proof promotion.

- Installed SDK: `dotnet --version` reports `8.0.131`.
- `git diff --check` passed in the isolated native worktree (including concurrent promotion changes).
- Recursively inspected native `plan/` and `wiki/`: no non-Markdown files present.
- Traced `ContractSourceSnapshot.ParseAsync` through dictionary-backed `SnapshotFileSystem`, `ContractRuntimeLibrary.ReadWithoutTerminator` through one assembly resource, preparation through string-only edits, and scope discovery/audit through AST traversal and in-memory fingerprints. The dedicated class inherits no fixture, uses no `Setup` instance and invokes no native solver/compiler.
- Delegated local build, executed by the proof promotion agent from the isolated native worktree: `dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -m:1 --verbosity minimal` succeeded in 44.95 seconds with four untouched-source warnings. `/workspace/tmp/pbt-main-hardening-20261020/native-testgen-build.log` includes an initial Gradle read-only-cache failure and the final successful build; the agent reused the unchanged canonical Java runtime jar before retrying. This was manual build preparation, outside test execution.
- Delegated pure test run: `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractRuntimeGeneratorProofTests|FullyQualifiedName~ContractGeneratorProofHelperTests' -m:1 --logger 'console;verbosity=minimal'` passed 121/121, zero skipped, in one second. All nine helper cases passed. Output: `/workspace/tmp/pbt-main-hardening-20261020/native-proof-unit.log`. This is shared implementation-context local validation, not independent verification or an actual Dafny proof result.
- Coordinated targeted formatter verification passed (exit0; workspace-load warning retained in the proof promotion log).

Parent completed fresh independent verification and actual manual proof acceptance, as recorded below. Plan/wiki index entries are registered; this logical change remains separate from engine promotion.

## Final independent and native acceptance

Nine helper controls passed within the independently repeated 140-case native selection. Actual public sibling lemma + transitive function proof certifies 10/10; a false helper body fails and keeps entry checks. Fresh independent quantified ghost-predicate/lemma controls certify 9/9 while target assertion, loop invariant, type and postcondition checks remain evaluated. Canonical Cosyn/native end-to-end smoke certifies 10/10 and finds the deliberately wrong target postcondition. Evidence: `/workspace/tmp/experiment/pbt-main-hardening-20261020/r02/`, `r02/independent/`, `canonical-smoke/`, and `/workspace/tmp/pbt-main-hardening-20261020/verify-proof-main.md`. Scoped formatter and Markdown audits pass. No helper insertion production change was necessary; this item closes a regression-coverage and agent-guidance gap. Parent owns the separate requested item-3 commit and main integration.
