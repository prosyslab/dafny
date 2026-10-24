# Commit the reviewed native PBT repairs

Status: done
Date: 2026-10-25
Owner: native Dafny repository
Related: [Cosyn delivery](../../plan/2026-10-25-pbt-reviewed-main-delivery.md), [native reconciliation](2026-10-24-pbt-agent-experience-delivery.md)

## Objective and acceptance

Land useful already implemented PBT fixes in dependency-closed `[PBT]` commits
on the existing expecto lineage, then pin them through Cosyn/integration main.
Do not merge upstream native main, alter generated compiler files, modify
benchmark contracts/scoring, resume paid experiments or reset unrelated work.
Acceptance requires independently reviewed source/test closure, truthful local
validation evidence and a reviewed staged diff for each logical unit.

## Scope and evidence

The exact 23 production and 13 test/project leaves listed in the earlier native
reconciliation plan are the candidate scope. The bounded existential reduction
changes in PartialEvaluatorEngine, PartialEvaluatorVisitor and QuantifierBounds
belong only if independent review confirms they are the PBT witness dependency.
Preserve the existing mixed iterator behavior in campaign/transformer files.
Test asset guards retain default behavior and avoid recursive asset copies.
Read current code rather than treating historical plans as proof.

| Files or symbols | Purpose | Validation |
| --- | --- | --- |
| DefinitionAnalysis*, Method.cs, bounded witness rewriters and ContractWitnessReductionTests.cs | Stable declaration/proof identities and finite contract witnesses. | Exact source parity to accepted detached builds and memory regressions. |
| ContractScreen*; ContractSolver/QueryBuilder/SpecificationChecker/InitialTypeProof; native screen tests | Body-independent inspection/screening with honest result and unsafe-option rejection. | Matching compiled inputs, selected fake-backend/schema tests and actual controlled image receipts. |
| ContractRuntime* selected preparation/transformer/heap; ContractCallableSelector; ContractGeneratorProof; TestContractsCommand; runtime/draft tests | Selected helper closure, original proof scope, output capture and supervised verifier-seed forwarding. | Matching compiled source identities, earlier memory/build evidence and fresh image worker/proof controls. |
| Three affected test csproj files | Explicit SkipFocusedTestAssets opt-out retains defaults while bounding copies. | Source review; no writes to existing shared output dependencies. |
| This plan; plan/INDEX.md; wiki/pbt-main-delivery.md; wiki/INDEX.md | Concise accepted source behavior, exact evidence and limits. | Markdown/link/staged diff review. |

Canonical N build preparation previously stopped on a regular existing
Boogie.AbstractInterpretation.dll with two hard links. No canonical build/test
was run; do not overwrite shared dependencies, relax write guards or describe
detached K checks as an N execution. For this source delivery the acceptance
scope is amended to permit exact source/config parity to independently accepted
detached builds and controlled-image evidence, with any N-specific difference
reviewed and disclosed. Run additional safe native checks only when they are
needed and their output boundaries are known. No whole-runtime hashing or bulk
test workload is authorized.

## Commit and close

Independent reviewer proposes exact path/hunk grouping and verifies current
parity before root stages. Keep useful inseparable native changes together;
split independent seed/closure/screen changes when their dependency graphs allow.
Inspect staged diffs, use English `[PBT]` subjects and short problem/change
bodies, and preserve all other dirty files/records. Root commits the child
gitlink after native commits exist. No remote push or new experiment is needed.
Use /workspace/tmp/pbt-reviewed-main-delivery-20261025/ for finite artifacts;
plan/wiki remain Markdown only. Record final commit IDs and remaining validation
limits below; no source delivery implies improved csplit success.

## Progress

Independent current-tree native dependency/evidence review accepted the source closure.

Independent review accepted the exact source closure and 35/36 N/K leaf parity;
the only difference is the default-on Driver.Test asset guard. New unused
ContractRuntimePreparationModels.cs and ContractRuntimeFrontendModelsTests.cs
remain unstaged. The witness rewriter edits are required by checked screen
queries and belong in that unit. No generated/package/benchmark files change.

Stage two units in this order:

1. `[PBT] preserve selected runtime execution`: Driver ContractRuntimeCampaignRunner;
   Driver.Test ContractRuntimeDraftDiscoveryTests, ContractRuntimeLibraryCommandTests
   and project guard; TG ContractCallableSelector, ContractGeneratorProof,
   ContractRuntimeObligationTransformer, ContractRuntimeSourcePreparation and
   ContractRuntimeSelectedDraftPreparation; TG.Test ContractRuntimeObligationTests,
   ContractRuntimeSelectedDraftPreparationTests, ContractRuntimeUnreachableBodyTests
   and project guard; only verifier-seed option/supervision from TestContractsCommand.
   Preserve whole mixed iterator/selected execution files. The index-only CLI
   projection removes every screen declaration/dispatch/method while preserving
   seed validation, option binding and supervised argument forwarding. It has no
   dependency on new Method/DefinitionAnalysis screen symbols.
2. `[PBT] add checked native contract screening`: Method, DefinitionAnalysis
   and its ProofInputs/SemanticFacts partials; PartialEvaluatorEngine,
   PartialEvaluatorVisitor and QuantifierBounds; Core.Test witness tests/project
   guard; remaining CLI screen hunks; TG ContractInitialTypeProof,
   ContractQueryBuilder, ContractRuntimeHeapChecking, ContractSolver,
   ContractSpecificationChecker and three ContractScreen files; TG.Test
   ContractQueryTests, ContractScreenModelTests and ContractScreenServiceTests.
   Add the concise delivery wiki and index after recording actual source limits.

Working files remain intact during index-only CLI/index projection. Historical
detached evidence covers exact selected 26/26, related 27/27, Core 209/209 and
screen 36/36 source checks, plus the actual compiled seed forwarding. These are
matching-source evidence, not executed canonical N checks. New owner records
supersede broad historical source-only handoff wording for this delivery only.

Runtime unit committed as `6f24e6046` after independent staged acceptance of
its exact 16 paths and source closure; git diff --cached --check passed. The screen
unit is committed separately with the concise wiki. Its source has unchanged exact
matching-build evidence; canonical N builds remain explicitly unrun.

The two source units have been committed after independent index review. The
source-delivery acceptance scope is complete; canonical build execution remains
outside this completed scope and is explicitly unrun. No paid run was resumed.
