# Checkpoint completed native PBT work on expecto

Status: in-progress
Date: 2026-10-12
Owner: Cosyn embedded Dafny implementation; parent gitlink belongs to Cosyn.

## Objective, authorization and acceptance

The user explicitly requests committing completed Cosyn Dafny changes into
expecto before proceeding. Earlier authorization requests Cosyn/main integration
by fast-forward without a merge commit. This is repository maintenance; the
broader improvement goal remains paused. This request supersedes the earlier
full-census gate only for the local checkpoint, without claiming final native
acceptance, improved benchmark scores, or completion of broader native plans.

Acceptance: commit exactly the 39 Source paths below, matching the tested v33
inventory, plus this new owner plan. Fast-forward primary expecto from
c6e96a59f679bb71e565a27ec1bf93ac68f0803d. Preserve pre-existing native documents,
all unrelated work, and dafnyutils native HEAD/index/files. Leave the two later
v34 test additions unchanged and uncommitted in the private worktree. Advance
only the Cosyn parent gitlink, then fast-forward main with exact preservation.
No merge commit, reset, stash, cleanup, remote push, dependency, paid provider,
benchmark/specification/oracle/scoring change, or benchmark run is authorized here.

## Inspected evidence and limitations

Primary expecto and private native HEAD are both c6e96a59f. Primary Source is
clean. Exclude pre-existing primary plan/INDEX.md and untracked
plan/2026-10-11-pbt-ten-of-fifteen.md, and private shared plan/wiki records.
Dafnyutils has separate local Git metadata for the same upstream and six dirty
Source paths, with no checkpoint overlap. Preserve them exactly.

Supported make build-dafny from the isolated Cosyn root passed in
53.69047146476805 seconds, exit0, provider none, Source changes empty. Receipt:
/workspace/tmp/pbt-remaining-coverage/build-v33-recursive-cache-controls/receipt.json
SHA256 192e7fc0cc17ce1d2ced57e29f1d363a5f33a1bb3c0051113658baba4da6be2a.
It inventories 5976 Source files and 682 packaged binaries. Stage the two witness
test files from their tested v33 preimages in
/workspace/tmp/pbt-remaining-coverage/v34-symbolic-branch-ownership/preimages/,
without altering current working files. The complete staged Source tree must
match the receipt's Source membership and SHA256 bytes.

The existing v33 nine gates passed 1774 executions, zero failures or skips;
counts overlap and are not unique tests. A later plan/wiki exposure invalidated
procedural isolation, so these technical results do not establish final isolated
acceptance. A separate clean review found a remaining symbolic short-circuit/ITE
problem: a simplified child AST can remain after its proof artifacts are rolled
back. This checkpoint does not repair that problem. Newly added v34 reproduction
tests are unrun and excluded. Current full-15 census and endpoint replays remain
unrun for v33. Broader plans remain in progress. No new durable finding: this
plan records existing provenance and unresolved work; no new wiki is needed.

## Exact change table

| Path / operation | How and why; otherwise unmet | Validation |
| --- | --- | --- |
| `Source/DafnyCore.Test/ContractExpressionReducerTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore.Test/ContractHeapReductionTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore.Test/ContractWitnessReductionTests.cs` | Stage tested v33 preimage; preserve later working tests; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/AST/FreeVariablesUtil.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/AST/Grammar/Printer/Printer.Expression.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/AST/Grammar/Printer/Printer.Statement.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/AST/Grammar/Printer/Printer.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/ContractTesting/ContractHeapReductionContext.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/ContractTesting/ContractReductionTraversal.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyCore/Rewriters/QuantifierBounds.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/AssertionTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/CampaignHarness.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/ClauseDependenciesTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/Fixtures/Assertions.dfy` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/Fixtures/LemmaGoal.dfy` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/ContractRuntime/LemmaGoalTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver.Test/Setup.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractClosedClauseTypeTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractHeapReductionTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractLemmaGoalTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractPhaseTimingTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractQueryTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration.Test/ContractWitnessQueryTests.cs` | Stage tested v33 preimage; preserve later working tests; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryBuilder.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryHeapReduction.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeClauseDependencies.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs` | Checkpoint completed native implementation or regression coverage; otherwise absent from expecto | Exact tested receipt SHA256 and prior native gates |
| This new plan | Record requested checkpoint and remaining limitations | Exact staged scope and Markdown hygiene |
| Private plan/INDEX.md | Register this plan only, leave unstaged | Preserve existing bytes |
| Primary expecto | git merge --ff-only the native checkpoint | One-parent history, full Source inventory and dirty-file guards |
| Cosyn dafny gitlink | Separate one-path commit referencing native checkpoint | Exact SHA, ancestry, unrelated file preservation |
| Cosyn main-fast-forward owner plan | Record explicitly authorized checkpoint scope; leave unstaged | Selective owned document edit |

## Validation and implementation sequence

Prerequisites: existing .NET supported-build and regression artifacts. No new
build/test run is necessary for byte-identical checkpoint Source. Snapshot heads,
indexes, dirty hashes/modes and private Source. Inspect exact 39 Source paths.
Stage only them and this new plan, with exact v33 test preimages in the index.
Verify all 5976 staged Source bytes against the supported receipt. Use ordinary
Git hooks, record commit parent/scope, and repeat actual committed Source check.
Recheck primary expecto tip and dirty guards; git merge --ff-only <checkpoint>.
Preserve private later tests, all excluded records, and dafnyutils unchanged.
For parent integration from the main-based worktree, recheck current main and
stage only the native gitlink via explicit cacheinfo. Commit and fast-forward
primary main. Record final SHAs and preservation. Recursively inspect native and
Cosyn plan/wiki trees for non-Markdown files; preserve any pre-existing violations.
Independent current-state Git/scope review does not imply semantic acceptance.
Artifacts: /workspace/tmp/pbt-main-ff-integration/native-expecto-checkpoint/.

Prior actual native gate commands (native cwd, no build/restore, raw TRX retained):

```text
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractHeapReductionTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate0 -m:1
```

```text
dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractWitnessReductionTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate1 -m:1
```

```text
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractWitnessQueryTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate2 -m:1
```

```text
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractClosedClauseTypeTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate3 -m:1
```

```text
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractQueryTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate4 -m:1
```

```text
dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~Contract' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate5 -m:1
```

```text
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~Contract' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate6 -m:1
```

```text
DAFNY_CONTRACT_TEST_KEEP_ARTIFACTS=1 dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~DafnyDriver.Test.ContractRuntime&FullyQualifiedName!~DafnyDriver.Test.ContractRuntime.NonterminationTests' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate7 -m:1
```

```text
dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~PartialEvaluatorTest|FullyQualifiedName~UnrollBoundedQuantifiersTest' --logger 'trx;LogFileName=results.trx' --results-directory /workspace/tmp/pbt-remaining-coverage/subset-conversion-independent-verification/v33-attempt-01/gate8 -m:1
```

## Outcome

Pending scoped commit and fast-forward.

## Git representation verification refinement

The first raw staged-blob SHA256 comparison failed on 47 unchanged baseline
paths while all Source membership matched and all 39 owned Source changes
matched exactly. Existing attributes check out 45 baseline files as CRLF, and
2 baseline paths are symlinks whose receipt hashes dereferenced file contents.
A second CRLF-only check correctly rejected those symlink paths; neither failed
check changed Source or selected unrelated paths. Preserve these failed checks.
Final validation requires every represented baseline path outside owned scope,
unchanged from base HEAD and byte-identical in the original working snapshot.
For CRLF files, require eol=crlf, clean-filter canonical blob identity and exact
checkout-filter bytes matching the receipt. For symlinks, require mode120000,
exact link target bytes, unchanged base blob, and dereferenced contents matching
the receipt and the target's committed Source content. Never normalize or stage
unrelated files. Retain exact representation path evidence in the receipt.
