# Commit existing native changes in logical units

Status: done
Date: 2026-10-19

## Objective and acceptance

This is repository maintenance, not an evaluated run. The user requested local commits for existing working-tree changes. Preserve each repository's distinct starting HEAD and behavior, stage exact paths or purpose-specific hunks, inspect every staged diff, and leave generated or unfinished historical records untouched. Complete commits and record validation limitations; no push, provider call, dependency addition, reset, cleanup, or new feature is authorized.

## Evidence, ownership and compatibility

Read applicable root/owner AGENTS.md, native CLAUDE.md, Makefile, current status/diffs, and plan/wiki indexes and relevant historical records. Existing native helpers and regression tests define the changes; no replacement implementation is needed. Native compiler/analysis/reporting changes belong to this repository. Benchmark contracts, datasets, scoring and evaluator behavior are outside this maintenance task. Historical records may contain earlier validation; they are not fresh acceptance. Different embedded Dafny worktrees must never be synchronized implicitly.

## Change table and commit classification

| Exact files or symbols | Change and purpose | Unmet without change | Validation |
| --- | --- | --- | --- |
| `Source/DafnyCore/Triggers/ComprehensionTriggerGenerator.cs`, `Source/DafnyCore.Test/TriggerBoundVariableScopeTests.cs`, `Source/IntegrationTests/TestFiles/LitTests/LitTest/triggers/split-matchingloop-bound-variable-scope.dfy{,.expect}`, corresponding 2026-10-14 trigger plan/wiki | Commit split-binder preservation as its own fix | Native transformation remains uncommitted | staged diff, whitespace, safe cached in-memory tests if available |
| `Source/DafnyCore/Triggers/TriggersCollector.cs`, `Source/DafnyCore/AssemblyInfo.cs`, `Source/DafnyCore.Test/MatchTriggerVariableScopeTests.cs`, corresponding 2026-10-16 match plan/wiki | Commit match-local trigger filtering separately | Independent match-scope fix remains mixed | staged diff and scoped format |
| `Source/DafnyDriver/{CliCompilation.cs,DafnyNewCli.cs,Legacy/DafnyBackwardsCompatibleCli.cs,Commands/MeasureComplexityCommand.cs}`, `Source/DafnyDriver.Test/InternalErrorExitTests.cs`, corresponding final internal-exit records | Stage internal-error-only hunks before reporting cleanup | Exit semantics remain mixed with reporting | staged diff; run only in-memory cached cases |
| `Source/DafnyCore/{DefinitionAnalysis.cs,DefinitionAnalysis.ProofInputs.cs}`, `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs`, `Source/DafnyCore.Test/DefinitionProofInputsTests.cs`, existing `Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs` where present, final proof-input plans/wiki | Commit proof projection and its owner-specific current tests | Analysis extension remains uncommitted | staged diff, scoped format; avoid file-producing command tests |
| `Source/DafnyCore/Options/{BoogieOptionBag.cs,CommonOptionBag.cs}`, `Source/DafnyDriver/{CSVTestLogger.cs,CliCompilation.cs,JsonVerificationLogger.cs,TextVerificationLogger.cs,VerificationResultLogger.cs,Commands/MeasureComplexityCommand.cs,Commands/VerifyCommand.cs}`, `Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs`, existing changed CLI/logger/CoinductiveProofs/SubsetTypes/SchorrWaite LIT fixtures and expectations, existing changed `docs/VerificationOptimization/VerificationOptimization.md`, final reporting plan/wiki | Commit resource-statistic reporting removal, preserving internal-error hunks already committed | Reporting changes remain mixed with compiler fixes | staged diff, whitespace, safe cached logger case |
| `Source/DafnyCore/DefinitionAnalysis.BodyVisibility.cs`, remaining `DefinitionAnalysis.cs` hunks, `Source/DafnyCore.Test/DefinitionBodyVisibilityTests.cs`, 2026-10-19 visibility plan/wiki | Commit resolved function-body metadata separately | Visibility API remains mixed with projection | staged diff, scoped format |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`, `Source/DafnyTestGeneration/ContractTesting/{ContractInitialTypeProof.cs,ContractRuntimeHeapChecking.cs,ContractRuntimeModels.cs,ContractSourceSnapshot.cs,ContractSpecificationChecker.cs}`, `Source/DafnyTestGeneration.Test/ContractTrustedSourcesTests.cs`, 2026-10-19 trust plan/wiki | Commit exact trusted-source binding separately | PBT trust changes remain uncommitted | staged diff and scoped format; no native campaign |
| `plan/2026-10-19-commit-native-working-trees.md`, `plan/INDEX.md`, `wiki/INDEX.md` | Record this maintenance classification and final results; preserve unfinished historical entries in working tree | No auditable handoff | Markdown-only recursive audit and link checks |
| `Source/DafnyDriver.Test/InternalErrorExitTests.cs`, this plan, existing internal-exit wiki where present | Remove the file-producing `CandidateOutcomesKeepTheirExitCodes` theory and its exclusive code after fresh review; retain in-memory exit controls | Committed development test violates temporary-directory policy | static transitive-I/O review, scoped whitespace check; no execution of removed cases |

Existing Markdown trailing whitespace found by staged `git diff --check` will be removed only from records included in this task, without changing their content or status. This is necessary for clean commit hygiene.


## Validation and risk scope

From this repository run `git diff --check` and `git diff --cached --check`, inspect `git diff --cached`, inspect staged path lists and `git status --short`; expect no whitespace errors or unintended paths. Run a local Python Markdown-link existence audit for staged owner records and recursively inspect every owner `plan/`/`wiki/` tree for non-Markdown files. Native C# formatting uses `dotnet format whitespace . --folder --verify-no-changes --include <changed C# paths>`; it checks only and does not rewrite source. If existing binaries are available, run `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~TriggerBoundVariableScopeTests|FullyQualifiedName~MatchTriggerVariableScopeTests|FullyQualifiedName~DefinitionProofInputsTests|FullyQualifiedName~DefinitionBodyVisibilityTests'` and `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~JsonVerificationLoggerTests|FullyQualifiedName~HandlerExceptionHasDistinctExitCode|FullyQualifiedName~InvalidCommandLineKeepsPreprocessingExitCode'`. These cached checks are explicitly not a fresh-source build or proof claim. Inspect test helper paths first and exclude file-producing/native campaign cases. Record unavailable binaries or socket restrictions as limits. No build, solver/LIT run, Python owner suite for documentation-only changes, image, paid run, or network is needed for this commit-only task. Existing historical in-progress plans and their index entries remain unstaged per preserved user scope.

## Progress and handoff

Starting status inspected. No durable findings: this work classifies and records existing changes without adding behavior or proving new compiler facts. Existing topic wiki pages remain the authoritative historical records. Parent coordinates fresh independent review after commits. No required approval remains for local commits.

## Results — 2026-10-19

Started at `dce5a96612b6516c5b180bb215d6eb3e3b430d5a`. Purpose commits: split binders `986de737e`, match-local candidates `c13436424`, internal exits `6c0098ff5`, proof-input projection `496b5cda5`, reporting schema `fae1e6e4a`, resolved body visibility `04cec7df9`, trusted source identity `93aa2536f`. Source files were preserved exactly; only trailing whitespace and surplus terminal blank lines in included historical Markdown were normalized. Commit staging used explicit paths and purpose-specific cached patches for shared files, with staged whitespace and diff review before each commit. Initial restricted Git staging could not write shared metadata; the approved elevated local Git path succeeded.

.NET SDK `8.0.131`; scoped folder whitespace verification passed. Cached `--no-build --no-restore -m:1` Core filter passed36/36 and Driver filter passed3/3, no skips. The Core cache lacks `DefinitionBodyVisibilityTests`; therefore these are cached-artifact smoke checks and do not certify the current source or new visibility/trust code. No native build, solver/LIT test, runtime campaign, image or paid execution was performed in this commit-only maintenance scope. Historical test/build claims remain historical. Parent schedules a fresh independent review.

`git diff --check` and every staged check passed after Markdown hygiene fixes. Owner plan/wiki recursive non-Markdown audit found none. Local Markdown references were checked for existence; excluded unfinished history remains locally available. The unfinished `plan/2026-10-15-json-verification-resource-overflow.md` and its index entry remain unstaged. The concluding documentation commit includes completed indexes and this record. No durable findings beyond existing owner wiki topics. No process remains running; scratch helper is `/workspace/tmp/native-commit-cleanup/stage_group.py`. Next action is parent review and the Cosyn parent gitlink update; no push is authorized.

## Fresh-review correction — 2026-10-19

Parent fresh review identified a newly committed theory that creates GUID directories and runs real verification. It was not executed in this maintenance task. Remove that development workload rather than retaining it behind a filter or marker. Reinspect every remaining newly committed test/helper path for filesystem and native-tool boundaries; no replacement test or benchmark contract change is planned.

Removed all8 `CandidateOutcomesKeepTheirExitCodes` cases and their directory/source/log writing body; no exclusive helper or using remains. Retained handler, malformed CLI and injected verifier controls use in-memory console/filesystem data. Trigger/match/body-visibility helpers parse in memory; trusted-source helpers use `SnapshotFileSystem` and in-memory heap preparation. Proof-input controls parse in memory, then hash a fixed set of at most six explicitly named loaded assemblies once through a lazy identity; there is no recursive runtime/toolchain traversal or output tree. No removed workload was executed.

Correction validation: scoped `dotnet format whitespace . --folder --verify-no-changes --include Source/DafnyDriver.Test/InternalErrorExitTests.cs` and `git diff --check` passed. Static retained-test/helper review found no temporary-directory creation, file-output, process compilation or sync boundary in the retained changed tests. No rebuild or replay of deleted cases was performed; earlier cached test results do not validate this deletion as a rebuilt source state. A separate correction commit records removal without altering runtime/compiler semantics. Parent fresh reviewer owns independent acceptance.


## Independent closure and attribution

Fresh independent review accepted the current scoped source and the removal of
file-producing development tests. Cached-binary checks remain separate from a
fresh source build. The coordinator corrected this record's table placement and
owner-specific review wording after that review; these edits change no source.
Current maintenance commit attribution was completed using the repository's
established Codex coauthor identity, with each original commit tree preserved.
The local before/after mapping is available under
`/workspace/tmp/organize-current-commits/`; it is maintenance metadata, not
benchmark evidence. No unchanged test or proof was rerun for these document edits.
