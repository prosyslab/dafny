# Resolve verification-facts rebase conflicts

Status: done
Date: 2026-10-22

## Objective and scope

Resolve the five unmerged paths while replaying `888f1b2b2` onto `5fa47c6e9`.
This is repository maintenance. Preserve compatible changes from both sides,
the two already staged verification-facts documents, and unrelated work. Mark
the resolved files in the Git index; do not create a commit or continue the rebase.
Compiler behavior, proof obligations, evaluator contracts, datasets, dependencies,
and scoring are unchanged.

## Evidence and approach

Inspected applicable `/workspace/AGENTS.md`, parent/subtree `AGENTS.md`,
`CLAUDE.md`, `.editorconfig`, `Makefile`, conflict stages, incoming commit,
rebase state, analyzer helpers, call sites, and existing regression tests.
The target branch already contains every incoming verification-facts code change,
plus proof-input support, body visibility, isolated test options, and a composition
regression. Retain that superset and append only the incoming documentation links.
No new implementation, test, package, or approval is needed for file edits.
Git index writes may require the approved escalation path because submodule
metadata resides outside the writable subtree.

## Change table

| Paths | Resolution and purpose | Validation |
| --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.cs` | Retain existing verification targets, proof-input projection, and body visibility | Compare both stages and resulting source; focused analyzer tests |
| `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` | Retain composed CLI flags, named inventory argument, and large-stack proof-input analysis | Compare incoming patch and target implementation; build |
| `Source/DafnyCore.Test/DefinitionVerificationFactsTest.cs` | Retain isolated options and the body-visibility composition regression | Focused in-memory analyzer tests |
| `plan/INDEX.md`, `wiki/INDEX.md` | Preserve target entries and add incoming verification-facts links | Diff and Markdown-only audit |
| This plan and its index entry | Record resolution, checks, limitations, and handoff | Final status and whitespace review |

## Validation and acceptance

Run from `/workspace/dafnyutils/dafny` with .NET SDK 8.0.131:
`dotnet build Source/Dafny.sln --no-restore -m:1 -nr:false`;
`dotnet test Source/DafnyCore.Test --no-restore -m:1 -nr:false --filter
'FullyQualifiedName~DefinitionVerificationFactsTest|FullyQualifiedName~DefinitionBodyVisibilityTests|FullyQualifiedName~DefinitionProofInputsTests'`.
Use the `make format` whitespace operation restricted to the three resolved C#
files to preserve unrelated source. No Dafny source changes require `make format-dfy`.
Inspect `git diff --check`, `git diff --cached --check`, remaining conflict markers,
unmerged paths, final staged scope, and non-Markdown files recursively in
`plan/` and `wiki/`. Obtain fresh independent review under repository guidance.
Build/test failures must be recorded, not reported as passing. These checks do
not establish benchmark proof results; no benchmark or paid execution is planned.

## Progress and handoff

Five files resolved. The three C# files exactly match their target-branch versions;
both index files retain the target entries and the incoming feature link.
No durable findings beyond the existing feature documentation; this task restores
an already implemented compatible source state.

## Validation results

Checked the working tree based on `5fa47c6e9` while replaying `888f1b2b2`,
from this native repository root with SDK 8.0.131/runtime 8.0.31.

- `dotnet build Source/Dafny.sln --no-restore -m:1 -nr:false` passed, zero errors.
  Four warnings remain in untouched files: CS0162 twice in
  `ContractRuntimeProfile.cs`, CS0618 in `PbtObservation.cs`, and VSTHRD103 in
  `ContractPhaseTimingTests.cs`. No generated tracked files changed.
- After that fresh build, `dotnet test Source/DafnyCore.Test --no-build
  --no-restore -m:1 -nr:false --filter
  'FullyQualifiedName~DefinitionVerificationFactsTest|FullyQualifiedName~DefinitionBodyVisibilityTests|FullyQualifiedName~DefinitionProofInputsTests'`
  passed 51/51, zero skipped. Initial sandbox execution could not open the
  test-runner communication socket; the approved escalated invocation passed.
  These are analyzer/translation tests, not solver or benchmark proof results.
- The `make format` target's whitespace operation, restricted to the three
  resolved C# files, passed: `dotnet format whitespace Source/Dafny.sln
  --no-restore --verify-no-changes --include Source/DafnyCore/DefinitionAnalysis.cs
  Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs
  Source/DafnyCore.Test/DefinitionVerificationFactsTest.cs`. Workspace-loading
  warnings were reported; no whitespace changes were required.
- A fresh `gpt-6.1-sol`/high reviewer independently compared all conflict stages,
  the incoming patch, current code, and documentation indexes. No findings.
  Its own marker, working/staged whitespace, and Markdown-only audits passed.
  It did not duplicate the build or test run.
- Working/staged whitespace checks passed, no markers remain in the five
  resolved paths, and recursive `plan/`/`wiki/` inspection found no non-Markdown
  files or artifact symlinks. The merged feature-document links exist.

The explicit resolved paths and this plan are staged. `git ls-files -u` is empty;
working/staged whitespace checks pass and no unstaged changes remain. The staged
diff contains only the two incoming feature documents, their index links, and
this maintenance plan/index entry. HEAD remains `5fa47c6e9`; no commit was created.
No process or blocker remains. Next action for the user: `git rebase --continue`
to resume the existing nine-commit sequence (eight later commits remain pending).
