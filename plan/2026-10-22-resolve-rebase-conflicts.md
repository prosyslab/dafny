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


## Authorized continuation — 2026-10-22

The user now requests completing the existing rebase through all conflicts.
Resume this maintenance plan for the remaining eight commits, beginning at
`583e2afd6`, onto `5fa47c6e9`. Preserve compatible source behavior, distinct
native-tree documentation provenance, existing commit messages, and unrelated
parent-repository work. No new functionality, dependencies or benchmark changes.

Additional change scope: the conflicted historical plan/wiki files and indexes
introduced by the remaining commits, plus this maintenance plan/index entry.
Inspect each conflict's base/current/incoming versions before resolving. The
first add/add plan contains independent Cosyn-native and benchmark-native
validation records; retain both in explicitly separated sections. Source and
regression files of the first replayed trigger commit already match HEAD.

Acceptance: all remaining rebase commands complete on `expecto`, no unmerged
paths or rebase metadata remain, both documentation histories survive, and the
native working tree is clean. Run working/staged whitespace and marker checks,
compare source changes against the target and original branch, recursively audit
Markdown-only plan/wiki trees, and obtain independent review. If any source
resolution changes behavior, run the affected native build, tests and formatting;
if only historical documentation differs, report that scope without claiming a
new proof or test result. Git metadata writes use the approved escalation path
when required because the submodule's Git directory lies outside the subtree.

No durable findings: this continuation reconciles duplicate implementation
history and preserves existing provenance; no new wiki page is necessary.


## Completed continuation and validation — 2026-10-22

All nine original rebase commands completed on `expecto` over `5fa47c6e9`.
The completed rebase had a clean native working tree, no unmerged index entries,
and no `rebase-merge` or `rebase-apply` metadata. The branch is nine commits ahead
of its existing `origin/expecto` tracking reference; no push was performed.

Resolved duplicate split-trigger, match-trigger, internal-exit, proof-input and
reporting patches by retaining the newer target source/tests. In particular,
repeatable proof-input translation, integrated verification facts, later test
removals, and accepted LIT diagnostic line positions remain intact. Historical
Cosyn-native records and benchmark-native bases, binary hashes, validation counts
and limitations are retained in separate sections. Index merging preserves the
current entries and adds only missing feature destinations. The 2026-10-19
benchmark snapshot's scope wording is explicitly historical to that owner.

From `/workspace/dafnyutils/dafny`, Git 2.51.1:

- `git diff --name-only 5fa47c6e9 HEAD -- Source docs` is empty. The final diff
  contains only fourteen Markdown files under `plan/` and `wiki/`.
- `git merge-base --is-ancestor 5fa47c6e9 HEAD` passes, and
  `git rev-list --count 5fa47c6e9..HEAD` reports nine.
- `git diff 5fa47c6e9 HEAD --check`, `git diff --check` and
  `git diff --cached --check` pass. `git ls-files -u` is empty.
- A bounded Python audit of changed Markdown finds no conflict markers. Recursive
  inspection of all `plan/` and `wiki/` files finds no non-Markdown artifacts or
  artifact symlinks; no existing files required cleanup.
- A separate read-only reviewer compared the resolved commits and documentation
  against both histories. It found no blocking issues and independently confirmed
  source/test/fixture identity with the target and preserved provenance.

No new build, C#/Dafny formatting or native tests were run for this continuation:
all compiler code, tests and Dafny fixtures are byte-identical to the target.
The earlier source-bound build and 51-case analyzer run above remain earlier
validation, not new results. No new proof, benchmark or experiment result is
claimed. No durable findings beyond the existing wiki topics; no new wiki page.

This completion record and its index status are folded into the final replayed
documentation commit. No new standalone commit, source change or parent-repository
edit is needed. Rebase work is complete; no remaining conflict, process or blocker.
