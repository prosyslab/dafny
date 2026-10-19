# Remove command tests that create temporary directories

Status: done; independently accepted static cleanup, no runtime changes
Date: 2026-10-16
Owner: Cosyn native Dafny integration
Related: [proof-input integration](2026-10-15-definition-proof-inputs-integration.md),
[native proof-input knowledge](../wiki/definition-proof-inputs.md)

## Objective and acceptance

Delete the command-level proof-input test class because its shared `Run` helper
creates a GUID-named temporary directory for each of six tests and deletes the
created files and directory in `finally`. Preserve runtime behavior and
historical test receipts while making the current wiki state clear. Acceptance:
the forbidden test file is absent, no source references to its class remain,
the test project continues to rely on SDK default source inclusion without a
custom compile entry for the deleted file, and the historical 6/6 receipt is
labeled as evidence from the earlier state. No replacement test is added.

## Inspected evidence

Read `/workspace/AGENTS.md`, `/workspace/cosyn/AGENTS.md`, native `AGENTS.md` and
`CLAUDE.md`, and confirmed there are no additional plan/wiki or test-directory
instruction files. The
native repository is at `dce5a96612b6516c5b180bb215d6eb3e3b430d5a` with extensive
pre-existing dirty source, test, plan, and wiki files; all are out of scope and
must be preserved. `Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs`
contains six tests routed through `Run`, which creates a GUID directory under
`/workspace/tmp/definition-proof-reuse-20261015/native-benchmark/cli` and deletes
its files and directory in `finally`. A source search found no other references
to the class. The project uses `Microsoft.NET.Sdk` and contains no explicit
compile item for this file, so removal relies on the SDK's default source
inclusion. The existing wiki page is already indexed and records the earlier
Driver 6/6 result as historical evidence.

## Change table

| File | Change and why it is necessary | Validation |
| --- | --- | --- |
| `Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs` | Delete this six-case class, whose shared helper creates and deletes temporary directories; without removal these prohibited development tests remain available to run. No replacement test. | Static source-reference search; inspect default SDK compile inclusion; no test execution. |
| `wiki/definition-proof-inputs.md` | Scope the 2026-10-15 five-file transfer, manifest parity, build/test/format receipts, and source-freeze statements as historical; state that four manifest paths remain and the command-test path was removed on 2026-10-16; link the cleanup plan. Without this, historical evidence reads as current five-file parity. | Review dated language, relative Markdown links, whitespace, and Markdown-only plan/wiki scan. |
| `wiki/INDEX.md` | Date the five-file match and validation receipts as 2026-10-15 history and identify the 2026-10-16 test removal/four remaining paths. Without this, the index still makes an undated current-looking five-file match claim. | Review summary against topic; relative Markdown links, whitespace, and Markdown-only plan/wiki scan. |
| `plan/INDEX.md` and this plan | Register the maintenance record and retain its scope, evidence, and handoff status. | Review links/status and Markdown-only plan/wiki scan. |

This change belongs to the Cosyn native Dafny integration repository. It changes
test availability and documentation only; Dafny specification, implementation,
proof semantics, evaluator, dataset, scoring, and report behavior are unchanged.

## Validation

Working directory: `/workspace/cosyn/dafny`. No runtime or test execution is
authorized for this cleanup. After editing, run only:

- `rg -n 'DefinitionProofInputsCommandTests' Source` (expect no matches; confirms
  no native source reference remains).
- Inspect `Source/DafnyDriver.Test/DafnyDriver.Test.csproj` and confirm there is
  no explicit `<Compile>` entry or default-compile opt-out tied to the deleted
  file; the SDK project includes remaining `.cs` sources by default.
- `test ! -e Source/DafnyDriver.Test/DefinitionProofInputsCommandTests.cs`
  (expect success).
- `git diff --check` (expect clean whitespace).
- Run this Markdown trailing-whitespace check (expect no output):

  ```sh
  awk '/[[:blank:]]$/ { print FNR ": trailing whitespace in " FILENAME; bad=1 } END { exit bad }' plan/INDEX.md plan/2026-10-16-remove-proof-input-tempdir-tests.md wiki/definition-proof-inputs.md wiki/INDEX.md
  ```

- `find plan wiki -type f ! -name '*.md' -print` (expect no output; inspect only
  the Markdown record trees).
- Check relative links in the four edited plan/wiki records:

  ```sh
  python3 -c 'from pathlib import Path; import re,sys; files=[Path(x) for x in ("plan/INDEX.md", "plan/2026-10-16-remove-proof-input-tempdir-tests.md", "wiki/definition-proof-inputs.md", "wiki/INDEX.md")]; bad=[f"{p}: {target}" for p in files for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", p.read_text()) if not target.startswith(("http://", "https://", "mailto:")) and not (p.parent / target.split("#", 1)[0]).exists()]; print("\n".join(bad) if bad else "relative Markdown links resolve"); sys.exit(bool(bad))'
  ```

Do not invoke `dotnet test`, `dotnet build`, native tools, containers, provider
calls, or the removed test class. Runtime compilation is unnecessary because no
production source or project configuration changes. No paid run or experiment
applies.

## Compatibility, risks, and approvals

Deleting the file reduces currently available command-level smoke coverage for
the optional proof-input command. Its prior six passing cases remain documented
as historical evidence and are not current validation. Runtime API and wire
behavior do not change. This deletion and the required wiki maintenance are
authorized by the repository instructions and task direction; no dependency or
other approval is required. Preserve all unrelated dirty work.

## Static implementation checkpoint

On 2026-10-16, removed the test source and updated the already-indexed wiki
topic. Static search `rg -n 'DefinitionProofInputsCommandTests' Source` found no
remaining source references. `DafnyDriver.Test.csproj` uses
`Microsoft.NET.Sdk`; the project and `Source/Directory.Build.props` have no
explicit source compile items or default-compile override, so remaining `.cs`
files continue to use SDK default inclusion. `git diff --check` exited 0, and a
trailing-whitespace scan of the three then-edited Markdown files found none. The
recursive `find plan wiki -type f ! -name '*.md' -print` scan returned no
violations. The deleted test file was untracked before cleanup, so its absence
does not appear as a tracked deletion in `git status`. No tests, builds, native
tools, containers, providers, or scratch artifacts were run or created.

## First independent review and documentation correction

The first fresh review was blocked only on historical-scope wording. Its
read-only artifacts are preserved at
`/workspace/tmp/native-proof-input-test-cleanup-20261016/review.md`
(SHA256 `6f889bc9055e8403e0ff6e1616eedaac564b289d2973d169887904a001aaaf61`)
and `review.json` (SHA256
`2efe324d77aa9890906587023379a6fde3639d5853a05947f1336e6eccde7147`). The
review found that the five-file transfer/parity, unchanged-source, and
Markdown-closure hash statements in the topic, plus the undated five-file
summary in `wiki/INDEX.md`, could read as current after the command-test source
was removed. It independently confirmed four surviving manifest paths match
the historical hashes and the fifth path is absent. No tests, builds, native
tools, or other execution ran. The plan change table was expanded to include
`wiki/INDEX.md` before either wiki file was edited. The correction retains the
original 2026-10-15 receipts explicitly as historical and dates the four-path
availability and hash check to the 2026-10-16 review; this review remains
unmodified. A fresh independent review of this correction was pending at that checkpoint.

Post-correction record checks on 2026-10-16 passed: the static source search
reported no class references and the deleted path remained absent;
`git diff --check` exited 0; the Markdown whitespace scan emitted no output; the plan/wiki
non-Markdown scan emitted no output; and the relative-link checker reported
`relative Markdown links resolve`. No tests, builds, native tools, formatters,
containers, providers, or experiments ran.

## Independent acceptance and closure

Fresh `gpt-6.1-sol/high` review accepted the documentation-only correction in
`/workspace/tmp/native-proof-input-test-cleanup-20261016/review-v2.md` (SHA256
`8c2dee43596b5cbc65ab04c9c8c255875bcb92fc2083da9ca93e1e1f52988e5b`)
and `review-v2.json` (`1197a5e550400423aadd5c022bf0c005368b031adfe3cdf61a3e81c27b5f4056`).
Root read the full review, matched its two receipt and four document pins, and
confirmed the deleted path is absent. Four surviving historical source hashes,
default source inclusion, source references, whitespace, links and Markdown-only
record trees passed the independent static checks. These checks do not establish
compilation or prove byte preservation for every unrelated dirty file.

Acceptance criteria are met. No tests, native tools, builds, containers or paid
calls ran for this cleanup. Historical validation remains dated; the runtime
producer and live C7 experiment are unchanged. This closure edits only the plan
and its index after the accepted document pins; the wiki remains at its accepted
hashes. The existing wiki topic records the durable finding about test availability.
No remaining implementation work in this cleanup scope.
