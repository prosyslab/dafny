# Keep match-pattern variables inside automatic trigger scope

Status: done
Owner: native Dafny repository (`cosyn/dafny`).
Date: 2026-10-16.

## Objective and acceptance

Repair a generic native compiler scope error implicated by the authorized C6
public-command diagnostics. Automatically exported trigger terms must not mention
any variable bound only by a match case. Preserve valid trigger terms and the
prior split-quantifier scope repair. Establish the failing generic case before
the fix, pass bounded in-memory regression cases after the fix, and show that a
generic native verifier command reaches ordinary proof results rather than
Boogie resolution errors. Run focused formatting and review the final diff.

This is repository maintenance after the interrupted run, not an evaluated run.
Do not edit benchmark tasks, contracts, evaluator, scoring, provider policy or
Python integration code. Do not launch providers, Docker, images, broad proof
suites, or new dependencies. Do not resume or mutate the stopped run.

## Evidence and existing implementation

- Native base HEAD is `dce5a96612b6516c5b180bb215d6eb3e3b430d5a` with substantial
  pre-existing dirty work, including `ComprehensionTriggerGenerator.CanCombine`.
- Read root, Cosyn and native `AGENTS.md`, native `CLAUDE.md`, native plan/wiki
  indexes and the 2026-10-14 trigger scope plan/wiki. No nested instruction files
  or templates were found in the affected native source/documentation trees.
- Existing scope repair checks split binder identity and ranges; it remains
  unchanged. `TriggersCollector.AnnotateNestedMatchExpr` and `AnnotateMatchExpr`
  currently permit a trigger referencing one local pattern binder if another
  pattern binder is absent. This is a separate hypothesis requiring regression.
- Permitted private records are the C6 observer failure summary and
  `analysis/native-failure-revision3/reconstruction-inputs.json`, its exact three
  referenced baseline source blobs, six selected patch records and relevant
  public native-command diagnostics from attempts a000001 through a000005.
  Candidate excerpts, reconstructions and run diagnostics stay in the private
  C6 `analysis/native-failure-revision3/` directory. No hidden evaluation,
  reference, other-run, credential or provider payload retrieval is permitted.

## Change table

| Exact file/symbol | What/how | Why and unmet behavior | Validation |
| --- | --- | --- | --- |
| `Source/DafnyCore/Triggers/TriggersCollector.cs`: `AnnotateNestedMatchExpr`, `AnnotateMatchExpr` | Confirm and minimally correct exported candidate scope predicates | Branch-local binders otherwise escape into quantifier triggers | Generic in-memory source/AST regression and bounded verifier reproduction |
| `Source/DafnyCore.Test/MatchTriggerVariableScopeTests.cs` | Add small in-memory compiler AST/source tests with no filesystem/subprocess/build/compilation calls | Reproduce escaped match binder and preserve valid candidates | Filtered `dotnet test --no-build --no-restore` |
| `Source/DafnyCore/AssemblyInfo.cs` | Standard `InternalsVisibleTo("DafnyCore.Test")` test access only | Direct collector boundary tests must cover both match AST forms without reflection or a new public API | Exact test assembly name and direct compiled collector access |
| `plan/2026-10-16-match-trigger-variable-scope.md`, `plan/INDEX.md` | Record scope, evidence, commands, state and handoff | Auditable owner workflow | Diff/link/file audit |
| `wiki/match-trigger-variable-scope.md`, `wiki/INDEX.md` | Record generic invariant and confirmed regression evidence | Durable native compiler knowledge without candidate content | Source verification and links |
| Private C6 `analysis/native-failure-revision3/` bounded artifacts | Reconstruct three exact candidate files if necessary, record exact command and provenance, generic pre/post reproduction | Establish relation of generic compiler failure to observed public-command failure | Exact hashes/patch receipts and bounded three-file native replay; no task proof success claim |
| `/workspace/tmp/dafny-match-trigger-scope/generic.dfy`, `before.stdout.txt`, `before.stderr.txt`, `after.stdout.txt`, `after.stderr.txt` | Small generic datatype/match existential and bounded CLI receipts | Prove generic malformed-trigger failure and recovery | Existing installed verifier, 30-second external timeout and five-second per-batch limit |
| Private C6 `analysis/native-failure-revision3/reconstructed/bench/utils/csplit/{Csplit,CsplitCore,CsplitProof}.dfy`, `reconstructed/bench/core` read-only support symlink, `reconstructed/bench/utils/csplit/{CsplitSpec,CsplitSchema}.dfy` support symlinks; `reconstruction-receipt.json`, `fixed-verify.{stdout,stderr}.txt`, `fixed-complexity.{stdout,stderr}.txt`, `fixed-replay.json`, `fixed-verification.{trx,json,txt}` | Recover accepted revisions 1–3 from exact baseline blobs and paired started/completed patch records; preserve includes; use existing public dependencies read-only | Relate generic defect to exact accepted candidate source without exposing private evidence | Three baseline and reconstructed hashes, patch success/revision receipts, bounded replay |
| Private C6 `analysis/native-failure-revision3/fixed-entry-complexity.{stdout,stderr}.txt`, `fixed-entry-replay.json`, `fixed-entry-verification.{trx,json,txt}` | Replay the confirmed nested entry declaration `Csplit.CsplitBenchmarkItem.RunCore` | Earlier inferred short filter selected no obligations and cannot establish compiler recovery | Require nonempty structured verification results and real assertion-batch progress |

All edited implementation and tests belong to native Dafny. Specification,
proof scope, benchmark data, evaluator, scoring and reports remain fixed. Parent
integration investigation owns experiment state and fresh independent review.

## Validation and operational commands

Working directory is `/workspace/cosyn/dafny` unless stated otherwise. .NET SDK
8.0.131 is installed; `global.json` requests 8.0.111 with latestFeature roll-forward.
Existing binaries, package restore state and Z3 installation must be checked.

1. Read bounded public candidate match clauses and native diagnostics through
   exact `sudo -n /usr/bin/python3 -B` reads; no private directory permission changes.
2. Before implementation, use an installed native CLI on a small generic source
   under `/workspace/tmp/dafny-match-trigger-scope/` (or private C6 analysis when
   derived from candidate content), with a bounded timeout and small output.
   Inspect commands before execution; no provider calls or code generation.
3. Operational deployment, separate from tests: `dotnet build Source/Dafny.sln
   --no-restore -m:1 -p:UseSharedCompilation=false` after source/tests settle.
   Existing supported native build is authorized to refresh local binaries.
4. `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter
   FullyQualifiedName~MatchTriggerVariableScopeTests` and existing in-memory
   `TriggerBoundVariableScopeTests` filtered similarly. Tests must only parse,
   resolve and inspect in-memory AST/trigger attributes; no temp directories,
   compilation, generated outputs, subprocesses, synchronization or heavy I/O.
5. Focused equivalent of `make format`: `dotnet format whitespace
   Source/Dafny.sln --no-restore --include
   Source/DafnyCore/Triggers/TriggersCollector.cs
   Source/DafnyCore.Test/MatchTriggerVariableScopeTests.cs --verify-no-changes`.
6. At final handoff, run the generic verifier probe on rebuilt binaries using
   existing solver only, bounded timeout and no compiled target output. If exact
   three-file replay is needed, keep all reconstruction/evidence in the private
   path and preserve original sources, includes and flags.
7. `git diff --check`; inspect relevant diffs and non-Markdown files recursively
   under native plan/wiki; preserve pre-existing work.

## Risks, compatibility and approvals

Rejecting malformed candidates can change automatic-trigger selection or emit a
no-trigger warning; valid in-scope candidates should remain. No logical expression,
bound variable, contract or verification obligation may be weakened. Native build
can expose pre-existing errors/warnings; report them accurately. Do not infer
candidate proof correctness or benchmark outcomes from compiler recovery.

The user authorizes direct native bug repair and parent-approved bounded private
C6 diagnosis. No new approval is required for the above reversible work. Fresh
independent verification must use a separate context, arranged by the parent;
this implementation agent will not self-certify independent acceptance.

## Progress

- Initial inspection completed. Root received the candidate-scope hypothesis.
- No reconstruction, probe, source or test writes occurred before this ready plan.
- At initial handoff, remaining: reproduce generically, confirm/fix predicate, run bounded validation,
  document durable evidence and provide exact handoff pins.

### Confirmed scope defect and local validation

The unchanged 11-line generic existential/match source produces eight undeclared
`leftValue`/`rightValue` identifiers before repair. Stack matches the observed
pre-SMT `GetVerificationTasks`/`DafnyProgramVerifier`/`Compilation` failure.
After correcting both match candidate filters to reject terms mentioning any
local pattern variable, the same command reaches ordinary verification: exit 4,
zero verified and one postcondition proof error, no internal binding error.
This is compiler recovery, not proof success. Four in-memory AST regressions pass
and focused formatting passes. Operational solution build passes with four
warnings from unchanged `DafnyTestGeneration` source. Default-sandbox vstest
cannot open its local communication socket; the approved escalated rerun passes.

Private reconstruction is bounded to three changed source files (27,679 bytes)
and 17 existing read-only public support dependencies (344,400 bytes) discovered
through their include closure. No public benchmark solution/reference is read.
The original `--library:bench/core` policy additionally loads five existing
public core files, so the complete replay library/support set is 22 files,
387,574 bytes. Reuse the existing directory through a read-only source symlink;
do not copy or modify its files. A one-core resource cap is an explicit replay
difference from Dafny's current 32-core default; obligations remain unchanged.
Run the inferred `measure-complexity --standard-libraries:false
--verify-included-files --filter-symbol=Csplit.RunCore. --mutations 3
--random-seed 0 --library:bench/core --allow-warnings --isolate-assertions
--progress:Batch --verification-time-limit:30 --cores 1` on the three recovered
source paths, writing its three logger receipts under private analysis. Use a
100-second external process deadline; incomplete mutation runs are timeouts.
Use exact `sudo -n /usr/bin/python3 -B` for private artifacts, without chmod/chown
of source artifacts. Native failure progress rows 10/13/16/19/22 contain no argv;
the replay command is explicitly derived from current harness command-building
code and recorded C6 policy, not presented as recovered original argv.

The first inferred entry filter `Csplit.RunCore.` selected zero obligations;
its exit 0 is invalid as compiler/proof acceptance. Original zero-result
receipts remain unchanged. Inspection of the recovered source confirms the
actual nested entry declaration and the corrected filter is
`Csplit.CsplitBenchmarkItem.RunCore.`. The corrected replay uses distinct
`fixed-entry-*` artifacts and otherwise preserves the recorded policy.

Independent review found that the four parser/resolver tests only exercise
`NestedMatchExpr`: flattening happens after trigger generation. Extend the test
file with direct collector calls on tiny resolved `MatchExpr` and
`NestedMatchExpr` trees, checking candidate identity retention for zero, one and
two pattern binders and rejection of a candidate mentioning just one of two
local binders. Standard friend-assembly access is authorized by the parent as a
routine test seam; no reflection, public API or dependency changes. A targeted
operational `dotnet build Source/DafnyCore.Test --no-restore -m:1
-p:UseSharedCompilation=false` is required for this new test/access change; then
rerun only focused no-build/no-restore cases and formatting. Mirror the settled
repair in the benchmark native owner under its separate linked plan before its
supported serial build. The prior four-case result is not full branch coverage.

### Final test coverage and deployment alignment

The eight direct collector cases and four source cases pass (12/12). Focused
formatting including friend access passes. The focused test assembly build has
zero warnings/errors. It updates `Binaries/net8.0/DafnyCore.dll` and test copies;
the CLI root copy is updated through the supported targeted operational command
`dotnet build Source/Dafny/Dafny.csproj --no-restore -m:1
-p:UseSharedCompilation=false --verbosity quiet` after the benchmark-native
solution build settles. This avoids a redundant full solution build while
aligning the CLI with the final friend-access source state.

The correct private replay reached actual SMT assertion-batch processing without
the internal error, but remained incomplete. Its wrapper attempted to parse an
empty, unfinalized JSON logger and lost the in-memory termination receipt before
saving its result. Private forensic receipt explicitly records the missing
process classification and likely deadline; no completed mutation/proof claim.
The generic unchanged source's ordinary proof-error result remains the completed
pre/post compiler evidence. No additional private replay is required.

Durable finding: [match trigger scope invariant](../wiki/match-trigger-variable-scope.md).
Second native owner: [benchmark compiler repair](../../../dafnyutils/dafny/plan/2026-10-16-match-trigger-variable-scope.md).
At this intermediate handoff, remaining: finish final CLI alignment,
benchmark-native checks, fresh independent acceptance and final documentation
hygiene. The plan remained `in-progress` until the acceptance recorded below.

### Implementation handoff — 2026-10-16

Local compiler repair and owner documentation are complete. The supported final
CLI project build passes in 20.60 seconds with zero warnings/errors; root CLI
and test copies of Core now match. Final unchanged generic probe again returns
the same ordinary exit-4 proof error and no internal error. Both native owner
implementations, friend access and regression files are byte-identical. The
pre-existing `ComprehensionTriggerGenerator.cs` SHA remains
`71e87fbabc7d750b3ed28078e4cc1deafbfb3314cdc96df3962b201f6b5cdb5f`.

| Check, from native owner root | Outcome |
| --- | --- |
| `dotnet build Source/Dafny.sln --no-restore -m:1 -p:UseSharedCompilation=false --verbosity quiet` | Pass, 1:08.20, four unchanged-source warnings (CS0162 twice, CS0618, VSTHRD103) |
| `dotnet build Source/DafnyCore.Test --no-restore -m:1 -p:UseSharedCompilation=false --verbosity quiet` | Pass, 22.05 seconds, zero warnings/errors; operational build separate from tests |
| `dotnet build Source/Dafny/Dafny.csproj --no-restore -m:1 -p:UseSharedCompilation=false --verbosity quiet` | Pass, 20.60 seconds, zero warnings/errors; aligns final CLI output |
| `dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~MatchTriggerVariableScopeTests --verbosity quiet` | Pass, 12/12, no skips; approved local-socket execution |
| Same test command with `FullyQualifiedName~TriggerBoundVariableScopeTests` | Pass, 3/3, no skips, final Core |
| Planned focused `dotnet format whitespace ... --verify-no-changes --verbosity quiet` | Pass, includes both changed source/test files and friend-access file |
| Unchanged generic verifier command in validation section | Before: eight undeclared Boogie identifiers; after/final: ordinary exit 4, zero verified/one proof error, stderr empty |
| `git diff --check`, exact three-file cross-owner comparison and recursive native plan/wiki non-Markdown audit | Pass; no non-Markdown artifacts found; unrelated changes preserved |

Runtime version: Dafny `4.11.1+dce5a96612b6516c5b180bb215d6eb3e3b430d5a`,
.NET SDK 8.0.131 and configured default Z3 4.16.0. Final bounded SHA256 pins:

| File | SHA256 |
| --- | --- |
| `Source/DafnyCore/Triggers/TriggersCollector.cs` | `a7ec105afe3bd79246089532909360c8813e46b8a615aca4e9f01ae1ebb847f5` |
| `Source/DafnyCore/AssemblyInfo.cs` | `c6f9dab39a49550d203edebb3fe7efc4f69246a93258c020b0f0a6ff7425a0c4` |
| `Source/DafnyCore.Test/MatchTriggerVariableScopeTests.cs` | `d1e794cbbfc66cab9ec9aec4d1cb2d8ae8f90636e5e095c83587d61aa266d28b` |
| `Binaries/DafnyCore.dll` (also test-bin Core) | `7269010c839cdb43cd25d196c8da4f1bd7c57f90f5718e45b0dc5f451572cdbd` |
| `Binaries/DafnyDriver.dll` | `fac7e982d7530e820b3f3efe9672b8bfaf73cbe856a6aded3dd8c5de277e4df0` |
| `Source/DafnyCore.Test/bin/Debug/net8.0/DafnyCore.Test.dll` | `ad9a061e058728b0496f04ce05612d042a381c27580e7074051b9e0404b5de19` |

No source edits, operational processes or paid calls remain in this context.
Generic scratch and private analysis artifacts remain at their planned paths.
Fresh independent acceptance was the only remaining repair gate at this handoff;
it is completed below. Parent owns subsequent image/experiment decisions.
No commits or new dependencies.

### Independent acceptance and closure — 2026-10-16

Fresh independent review accepts the exact native scope repair at
2026-10-16T10:18:52.662637Z. Workspace-only receipts:
[acceptance JSON](/workspace/tmp/match-trigger-scope-independent-review-20261016/independent-acceptance.json)
and [review](/workspace/tmp/match-trigger-scope-independent-review-20261016/review.md).
All ten reviewed source hashes across the two native owners still match current
files, including both repaired filters, friend access, new tests and preserved
split-quantifier implementation/tests.

The fresh context independently passes 12 new match-scope cases and 3 preserved
split-scope cases per owner (30 checks total, no failures/skips), focused
formatting, diff checks and Markdown-only plan/wiki audits. It confirms candidate
identity retention with zero/one/multiple binders, rejection of any case-local
reference in both AST forms, the enclosing free sequence variable and quantified
index controls, and in-memory test call paths. Both unchanged generic stdin
probes return ordinary exit 4, zero verified/one unproved postcondition and no
internal binding error. This establishes compiler recovery, not proof success.

The benchmark-native independent formatter initially times out at 90 seconds
(exit 124, no output). Approved escalated retry passes in 12.334 seconds and
reports unspecified workspace-load warnings; neither attempt is omitted or
relabeled warning-free. The reviewer performs no solution build, provider,
Docker/image, root/Python, broad proof-suite, benchmark/private input or scoring
check. Operational builds remain implementation-owned evidence above.

Acceptance is limited to the exact reviewed source paths/hashes in the dirty
native working trees. The private replay remains incomplete with its missing
termination receipt; it is not a completed proof or experiment result. All
compiler-repair criteria are met, with no remaining native repair work. This
plan is `done`; image and experiment decisions remain parent-owned.
