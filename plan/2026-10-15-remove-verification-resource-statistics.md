# Remove verification resource statistics from active Dafny reports

Status: done
Date: 2026-10-15
Owner: embedded native Dafny driver
Parent: [integration coordination](../../../plan/2026-10-15-remove-verification-resource-statistics.md)
Cosyn reader: [typed diagnostic compatibility](../../plan/2026-10-15-remove-verification-resource-statistics.md)

## Objective and acceptance

Remove verification resource-usage statistics from active modern CLI progress,
JSON, text, TRX and CSV reports, the verify performance summary, and the
measure-complexity console summary. Remove the now-unused hidden
`--performance-stats` and `--worst-amount` options. Preserve all verification
outcomes, assertion identities, durations, random seeds, mutation iterations,
proof-dependency reporting, diagnostics, internal-error exits, cancellation,
timeouts and out-of-resource outcome counts and limits.

Acceptance requires the modern formats and progress output to retain their
remaining data, measure-complexity to run every requested mutation with the same
seed sequence, normal and failing commands to retain their exits, and affected
native tests/build/format checks to pass. The legacy backwards-compatible JSON/XML
reporter is outside the modern pipeline and remains unchanged. Internal Boogie,
language-server and solver `ResourceCount` values remain because they enforce
limits or power non-reporting behavior.

## Evidence and boundaries

This is maintenance after the parent recorded the separate B3 source audit as
frozen. No experiment/private candidate/model/evaluator logs were read. Current
source confirms the active writers are `JsonVerificationLogger`,
`TextVerificationLogger`, `VerificationResultLogger`/TRX and `CSVTestLogger`;
`CliCompilation` emits the batch suffix, `VerifyCommand` owns an RU-only hidden
summary, and `MeasureComplexityCommand` owns an RU-only subscriber and option.

The tree already contains unrelated trigger-scope, explicit internal-exit and
JSON overflow work. The internal-exit edits in `CliCompilation` and
`MeasureComplexityCommand` must be preserved. The accepted JSON overflow test and
wiki remain as historical evidence but are superseded because the reported field
is removed. No benchmark/specification/proof/evaluator/scoring/dataset, package,
provider, experiment, image or commit change is authorized.

## Change table

| Exact files or symbols | Change, necessity and preserved behavior | Validation |
| --- | --- | --- |
| `Source/DafnyDriver/JsonVerificationLogger.cs` | Remove scope and per-VC `resourceCount`; retain names, outcomes, durations, seeds, assertions and proof dependencies | Updated mixed-outcome logger test and `logger/JsonLogger.dfy` |
| `Source/DafnyDriver/TextVerificationLogger.cs` | Remove total, maximum and per-batch RU lines; retain outcome/time/seed/assertion/dependency text | `logger/TextLogger.dfy`, `logger/TextLoggerBatch.dfy` |
| `Source/DafnyDriver/VerificationResultLogger.cs`, `CSVTestLogger.cs` | Remove the TRX RU property and CSV RU column/value; retain duration, outcome and random seed | `logger/CSVLogger.dfy`, `logger/VerificationLogger.dfy` |
| `Source/DafnyDriver/CliCompilation.cs` | Remove only the `resource count` suffix from active `--progress:Batch`; retain time/outcome/origin and protected internal-exit edits | build and bounded direct success/failure progress checks |
| `Source/DafnyDriver/Commands/VerifyCommand.cs` | Remove hidden `--performance-stats`, RU aggregation/fields/output; retain result/out-of-resource/error/timeout summaries | affected CLI fixtures and direct verify checks |
| `Source/DafnyDriver/Commands/MeasureComplexityCommand.cs` | Remove `TopX`, resource summary subscription/await/output; retain every mutation, seed, diagnostic, logger, dependency and exception path | `cli/measure-complexity.dfy`, internal-exit tests and direct three-mutation success/failure checks |
| `Source/DafnyCore/Options/CommonOptionBag.cs`, `Source/DafnyCore/Options/BoogieOptionBag.cs` | Make the active progress/text and CSV help descriptions truthful about remaining time, assertion and outcome diagnostics; preserve resource-limit option/binding/default behavior | build plus relevant existing help/rendered-option checks |
| `Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs` | Remove obsolete overflow-only test; adapt the mixed-outcome/schema control to retained fields and runtimes | focused driver test |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/logger/{TextLogger.dfy,TextLoggerBatch.dfy,CSVLogger.dfy}` | Update existing remaining-field contracts | focused LIT runs |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/{measure-complexity.dfy,measure-complexity.dfy.expect}` | Remove the deleted option/summary expectation while retaining mutation/error/exit coverage | focused LIT run |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny0/{SubsetTypes.dfy,SubsetTypes.dfy.expect,CoinductiveProofs.dfy,CoinductiveProofs.dfy.expect}` | Remove the deleted hidden option, RU-only expected lines and obsolete macOS exclusion | focused LIT runs |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny1/{SchorrWaite.dfy,SchorrWaite.dfy.expect,SchorrWaite.dfy.refresh.expect}` | Remove the deleted hidden option and RU-only expected lines | focused LIT run |
| `docs/VerificationOptimization/VerificationOptimization.md` | Align text/CSV examples with duration/seed reports and remove instructions that require deleted RU output | documentation review |
| `wiki/json-verification-resource-count.md`, `wiki/INDEX.md` | Mark the prior exact aggregation invariant superseded while preserving its accepted historical receipts and limits | Markdown/link review |
| This plan and `plan/INDEX.md` | Record commands, results, source hashes and handoff | diff/link and Markdown-only review |

Without these fixture and documentation updates, supported tests and user-facing
examples would invoke deleted options or assert deleted columns. No new
absence-only test is added.

### Accepted fixture line-position repair

Fresh independent LIT execution found deterministic diagnostic-location drift in
`logger/TextLogger.dfy`, `logger/TextLoggerBatch.dfy`,
`cli/measure-complexity.dfy`, and `dafny0/CoinductiveProofs.dfy`: deleting
RU-only comment/directive lines moved the unchanged Dafny programs upward by
eight, three, two and two lines respectively. Preserve the original source
positions by replacing those deleted non-program lines with blank lines. Do not
change a Dafny declaration, specification, proof body or existing expected
diagnostic location. Re-run only these four failed fixtures with `build=false`;
the parent reuses its fresh independent verifier for acceptance.

## Validation plan

Run from `/workspace/cosyn/dafny` with installed caches and no restore/network:

- scoped `dotnet format whitespace Source/Dafny.sln --no-restore --include ...`
  followed by `--verify-no-changes` for touched C#;
- `dotnet build Source/Dafny.sln --no-restore -m:1
  -p:UseSharedCompilation=false`;
- focused `dotnet test Source/DafnyDriver.Test --no-restore -m:1
  -p:UseSharedCompilation=false --filter
  'FullyQualifiedName~JsonVerificationLoggerTests|FullyQualifiedName~InternalErrorExitTests'`;
- supported `make test name=<affected-case> build=false` for the listed logger,
  measure-complexity and removed-option fixtures;
- two public toy files under
  `/workspace/tmp/remove-verification-resource-statistics/cosyn/`, each with
  `--mutations 3 --random-seed 7`, to confirm all three seeds execute and success
  remains 0 while a real failed assertion remains 4;
- `git diff --check`, scoped diff review, remaining-report `rg`, and recursive
  Markdown-only checks for `plan/` and `wiki/`.

Do not run the unrelated full Driver contract-runtime campaigns; their three
pre-existing failures are already preserved by the prior owner record. Local
checks do not prove a benchmark, image or experiment. The parent starts a fresh
independent verifier after all source and record edits freeze.

## Implementation and results

Modern JSON/text/TRX/CSV writers no longer emit RU fields, properties or columns.
Batch progress ends after its duration. Verify no longer registers or aggregates
the hidden performance summary, and measure-complexity no longer registers,
subscribes to, awaits or prints an RU ranking. Its mutation loop, seed sequence,
diagnostic subscriber, proof-dependency logger, result logger and protected
internal-exit return remain. Existing logger/CLI fixtures and current help/docs
now describe and expect the remaining outcomes, durations, seeds and assertions.
Legacy JSON/XML and internal solver/language-server counters remain unchanged.

Validation from `/workspace/cosyn/dafny` used .NET SDK 8.0.131 and the existing
restore cache. Scoped `dotnet format whitespace ... --no-restore --include ...`
completed with only its workspace-load warning. `dotnet build Source/Dafny.sln
--no-restore -m:1 -p:UseSharedCompilation=false` passed in 8:33 with zero warnings
and errors. `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1
--filter 'FullyQualifiedName~JsonVerificationLoggerTests|FullyQualifiedName~InternalErrorExitTests'`
passed 12/12.

The direct built CLI ran both public toy files with `measure-complexity
--mutations 3 --random-seed 7 --progress:Batch`. Success returned 0 and failure
returned 4; both executed seeds 7, 822959691 and 1871007331. Every batch retained
outcome and duration output without RU. Scratch inputs remain under
`/workspace/tmp/remove-verification-resource-statistics/cosyn/`.

`make test name=logger build=false` and `make test
name=cli/measure-complexity.dfy build=false` copied their fixtures but aborted
before test execution because sandboxed vstest could not create its TCP listener
(`SocketException (13): Permission denied`). They were not retried or escalated.
The removed-option `SubsetTypes`, `CoinductiveProofs` and `SchorrWaite` LIT cases,
scoped format verification, and rendered help checks remain for the fresh
verifier. The known unrelated full Driver 293/296 campaign result was not rerun.

Production, tests and documentation are frozen for parent-owned independent
verification. This plan remains `in-progress` until those bounded checks pass.

### Fixture line-position repair results

The fresh verifier's permitted report identified only line-offset failures in
four fixtures. Eight, three, two and two blank lines now replace the removed
RU-only lines in `TextLogger.dfy`, `TextLoggerBatch.dfy`,
`measure-complexity.dfy` and `CoinductiveProofs.dfy`, respectively. Their Dafny
programs and existing expected diagnostics remain unchanged.

Using the approved local-IPC path and cached build, each exact command passed one
test: `make test name=logger/TextLogger.dfy build=false`, `make test
name=logger/TextLoggerBatch.dfy build=false`, `make test
name=cli/measure-complexity.dfy build=false`, and `make test
name=dafny0/CoinductiveProofs.dfy build=false`. No build, restore, broad test,
provider, experiment or production edit followed. Source/tests/docs are frozen
again for the parent-owned fresh recheck; status remains `in-progress` until that
independent acceptance.

## Independent acceptance and closure

The fresh verifier independently built the Driver test project with0warnings/
0errors and passed3selected logger/internal-exit tests. The first logger group
was14/16 and the complexity/coinductive fixtures exposed four diagnostic-line
position regressions. After the blank-line repair, the same independent context
reran only those four cached build=false cases:1/1 each. Together with the
initial14passing logger cases, SubsetTypes and SchorrWaite, all20unique affected
LIT cases are now passing. The separate JsonLogger check duplicates one of those
cases and is not added to that denominator.

The verifier confirms unchanged Dafny bodies/specifications/proofs and non-RU
outcome checks; it also confirms the protected warning/exit/mutation/resource-limit
code is retained. Exact commands, current fixture hashes and source pins are in
/workspace/tmp/remove-verification-resource-statistics/cosyn-independent/report.md.
Implementation-owned full solution build, scoped formatting and12focused Driver
tests remain the build/format evidence; no full upstream campaign rerun occurred.
Rendered help was source-inspected, not independently runtime-asserted. The known
historical3ContractRuntime failures are not repaired or relabeled.

Parent coordination accepts the bounded reporting-removal scope. No provider,
benchmark, image or new paid result follows; no native implementation work
remains. Historical RU-overflow knowledge remains marked superseded, and raw
earlier evidence is preserved. Verifier-owned test processes have exited.

## Separate benchmark-native propagation record

The following record covers the separate benchmark-native tree and retains its
original build and validation provenance.

# Remove verification resource statistics from modern native reports

Status: done
Date: 2026-10-15
Owner: dafnyutils/dafny
Root coordination: [integration plan](../../../plan/2026-10-15-remove-verification-resource-statistics.md)

## Objective and acceptance

User explicitly requested removal of RU recording. Remove modern JSON scope/VC
resourceCount, text RU totals/max/per-VC lines, TRX property, CSV column, batch
progress suffix, hidden verify --performance-stats and complexity RU summary plus
--worst-amount. Preserve solver counters and resource limits, OutOfResource
outcomes, assertion selection/identities, runtimes, seeds/iterations, proof
dependencies, warnings, cancellation and terminal internal-error exits.

This is maintenance, not an evaluated experiment. No task/private run material
is read. No dependencies, network/restore, images, providers or commits. Legacy
optional reporting remains out of scope. Historical overflow receipts remain.

## Inspected evidence, compatibility and risks

Inspected root/dafnyutils/native instructions, CLAUDE.md, DAFNYSTYLE.md, native
Makefile, Driver/IntegrationTests csproj, current writer/command source, directly
affected public LIT fixtures, existing JSON tests and internal-error tests,
plan/wiki indexes and logger wiki. HEAD bc427b21461f258fd8de34232e01bb6be03cee39.
Pre-existing trigger/internal-exit/JSON operand-widening changes are preserved;
the resource fields are now intentionally removed. External report schema and
removed report-only options change intentionally. No specifications, proofs,
evaluators, datasets or scoring change; only native reporting implementation and
its test expectations. Known three ContractRuntime baseline failures are not
part of this focused validation and must not be reported as repaired.

## Change table

| Exact paths/symbols (native owner) | What/how/why and unmet behavior | Validation |
| --- | --- | --- |
| Source/DafnyDriver/JsonVerificationLogger.cs; TextVerificationLogger.cs; VerificationResultLogger.cs; CSVTestLogger.cs | Remove emitted RU fields/property/column and report-only sums/max; remaining reporting otherwise retained | Existing synthetic JSON controls; logger LIT cases |
| Source/DafnyDriver/Commands/MeasureComplexityCommand.cs | Remove ReportResourceSummary, subscriber/await and TopX option; preserve mutation workflow/internal exits | Complexity LIT and three-mutation toy success/failure |
| Source/DafnyDriver/Commands/VerifyCommand.cs; Source/DafnyDriver/CliCompilation.cs | Remove hidden performance statistics feature, report-only fields/updates and progress RU suffix | InternalErrorExitTests, existing batch-progress LIT |
| Source/DafnyCore/Options/CommonOptionBag.cs; Source/DafnyCore/Options/BoogieOptionBag.cs | Correct modern CLI help that still promises assertion/CSV resource usage; preserve resource-limit option name, parser, binding and semantics | No-restore native Core build, two-file scoped format and existing cli/help.dfy plus direct rebuilt CLI help inspection |
| Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs | Remove obsolete RU numeric feature cases; retain normal/empty/mixed outcome/schema/runtime controls | Focused Driver test filter |
| Source/IntegrationTests/TestFiles/LitTests/LitTest/logger/TextLogger.dfy; TextLoggerBatch.dfy; CSVLogger.dfy | Update existing output expectations; preserve public Dafny programs and source line numbers | make test logger/ build=false |
| Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/measure-complexity.dfy and .dfy.expect | Remove removed-option use and resource-summary expectations; preserve source line numbering | make test name=cli/measure-complexity.dfy build=false |
| Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny1/SchorrWaite.dfy, .dfy.expect, .dfy.refresh.expect; dafny0/SubsetTypes.dfy, .dfy.expect; dafny0/CoinductiveProofs.dfy, .dfy.expect | Remove hidden option use and RU-only expected lines | Existing focused resolver integration tests |
| plan/2026-10-15-remove-verification-resource-statistics.md; plan/INDEX.md; wiki/verification-json-logging.md; wiki/INDEX.md | Record current behavior and historical overflow fix without erasing receipts | Diff/link/Markdown-only audit |

## Validation commands and scope

All commands from /workspace/dafnyutils/dafny, cached .NET SDK 8.0.131/runtime 8.0.31,
DOTNET_ROOT=/usr/lib/dotnet when required. `dotnet build Source/Dafny.sln
--no-restore` (native Makefile exe command with explicit no-restore constraint).
`dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter
"FullyQualifiedName~JsonVerificationLoggerTests|FullyQualifiedName~InternalErrorExitTests"`.
`dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes
--include <the eight changed C# paths>` is scoped Makefile format equivalent.
Supported `make test name=<fixture> build=false` for logger/, complexity, the three
removed-option fixtures and verification/proofDivision/ plus
verification/outOfResourceAndIsolateAssertions.dfy; existing normal progress case
is also inspected. Expected: public outcome/assertion/proof/seed/exit controls
pass with matching current output. Test phase/build logs and generic three-mutation
success/failure source/output go in
/workspace/tmp/remove-verification-resource-statistics/benchmark-native/.
No full Driver contract-runtime campaign or benchmark suite rerun.

## Progress and handoff

Implementation in progress. Fresh verification belongs to parent-started agent
with independent context after freeze. Remaining: implementation, local checks,
wiki update, exact final file hashes and handoff. Plan stays in-progress until
independent acceptance is recorded by coordination.

Finding: first logger LIT run was15/16; TextLogger legacy-syntax invocation also
uses the modern writer, so its second expectation block needs the same removal.
The legacy class implementation remains untouched. Correcting existing checks
within the planned fixture; source line numbers remain unchanged.

## Implementation results and frozen handoff

Modern RU report fields, sums/maxima, progress suffix and report-only options are
removed; no solver or verification-policy code changed. All 8 changed C# files
and 12 changed fixture files are frozen; exact SHA256 manifest is
`/workspace/tmp/remove-verification-resource-statistics/benchmark-native/source-sha256.json`.
The pre-existing trigger, internal-error exit, compilation and mutation-stop
changes remain in the working tree. No commit or gitlink update was made.

Validation from native root, SDK 8.0.131/runtime 8.0.31 and native HEAD
bc427b21461f258fd8de34232e01bb6be03cee39 plus existing dirty state and this change:

| Command/check | Result and evidence |
| --- | --- |
| `DOTNET_ROOT=/usr/lib/dotnet dotnet build Source/Dafny.sln --no-restore` | Default sandbox exits 1 before work (0 warnings/errors); approved escalated local IPC rerun passes,0 warnings/errors, 20.27s. `build.log`, `build-escalated.log` |
| `DOTNET_ROOT=/usr/lib/dotnet dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter 'FullyQualifiedName~JsonVerificationLoggerTests\|FullyQualifiedName~InternalErrorExitTests' --logger 'console;verbosity=normal'` | 16/16 pass, 4.3005s; `driver-focused.log` |
| Scoped `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include` the 8 C# paths above | exit 0; generic workspace-loader warning retained in `format.log` |
| `DOTNET_ROOT=/usr/lib/dotnet make test name=logger/ build=false` | First 15/16: second legacy-syntax TextLogger expectation block still expected RU. Corrected that existing block; `make test name=logger/TextLogger.dfy build=false` passes 1/1. `lit-logger.log`, `lit-textlogger-corrected.log` |
| `make test name=cli/measure-complexity.dfy build=false` | 1/1 pass; old source line numbers retained |
| `make test name=verification/proofDivision/ build=false` | 3/3 pass; existing redaction already covers time suffix |
| `make test name=verification/outOfResourceAndIsolateAssertions.dfy build=false` | 1/1 pass; actual resource exhaustion diagnostics/outcome retained |
| `make test name=verification/progress.dfy build=false` | 1/1 pass |
| `make test name=dafny0/SubsetTypes.dfy build=false`; `make test name=dafny0/CoinductiveProofs.dfy build=false`; `make test name=dafny1/SchorrWaite.dfy build=false` | 1/1 each pass; removed option usages/expected RU lines only |
| Generic `dotnet Binaries/Dafny.dll measure-complexity <scratch success/failure.dfy> --mutations=3 --random-seed=7 --standard-libraries=false --cores=1 --verification-time-limit=10 --log-format=json;LogFileName=<scratch result.json>` | Each runs 3 iterations. Success exit 0 and Correct × 3; assertion failure exit 4 and Errors × 3. Sources/stdout/stderr/exit/JSON remain separate scratch artifacts |
| `git diff --check`; recursive native `find plan wiki -type f ! -name '*.md' -print` | pass; no non-Markdown files found |

The 25 unique public LIT cases pass after the targeted expectation correction;
no full Driver campaign rerun was performed. The historical full Driver 299/302
and its 3 reproduced ContractRuntime failures remain explicitly unresolved; this
change neither repairs nor reclassifies them. No providers, evaluated candidates,
private artifacts, package restore, image rebuild, or benchmark suite execution.
Formatting and process success do not establish benchmark or proof success.

Updated [native logging knowledge](../wiki/verification-json-logging.md) and its
index with current modern behavior, retained legacy API scope and historical
resource-overflow receipts. Plan remains in-progress solely for fresh independent
acceptance owned by root coordination. Implementation/source freeze handed to
parent; next action is independent source inspection and focused checks. No
implementation work remains after this handoff; artifacts are workspace-lifetime
maintenance evidence at the directory above.

## CLI help correction follow-up — 2026-10-15

Before edits, scope expanded to the two exact option-help files above. Inspection
of existing Source `.expect*`/`.check` fixtures found neither removed sentence;
`cli/help.dfy` checks only --rprint and needs no expectation changes. Correct only
the stale descriptions: assertion logs retain approximate verification times;
--resource-limit remains a deterministic solver limit without a CSV resource-use
claim. No option parser/binding/default/semantics change. Validation is
`dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore`, scoped two-file
whitespace verification, and existing `make test name=cli/help.dfy build=false`
after copying the rebuilt Core DLL into its existing test runtime output. Direct
`dotnet Binaries/Dafny.dll verify --help` output is saved as maintenance evidence.

Follow-up freeze: both help files are text-only one-line edits. Native Core
no-restore build passes (0 warnings/errors, 1m48.21s); two-file scoped whitespace
verification exits0 with the pre-existing generic workspace warning. Existing
cli/help.dfy passes1/1 after refreshing only its local Core DLL. Direct CLI help
was captured, but a literal substring control failed because help rendering wraps
text; no further runtime-help claim is made. First approval review timed out
without execution; a single retry ran the existing fixture. Exact new source
hashes are appended to source-sha256.json. All source changes are frozen and
fresh independent acceptance remains with root coordination.

## Independent acceptance and closure

Fresh independent source inspection and cached native builds passed. Its own
Driver16/16, logger16/16 and complexity1/1 checks passed,33focused tests total.
An independent public-result probe preserved Valid/Invalid/TimeOut/OutOfResource
outcomes and runtimes. Its generic three-mutation failing control exited4 with
all expected seeds; source checks preserved proof dependencies, resource limits,
cancellation paths, warning handling and internal exit6. Scoped formatting passed.
Source/binary and fixture boundaries, exact commands and limitations are recorded
in /workspace/tmp/remove-verification-resource-statistics/benchmark-native-independent/report.md.

Independent successful multi-format controls have a provenance limit: the initial
successful assertions were followed by a timed-out rerun that reused their raw
writer paths. A final attempt used a new good-final-20261015T081811903746Z
directory, but its30second watchdog expired with no output/report; SIGTERM and
SIGKILL cleanup waits also timed out. Elevated exact-path process inspection
found no matching active command. The original PID was not persisted, so reaping
cannot be confirmed; no unrelated process was killed and no rerun followed.
status.json/manifest.json preserve that incomplete probe, never a passing result.
Actual solver timeout/resource controls were not independently reached; public
synthetic outcomes and existing focused cases provide the stated coverage.

The implementation-owned full build,25unique public LIT passes and independent
33focused passes satisfy the bounded reporting-removal acceptance. The default
full reference rebuild's Gradle cache lock limitation and historical3ContractRuntime
failures remain explicit. Rendered help has source and existing cli/help fixture
coverage, not a successful direct substring assertion. No claim of full suite,
image admission, benchmark proof or experiment success is made. Current native
logging wiki/index is updated; no implementation work remains for this scope.
