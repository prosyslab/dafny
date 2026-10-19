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
