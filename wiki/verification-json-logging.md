# Native verification logging

## Current modern reporting — 2026-10-15

Status: bounded reporting-removal scope independently accepted. Implementation
build/format, Driver16/16 and25unique public LIT cases pass; fresh independent
33focused checks and public synthetic outcomes pass. Standalone multi-format
probe/provenance limits and historical campaign failures remain in the plan.
Origin: [RU reporting removal plan](../plan/2026-10-15-remove-verification-resource-statistics.md).

The modern JsonVerificationLogger no longer emits resourceCount at scope or VC
level. TextVerificationLogger retains outcomes, times, assertions and dependency
records without resource sums/maxima/per-batch counts. VerificationResultLogger
no longer attaches TestResult.ResourceCount to TRX records; CSVTestLogger writes
DisplayName, Outcome, Duration and RandomSeed columns. CliCompilation batch
progress retains elapsed time and outcome without RU. VerifyCommand no longer
aggregates TotalResourcesUsed/MaxVcResourcesUsed or registers --performance-stats;
measure-complexity no longer subscribes to ReportResourceSummary or registers
--worst-amount. Its mutation count, seed sequence and terminal exception behavior
remain intact. Native solver ResourceCount APIs, resource-limit options and
OutOfResource failure outcomes/summaries are unchanged.

This applies to the modern reporting pipeline, including legacy CLI syntax
that routes through it. LegacyJsonVerificationLogger,
LegacyTextVerificationLogger and LegacyVerificationResultLogger, legacy XML,
Boogie internals and optional legacy-driver performance/trace reporting remain
out of scope. Legacy CSV reuses the shared CSV writer, whose output column is
removed. No image admission, benchmark execution or proof result follows from
this source change.

## Historical JSON resource-total repair (superseded interface)

Current commands, source hashes, exact test cases and limitations are in the
linked removal plan; scratch evidence lives under
`/workspace/tmp/remove-verification-resource-statistics/benchmark-native/`.
The historical full Driver 299/302 with 3 reproduced ContractRuntime failures remains
unresolved, and no full campaign rerun was performed for this removal.

The following receipts describe the earlier resource-reporting interface. Its
operand-widening fix remains historical evidence; removal of the statistic
supersedes the active field contract and its overflow-specific feature tests.

Status: implementation-owned logger/build/format checks passed; full Driver
acceptance unmet (299/302, three reproduced campaign failures); fresh independent
verification pending.
Verified: 2026-10-15, native revision
`bc427b21461f258fd8de34232e01bb6be03cee39` plus the resource-total working-tree fix.
Origin: [native repair plan](../plan/2026-10-15-json-verification-resource-overflow.md).

## Numeric contract and repair

`Source/DafnyDriver/JsonVerificationLogger.cs` logs a scope from
`VerificationScopeResult` and serializes every `VerificationTaskResult.Result`.
The Boogie `VerificationRunResult.ResourceCount` constructor accepts Int32, also
reflected in `VerificationRunResultPartialCopy.ResourceCount` in
`Source/DafnyCore/DafnyConsolePrinter.cs` and the existing legacy adapter.

Promote each resource count before `Enumerable.Sum`:
`results.Sum(r => (long)r.Result.ResourceCount)`. Casting the already-computed
Int32 sum would leave the overflow unchanged. An `IReadOnlyList` has at most
Int32.MaxValue entries; summing that many Int32 values fits Int64 exactly.
The scope `resourceCount` remains a JSON number and per-VC values remain Int32.
No exception suppression, saturation, wrapping, resource limit, proof, or runtime
formatting change is involved.

## Public reproduction and commands

`Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs` constructs synthetic
public `VerificationRunResult` records with empty assertions and covered
elements, wraps them in `VerificationTaskResult`, and invokes
`JsonVerificationLogger.Initialize`, `LogScopeResults`, and `Flush`. The test
parses the emitted document; it does not call private serialization helpers,
consume evaluated inputs, or run a solver to accumulate billions of resources.

From `/workspace/dafnyutils/dafny`, run
`dotnet test Source/DafnyDriver.Test --no-restore --filter FullyQualifiedName~JsonVerificationLoggerTests --logger "console;verbosity=normal"`.
With cached dependencies this took about 2 seconds for the test phase, plus
native build time. Original source: 8 total, 2 controls passed and 6 failed with
`System.OverflowException` through `SerializeVerificationResult` and
`LogScopeResults`. Fixed source: 8/8 passed. Exact totals include 2147483648,
4294967294, and 6442450941. Controls preserve ordinary/empty scope output and
Invalid, TimeOut, and OutOfResource outcomes.

Native .NET SDK is `8.0.131`, runtime `8.0.31`, Boogie package `3.5.5`.
MSBuild/testhost local socket creation is blocked in the sandbox here; use the
approved escalated local execution path. The sandbox failure (`MSB1025`,
`SocketException (13)`) happens before test execution and is not a logger result.
Non-sensitive red/green logs are available in
`/workspace/tmp/native-json-overflow-benchmark/` for this workspace lifetime.

The owning Makefile's `exe` target builds `Source/Dafny.sln`. Its `format` target
uses `dotnet format whitespace`; scope the same command with `--include` when
unrelated native files have existing changes. Do not use a solution-wide mutation
to format only this repair.

`make exe` passed with 0 warnings / 0 errors in 14.69 seconds. Scoped whitespace
verification passed with 0 files formatted. The workspace loader reported a
missing matching metadata reference for `Source/DafnyRuntime/DafnyRuntime.csproj`;
the diagnostic log confirms Driver and Driver.Test configurations loaded.

The complete Driver command,
`dotnet test Source/DafnyDriver.Test --no-restore --logger "console;verbosity=normal"`,
finished with 299 passed and 3 failed out of 302 in 11.7089 minutes. Existing
`ClauseDependenciesTests.ClassifiesEveryBucket`,
`UncertifiedDependencyKeepsCalleeClauseUnchecked` (bucket 3), and
`InitialAdmissionTests.ScalarClosedCalleeUsesOriginalSources` (bucket 2) failed.
One exact three-method OR-filter recheck reproduced the same failures (3 passed,
3 failed, 6 total, 2.5999 minutes). Their cause is not established by this repair;
the broad suite is not green. The initial full and single recheck logs remain
separate in the maintenance artifact directory. No campaign fixture, limit,
shared cache, or campaign artifact was changed.

## Applicability and limits

This finding applies to the current native JSON scope logger. The text logger
also has an Int32 resource sum, and the JSON scope runtime currently aggregates
`RunTime.Seconds`. Those separate behaviors were reported and are unchanged.
The legacy JSON logger receives its aggregate from a different preexisting
result contract. This repair establishes serialization behavior for legal
synthetic VC records; it does not claim a benchmark, live run, image, proof,
or statistical result. Fresh independent acceptance is owned by another agent.

## Independent targeted acceptance — 2026-10-15

A fresh source-based verifier accepts the logger repair after8focused and42
independent boundary/outcome checks, with original and cast-after-Sum negative
controls reproducing overflow. Its source tracing finds the three recorded
ContractRuntime failing campaign paths bypass this aggregation; it leaves full
Driver acceptance unmet and makes no benchmark/image/proof-success claim.
Exact evidence is `/workspace/tmp/native-json-overflow-benchmark-independent/report.md`.
The linked plan remains in-progress for the broader full-suite criterion.
