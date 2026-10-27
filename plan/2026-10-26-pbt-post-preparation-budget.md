# Preserve sampling time after PBT preparation

Status: done
Date: 2026-10-26
Parent: [counterexample loop](../../plan/2026-10-26-pbt-counterexample-loop.md)

## Objective and evidence

R13's fourth child campaign returns `inconclusive`, with every population counter
and obligation evaluation count zero. The retained `pbt-4.json` under the R13
root revision001/attempt001 PBT receipts records a 231782 ms request and 156624 ms
tool duration. This is operator maintenance evidence, never input to a fresh
evaluated model run. The active R13 image and run remain unchanged.

Read-only source inspection establishes the zero-sample path: the runner starts
its clock before parsing/proof/transformation/compilation, then reserves half the
original total before sampling. Its first-ordinal cutoff is 115891 ms, so slow
preparation can skip every sample while aggregate time remains. Every launched
ordinal otherwise produces a Sample and increments a classification bucket;
the all-zero receipt therefore proves no sample was scheduled. Exact per-phase
preparation times are not present in the receipt and are not claimed.

Existing `GeneratorProofBudgetMilliseconds` already allocates from remaining
time. Reuse the runner's existing absolute clock, request limits, cancellation
and sample timeout. No new arbitrary timeout or larger experiment budget.

## Scope and acceptance

After successful compilation, compute one fixed sampling deadline from the
remaining aggregate campaign time. Retain the existing half/half split, applying
it to that remainder; round sampling time down so classification retains at least
half. A preparation time beyond half the original total must still leave a
positive sampling allowance when at least two milliseconds remain. No expired
deadline may permit a sample. Do not recompute a moving half-remaining cutoff on
each iteration. Each process stays bounded by the existing sample limit and the
remaining fixed sampling allowance. Classification retains the original absolute
campaign deadline, cancellation and all evidence validity checks.

Non-goals: default-argument instrumentation (separate finding), new result schema,
changed generator-proof budget, relaxed admission/contract checks, benchmark or
provider changes, live image mutation, new packages, or a claim of a counterexample.
No heuristic fallback or forced sample after timeout is permitted.

## Change table

| Files or symbols | Change and necessity | Validation |
| --- | --- | --- |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`: sampling deadline helper and loop | Select the fixed cutoff after preparation from remaining time; current subtraction can suppress all sampling before total expiry. Preserve existing process/classification limits and result accounting. | Independent source review; pure clock/budget regression cases; later operator evidence belongs to the parent plan. |
| `Source/DafnyDriver.Test/ContractRuntime/SamplingBudgetTests.cs` | Small process-free tests for late preparation, fixed cutoff, expiry, odd/sub-millisecond split boundaries and large int timeouts. | Full call-path audit; invoke only pure helper logic, with no directory, file, synchronization, campaign or solver activity. |
| This plan and `plan/INDEX.md` | Preserve evidence, exact scope, commands and remaining validation. | Diff and Markdown-only audit. |
| `wiki/pbt-trusted-sources.md` and `wiki/INDEX.md` | Record the generic phase-budget boundary and its limits after acceptance. | Source references, actual validation and link to this plan; no benchmark bodies or witness inputs. |
| Parent Cosyn PBT plans/index/wiki | Track active R13 and the separate source repair without claiming deployment or samples. | Exact status and frozen-run boundaries. |
| `/workspace/tmp/pbt-post-preparation-budget-20261026/native-test-build.py` | Reuse the prior bounded native test-build worker for the Driver test project, fourteen exact production inputs and the new test file. Pins remain unset until reviewed source freeze; coordinator alone dispatches it. | AST/static review, exact command/output bounds, exclusive artifacts and pre/post source identity. |

## Validation and implementation boundary

Read `AGENTS.md`, `CLAUDE.md`, Makefile, current runner/proof-budget helper and
existing pure Driver tests. No additional directory instructions or planning
template exist in these scopes. Implementation and verification remain independent.

From `/workspace/cosyn/dafny`, scoped formatting:
`dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs Source/DafnyDriver.Test/ContractRuntime/SamplingBudgetTests.cs`.
Separate operator test assembly build, in a named tmux session with bounded log:
`dotnet msbuild Source/DafnyDriver.Test/DafnyDriver.Test.csproj -nologo -t:Build -verbosity:minimal -maxCpuCount:1 -nodeReuse:false -p:SkipFocusedTestAssets=true`.
Then, after complete call-path audit:
`dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~SamplingBudgetTests' -v:minimal`.
Run `git diff --check`. Never run the real-campaign Driver fixtures as unit checks.
Use `/workspace/tmp/pbt-post-preparation-budget-20261026/` for bounded operator
artifacts (600-second build, 256 KiB output maximum); any write there requires the
environment's normal escalation. No artifacts belong under plan/wiki.

Source acceptance precedes CLI publication and any replacement image, which
remain separately tracked parent operator actions. R13 must continue against its
already captured immutable image; no new evaluated run reuses its candidate.
The Driver test-project build normally updates its host `Binaries` dependency
products because `DafnyDriver.csproj` has that output path. Record this build
effect; it is not accepted CLI publication, and the live image cannot observe it.

## Implementation handoff

The scoped source and pure tests were frozen on 2026-10-26. The runner now
computes one absolute sampling deadline after compilation by assigning half of
the remaining campaign time to sampling. Every ordinal consumes that fixed
allowance, while the existing absolute campaign deadline still governs result
classification.

`SamplingBudgetTests` covers the R13 late-preparation boundary, the difference
between a fixed cutoff and a moving recomputation, expired campaigns, odd and
tiny remainder rounding, and near-`int.MaxValue` arithmetic. Its complete call
path is the pure `SamplingDeadlineMilliseconds` helper; it creates no campaign,
file, directory, process, solver, synchronization operation or native output.

Executed from `/workspace/cosyn/dafny`:

- `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs Source/DafnyDriver.Test/ContractRuntime/SamplingBudgetTests.cs` exited 0, with the workspace-load warning emitted by the formatter.
- Scoped `git diff --check` for the runner, test and plan files exited 0.
- The Markdown-only `plan/` and `wiki/` audit found no violations.

The implementation handoff itself performed no build, test, native campaign,
image publication or live-run mutation. Independent review subsequently accepted
the source and audited the pure test path. The coordinator's bounded test-project
build exited 0 with every declared source pin matched and produced
`DafnyDriver.Test.dll` SHA-256
`83cf812da957012c42dde562d5475af3be2309ad49371a90df99d75008f7aec9`.
The focused `SamplingBudgetTests` run used that exact assembly and source-bound
Driver, Core and TestGeneration dependencies; it passed 9/9 in 8 ms with zero
failures or skips. The independent `dotnet format whitespace --verify-no-changes`
and scoped diff check both exited 0. Structured results and bounded logs are under
`/workspace/tmp/pbt-post-preparation-budget-20261026/`.

This closes source/local acceptance only. The build updated ordinary host
`Binaries` products as expected, but it did not publish an accepted CLI, replace
an image, mutate R13 or run a campaign. Publication and later runtime evidence
remain owned by the parent plan. Frozen source SHA-256 identities:

- `ContractRuntimeCampaignRunner.cs`: `90fb1858e2c20cb7e17275d7714a965d0bb8c1f1702f5244273691b511834826`
- `SamplingBudgetTests.cs`: `78ba1c5a4b186b69113a50293fb8675b8097ac8e02dd406e57334728424e130f`

## Risks and approvals

Sampling must receive a fixed allowance, or repeated halving could consume
classification time. Arithmetic must not overflow at valid int timeout limits
or grant time after expiry. Preserving the declared overall deadline and validity
checks is required even when fewer samples are classified. The continuing user
goal authorizes this demonstrated tool repair; no package, policy expansion or
additional approval round is required. The bounded build, nine pure tests and
scoped format/diff checks pass; CLI publication, image adoption and campaign
evidence remain outside this plan.
