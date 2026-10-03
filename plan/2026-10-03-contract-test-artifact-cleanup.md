# Contract test artifact cleanup

Status: done — implementation and fresh independent verification complete

## Objective and authorization

User request 2026-10-03: the contract test harness must clean up its campaign
directories automatically. `/workspace/tmp` holds ~6,400 leftover
`contract-runtime-*` directories (46 GB total in `/workspace/tmp`) because no
contract test deletes what it creates. Test-only change; follows
[contract test fixture merge](2026-10-03-contract-test-fixture-merge.md).

## Acceptance criteria

- Directories created by contract tests are deleted when the owning fixture or
  test finishes: `CampaignHarness` campaign directories (`contract-campaign-*`),
  `CliBoundaryTests` (`contract-runtime-cli-*`), `ContractRuntimeRecordingTests`
  fixture (`contract-runtime-recording-*`), and
  `DafnyTestGeneration.Test/ContractRuntimeHeapQueryTests` (`contract-readonly-dependency-*`).
- No directory is deleted while another test can still read it (cached campaigns
  shared across classes are owned by whoever deletes last, or deleted at process end).
- Setting `DAFNY_CONTRACT_TEST_KEEP_ARTIFACTS=1` keeps the directories for debugging.
  Assertion messages keep naming the campaign directory.
- A full `~Contract` run leaves no new matching directories under `/workspace/tmp`.

## Non-goals

Production temp directories (`TestContractsCommand.SuperviseRuntimeAsync`
leaves `dafny-runtime-check-*` in the temp directory; reported separately),
deleting existing leftovers (needs user confirmation).

## Change table

| File | Change | Validation |
| --- | --- | --- |
| `DafnyDriver.Test/ContractRuntime/CampaignHarness.cs` | Track created campaign directories; delete on fixture dispose or process exit per ownership; keep with env var | `~Contract` run, directory count before/after |
| `DafnyDriver.Test/ContractRuntime/CliBoundaryTests.cs`, `ContractRuntimeRecordingTests.cs`, `DafnyTestGeneration.Test/ContractRuntimeHeapQueryTests.cs` | Delete their directories on completion | same |
| `DafnyDriver.Test/ContractRuntime/InitialAdmissionTests.cs` | List `HeapProofReuseTests.PositiveCell` (used by a test but previously unlisted, shared with another class) in `Campaigns()` | same |
| `wiki/contract-testing.md` | Note cleanup and keep switch in the test-pattern section | review |

## Validation (cwd `/workspace/cosyn/dafny`)

1. `dotnet build Source/Dafny.sln --no-restore -m:1`
2. Count `/workspace/tmp/contract-*` before and after
   `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~Contract'` and
   `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~Contract'`: all pass, no new directories.
3. Same Driver run with `DAFNY_CONTRACT_TEST_KEEP_ARTIFACTS=1`: directories kept.
4. `make format`

## Progress log

- 2026-10-03: plan written.
- 2026-10-03 implementation: design = per-fixture reference counting in `Campaign` (AcquireAsync/ReleaseAsync; last
  releaser removes the cache entry and deletes the directory; a later request reruns). Justification: `HeapProofReuseTests.PositiveCell`
  is used by `InitialAdmissionTests`, so specs are shared across classes; refcounting never deletes under a reader. A first
  attempt (delete all at `ProcessExit`) left 65 directories after a Driver+TestGeneration run (hook ineffective under `dotnet test`)
  and was dropped. Second finding: 4 failed/cancelled campaigns left partial directories, so `Start` deletes its directory when not
  completed. Third: `PositiveCell` was awaited by `InitialAdmissionTests` without being in its `Campaigns()` (unreleased leak);
  added. `ContractExecutionProcess.RunAsync` kills the process tree and awaits exit before returning, so nothing writes at deletion.
  `ContractArtifacts` (in CampaignHarness.cs, Driver.Test) honours the keep switch; `ContractRuntimeHeapQueryTests` has a tiny local
  copy (no project reference between test projects).
- Validation: build 0 errors. Final run: before 71 dirs; Driver `~Contract` 254 passed; TestGeneration `~Contract` 499 passed;
  after 71 (no increase). Keep run (Driver, switch=1): 71 -> 154 (+83: 80 campaign, 2 runtime-cli, 1 runtime-recording), 254 passed.
  `make format`: no churn beyond the five edited files. Removal of the 154 verification directories was denied by the permission
  system; list saved in the session scratchpad `verification-dirs.txt`; they are all created by my runs and need removal by the user.
- 2026-10-03 independent verification (fresh agent): PASS on all requirements; only test files/plan/wiki changed; no awaited
  spec missing from its fixture's `Campaigns()` (scripted check plus manual review of six non-literal arguments); failure path
  deletes partial directories without masking the original exception; Driver `~Contract` 254/254 twice, TestGeneration 499/499,
  zero new directories. Notes: a deletion IOException inside `finally` could mask an original failure (theoretical); temp
  directories under `Path.GetTempPath()` from ContractPhaseTimingTests/ContractEntryTests not examined.
- Coordinator: older leftovers under /workspace/tmp were removed with user approval (contract-*/dafny-runtime-check-* and other
  temporary directories; experiment/ and registered worktrees kept).
