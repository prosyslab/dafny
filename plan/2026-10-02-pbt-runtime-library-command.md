# PBT runtime library command and located parse errors

Status: done — implementation and fresh independent verification complete (long DafnyDriver suites rerun only by implementer)

## Objective and authorization

Engine half of exposing the generator API to the model (user decision
2026-10-02: reference exposure plus error positions; no prepare-only mode, no
model-run standalone resolve). Cosyn half:
`/workspace/cosyn/plan/2026-10-02-pbt-runtime-library-exposure.md`. Depends on
[Runtime/SMT naming](2026-10-02-pbt-runtime-smt-naming.md) (final library text).

## Acceptance criteria

- New `dafny contract-runtime-library` command writes the embedded
  `PbtRuntime.dfy` resource to stdout byte-for-byte (no arguments, exit 0). The
  output minus its final LF equals `ContractRuntimeInstrumentation.DafnySource`.
- Generator/draft parse errors in `ContractRuntimeSourcePreparation`
  (`ParseDeclarations`) report `<.top-down-pbt relative path>:line:col` like the
  existing resolution diagnostics, instead of location-free joined messages.
- No request/result DTO or status change; existing tests pass.

## Non-goals

`--prepare-only` mode, new statuses, changing resolution diagnostics, benchmark changes.

## Inspected evidence

- Precedent command: `Source/DafnyDriver/Commands/SourceFingerprintCommand.cs`,
  registered in `DafnyNewCli.cs:53-54`.
- `ContractRuntimeSourcePreparation.cs:113-119` joins parse messages without
  location; resolution errors already mapped via `Diagnostics(reporter, sourceMap)`
  in `ContractRuntimeCampaignRunner.cs:86-89, 938-948`.
- Unresolved generator/draft errors return status `unsupported` with `reason`.

## Change table

| File / symbol | Change | Why | Validation |
| --- | --- | --- | --- |
| new `DafnyDriver/Commands/ContractRuntimeLibraryCommand.cs`, `DafnyNewCli.cs` | Print `ContractRuntimeLibrary.Read("PbtRuntime.dfy")` | Single source of truth for Cosyn's model-visible copy | New DafnyDriver test: output equals resource, SHA pin |
| `ContractRuntimeSourcePreparation.ParseDeclarations` | Include mapped path:line:col per parse error | Model can locate syntax errors | New DafnyDriver test with a syntax-error generator |
| `wiki/contract-testing.md`, `plan/INDEX.md` | Note command and located parse errors | Knowledge | Review |

## Validation (cwd `/workspace/cosyn/dafny`)

1. `dotnet build Source/Dafny.sln --no-restore -m:1`
2. `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeLibraryCommand|FullyQualifiedName~ContractRuntimeCheckTests'`
3. `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntime'`
4. `make format`

## Progress log

- 2026-10-02: plan written.
- 2026-10-02: implemented `ContractRuntimeLibraryCommand` (+ `DafnyNewCli` registration, writes UTF-8 bytes to the
  standard output stream); `ParseDeclarations` now reports `<supplied path>:line:col: message` per error using the
  snapshot's own path and token position (the source map covers prepared sources only, so it is not reused; the
  standalone parse needs no mapping). Parse failure is still a `NotSupportedException` that `test-contracts` maps to
  `unsupported`, so the new test asserts the exception message from `ContractRuntimeCampaignRunner.RunAsync`.
- Tests added: `ContractRuntimeLibraryCommandTests.PrintsEmbeddedRuntimeLibraryBytes` (runs `dotnet DafnyDriver.dll`),
  `ContractRuntimeCheckTests.LocatesGeneratorSyntaxError`.
- Results (cwd `/workspace/cosyn/dafny`): build 0 errors; DafnyDriver.Test filter 129 passed (10m53s);
  DafnyTestGeneration.Test `ContractRuntime` 195 passed; `make format` no churn; `make build-dafny` from
  `/workspace/cosyn` 0 errors; `dotnet Binaries/DafnyDriver.dll contract-runtime-library` exit 0 and `cmp` equals
  `PbtRuntime.dfy`.
- Wiki `wiki/contract-testing.md` updated.
- 2026-10-02 coordinator closure: fresh independent verification (no implementer context) PASS, no functional defects:
  build ok; DafnyTestGeneration filter 232/232; DafnyDriver `ContractRuntimeRecordingTests|ContractExternExecutionTests|ContractRuntimeLibraryCommand`
  27/27; `contract-runtime-library` output cmp-identical to `Library/PbtRuntime.dfy` (no BOM, LF only); Cosyn `read_pbt_runtime_library`
  against the built fork dafny equals the file; `COSYN_CONTRACT_INTEGRATION=1 pytest tests/test_goal_pbt_integration.py` 4 passed.
  Long suites ContractRuntimeCheckTests/HeapTests/PrefixTests were skipped by user direction in independent verification
  (implementer: 237/237 and 129/129). Three inaccurate role comments (Write, SerializeNamed, Check) fixed afterwards; pins now
  `b858e89c…aaa0` (DafnySource) and `5d179a05…e0be` (inserted declarations); implementer reran library 7/7, Driver 23/23, cmp ok.
  Known gaps: no test asserts the Runtime/Smt member placement; role comments are text-only.
