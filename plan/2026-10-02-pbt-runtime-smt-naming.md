# PBT instrumentation Runtime/SMT naming

Status: done — implementation and fresh independent verification complete (long DafnyDriver suites rerun only by implementer)

## Objective and authorization

Replace the ambiguous "Bridge" naming in PBT / contract-runtime instrumentation
with role names, per user direction 2026-10-02: instrumentation that requests SMT
from the parent process is named `Smt`; runtime-check / observation parts are
named `Runtime`. User chose the three-way split:

| Role | Dafny | C# namespace |
| --- | --- | --- |
| Generator random stream (model-facing API) | module `PbtRandom`, class `Source`, `New()` (unchanged names) | `DafnyPbtRandom` (was `DafnyPbtRuntime`) |
| Runtime checks, observation recording, value/heap encoding | module `PbtRuntime` (was class `PbtBridge`) and the non-SMT part of `ContractDiagnosticBridge` | `DafnyPbtRuntime` (was `DafnyPbtBridgeRuntime` and part of `DafnyContractRuntime`) |
| SMT RPC to parent (`Realize`, `Choose`, `Output`, `CheckPrecondition`, `StartTarget`, `EndTarget`, `EndTargetValue`, private `Request`) | separate Smt extern class | `DafnyPbtSmt` (class `Oracle`) |

Follows [static contract-runtime library](2026-10-02-static-contract-runtime-library.md).
Engine maintenance only; no paid run or dependency. Committed together with the
library exposure work ([library command](2026-10-02-pbt-runtime-library-command.md)
and Cosyn `plan/2026-10-02-pbt-runtime-library-exposure.md`).

## Acceptance criteria

- No `Bridge` identifier remains in contract-testing instrumentation code,
  generated Dafny/C# text, library files, or their tests (engine helpers such as
  `BridgeName`, `BridgeSource`, `BridgeDeclaration`, generated `ContractBridge.cs`
  are renamed by role). Unrelated upstream Dafny uses are untouched.
- SMT RPC operations live only in the Smt class; runtime checks/observation/
  encoding only in Runtime; RNG only in `DafnyPbtRandom`.
- Model-facing Dafny `PbtRandom.Source` API (module, class, method names,
  signatures, contracts) is unchanged.
- Observation JSONL contents/order, RPC request/response file protocol, verdicts,
  seeds and random stream are unchanged: existing exact-JSONL recording, heap,
  prefix, extern-execution and entry tests pass without expectation changes
  (other than identifiers in generated source text).
- Library `.dfy` files still resolve standalone; SHA pins are intentionally
  updated to the new text and the old values recorded here.
- Reserved-name checks cover the new generated names; module-name filters
  (`"PbtRuntime" or "PbtRandom"`) include any new module.

## Non-goals

Behaviour changes, new features, renaming user-visible JSON fields or statuses,
renaming `ContractTesting` namespaces/classes unrelated to the bridge role.

## Inspected evidence

- `Library/PbtRuntime.cs`: `DafnyPbtRuntime.Source` (RNG) and
  `DafnyPbtBridgeRuntime.Bridge` (JSONL check recorder; no SMT).
- `Library/ContractDiagnosticRuntime.cs` `DafnyContractRuntime.ContractDiagnosticBridge`:
  value/heap serialization and observation (`Capture`, `Register`, `Snapshot`,
  `Serialize`, `SerializeNamed`, `InstantiateShape`, ...) mixed with file RPC
  `Request` (`.rpc.*.request/.response`) used by `Realize`, `Choose`,
  `CheckPrecondition`, `StartTarget`, `EndTarget`; parent handles requests in
  `ContractStubRuntime.cs:136` area by SMT realization.
- `Library/PbtRuntime.dfy` `PbtBridge` externs map `Serialize`/`SerializeNamed`/
  `InstantiateShape` onto `DafnyContractRuntime.ContractDiagnosticBridge`.
- Identifier counts in engine C# (incl. tests): `ContractDiagnosticBridge` 48,
  `BridgeName` 37, `Bridge` 37, `PbtBridge` 28, `BridgeSource` 6,
  `ContractBridge` 3, `DafnyPbtBridgeRuntime` 2, `BridgeDeclaration` 2.
- Campaign runner parses `PbtBridge.Check("` from source lines; transformer and
  runner filter modules by name; legacy harness inserts the bridge class inline
  into each user module (callers unqualified), guarded by a reserved-name check.
- Cosyn Python/tests/docs reference none of these names (grep).

## Change table

| File / symbol | Change | Why | Validation |
| --- | --- | --- | --- |
| `Library/PbtRuntime.cs` | Split: `DafnyPbtRandom.Source`; runtime recorder into `DafnyPbtRuntime` | Role names | Build, recording tests |
| `Library/ContractDiagnosticRuntime.cs` (rename file by role, e.g. `PbtRuntimeObservation.cs`) | Non-SMT part into `DafnyPbtRuntime`; RPC part into new `Library/PbtSmt.cs` `DafnyPbtSmt.Oracle`; shared state access made explicit (no behaviour change) | Separate SMT from runtime | Build, extern/recording tests |
| `Library/PbtRuntime.dfy` | `PbtBridge` -> Runtime-named class; extern targets updated; `PbtRandom` extern -> `DafnyPbtRandom` | Role names | Resolve test, new SHA pin |
| `Library/ContractDiagnosticBridge.dfy` (rename by role) | Inline declarations split into Runtime and Smt extern classes | Role names | Resolve test, new SHA pin |
| `ContractHarnessBuilder`, `ContractRuntimeObligationTransformer`, `ContractRuntimeInstrumentation`, `ContractStubRuntime`, `ContractHeapFactory`, `ContractRuntimeSourcePreparation`, `ContractRuntimeCampaignRunner`, `ContractCompilerWorker`, other referencing files | Update generated call sites, constants, helper names, generated file name, module filters, reserved-name checks | Consistency | Full filters below |
| `DafnyTestGeneration.Test`, `DafnyDriver.Test` references, `ContractRuntimeConfigurationStub.cs`, `ContractRuntimeLibraryTests` | Update identifiers and SHA pins | Tests follow names | Same |
| Library `.dfy` files (every extern class, module, function, method) | Add `//` comments stating each API's role: who calls it (generator author, generated runtime-check instrumentation, legacy harness), what it records or requests, return meaning, and Runtime vs Smt role (user request 2026-10-02) | User cannot tell what each API does | Resolve tests; SHA pins updated to the commented text |
| `wiki/contract-testing.md`, `plan/INDEX.md` | Record role names; mark old names superseded | Knowledge | Review |

Exact Dafny extern class names for the Runtime/Smt roles are chosen during
implementation to avoid resolution clashes (module `PbtRuntime` is opened into
user modules in the runtime path; legacy declarations are inlined into user
modules) and recorded in the progress log.

## Validation (cwd `/workspace/cosyn/dafny`)

1. `dotnet build Source/Dafny.sln --no-restore -m:1`
2. `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntime|FullyQualifiedName~ContractEntryTests|FullyQualifiedName~ContractPhaseTimingTests'`
3. `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeHeapTests|FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractRuntimePrefixTests|FullyQualifiedName~ContractExternExecutionTests|FullyQualifiedName~ContractRuntimeCheckTests'`
4. `grep -rn 'Bridge' Source/DafnyTestGeneration/ContractTesting Source/DafnyDriver/ContractTesting` and contract tests: no remaining role-ambiguous uses.
5. `make format`

## Progress log

- 2026-10-02: plan written.
- 2026-10-02 (implementation): chosen names.
  - C#: `DafnyPbtRandom.Source` (`PbtRandom.cs`); `DafnyPbtRuntime.Checks` (`PbtChecks.cs`, was `DafnyPbtBridgeRuntime.Bridge`);
    `DafnyPbtRuntime.Observation` (`PbtObservation.cs`, non-SMT part of `ContractDiagnosticBridge`: encoding, heap, observation records;
    internal `Encode/Shape/SnapshotHeap/ApplyHeap/Decode/ConcreteTypes/Unsupported` for Oracle); `DafnyPbtSmt.Oracle` (`PbtSmt.cs`:
    `Request`, `Realize`, `Choose`, `Output`, `CheckPrecondition`, `StartTarget`, `EndTarget`, `EndTargetValue`, `pureChoices`, target state,
    plus `Begin`/`Input`/`End` because `End` sends the "precondition" request using `currentCall`/`currentInputs`).
    `ContractRuntimeProfile` stays in `DafnyContractRuntime` (`ContractRuntimeProfile.cs`), as does generated `ContractRuntimeConfiguration`.
  - Dafny: `PbtRuntime.PbtChecks` (was `PbtBridge`; its `Serialize/SerializeNamed/InstantiateShape` externs now target `DafnyPbtRuntime.Observation`),
    inlined `PbtObservation` and `PbtSmt` (`PbtObservation.dfy`, `PbtSmt.dfy` replace `ContractDiagnosticBridge.dfy`). No new Dafny module, so the
    `"PbtRuntime" or "PbtRandom"` filters are unchanged; legacy reserved-name check now covers `MainName`, `ObservationName`, `PbtSmt`; runtime-path check
    is the existing `Pbt*` member-prefix rule.
  - Engine: `BridgeName` -> `ContractHarnessBuilder.ObservationName`/`SmtName` (call sites routed per method), `BridgeDeclaration` -> `RuntimeDeclaration`,
    `BridgeSource` -> `RuntimeSource` (both classes), `ContractBridge.cs` -> `ContractRuntime.cs`, `PbtBridge.Check("` parser -> `PbtChecks.Check("`.
    Generated C# order: `PbtObservation.cs` (only file with usings) + `ContractRuntimeProfile.cs` + `PbtSmt.cs` + config (+ `PbtChecks.cs` + `PbtRandom.cs`
    in runtime path); later files are fully qualified. No JSON/observation payload contains class names (grep).
  - SHA pins (intentional): DafnySource old `8709e5ac34e7a4d0a71bac53d0ec70781d70df7c3e8d94b7c7c177190907420f` -> new
    `b5e8603401bee02aebc593b5f720d8eb3c7a9871ffa038dcab762ba979c329c2`; bridge fragment old
    `eb8b901da0b17dba6bdb1f3fd46d21fbea8b0d8e61f8f7015634b53b9f6e4f6f` -> single pin over `"\n"+PbtObservation.dfy+"\n"+PbtSmt.dfy`
    `9bd9517b77b1b11d597915e695a6761f71f7a4d575ee195ee4d0234fdbd502e9`. Tests renamed by role; standalone resolve tests kept (one per dfy file).
  - Deviation: the single bridge pin became one pin over the concatenated inserted text (two files now). Wiki updated.
- Validation: build succeeded 0 errors (3 pre-existing warnings); DafnyTestGeneration.Test filter 232/232 passed.
- 2026-10-02 scope addition (user): role comments on every API in the library `.dfy` files.
- 2026-10-02 user decision: the legacy fixed-input harness (ContractHarnessBuilder diagnostic main, ContractCompilerWorker.CompileAsync, Smt RPC) and Cosyn `contract_testing` policy will be removed in a separate follow-up plan after this combined commit; keep the Smt naming here.
- 2026-10-02 (role comments, user scope addition): added `//` role comments (caller, behaviour, parameters, Runtime/Smt role) to every
  module/class/member of `PbtRuntime.dfy`, `PbtObservation.dfy`, `PbtSmt.dfy` (PbtRandom contracts stated in plain words), derived from the C#
  and transformer/harness call sites; `///` summaries on all C# library classes (`ContractRuntimeProfile` added). **Final SHA pins** (replace the
  intermediate values above): DafnySource (`PbtRuntime.dfy` minus final LF) `987d17811031f89008c18d605c921764aacee4bc77aa80d84177d08825d0d61f`;
  inserted declaration `"\n"+PbtObservation.dfy+"\n"+PbtSmt.dfy` `2d39b381e35692320258411f8ea51e9d030d0a99a622dc39fd4dab33a5f9b0ac`.
- Final validation (cwd `/workspace/cosyn/dafny`): `dotnet build Source/Dafny.sln --no-restore -m:1` succeeded, 0 errors (3 pre-existing warnings);
  DafnyTestGeneration.Test filter 232/232 passed; DafnyDriver.Test filter 237/237 passed (10.98 min; an earlier run was killed by my own
  tooling timeout/pkill, not a test failure); `grep -i bridge` over scoped dirs/tests: no matches; `make format` ran with `git diff --stat`
  unchanged (22 files, 1094+/1339-, no churn).
- 2026-10-02 (comment fixes after independent verification: Write throws outside observed heap/only first frame violation recorded; SerializeNamed extra runtime-field pairs; Check writes complete then exits): new SHA pins DafnySource `b858e89cca9f646e394eb5049cc3b1e481a6c4a07ca8bbfc269cfbbfa335aaa0`; inserted declaration `5d179a05858cd3389ac0d69cdf45ec80f530e3b1cd9418e7cf86ad7a813ae0be` (replace `987d1781...` and `2d39b381...`; also pinned in `DafnyDriver.Test/ContractRuntimeLibraryCommandTests`).
- 2026-10-02 coordinator closure: fresh independent verification (no implementer context) PASS, no functional defects:
  build ok; DafnyTestGeneration filter 232/232; DafnyDriver `ContractRuntimeRecordingTests|ContractExternExecutionTests|ContractRuntimeLibraryCommand`
  27/27; `contract-runtime-library` output cmp-identical to `Library/PbtRuntime.dfy` (no BOM, LF only); Cosyn `read_pbt_runtime_library`
  against the built fork dafny equals the file; `COSYN_CONTRACT_INTEGRATION=1 pytest tests/test_goal_pbt_integration.py` 4 passed.
  Long suites ContractRuntimeCheckTests/HeapTests/PrefixTests were skipped by user direction in independent verification
  (implementer: 237/237 and 129/129). Three inaccurate role comments (Write, SerializeNamed, Check) fixed afterwards; pins now
  `b858e89c…aaa0` (DafnySource) and `5d179a05…e0be` (inserted declarations); implementer reran library 7/7, Driver 23/23, cmp ok.
  Known gaps: no test asserts the Runtime/Smt member placement; role comments are text-only.
