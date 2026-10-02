# Static contract-runtime library

Status: done — implementation and fresh independent verification complete

Wiki: [static runtime library](../wiki/contract-testing.md#static-runtime-library-2026-10-02-implementation-checks)

## Objective and authorization

Move the task-independent Dafny declarations and C# runtime code that the PBT /
contract-runtime engine currently builds from string literals into checked-in
library files, so they are type-checked ahead of time (Dafny resolution in
tests, C# compiled by the test build). Task-specific harness and instrumentation
text stays generated. User request 2026-10-02 ("다프니 서브트리 수정"): Dafny
subtree only. Engine maintenance; no paid run, benchmark change, or dependency.

## Acceptance criteria

- `PbtRuntime.dfy` and `ContractDiagnosticBridge.dfy` exist as real files and a
  test resolves each standalone with zero errors.
- The Dafny text fed to the engine is byte-identical to the pre-refactor text
  (snapshot SHA-256 values reach `transformed-sources.json` and proof
  `sourceSetSha256`); pinned by a test using hashes captured before editing.
- `PbtRuntime.cs` and `ContractDiagnosticRuntime.cs` exist as real files and are
  compiled by `DafnyTestGeneration.Test` against `DafnyRuntime`.
- The six textual placeholders in `ContractStubRuntime.BridgeSource` are replaced
  by a generated `ContractRuntimeConfiguration` constants class; the fragile
  sequential `.Replace` chain is removed (only intended behaviour change: a user
  identifier such as `DATATYPE_SHAPES` can no longer corrupt the bridge).
- Library text ships as explicitly named embedded resources of
  `DafnyTestGeneration.dll`; a missing resource or a `\r` in the text fails loudly.
- Existing runtime recording/heap/prefix tests (exact JSONL assertions) and
  contract-entry tests pass unchanged.

## Non-goals

- Cosyn Python changes, exposing the library to the model, `--library`/doo
  packaging, benchmark/evaluator changes.
- Changing generated harness (`ContractDiagnosticMain`), obligation
  instrumentation, module names `PbtRuntime`/`PbtRandom`, or compile flags.

## Inspected evidence

Engine HEAD `12065bbe8` with substantial uncommitted pre-existing work (plans
2026-10-01-*, done) in `ContractRuntimeInstrumentation.cs`,
`ContractStubRuntime.cs`, campaign runner and tests. That working tree is the
baseline; library text is extracted from it and unrelated diffs are preserved.

- `ContractRuntimeInstrumentation.cs:8-49` `DafnySource` (Dafny `PbtRuntime`,
  `PbtRandom`), consumed by `ContractRuntimeCampaignRunner.cs:74` as snapshot
  `PbtRuntime.dfy` and by two TestGeneration tests.
- `ContractRuntimeInstrumentation.cs:55-218` `RuntimeSource` (C#
  `DafnyPbtRuntime`, `DafnyPbtBridgeRuntime`), appended in `BridgeSource`.
- `ContractStubRuntime.cs:53-914` ~850 lines of static C# (`DafnyContractRuntime`)
  with six placeholders filled at 909-914; lines 15-52 compute task shapes.
- `ContractHarnessBuilder.cs:213-234` `ContractDiagnosticBridge` extern class
  built by concatenation plus a `[..^2]` splice (20 members, no duplicates).
- C# bridge text is written to `ContractBridge.cs` and compiled by the generated
  csproj (`CsharpBackend.cs:91-102`, net8.0, Nullable and ImplicitUsings on).
- Precedent: `DafnyPipeline.csproj` embeds `DafnyRuntime.cs` compiled elsewhere.
- `DafnyTestGeneration.csproj` has `Nullable=enable` (library C# must not compile
  into the tool DLL); `DafnyTestGeneration.Test.csproj` references DafnyRuntime,
  no Nullable/ImplicitUsings.

## Change table

| File / symbol | Change | Why / gap without it | Validation |
| --- | --- | --- | --- |
| new `DafnyTestGeneration/ContractTesting/Library/PbtRuntime.dfy` | Exact `DafnySource` text, de-indented, single final LF | Static resolvable Dafny library | Resolve test, SHA pin |
| new `.../Library/ContractDiagnosticBridge.dfy` | Merged extern class (no leading LF, final LF) | Static declaration instead of spliced strings | Resolve test, golden equality |
| new `.../Library/PbtRuntime.cs` | `RuntimeSource` verbatim | Compiled ahead of time | Test-project build, recording tests |
| new `.../Library/ContractDiagnosticRuntime.cs` | Static part of `BridgeSource`; placeholders become `ContractRuntimeConfiguration.*` internal consts; explicit `using System.Linq` | Compilable; removes `.Replace` chain | Build, exact-JSONL tests |
| new `ContractTesting/ContractRuntimeLibrary.cs` | Internal loader: manifest resource by explicit name, UTF-8, throw if missing or contains `\r`; terminator-stripping variant | One fail-fast loader | Unit tests |
| `DafnyTestGeneration.csproj` | `Compile Remove` + `EmbeddedResource` with `LogicalName` for `Library/**` | Ship text in DLL, keep runtime types out of tool DLL | Load test |
| `ContractRuntimeInstrumentation` | `DafnySource` -> `static readonly` from resource; drop `RuntimeSource` const; `BridgeSource` appends `PbtRuntime.cs` resource | Use library | Pin test, recording tests |
| `ContractStubRuntime.BridgeSource` | Keep shape computation; emit library text + generated config class with same literal values | Task-specific part only | Config-block test, recording tests |
| `ContractHarnessBuilder.RuntimeSourceForFile` | `bridgeDeclaration = "\n" + resource` | Use library | Golden equality, `ContractEntryTests` |
| `DafnyTestGeneration.Test.csproj` + test-only `ContractRuntimeConfigurationStub.cs` | Compile linked `Library/*.cs` with stub constants | C# type-checked by build | `dotnet build` |
| new `DafnyTestGeneration.Test/ContractRuntimeLibraryTests.cs` | Standalone resolve of both `.dfy`; SHA pin of `DafnySource`; bridge golden; config literal escaping (quotes, backslash, non-ASCII) | Ahead-of-time checks and byte-identity proof | Test filter below |
| `wiki/contract-testing.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Record library location/invariants; index | Durable knowledge | Review |

## Risks and compatibility

- `const` -> `static readonly`: DafnyDriver inlined the old const; full solution
  build required (covered below).
- Hash identity depends on LF checkout; loader rejects `\r` instead of normalising.
- `make format` will format linked `Library/*.cs`; C# byte identity is not
  required (C# text is not hashed). `.dfy` files are not formatted; pin test
  catches drift.
- Static ctors in library types (exit hooks, `--pbt-*` arg reads) run only if
  touched; tests do not touch them.

## Validation (working directory `/workspace/cosyn/dafny`)

Before editing: dump old `DafnySource`, bridge fragment, and SHA-256 values to
the scratchpad for the pin/golden tests.

1. `dotnet build Source/Dafny.sln --no-restore -m:1` — succeeds.
2. `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntime|FullyQualifiedName~ContractEntryTests|FullyQualifiedName~ContractPhaseTimingTests'` — all pass.
3. `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeHeapTests|FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractRuntimePrefixTests'` plus a legacy `test-contracts` compile filter — all pass (~7 min).
4. `make format` — no unrelated churn.
5. From `/workspace/cosyn`: `make build-dafny` — packaging smoke.

Implementation by a Sonnet sub-agent; fresh independent Sonnet verification.

## Progress log

- 2026-10-02: plan written.
- 2026-10-02 implementation (Sonnet sub-agent), working tree on engine HEAD with the pre-existing uncommitted baseline:
  - Step 0 capture (text extracted from the working tree, cross-checked by a temporary xunit dump, later deleted):
    `ContractRuntimeInstrumentation.DafnySource` SHA-256 `8709e5ac34e7a4d0a71bac53d0ec70781d70df7c3e8d94b7c7c177190907420f` (2639 chars);
    bridge fragment inserted into sources (with its leading LF, 2724 chars) SHA-256 `eb8b901da0b17dba6bdb1f3fd46d21fbea8b0d8e61f8f7015634b53b9f6e4f6f`
    (confirmed to occur exactly once in the pre-refactor `RuntimeSource` output). Dumps live in the session scratchpad.
  - Before/after temp dump on a datatype+class sample: `ContractHarnessBuilder.RuntimeSource` output and `DafnySource` byte-identical (cmp);
    `ContractStubRuntime.BridgeSource` differs only by `using System.Linq;`, placeholder references, and the appended config class.
  - Created `ContractTesting/Library/{PbtRuntime.dfy, ContractDiagnosticBridge.dfy, PbtRuntime.cs, ContractDiagnosticRuntime.cs}`,
    `ContractRuntimeLibrary.cs`, csproj embedding, `ContractRuntimeConfigurationStub.cs`, `ContractRuntimeLibraryTests.cs` (6 tests); edited
    `ContractRuntimeInstrumentation`, `ContractStubRuntime`, `ContractHarnessBuilder`, both csprojs.
  - Deviations: (1) `ContractRuntimeLibrary` is `public` (test project has no InternalsVisibleTo; neighbours are public) instead of internal;
    (2) `PbtRuntime.cs` uses `new System.Span<byte>(bytes, o, n)` instead of `bytes.AsSpan(o, n)` and `ContractDiagnosticRuntime.cs` adds `using System.Linq;`
    so they compile without ImplicitUsings (usings cannot follow the namespace when `PbtRuntime.cs` is appended); (3) `.gitattributes` gains
    `Library/* text eol=lf` so checkouts cannot introduce `\r`; (4) the C# config class is appended after the library text (usings stay first).
  - Commands (cwd `/workspace/cosyn/dafny`): `dotnet build Source/Dafny.sln --no-restore -m:1` succeeded, 0 errors (3 warnings: CS0162 x2 from the
    constant-folded `RuntimeReferences` branches and CS0618 `ISequence.Elements`, all from pre-existing library code);
    `dotnet test Source/DafnyTestGeneration.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntime|FullyQualifiedName~ContractEntryTests|FullyQualifiedName~ContractPhaseTimingTests'` 231/231 passed (incl. 6 new);
    `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeHeapTests|...RecordingTests|...PrefixTests'` 106/106 passed (7m22s);
    legacy `test-contracts` compile path (`ContractCompilerWorker.CompileAsync`, runtimeReferences=false) via `--filter 'FullyQualifiedName~ContractExternExecutionTests'` 4/4 passed;
    `make format` ran with no change to the `git status`/`git diff --stat` set (compared before/after); post-format rebuild and the TestGeneration filter again 231/231.
  - Not run by the implementer: `make build-dafny` from `/workspace/cosyn` (packaging smoke) is left to verification.
- 2026-10-02 coordinator baseline: `DafnySource` and bridge fragment independently reconstructed from source captured before the refactor
  (session scratchpad `coordinator/`); SHA-256 values match the pinned `8709e5ac…` and `eb8b901d…`.
- 2026-10-02 independent verification (fresh Sonnet agent, no implementer context), cwd `/workspace/cosyn/dafny`:
  `dotnet build Source/Dafny.sln --no-restore -m:1` succeeded; TestGeneration filter above 231/231;
  `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter 'FullyQualifiedName~ContractRuntimeRecordingTests|FullyQualifiedName~ContractExternExecutionTests'` 26/26;
  `make build-dafny` (cwd `/workspace/cosyn`) rc=0; reflection on `Binaries/DafnyTestGeneration.dll` shows exactly the four
  `DafnyTestGeneration.ContractTesting.Library.*` resources and loaded Dafny text equals the coordinator baselines byte-for-byte;
  `dotnet Binaries/Dafny.dll resolve` accepts both library `.dfy` files and rejects injected type/parse errors. All seven requirements PASS.
  Heap/prefix Driver suites (106/106) and `make format` were run only by the implementer.
- Remaining limits: the loader's `\r` rejection branch has no test; the `.Replace`-chain removal (user identifiers such as `DATATYPE_SHAPES`)
  is argued from code, not tested. Not committed.
