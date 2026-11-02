# Contract screen omitted-body identity

Status: done (native source phase)

## Scope and ownership

Native maintenance in this repository at baseline `949a62450c8a415f0c1a7a7252bbcd9a7c6acd83`. Parent plan: [fold child screen comparison](/workspace/plan/2026-11-02-fold-child-screen-comparison.md). Layers: native source preparation and local regression tests; no dataset, scorer, provider, wire, proof policy or benchmark change. Only current native source/tests/build configuration and this task's plans are inputs. No benchmark candidates, solutions, SDK logs or history are read.

## Goal and pass criteria

Defer omitted method names until successful resolution. Preserve pre-removal source positions, native qualified identities, contract-only projection, source option rejection and reporter-based resolution failure handling. A generic named class containing a method body alongside global Child must project Child and retain both original body identities/ranges without a null dereference. Resolution errors must remain reported with no projection or invented identity.

## Reviewed code and design

Reviewed ContractScreenSourcePreparation.ParseAsync/ParseProjectedAsync and raw visitors; ContractSourceSnapshot.ParseAsync and its snapshot filesystem; MemberDecl.FullDafnyName and its resolution-only EnclosingClass; TopLevelDeclWithMembers.SetMembersBeforeResolution; ContractCallableSelector; ContractScreenService.NativeBackend.InspectAsync; ContractPhaseRecorder.MeasureAsync; focused test helpers and project configuration. MemberDecl.FullDafnyName documents that it is available only after resolution. At the baseline the discovery loop dereferenced it before resolution. The baseline projected loop also constructed a local omitted list which was never returned; both early reads are removed by this change.

Capture original body ranges and native Method references before clearing bodies. Resolve discovery, check reporter errors first, then materialize qualified names. On failed resolution return original spans and no omitted identity records, with a null projection; the service already rejects the reporter errors before using projection or metadata. Remove unused projected-loop omission metadata while retaining body removal and authoritative projection.OmittedBodies.

## Planned changes

| Exact file/symbol | Change | Why / missing behavior | Verification |
| --- | --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs: ParseAsync, ParseProjectedAsync.VisitModule | Capture body offsets before removal, create names after successful discovery resolution; remove unused premature projected identity | Named class methods have unresolved owners before resolution | Synthetic original CLI repro; focused in-memory tests; source review |
| Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs | Add named ambient class body/projection scenario and reporter resolution error scenario, each with an intention comment | Existing global typed-local controls miss qualified ambient identities | Parent runs class filter after coordinated build |
| plan/2026-11-02-contract-screen-omitted-body-identity.md and plan/INDEX.md | Record implementation, evidence, commands and scope | Owning repository workflow | Narrow diff and index check |
| wiki/contract-screen-omitted-body-identity.md and wiki/INDEX.md | Record resolution identity lifecycle and diagnostic limits after verification | Reusable AST phase contract | Source-backed note linked to plan |

## Checks, prerequisites and approvals

Working directory for native checks: `/workspace/tmp/fold-native-screen-recovery/dafny-native`. All checks are free local maintenance, using synthetic sources only. No paid runs or publication by this worker. Parent owns all builds; fresh `verify_omitted_body_identity` agent owns independent unit/CLI verification. This implementation worker owns records and read-only formatting only.

Original baseline reproduction was executed by parent with preserved clean `949a62450c8a415f0c1a7a7252bbcd9a7c6acd83` binaries using `test-contracts /workspace/tmp/fold-native-screen-recovery/omitted-body-identity/inspect.json --screen-contract`. Receipt: [original-bounded-repro.json](/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/original-bounded-repro.json). Expected original failure was confirmed (see execution record).

Actual parent driver command: `dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -p:SkipFocusedTestAssets=true`. Actual parent test-assembly command: `dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -p:SkipFocusedTestAssets=true`. The environment uses .NET SDK 8.0.133. Actual fresh verifier selected test command: `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore -p:SkipFocusedTestAssets=true --filter 'FullyQualifiedName~DafnyTestGeneration.Test.ContractScreenSourcePreparationTests' --logger 'console;verbosity=normal'`. All five selected tests passed without a solver, native compilation, staging or filesystem writes in test execution; the runner required approved local-socket escalation.

Read-only narrow formatter command: `dotnet format whitespace --folder --include Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs --verify-no-changes`. This folder mode omits the unsupported `--no-restore` option. Also run `git diff --check` and `find plan wiki -type f ! -name '*.md'`.

Independent native CLI controls use `dotnet Binaries/net8.0/DafnyDriver.dll test-contracts <fixed-request.json> --screen-contract`, with bounded fixed request/result/receipt artifacts and summary under `/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification`. Use synthetic `Ambient<T>.Helper` plus global Child only. Inspect positive (`requires x >= 0; ensures y == x + 1`) and contradictory (`ensures y == x + 1 && y == x + 2`) sources separately and use each inspection's own binding. Screen positive x=0 (admissible/realizable), positive x=-1 (precondition_rejected/not_checked), and contradictory x=0 (admissible/unrealizable). Verify exact source digests, each source-set identity and binding echo, protocol status, target identity, case/input echo, counts, native query reason/provenance identities and effective option identities. Each decided query must have its actual identity; no reused or fabricated binding across sources. These are local native solver integration controls, distinct from unit tests and universal proofs.

The existing development link is `Binaries/net8.0/z3 -> /workspace/cosyn/_build/dafny/Binaries/z3`; top-level `Binaries/z3` absence is expected. Do not stage/copy a runtime, compile a contract program, create wrapper temporary directories, synchronize files or hash runtime trees. Existing native toolchain identity hashing remains unchanged.

Tests trace: Reporter uses null readers/writers; Prepare creates one tiny immutable source and hash in memory; ContractSourceSnapshot closes parser reads over SnapshotFileSystem and in-memory directory enumeration; ProgramResolver runs name/type checking only; no recorder instantiated, compiler, verifier, solver, directory creation, durable writes, fixture, setup or teardown. Existing parser may read packaged immutable resources; no new disk work. Aggregate additions: two tiny source strings and two preparation calls.

## Risks and non-goals

Do not set resolver owner fields, synthesize fallback names, catch syntax failures, prune discovery declarations or weaken contract/option/proof checks. Do not change public records or wire schema. Preserve body offsets before lazy AST ranges change. Resolver failures cannot authenticate symbol identities and intentionally produce no omission records; public invalid-input handling remains reporter-based. No commits, pushes, pin changes, containers or provider actions by this worker.

## Execution record

- Baseline clean; HEAD verified as above. Local rules read: root/native AGENTS.md, native CLAUDE.md, root tests/AGENTS.md; no plan/wiki scoped rules or native Source scoped rules present.
- Implementation prepared in the two planned C# files. Discovery body ranges are captured with Method references; qualified names materialize after successful resolution. Projected pass no longer builds dead omission metadata. Two in-memory scenarios added; existing three controls unchanged.
- Generic synthetic source and fixed JSON request written to `/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/{ambient.dfy,inspect.json}`; original runtime execution requested from parent before any production rebuild. No CLI, build or test was run by this worker.
- `git diff --check` in the owning repository: pass. Manual scoped format check matches .editorconfig (2 spaces, LF, existing brace style). `find plan wiki -type f ! -name '*.md'`: no output. No unrelated records read.
- [Reusable lifecycle finding](../wiki/contract-screen-omitted-body-identity.md) records verified development behavior with source-backed scope/limits; index mechanically appended and current entry updated.
- Parent confirmed the bounded clean-949 generic reproduction: native exit 6 after 0.644960 seconds, stdout 0 bytes, stderr 3468 bytes, NullReferenceException and MemberDecl.FullDafnyName frame; 64 KiB output cap, 20-second timeout and process tree reaped. Receipt: `/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/original-bounded-repro.json`. Earlier exit-153 resource-limit probe ended before the CLI exception and is not counted as the native failure.
- Fresh independent source review found no concrete defect and approved testing. Source remained unchanged after handoff; verification was performed from current repository state by the separate verification agent.
- Parent driver build first returned sandbox exit 1, zero errors, 0.57 seconds without a compiler diagnostic (`driver-build.log`); the exact approved-environment retry passed exit 0 in 21.66 seconds with eight existing warnings (`driver-build-retry.log`). Both logs are temporary artifacts under the omitted-body-identity scratch directory.
- Parent test-assembly build passed exit 0 in 10.08 seconds with 32 existing warnings and zero errors (`test-build.log`). Read-only narrow format command above passed exit 0 with no output on SDK 8.0.133.
- Fresh verifier passed all five selected preparation tests (zero failed) in 2.1402 seconds. Versions: .NET SDK 8.0.133, runtime 8.0.33, VSTest 17.8.0, xUnit adapter 2.4.3+1b45f5407b. The tests use the prebuilt assembly with no restore/build.
- Four direct CLI calls (positive inspect/screen and contradictory inspect/screen) all returned exit 0, completed status and empty stderr. Synthetic sources contained `Ambient<T>.Helper` alongside global Child. Positive x=0 was admissible/realizable; positive x=-1 was precondition_rejected/not_checked; separately inspected contradictory x=0 was admissible/unrealizable. Strict source hashes, each source's own binding and echo, case/input echo, exact counts, query identities, effective options and native query reasons were checked. Query counts were 2, 2 and 3 respectively. Solver: Z3 4.16.0.
- Development CLI reports version 0.0.0.0. It is not the pinned release. Verification provenance is baseline commit plus exact current source and assembly hashes in [verification summary](/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/summary.json), a temporary artifact. Native diagnostic text reported protocol truncation; independently checked structured states and identities are the evidence.

Exact direct CLI commands, all from this owner repository and all exit 0:

- `dotnet Binaries/net8.0/DafnyDriver.dll test-contracts --screen-contract /workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/positive-inspect-request.json`
- `dotnet Binaries/net8.0/DafnyDriver.dll test-contracts --screen-contract /workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/positive-screen-request.json`
- `dotnet Binaries/net8.0/DafnyDriver.dll test-contracts --screen-contract /workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/contradictory-inspect-request.json`
- `dotnet Binaries/net8.0/DafnyDriver.dll test-contracts --screen-contract /workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/contradictory-screen-request.json`

Each command's fixed request/result/stderr path, runner versions, source/assembly hashes and counts are recorded in the linked summary. Artifacts are 16 fixed bounded files, including four empty stderr files; no runtime staging, wrapper temporary directories, durable writes, tree copying or tree hashing were added.

## Close

The native source acceptance criteria are fulfilled: independent source review, both native builds, all five focused unit scenarios, four direct native CLI controls, narrow formatting and diff checks pass. No full suite or final implementation proof was run; these finite maintenance controls establish neither benchmark efficacy nor universal correctness. No benchmark candidates, paid providers, containers or scored experiments were accessed or run. Final diff matches the planned two source files and four owner record files. Plan/wiki contain only Markdown. No code changes followed verification.

The source phase has no remaining blocker. The user's earlier native publication and pin-recovery authorization remains an ongoing corrective follow-up owned by the root agent. Root will check remote state and use a normal fast-forward publication only, then manage pins/images and any later authorized evaluation. This worker has not staged, committed, published or changed pins. Verified development binaries are not a deployed or pinned release.
