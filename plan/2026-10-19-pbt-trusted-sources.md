# Bind PBT declaration trust to exact source snapshots

Status: done

## Objective and authorization

The user explicitly requests skipping PBT re-verification of the trusted core
library while retaining concrete-input, type, heap, predicate and candidate/helper
checks. This native child belongs to the [Cosyn plan](../../plan/2026-10-19-pbt-trusted-core.md).
The original PBT implementation was based on
`bef89d2244ddd9a3bc898ad97252d82049ff5cdd`; it has since been rebased onto
integration base `29da48b6c47e9c8484c8a2818e2be2032ad14206`, which includes
DefinitionAnalysis visibility additions. The current native validation target is
`0e5338b75e4094be20e005d79abcc750cf69a44e`. No benchmark, scoring, provider,
dependency or early-child change is authorized.

## Acceptance criteria and design

Add optional exact trusted source identities to schema-v2 runtime requests.
Validate uniqueness and exact membership in the immutable source snapshots.
A default checker remains strict. Explicit trust omits only declaration proof
obligations and declaration trust audits for those original source identities;
source ownership and transitive untrusted dependencies remain checked. Keep
runtime/type/heap/predicate checks separate and intact. Include the trust set in
scope/cache identity. Do not grant trust by module names, draft attributes or
unbound paths.

## Changes and validation

| Files or symbols | Change, reason and unmet behavior | Check |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs` | Optional source identity list; otherwise no wire trust boundary exists. | In-memory DTO/default/identity checks. |
| `Source/DafnyTestGeneration/ContractTesting/ContractSourceSnapshot.cs` | Retain existing snapshot checks and add exact unique trusted identity membership validation. | In-memory path/digest/duplicate rejection. |
| `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs` | Bind trusted originals, preserve dependency traversal and skip only their audits/native checks; bind scope and certificate context. | In-memory parsed scopes, default strict, axiom audit skipping only under trust, untrusted transitive dependencies and trust-separated cache identity. |
| `Source/DafnyTestGeneration/ContractTesting/ContractInitialTypeProof.cs` | Compare campaign trust identity against its checker where the campaign DTO is available. | Static call-path audit plus heap-provenance checks; preserve existing input/type/heap checks. |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs` | Carry a defensive copy of campaign trusted-source identities as internal heap-check provenance; include it in initial-preparation attestation and compare it at preparation, matching, and observed-proof entry. Keep `ContractTestRequest` unchanged. | Memory-only strict/trusted cross-context preparation tests; changed/replayed provenance must fail closed. |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | Validate and pass explicit trust without modifying input admission. | Static integration review and driver build. |
| `Source/DafnyTestGeneration.Test/ContractTrustedSourcesTests.cs` | Focused memory-only regressions; no solver files, generated code, native compilation, temporary directories or sync calls inside tests. | Filtered test command after separate operational build; exact identity and same-path AST rejection, strict assume/extern rejection, axiom trust, transitive helper checks, module-name lookalike, cache separation, false-predicate reduction, and initial/observed cross-context rejection. |
| This plan/index, `wiki/pbt-trusted-sources.md` and wiki index | Record public trust contract, validation and limits for native maintainers. | Diff/link and Markdown-only audits. |

Read owner AGENTS/CLAUDE and governing instructions first. Reuse existing native
source/identity helpers rather than introducing a second snapshot parser. Inspect
all test fixtures and callees before execution. Run a separate operational
`dotnet build Source/DafnyDriver/DafnyDriver.csproj` and
`dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj`
with existing prerequisites; then run
`dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractTrustedSourcesTests`.
Record versions, commands, results and missing prerequisites. Fresh independent
verification accepted the original native source before the integration rebase;
the combined tree requires fresh validation and review. No paid experiments or
existing disk-heavy test suites.

### Validation on the original native tree

The initial builds and tests used .NET SDK 8.0.131 and Gradle 8.14/JVM 17.0.19
from `/workspace/tmp/pbt-trusted-core-20261019/cosyn/dafny`, branch
`codex/pbt-trusted-core-native-01a13fc5`, starting at
`bef89d2244ddd9a3bc898ad97252d82049ff5cdd`. Scratch `Directory.Build.props` redirected intermediate/output paths; a scratch
`Directory.Build.targets` set package outputs. The first offline test build reached
the existing Java runtime Gradle target but its default wrapper cache under
read-only `/home/vscode/.gradle` lacked the executable and libraries. After the
official wrapper distribution was prepared in task scratch, the successful
commands were:

```sh
dotnet restore Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --source /workspace/tmp/pbt-trusted-core-20261019/nuget-empty -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:RestoreIgnoreFailedSources=true -v:minimal
GRADLE_USER_HOME=/workspace/tmp/pbt-trusted-core-20261019/gradle dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -v:minimal
dotnet restore Source/DafnyDriver/DafnyDriver.csproj --source /workspace/tmp/pbt-trusted-core-20261019/nuget-empty -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:DirectoryBuildTargetsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.targets -p:RestoreIgnoreFailedSources=true -v:minimal
GRADLE_USER_HOME=/workspace/tmp/pbt-trusted-core-20261019/gradle dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:DirectoryBuildTargetsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.targets -v:minimal
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractTrustedSourcesTests -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:DirectoryBuildTargetsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.targets -v:minimal
```

The first test restore attempt failed during the MSBuild restore-project-reference
walk (`DafnyTestGeneration.Test` → `DafnyCore.Test` → `DafnyCore`) without an
emitted error diagnostic. The serial restore using the scratch-only empty NuGet
source and redirected build properties then passed; the Driver restore also
passed. The first Java runtime build attempt used the default Gradle wrapper cache
under read-only `/home/vscode/.gradle`, which lacked the required wrapper
distribution. The official Gradle 8.14 distribution was prepared in task scratch;
no repository dependency or build rule changed.

Both final builds passed. The test project build had zero errors and four existing
warnings in unrelated runtime/test files; the driver build had zero warnings and
errors. The focused filter passed 15/15, no skips. Its ordinary sandbox attempt
was blocked before tests by VSTest's local TCP socket permission (`SocketException
(13): Permission denied`). The authorized socket run initially found one test
expecting the Dafny declaration label `Function` where the parser reports
`Predicate`; the assertion was corrected and the final filtered run passed.
Fresh independent review accepted that native source and independently passed all
15 native focused tests. These logs and the compiled test assembly are under
`/workspace/tmp/pbt-trusted-core-20261019/`; no solver was invoked by the focused
tests. No Dafny proof, benchmark or performance claim is made.

### Integration revalidation

The native patch was rebased onto `29da48b6c47e9c8484c8a2818e2be2032ad14206`;
current HEAD is `0e5338b75e4094be20e005d79abcc750cf69a44e`. The code diff relative
to that base contains only the planned trusted-source request/checker/runtime
binding changes and `ContractTrustedSourcesTests.cs`; the base supplies the
separate DefinitionAnalysis visibility additions. On 2026-10-19, the test and
Driver builds were rerun serially on this HEAD using the prepared task-scoped
Gradle cache and scratch output paths:

```sh
GRADLE_USER_HOME=/workspace/tmp/pbt-trusted-core-20261019/gradle dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -v:minimal
GRADLE_USER_HOME=/workspace/tmp/pbt-trusted-core-20261019/gradle dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:DirectoryBuildTargetsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.targets -v:minimal
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractTrustedSourcesTests -m:1 -p:DirectoryBuildPropsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.props -p:DirectoryBuildTargetsPath=/workspace/tmp/pbt-trusted-core-20261019/Directory.Build.targets -v:minimal
```

The test build passed with zero errors and the same four unrelated existing
warnings; the Driver build passed with zero warnings/errors; the focused in-memory
filter passed 15/15 with no skips. VSTest used the approved local-socket execution
path. Logs are `/workspace/tmp/pbt-trusted-core-20261019/build-test-integration.log`,
`build-driver-integration.log`, and `test-focused-integration.log`. `git diff
--check` passed; the only uncommitted files are this plan/wiki and their indexes.
Fresh independent review accepted the combined source and independently reran the same 15 memory-only tests: 15 passed, zero failures/skips (186 ms).

## Risks and progress

Trusted library declarations become explicit host assumptions; incorrect host
trust configuration can make declaration certificates unsound. Keep the boundary
exact and default empty. Preserve the unrelated dirty canonical `expecto` checkout.
Commit only this native child and point the focused Cosyn main commit at it.

Implemented: optional exact source identities; default-strict declaration audits;
trusted-origin audit/native-check omission; scope trust hashing; and internal heap
check provenance bound through initial preparation, request attestation and
observed construction. The focused memory-only test class covers exact membership,
ownership, audit boundaries, transitive dependencies, cache identity, false
concrete predicates, and trust-context mismatch. `git diff --check` passes.

The original native tree passed its builds and 15 focused in-memory tests and was
independently accepted. The integration tree at HEAD
`0e5338b75e4094be20e005d79abcc750cf69a44e` also passes both builds and 15 focused
tests; fresh independent review accepted the combined source and passed all 15 tests. No performance or benchmark success
claim is made.
