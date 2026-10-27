# Canonical source-authoring schema for both extern policies

Status: done
Date: 2026-10-26
Parent: [Cosyn schema consolidation](../../plan/2026-10-26-pbt-canonical-schemas.md)

## Objective, evidence and acceptance

Repository maintenance authorized by the request to consolidate Cosyn PBT schemas.
Read AGENTS/CLAUDE and the existing source-authoring request/model implementation.
Authoring wire schema2 currently recognizes only explicit native policy; draft
authoring already exists under legacy schema1. Reuse the same runtime policy
implementation to accept explicit draft or native policy under schema2 without
changing their semantics. Keep exact manifest-policy binding and reject malformed
schema/policy combinations. Preserve pre-existing dirty native changes.

## Change table

| Files | Change, necessity and validation |
| --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourceAuthoring.cs` | Accept both existing explicit policy values under schema2; no admission/proof or source authority changes. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSourceAuthoringTests.cs` | Focused in-memory schema2 draft/native and mismatched-manifest controls using existing helpers; no runtime builds, temporary directories or synchronization in tests. |
| This plan and `plan/INDEX.md` | Record actual checks and ownership; durable API findings stay in parent Cosyn wiki. |

## Validation, risks and approvals

Inspect test helpers and available SDK/build assets. From native root run scoped
`dotnet test Source/DafnyTestGeneration.Test --filter
FullyQualifiedName~ContractRuntimeSourceAuthoringTests` with bounded in-memory
selection if any cases invoke external compilers. Use scoped `dotnet format`
verification and a production project build if prerequisites are available.
No dependency or new approval is required. No benchmark, scoring, proof weakening,
image publication, live experiment or commit is included. Native legacy transport
acceptance need not be removed to eliminate duplicate Python DTOs.

## Results

Implemented the schema2 explicit-draft validation branch without changing effective
extern execution, exact manifest matching, runtime preparation or native legacy
wire acceptance. Added an in-memory extern-draft prepare/extract roundtrip and
updated the policy-change regression to reject a mismatched manifest while both
requests use schema2. The full affected class covers preserved native preparation
and malformed legacy-mode controls.

Validated from `/workspace/cosyn/dafny` on native HEAD
`3eeedd010d05c9bcc556c79bc6f62447380b58ad` plus the extensive pre-existing dirty
working tree and this narrow change. SDK `/usr/bin/dotnet --version`: `8.0.131`;
test runner version `17.8.0`; existing NuGet/build assets were available.

- `/usr/bin/dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -p:SkipFocusedTestAssets=true -v:minimal`
  initially exited1 with zero reported errors/warnings and no actionable diagnostic.
- `/usr/bin/dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -p:SkipFocusedTestAssets=true -m:1 -nr:false -v:normal`
  passed in16.20s,33 warnings in existing sources, zero errors. This scoped
  production/test assembly build is separate from the in-memory test bodies.
- `/usr/bin/dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore -p:SkipFocusedTestAssets=true --filter FullyQualifiedName~ContractRuntimeSourceAuthoringTests --logger 'console;verbosity=minimal'`
  first aborted before executing tests because the sandbox denied the runner's
  localhost socket. The identical command passed after approved execution
  escalation:26 passed, zero failed/skipped,1s test duration. Test helpers were
  traced through snapshot parsing, AST preparation and extraction; no runtime
  compilation, temporary directory creation or synchronization is invoked.
- `/usr/bin/dotnet format whitespace Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --verify-no-changes --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourceAuthoring.cs Source/DafnyTestGeneration.Test/ContractRuntimeSourceAuthoringTests.cs --verbosity quiet`
  passed.
- `/usr/bin/dotnet format whitespace Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore --verify-no-changes --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourceAuthoring.cs --verbosity quiet`
  passed.
- `git diff --check` and `find plan wiki -type f ! -name '*.md' -print` passed;
  no non-Markdown plan/wiki artifacts were found.

No durable findings beyond the parent canonical API record: this only enables an
existing native policy under the canonical authoring wire version. No native wiki
page is needed. No provider, experiment, solver, generated-runtime execution,
image or benchmark checks were run or claimed. No active process or new scratch
artifact remains.

## Fresh independent verification

A separate fresh-context verification agent inspected source authority, exact
manifest equality, policy forwarding and all focused test helper paths, then
independently ran from the same native root:

- `/usr/bin/dotnet build Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore -p:SkipFocusedTestAssets=true -m:1 -nr:false -v:minimal`:
  passed with zero warnings/errors.
- The focused `dotnet test --no-build --no-restore` command recorded above:
  26 passed, zero failed/skipped. Its first sandbox attempt failed before running
  tests on a localhost socket denial; approved escalation passed identically.
- `/usr/bin/dotnet format whitespace Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore --verify-no-changes --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourceAuthoring.cs Source/DafnyTestGeneration/ContractTesting/ContractRuntimeAuthoringModels.cs --verbosity quiet`:
  passed.
- `/usr/bin/dotnet format whitespace Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --verify-no-changes --include Source/DafnyTestGeneration.Test/ContractRuntimeSourceAuthoringTests.cs --verbosity quiet`:
  passed.
- Scoped diff/Markdown-only audits passed, no blocking issue found. Exact
  original/prepared source, packet and policy authority remain intact. Successful
  native extraction is reviewed in source rather than a dedicated positive test;
  draft2 prepare/extract is exercised. No downstream proof/runtime claim follows.

The native acceptance criteria are met; broader Python/API closure is recorded
in the parent plan.
