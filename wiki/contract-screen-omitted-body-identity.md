# Contract screen omitted-body identities

Status: verified in development; native source phase complete, not deployed or pinned.
Verification date: 2026-11-02. Baseline: `949a62450c8a415f0c1a7a7252bbcd9a7c6acd83`; working changes are uncommitted.
Plan: [omitted-body identity](../plan/2026-11-02-contract-screen-omitted-body-identity.md).

## Resolution lifecycle

`Source/DafnyCore/AST/Members/MemberDecl.cs` declares EnclosingClass as FilledInDuringResolution. Its FullDafnyName property explicitly documents availability only after resolution and dereferences EnclosingClass. A global default-class target can hide this lifecycle error: an unrelated named class method can still have no owner in a fresh parse. Raw traversal alone does not make resolved identity properties safe.

`Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs` captures original syntax ranges and Method references before removing ordinary method/lemma bodies. It resolves that discovery program, checks reporter errors, then creates ContractScreenOmittedBody using native qualified names. This preserves original offsets while using the resolver to authenticate symbol ownership. The projected pass returns discovery omission metadata from projection.OmittedBodies; constructing its former unused local omission list only introduced another early resolved-name read.

On discovery resolution error, preparation returns the parsed program, original spans, empty omission records and no projection. No qualified identity is invented from unresolved syntax. ContractScreenService.NativeBackend.InspectAsync checks reporter errors first and maps them to the existing source_parse_or_resolution invalid-input failure. This note does not claim every invalid source has stable omission metadata.

## Evidence and limits

Focused in-memory tests in `Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs` add a named Ambient.Helper body alongside global Child. They require both original body ranges and qualified names while retaining only Child in the projection, and cover an unresolved ambient parameter type without a projection or manufactured identity. Existing typed-local and source-options rejection controls remain unchanged.

The generic original-runtime request and source are temporary maintenance artifacts at `/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/inspect.json` and `ambient.dfy`. They contain synthetic source only. Parent confirmed that the clean baseline generic request reproduced exit 6 with a MemberDecl.FullDafnyName NullReferenceException in 0.645 seconds; stdout was empty and stderr was 3468 bytes. The bounded receipt is `/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/original-bounded-repro.json` (temporary). This failure concerns parser/resolver phase use; it is not a contract decision. Fresh independent source review found no concrete source or test defect.

The exact scoped command `dotnet format whitespace --folder --include Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs Source/DafnyTestGeneration.Test/ContractScreenSourcePreparationTests.cs --verify-no-changes` passed exit 0 on SDK 8.0.133. Parent driver and test-assembly builds passed with zero errors (21.66 and 10.08 seconds, respectively; eight and 32 existing warnings). A fresh independent verifier passed all five preparation tests in 2.1402 seconds using prebuilt assemblies and no restore.

Four direct development CLI calls, with `Ambient<T>.Helper` alongside global Child, passed exit 0 with empty stderr. The positive source produced admissible/realizable at x=0 and precondition_rejected/not_checked at x=-1. A separately inspected contradictory-postcondition source produced admissible/unrealizable at x=0. Each source used its own inspection binding. Strict source/binding, input echo, count, query provenance and effective-option checks passed, with case query counts 2, 2 and 3. Solver version was Z3 4.16.0.

Detailed exact commands, result paths, counts and current source/assembly hashes are in [verification summary](/workspace/tmp/fold-native-screen-recovery/omitted-body-identity/verification/summary.json), a temporary maintenance artifact. The native development CLI reports version 0.0.0.0; provenance uses the baseline commit and those exact hashes. This is verified development behavior, not a pinned or deployed native release. Protocol diagnostic text was truncated; structured result states and identity fields were independently asserted.

These are finite synthetic maintenance checks. No full test suite, final implementation proof, benchmark efficacy/scoring experiment, container or live provider run supports this note. Earlier user authorization for native publication and pin recovery remains an ongoing root-owned follow-up, subject to a remote-state check and normal fast-forward publication. This note does not claim that follow-up is complete.
