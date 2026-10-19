# Resolved function body visibility

Status: done (source and independent local acceptance; parent owns delivery)
Date: 2026-10-19
Owner: embedded native Dafny repository; integration plan: [/workspace/plan/2026-10-19-opaque-function-proof-reuse.md](/workspace/plan/2026-10-19-opaque-function-proof-reuse.md).

## Objective and acceptance

Expose optional resolved `bodyVisibility` for definition analysis, with effective `isOpaque`, sorted unique canonical `revealedFunctions` and `referencedDeclarations`, and conservative `revealsAllFunctions`. Traverse the complete resolved declaration dependency closure, including contracts, bodies, included declarations, generated wrappers and typed fuel. Explicit wildcard, unrecognized reveal targets, or unmappable relevant declaration dependencies fail closed via `revealsAllFunctions`. Span-only results omit metadata. Preserve existing definition selection and direct dependency output. Parent authorized the additional closure names on 2026-10-19 to preserve transparent-function consumers through frozen wrappers.

## Evidence, scope, and compatibility

Inspected `DefinitionAnalysis.cs`, `HideRevealStmt.cs`, `OpaqueMemberRewriter.cs`, `AutoRevealFunctionDependencies.cs`, `FuelAdjustment.cs`, `BoogieGenerator.cs`, parser/resolver test patterns, Makefile and native instructions. Existing `DefinitionNode` includes can omit contract expressions; the new closure therefore follows original resolved AST declarations and IHasReferences, explicit call targets and typed attributes rather than the filtered dependency list. Generated auto-reveals carry `revealedFunction` on the target method and can have no OffsetMembers. No source keyword or function-name heuristics.

This is maintenance, with no evaluated/private inputs. No specification, proof, evaluator, dataset, scoring or reporting changes. No packages, paid runs, global binaries, existing original-checkout edits, or commits. User-authorized integration feature needs no additional approval. Metadata is additive and omitted where unavailable.

The implementation caches direct AST facts by declaration identity within one analysis document, then computes each root's conservative graph closure. No global/cross-run cache. The initial full `make exe` failed before compiler diagnostics (1.31s, zero warnings/errors); narrow project diagnosis is in progress.

Serial `-m:1` removes the silent MSBuild project-reference failure. The narrow project then reaches unrelated Java runtime compilation, whose Gradle wrapper cannot write its read-only home-cache lock; the command was interrupted (130). Parent approved copying the single unchanged prebuilt `/workspace/cosyn/dafny/Binaries/netstandard2.0/DafnyRuntime.dll` to isolated `Binaries/netstandard2.0/` as a build prerequisite. Build changed Core freshly with `dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore -m:1 -nodeReuse:false -p:BuildProjectReferences=false`, then Core.Test with the equivalent flags. Do not claim a full solution/Java build. Package restore uses existing cache only and a nonexistent local source, no network installs.

## Change table

| Files/symbols | Change and necessity | Validation |
| --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.cs` | Optional result property and resolved result attachment; otherwise consumers cannot obtain compiler-authored visibility. | Focused in-memory tests, build, whitespace format |
| `Source/DafnyCore/DefinitionAnalysis.BodyVisibility.cs` | Native record and conservative resolved AST closure with canonical referenced declaration names, including actual reveal/fuel semantics; otherwise opacity filtering can reuse invalid proofs or miss consumers through frozen wrappers. | Focused behavior tests, including full referenced closure |
| `Source/DafnyCore.Test/DefinitionBodyVisibilityTests.cs` | In-memory parse/resolve normal, transitive, wildcard, auto-reveal, fuel and span controls; no disk or solver/build path in tests. | Filtered no-build/no-restore dotnet test |
| `wiki/function-body-visibility.md`, `wiki/INDEX.md` | Document wire shape, semantic boundary and bounded validation. | Source comparison and link checks |
| This plan and `plan/INDEX.md` | Track outcomes and handoff limitations. | Diff review |

## Validation

Working directory: `/workspace/tmp/opaque-function-proof-reuse/native` (clean starting revision `bef89d224`). Run `make exe` as maintenance build, with existing .NET8/package/tool prerequisites; expected full solution build. If unrelated optional project prerequisites block it, record failure and run `dotnet build Source/DafnyCore.Test/DafnyCore.Test.csproj` for the supported narrow project. Run `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionBodyVisibilityTests` after build; expected all focused tests pass without skips. Inspect helper call paths for in-memory parse/resolve, no temporary directories, source writes, solver or build. Format touched C# via existing dotnet whitespace formatter and verify diff. Inspect all plan/wiki trees for non-Markdown violations. Fresh independent verification is coordinated by parent; implementation findings are not independent evidence.

## Risks and remaining work

Conservative over-approximation may prevent reuse, intentionally. Graph cycles require identity guards; enclosing class/module attributes must be included without traversing sibling members. Failed/unresolved analysis must not claim known opacity. Implementation, local checks and owner wiki are complete. Independent reviewer final rerun and parent integration remain; no native commit has been created.

## Independent review finding

The reviewer identified that resolved `Expression.Children` omits instantiated `ComponentTypes`, while generic ApplySuffix nodes discard original syntax. The full closure must explicitly traverse resolved component/result types and normalized type proxies to retain subset/type-alias declarations and their constraint dependencies. Add an in-memory generic subset regression (`G<S>()`, where S's constraint calls Leaf), then freshly rebuild Core/Test and rerun focused cases. This repairs the already-required closure scope; no dependency or protocol scope expansion.

The first corrected22-case run passed20 and failed two no-wildcard controls: native `OpaqueMemberRewriter.AnnotateRevealFunction` intentionally creates an intrinsic ArrowType with no resolved declaration for its member-selection type. Treat that actual typed intrinsic as a shape whose source dependencies are its arguments/results; retain conservative handling for ordinary null declaration references. Do not use name heuristics.

## Final local validation and handoff

Working directory for all commands: `/workspace/tmp/opaque-function-proof-reuse/native`.
Base: `bef89d224`; final state has only the planned source/test/plan/wiki delta, no generated tracked changes. SDK `dotnet --version`: 8.0.131. Outputs remain in the isolated worktree; the original native checkout, installed binary and running bundles were not changed.

| Command | Result and scope |
| --- | --- |
| `make exe` | Failed1 before compiler diagnostics (parallel MSBuild,1.31s, zero warnings/errors); not a passing full build. Log `native-build.log`. |
| `dotnet build Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore -v:normal` | Failed NETSDK1004: fresh isolated assets file missing. |
| `dotnet restore Source/DafnyCore.Test/DafnyCore.Test.csproj --ignore-failed-sources --source /workspace/tmp/opaque-function-proof-reuse/unused-package-source -p:NuGetAudit=false` | Passed using existing packages; no new packages/dependencies or network source. Log `native-restore.log`. |
| Narrow build without serial flag | Failed before compiler diagnostics; diagnostic log confirms MSBuildNodeCount64 and GetTargetFrameworks project-reference failure. |
| Narrow build with `-m:1` | Parser generation passed; unrelated Java Gradle wrapper failed opening read-only cache lock. Interrupted130. No Gradle install/download or project safeguard change. |
| `dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore -m:1 -nodeReuse:false -p:BuildProjectReferences=false` | Passed final changed Core,16.22s,0 warnings/errors; one unchanged prebuilt runtime DLL is the explicit isolated prerequisite. Log `native-core-only-build.log`. |
| `dotnet build Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore -m:1 -nodeReuse:false -p:BuildProjectReferences=false` | Passed final Test build,1.34s,0 warnings/errors. Log `native-tests-build.log`. |
| `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionBodyVisibilityTests` | Final22/22 passed,0 skipped,149ms. Test runner required approved local socket execution after restricted listener denial. Log `native-visibility-tests.log`. Earlier18/20 checkpoints are historical; corrected type-edge run20/22 failed false-positive controls, preserved in `native-visibility-tests-type-edge-failure.log`, then native intrinsic ArrowType handling fixed them. |
| `cmp Binaries/net8.0/DafnyCore.dll Source/DafnyCore.Test/bin/Debug/net8.0/DafnyCore.dll` | Passed: tests loaded exact freshly built changed Core. |
| `dotnet format whitespace . --folder --verify-no-changes --include Source/DafnyCore/DefinitionAnalysis.cs Source/DafnyCore/DefinitionAnalysis.BodyVisibility.cs Source/DafnyCore.Test/DefinitionBodyVisibilityTests.cs` | Passed final formatting. Project-workspace formatter was interrupted while loading; folder mode uses repository editorconfig and avoids unrelated project loads. `--folder --no-restore` was rejected by tool, then corrected; no formatting failure remains. |
| `git diff --check` | Passed. |
| Recursive plan/wiki extension inspection | No non-Markdown files in owner plan/wiki trees. |

All named logs live under `/workspace/tmp/opaque-function-proof-reuse/`, outside plan/wiki, available in this workspace. Builds are maintenance commands, not inside tests. Test helpers were traced through ProgramParser.ParseFiles, in-memory `DafnyFile` content/exists, ProgramResolver.Resolve, SourceFacts and DefinitionAnalysis. Tiny provided root/include maps satisfy file boundaries; XML/snapshots/tracing are off; no test invokes build, solver, native process, temp directory, source writes, synchronization or cleanup. No paid provider calls, benchmark suite, scoring change, proof verification or performance claim.

Durable findings: [resolved function body visibility](../wiki/function-body-visibility.md), indexed from owner wiki. Fresh independent reviewer `/root/verify_native_visibility` accepted the corrected final source after its own22/22 focused checks (127ms, no skips), exact fresh/loaded Core comparison, scoped formatting, whitespace and Markdown-only audit. It independently confirmed the constrained-generic closure correction and intrinsic ArrowType handling. Its first restricted test command hit only the local socket restriction; the identical approved command passed. No source acceptance work remains; parent owns integration and requested commits. No running build/test/format process remains.
