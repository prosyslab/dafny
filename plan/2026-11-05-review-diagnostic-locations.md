# Map session diagnostic locations to each physical request

Status: done
Date: 2026-11-05

## Objective and scope

Maintenance repair explicitly requested as one of three P2 optimization-review
fixes. Display primary and related diagnostic locations using the request's
physical source root when native compilation caches use a stable logical root.
Keep cached tokens, diagnostic severity/id/message, JSON analysis mapping and
captured-source excerpts correct for every request. No compiler/proof/cache
policy, native pin, dependency, provider or benchmark changes; no commits.

Parent: [Cosyn review repairs](../../cosyn/plan/2026-11-05-optimization-review-fixes.md).
Native HEAD is `0776df27c2449bad68e9a28e687bb6c70bf4b401`; existing dirty/untracked
optimization work is preserved. Repository AGENTS/CLAUDE rules and current
diagnostic/output/snippet paths were inspected. Plan/wiki rules/templates absent.

## Planned changes

| Exact files/symbols | Change and why | Missing behavior | Validation |
| --- | --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: `RemapDiagnostic` and directly necessary request-output helpers | Delegate physical presentation paths without mutating retained compilation tokens | Message text is mapped but diagnostic locations retain logical URIs | Pure in-memory primary/related location and request remapping controls |
| `Source/DafnyCore/DafnyOptions.cs`: request-local print-path mapper; `Source/DafnyCore/AST/Tokens.cs`: `GetRelativeFilename` | Reuse the existing print-path boundary for request-local display paths; keep original logical ranges and snippet sources | Excerpts need captured logical bytes while rendered paths need physical roots | In-memory physical headers, original snippets, external aliases and filename/range modes |
| `Source/DafnyCore/JsonOutputWriter.cs`: `SerializeToken` | Apply the same request mapping to file URIs without basename truncation | Mapping only filePath would leave inconsistent logical URI fields in supported JSON diagnostics | In-memory primary/related JSON filePath and URI consistency, non-file URI preservation |
| New `Source/DafnyDriver.Test/AnalysisSessionDiagnosticLocationTests.cs` | Bounded in-memory regression controls with no directory/native-process lifecycle | Current tests focus on message text | Targeted native test class |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, this plan and `plan/INDEX.md` | Record request-local presentation guarantee and evidence | Durable diagnostic correction | Links/diff review |

## Verification and risks

Use native repository commands from `/workspace/dafny-optimization`; first inspect
test/build prerequisites and bound test I/O. No paid or provider calls. New
regressions use synthetic diagnostics/tokens and in-memory captured sources, not
temporary directories or native processes. Prefer targeted `dotnet test
Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --filter
FullyQualifiedName~AnalysisSessionDiagnosticLocationTests --verbosity minimal` if
the local build prerequisite is usable; otherwise report exact missing tooling
or restoration/build constraints. Parent performs independent fresh source
verification. Do not claim existing binaries test edited sources.

Cached diagnostics must remain logical and immutable across requests; related
locations outside the request root must remain unchanged. Preserve filename
rendering options and exact captured-source snippets. Update this plan before
expanding files. Task artifacts, if any, belong in
`/workspace/tmp/cosyn-optimization-review-fixes/`, never plan/wiki.

## Progress

Delegated implementation complete (`fix_diagnostic_paths`, gpt-6.1-sol/high).
Initial implementation cloned range endpoints and inverted physical URI excerpt
lookups. Self-review and fresh verification found an ambiguity for external
locations already under the physical root; the prior 13-test pass did not cover
that case. A temporary range-subclass/source-selector approach was rejected as
unnecessary presentation/source coupling before final acceptance.

Scope updated before the final implementation: add an optional request-local
print-path mapper to the existing `DafnyOptions.GetPrintPath` boundary and use it
from `TokenExtensions.GetRelativeFilename` before cwd-relative formatting.
Set the mapper on response options only after native compilation selection.
Cached tokens, source ranges and captured snippet keys remain logical. Undo the
temporary Snippets change and source-range selector. Include a regression with
an external URI under the physical root. Directly necessary captured-excerpt
existence checks must recognize already captured bytes if disk inputs vanish;
preserve input capture and cache freshness semantics.
Fresh review also requires supported JSON diagnostic `filePath` and `uri` fields
to agree: JSON URI mapping uses the full mapped file path, preserving non-file
URIs and independent basename formatting.

Initial native validation command (owner root, .NET SDK 8.0.133):
`dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --filter
FullyQualifiedName~AnalysisSessionDiagnosticLocationTests --verbosity minimal
--disable-build-servers -m:1 -p:SkipFocusedTestAssets=true
-p:DafnyGradleArguments=--offline`.
It reached BuildDafnyRuntimeJar and Gradle failed creating a lock in the read-only
`/home/vscode/.gradle`; stopped the check (exit 130), no expansion/network retry.
Log: `/workspace/tmp/cosyn-optimization-review-fixes/native-diagnostic-tests.log`.

Bounded fallback validation will compile the edited driver and test assemblies
with `BuildProjectReferences=false` against existing core/runtime references,
then run only the new memory-only class. This validates edited source with those
dependencies, and does not claim the entire dirty native tree was rebuilt.

## Final source and validation

Implemented in `DafnyOptions.cs`, `AST/Tokens.cs`, `JsonOutputWriter.cs`,
`AnalysisSessionCommand.cs` and the new diagnostic test class. No task edits remain
in `Snippets.cs`; its pre-existing dirty changes are preserved. Request-local
`PrintPathMapper` is set only on response options after compilation selection.
It changes displayed filenames and JSON file URIs while ranges, token chains and
captured source keys stay logical. Unchanged URIs keep their components; mapped
URIs retain query/fragment. The excerpt-only existence predicate accepts captured
inputs without changing input capture/freshness.

Final core, driver and test assemblies were rebuilt serially/offline with project
reference builds disabled. Core and driver report zero warnings/errors; the test
build has one existing VSTHRD103 warning in CompilationResolutionTests. Final
synthetic class: 18 passed, 0 skipped in 79 ms. VSTest's local coordination socket
required the approved execution path after sandbox SocketException(13); no
network/provider test or dependency restoration occurred.

Fresh independent source verification (`verify_native_diagnostics`, separate
context) accepted human and JSON location mapping, preserved source identity,
captured excerpts, physical-root collision and URI component cases. That verifier
ran static/source checks only; executed native tests are the implementation owner's.
Scoped native whitespace validation and git diff checks pass.

Build/test/format logs are temporary at
`/workspace/tmp/cosyn-optimization-review-fixes/native-diagnostic-*.log`. Durable
findings are in [native sessions](../wiki/native-analysis-session.md#request-local-diagnostic-locations-2026-11-05).
No full dependency rebuild, native proof/cache efficacy, image, clean pinned
install, benchmark or paid result is claimed. All requested local repair work is
complete; native pin/publication is parent-owned and unchanged. No commits.

### Exact final commands and retained references

Working directory `/workspace/dafny-optimization`; SDK 8.0.133,
MSBuild 17.8.60+293f66545, VSTest 17.8.0. All final commands exit 0:

```sh
dotnet build Source/DafnyCore/DafnyCore.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false
dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false
dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false -p:SkipFocusedTestAssets=true
dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter FullyQualifiedName~AnalysisSessionDiagnosticLocationTests --verbosity minimal -m:1
dotnet format whitespace . --folder --include Source/DafnyCore/DafnyOptions.cs Source/DafnyCore/AST/Tokens.cs Source/DafnyCore/JsonOutputWriter.cs Source/DafnyDriver/Commands/AnalysisSessionCommand.cs Source/DafnyDriver.Test/AnalysisSessionDiagnosticLocationTests.cs --verify-no-changes --verbosity minimal
```

Outputs respectively: freshly built core, driver, test DLLs; 18 passing bounded
synthetic tests; whitespace check success. Resolved retained references verified
with offline MSBuild ResolveReferences/GetItem: runtime
`Binaries/netstandard2.0/DafnyRuntime.dll`, language-server
`Binaries/DafnyLanguageServer.dll`, test-generation
`Binaries/net8.0/DafnyTestGeneration.dll`; rebuilt core
`Binaries/net8.0/DafnyCore.dll`. Earlier generic net8.0 dependency assumptions
were corrected before final acceptance. Build outputs include the normal local
core NuGet package; no generated artifacts live in plan/wiki.
