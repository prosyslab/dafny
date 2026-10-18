# Resolved verification target facts

Status: done
Date: 2026-10-18
Owner: Dafny compiler subtree
Related integration plan: [verification alignment](../../../plan/2026-10-18-align-codex-topdown-verification.md)

## Objective and acceptance

Expose opt-in resolved verification targets from the exact `ResolutionResult.CanVerifies`
inventory used by compilation. Each record contains native full name, source path,
and authored attributes. Include constructor obligations and function by-method
ownership without deriving names. Preserve legacy analysis JSON when not requested.
Normalize authored modern time-limit attributes so callers can apply policy without
parsing Dafny text. No proof/evaluator semantics,
benchmark data, dependencies, or provider calls change.

Inspected evidence: `TextDocumentLoader.ResolveInternal` constructs the inventory;
`DefinitionAnalysis.AttributesFor` only exposes brace attributes; built-in @ attributes
expand before `TimeLimitRewriter`. Existing source-facts documents provide compatible
optional metadata. Clean baseline native revision `bc427b214`.

## Changes and validation

| Files/symbols | Change, necessity, and validation |
| --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.cs`, new `DefinitionAnalysis.VerificationFacts.cs` | Optional inventory argument and nullable omitted source-facts property; authored brace/modern declaration metadata. Required for exact targets and structured candidate budget checks. In-memory resolved AST tests. |
| `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` | Register `--include-verification-facts`, imply document wrapper, pass resolved inventory; reject parse-only combination. CLI smoke after unit checks. |
| `Source/DafnyCore.Test/DefinitionVerificationFactsTest.cs` | Bounded parse/resolve in-memory scenarios; no temp directories, solver or writes. |
| `wiki/verification-target-facts.md`, `wiki/INDEX.md`, this plan/index | Describe wire, provenance and limitations with reciprocal links. |

Run from this native root: `dotnet build Source/DafnyDriver/DafnyDriver.csproj`
and `dotnet test Source/DafnyCore.Test --filter FullyQualifiedName~DefinitionVerificationFactsTest`.
Use existing cached dependencies/offline restore, no package additions. Format touched C#
with repository `make format` target, restricting include paths through its dotnet
invocation if necessary to preserve unrelated files. Final bounded CLI smoke is owned
by parent and uses synthetic sources in maintenance scratch. Compiler build and
analyzer tests do not establish benchmark proof results. No approval outstanding.

## Progress and handoff

Implementation in progress. Supported timeout attributes apply to `ICanVerify`;
statement/module attributes are outside this metadata scope. Scratch/build artifacts remain outside plan/wiki.

## Implementation checks

- Revision: `bc427b21461f258fd8de34232e01bb6be03cee39` plus this scoped working diff;
  .NET SDK 8.0.131, runtime 8.0.31, test platform 17.8.0.
- `dotnet build Source/DafnyDriver/DafnyDriver.csproj --ignore-failed-sources -p:NuGetAudit=false -v:minimal -m:1`
  restored existing dependencies; initial Java runtime build could not write the
  read-only global Gradle wrapper lock and was canceled. Original runtime source
  subtree is clean at the same baseline. Reused only its existing single
  `Source/DafnyRuntime/DafnyRuntimeJava/build/libs/DafnyRuntime-4.11.1.jar`
  in this isolated tree as a build prerequisite; no dirty sources copied.
- `dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore -v:minimal -m:1`
  passed with zero warnings/errors. Output:
  `Binaries/net8.0/DafnyDriver` and `Binaries/net8.0/DafnyDriver.dll`.
- `dotnet test Source/DafnyCore.Test --filter FullyQualifiedName~DefinitionVerificationFactsTest -p:RestoreIgnoreFailedSources=true -p:NuGetAudit=false -m:1 -v:minimal`
  compiled; sandbox denied the runner's loopback socket. Approved execution
  escalation enabled this existing local test runner boundary. A preliminary
  invocation with `--ignore-failed-sources` failed because `dotnet test` does not
  accept that restore switch; the MSBuild property above is the supported form.
- Initial focused run failed two fixture assumptions: iterator resolution adds
  generated functions, and the clean parser rejects underscore-prefixed authored
  attribute names. Corrected the authored function selection and tested supported
  brace `timeLimit` instead. No production behavior was changed to pass fixtures.
- Final `dotnet test Source/DafnyCore.Test --no-restore --filter FullyQualifiedName~DefinitionVerificationFactsTest -m:1 -v:minimal`
  passed 7/7, zero skipped, using approved socket execution. Tests parse/resolve
  bounded source strings in memory; no solver or temporary source directories.
- Ran the `make format` target's `dotnet format whitespace Source/Dafny.sln`
  operation with `--include` limited to four touched C# paths, `--no-restore`;
  matching `--verify-no-changes` check passed. No Dafny files changed.

No provider calls, benchmark runs, build-image claims, or proof success claims.
Parent owns independent review and synthetic final evaluator smoke. Durable wire
facts are recorded in [verification target facts](../wiki/verification-target-facts.md).

- Final bounded native CLI smoke, invoked from this root with Python subprocesses
  against the parent's existing `smoke/positive/Entry.dfy`, passed: opt-in reports
  six actual targets (`#PolicySmoke.Data.Item`, helper, function by-method,
  subset/newtype, entry method); legacy source-facts omits `verificationTargets`;
  `--spans-only --include-verification-facts` rejects the unsupported combination.
  Captured output stayed in memory; no fixture or evidence files were written.
- `git diff --check` and recursive `find plan wiki -type f ! -name '*.md' -print`
  passed (no non-Markdown files). All eight task paths are scoped; baseline dirty
  changes in the original checkout remain untouched.

Implementation handoff: native changes and checks complete. Keep plan in-progress
pending fresh parent-owned independent review/final evaluator smoke. No blockers;
next action is independent review, followed by parent-owned nested commit/landing.

## Independent acceptance and closure

Fresh Sol/high reviewer accepted the native and Dafnyutils changes on 2026-10-18
from requirements and current source, without implementation-agent context.
Independent driver/core-test builds used `--no-restore -m:1 -nr:false
-p:UseSharedCompilation=false` and completed with zero warnings/errors; seven
focused analyzer tests passed. Handwritten fixtures exercised constructor defaults,
class constructors, function-by-method bodies, subset/newtype witnesses, constants,
iterators, authored modern/legacy time limits, protected support and legacy schema
compatibility. Five invalid obligations produced three failed receipts each.
Evidence: `/workspace/tmp/align-codex-topdown-verification/independent-verification/`.

Independent full native style verification retains four unchanged baseline
IDE0048 diagnostics (`DefinitionAnalysis.cs:764,765,1217`,
`DefinitionAnalysisCommand.cs:147`); the same expressions exist at `bc427b214`.
Touched-file whitespace verification passes; no style-clean whole-tree claim.
Parent's final synthetic evaluator smoke also passes positive (18 receipts),
constructor failure and candidate-time-limit rejection. No benchmark run or
provider call occurred. No remaining implementation work; parent owns commits
and landing, preserving unrelated original compiler edits.
