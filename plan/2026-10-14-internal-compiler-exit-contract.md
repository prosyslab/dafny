# Preserve native internal failures as an explicit exit contract

Status: done
Date: 2026-10-14
Owner: embedded native Dafny driver
Parent: [integration stop/debug/resume](../../../plan/2026-10-13-shared-ownership-repair-and-rerun.md)
Consumer: [Cosyn classification](../../plan/2026-10-14-dafny-internal-failure-classification.md)

## Objective and acceptance

The user authorizes stopping infrastructure-dominated experiments, debugging
directly in main sources and resuming afterwards. Preserve typed compiler
exceptions through the native CLI as exit code 6, without changing existing
candidate codes 0–5, verification scope, diagnostics, specifications or scoring.
The current interrupted cohort and its original images/results remain immutable.

Acceptance: unexpected command-handler exceptions and typed internal compilation
events produce INTERNAL_ERROR; a terminal mutation error stops further mutation
work and never emits completion afterwards. Local injected-error tests and tiny
candidate-error controls demonstrate the producer contract. The full native
solution builds; changed C# formatting and affected driver/trigger tests pass;
fresh independent verification inspects and runs the actual source.

## Inspected evidence and compatibility

The current native driver uses System.CommandLine UseDefaults, whose exception
handler maps escaped exceptions to 1. CliCompilation receives a typed
InternalCompilationException but only counts it in a local printing variable.
MeasureComplexityCommand forwards exceptions through OnError and can continue
when an observer does not throw. Verification JSON and diagnostic errorId/source
do not distinguish these exceptions reliably from candidate errors. The existing
exception-handler API supports an explicit errorExitCode; reuse it, not a textual
heuristic. Old-image exit-1 receipts remain ambiguous and are not rewritten.
The previously accepted trigger-scope repair remains in this dirty main tree.

## Change table

| File/symbol | Change, necessity and unmet behavior | Validation |
| --- | --- | --- |
| Source/DafnyDriver/Legacy/DafnyBackwardsCompatibleCli.cs, ExitValue | Add INTERNAL_ERROR = 6; existing values remain fixed | Producer and consumer numeric contract controls |
| Source/DafnyDriver/DafnyNewCli.cs, parser construction | Configure the existing exception handler to return 6 while retaining native exception diagnostics | Injected handler failure and preprocessing negative control |
| Source/DafnyDriver/CliCompilation.cs, Start/GetAndReportExitValue | Keep typed internal-exception state and give it priority in final classification | Injected compilation event and candidate diagnostic controls |
| Source/DafnyDriver/Commands/MeasureComplexityCommand.cs, RunVerificationIterations | Return after terminal OnError; reuse the existing verifier seam if a focused test requires accessible internal scheduling | Failing fake verifier yields one mutation/error and no completion |
| Source/DafnyDriver.Test/InternalErrorExitTests.cs | Add focused generic fake/native driver behavior regressions, one intention per scenario; no copied benchmark cases | Focused dotnet test; retain syntax/type/assertion classifications |
| This plan/index; wiki/internal-compiler-exit-contract.md and wiki/INDEX.md | Record contract, provenance, compatibility and validated limitations | Diff and Markdown-only checks |

No dependencies, provider calls, task changes, proof skips, broad catches or
commits. Keep implementation directly in /workspace/cosyn/dafny; generic scratch
under /workspace/tmp/dafny-internal-exit-contract/. Benchmark-native propagation
uses its owning plan after the producer is checked. Update exact test/symbol
scope before any additional edits.

## Validation commands

From /workspace/cosyn/dafny, with installed .NET and existing restore caches:

- dotnet build Source/Dafny.sln --no-restore -m:1 -p:UseSharedCompilation=false
- dotnet test Source/DafnyDriver.Test --no-restore --filter FullyQualifiedName~InternalErrorExitTests
- dotnet test Source/DafnyCore.Test --no-restore --filter FullyQualifiedName~TriggerBoundVariableScopeTests
- dotnet format whitespace Source/Dafny.sln --no-restore --include <changed C# files> --verify-no-changes
- Bounded generic CLI syntax/type/assertion and injected-error checks, retaining
  exact source/binary hashes, stdout/stderr and raw return codes in scratch.

Any required outside-sandbox local cache/IPC access follows normal approval.
Local compiler checks do not establish paid experiment success. A separate fresh
verification context starts from requirements/current source, not implementation
claims. Root alone owns image admission and the authorized restart population.

## Exact test seams before implementation

Keep changes within the four planned driver files. In `DafnyNewCli.cs`, extract
existing parser construction into internal `CreateParser(RootCommand)` so tests
can inject a throwing command through the same production middleware without
mutating the process-global command tree. Grant `DafnyDriver.Test` internal
visibility in that same assembly source file. Make the existing
`CliCompilation(CreateCompilation, DafnyOptions)` constructor internal, preserving
its factory contract, and make the existing mutation-loop method internal. Tests
use these existing dependency boundaries and real compiler events; no reflective
field access, production failure flags or new packages. The mutation test uses
a generic source and a failing `IProgramVerifier` that counts calls.

Planned controls: handler exception -> 6; actual invalid CLI input -> 1;
parse/type failure -> 2; ordinary assertion failure -> 4; valid source -> 0;
existing numeric values 0–5 remain unchanged. Typed internal compilation events
out-prioritize ordinary diagnostic classification. A mutation error reaches an
observer once, invokes the fake verifier once, and produces no completion.

## Implementation and local results

The four planned driver files now implement the explicit exit contract:
`ExitValue.INTERNAL_ERROR` is 6; existing System.CommandLine exception middleware
uses that code; `CliCompilation` retains the typed exception counter and checks
it before ordinary diagnostic categories; the mutation loop returns immediately
after `OnError`. No source-message parsing, new catch blocks or fallback proof
behavior were added. Existing candidate values 0–5 are unchanged.

The small internal test seams described above were sufficient. Eleven focused
regression cases pass: production parser middleware with an injected handler
exception, preprocessing rejection, generic success/syntax/type/assertion cases
in both verify and measure-complexity, and a real compilation whose injected
verifier raises an exception. The latter checks one verifier call, one terminal
error, no results/completion, and internal exit priority over a subsequent
project diagnostic. Generic files and raw CLI stdout/stderr/exit records remain
under `/workspace/tmp/dafny-internal-exit-contract/tests/`.

All commands below ran from `/workspace/cosyn/dafny`, based on revision
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a` with the accepted trigger repair and
this driver repair in the working tree. SDK 8.0.131; test runtime .NET 8.0.31.
No commits were created.

- `dotnet test Source/DafnyDriver.Test --no-restore -m:1 -p:UseSharedCompilation=false --filter FullyQualifiedName~InternalErrorExitTests --logger 'console;verbosity=normal'`: 11 passed. Initial compile iterations corrected ambiguous Parser/Token/InvokeAsync names; one test setup iteration corrected normalized option-name lookup to `HasAlias`. Failed-attempt logs are preserved as `tests-first.log` through `tests-third.log`; successful build/run is `tests-fourth.log`.
- `dotnet build Source/Dafny.sln --no-restore -m:1 -p:UseSharedCompilation=false`: passed with zero warnings and zero errors; logged elapsed time 15:46.46. `build.log`.
- `dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~InternalErrorExitTests`: final rebuilt solution, 11 passed. `tests-final.log`.
- `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~TriggerBoundVariableScopeTests`: accepted trigger repair retained, 3 passed. `trigger-regression.log`.
- `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyDriver/DafnyNewCli.cs Source/DafnyDriver/CliCompilation.cs Source/DafnyDriver/Commands/MeasureComplexityCommand.cs Source/DafnyDriver/Legacy/DafnyBackwardsCompatibleCli.cs Source/DafnyDriver.Test/InternalErrorExitTests.cs`, then the same command with `--verify-no-changes`: passed; workspace-loading warning only. `format.log`, `format-check.log`.
- `git diff --check`: passed. Native plan/wiki recursive inspection found no non-Markdown artifacts.

All logs named above are in `/workspace/tmp/dafny-internal-exit-contract/`.
The .NET runner used the authorized escalation path for its local IPC socket.
No benchmark replay, provider call, broad suite, dependency installation, image
restart or benchmark-native propagation was performed.

Rebuilt binary SHA256 identities:

| Binary | SHA256 |
| --- | --- |
| `Binaries/Dafny.dll` | `59b6446e0d0b3696cd8b65113e819c19bf6928c8b961db0b499df144a86ff2c7` |
| `Binaries/DafnyDriver.dll` and `Binaries/net8.0/DafnyDriver.dll` | `02d3c265ce69b480148e77142f80548f802d8063cda73bf12d34d21d55e48c98` |
| `Binaries/DafnyCore.dll` | `6203565e149a6a05f4dd020b603ad2b60eefe92fa5d2394f140bdf71ae034ebd` |

Durable record: [internal compiler exit contract](../wiki/internal-compiler-exit-contract.md).
Source/tests are frozen for fresh independent verification. This plan remains
`in-progress` until that acceptance result is recorded. Parent owns downstream
consumer integration, bounded propagation, image admission and experiment resume.

Scoped propagation artifacts (not yet applied to another checkout):
`/workspace/tmp/dafny-internal-exit-contract/native-internal-exit-contract.patch`
and `source-hashes.json`. Patch contains only the four driver changes and the
new native test, excluding the earlier trigger repair and owner documentation.
SHA256 `c00c4155a9b76dbd54ffb2e6007d286fb5cd24ffec8e247aca31c6200d322550`.
`git apply --reverse --check` against this completed main tree passed.

### Fresh independent acceptance

Separate read-only verifier ran driver11/11, retained trigger3/3, direct built
CLI controls for all prior exit codes0–5 and three-mutation valid/assertion
controls0/4. Production parser, subscription-before-start, atomic internal-event
priority and terminal mutation behavior were independently traced. Loaded test
driver equals Binaries/DafnyDriver.dll at SHA256
02d3c265ce69b480148e77142f80548f802d8063cda73bf12d34d21d55e48c98.
Scoped whitespace/diff and Markdown-only checks pass. Reviewer did not repeat the
full solution build; implementation's full build remains separate evidence.
Generic evidence: /workspace/tmp/native-internal-exit-independent/. No paid calls.
All owner acceptance requirements pass. Benchmark-native propagation, Python
consumer acceptance, final image admission and paid restart remain separately
tracked; this completion does not assert benchmark success.
