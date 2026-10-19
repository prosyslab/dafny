# Repair free generated variables during automatic trigger rewriting

Status: done
Date: 2026-10-14
Authorization: user requests immediate direct-source repair of the identified
Boogie/Dafny bug; no independent implementation worktree, paid calls or commits.
Parent: [integration investigation](../../../plan/2026-10-13-shared-ownership-repair-and-rerun.md).

## Objective and acceptance

Fix the compiler transformation that emits a generated variable outside its
quantifier scope. Work directly in `/workspace/cosyn/dafny`, the native source
used to build the running Cosyn image. Preserve all source/proof obligations,
automatic trigger generation, variable identity and lexical binding.

Acceptance: a small generic regression reproduces the erroneous intermediate
binding before the fix and succeeds afterwards; affected native unit/integration
checks and formatting pass; rebuild the supported local CLI and recheck the
exact private revision2 input without internal errors. Remaining ordinary proof
failures are reported rather than erased. A fresh independent verifier inspects
the changed compiler/test logic and executes its own bounded checks.

## Inspected evidence and existing solutions

Clean starting native tree HEAD`dce5a96612b6516c5b180bb215d6eb3e3b430d5a`.
Offline same-image diagnostic uses24public input files and two authenticated
accepted patches, without candidate/evaluator/private-oracle sharing. Generated
Boogie output contains seven free `_t#0#6` uses in one implementation whose
surrounding quantifier instead binds `_t#0#3`; another implementation correctly
binds `_t#0#6`. Ordinary`verify` returns SIGABRT(-6) and`measure-complexity`
returns1for the identical pre-SMT resolution errors. Printed resolved and Boogie
artifacts are in the current run's private`analysis/boogie-repetition-audit/`.
Restricted task source is not copied into this repository or its documentation.

Existing automatic matching-loop rewrite lives in
`Source/DafnyCore/Triggers/SplitPartTriggerWriter.cs` and`ExprSubstituter.cs`.
Inspect expression equality, subtree sharing and quantifier/bounded-pool
substitution before choosing the exact repair. Numeric exit-classification and
background exception behavior are observed secondary issues, not a reason to
disable native checks or classify this as an ordinary failed proof.

## Change table

| File / symbol | What, how and why | Unmet without change / validation |
| --- | --- | --- |
| `Source/DafnyCore/Triggers/ComprehensionTriggerGenerator.cs`, `CombineSplitQuantifier` grouping | Require compatible bound-variable identities and ranges in addition to equal trigger candidates before merging terms; independently rewritten splits must keep their own binders | Empty candidate lists currently compare equal despite different generated binders; generic native regression and exact private intermediate dump |
| `Source/DafnyCore.Test/TriggerBoundVariableScopeTests.cs`; `Source/IntegrationTests/TestFiles/LitTests/LitTest/triggers/split-matchingloop-bound-variable-scope.dfy` and `.dfy.expect` | Add a minimal independent generic input covering the observed malformed binding and an appropriate nested/distinct-variable case | A task-specific workaround cannot establish compiler correctness; reproduce on old source, pass with fixed source |
| `plan/2026-10-14-trigger-bound-variable-scope.md`, `plan/INDEX.md` | Record diagnosis, chosen exact patch, build/test provenance and outstanding work | Acceptance is not a successful compile alone; review diffs and evidence |
| `wiki/trigger-bound-variable-scope.md`, `wiki/INDEX.md` if durable findings confirmed | Record generic transformation invariant and regression command without task bodies | Future fixes could repeat the scope error; link originating plan and verification |

## Boundaries and non-goals

No candidate/specification/benchmark/evaluator/scoring changes; no broad trigger
disable, manual-trigger workaround, solver/time-limit increase, verification skip,
new package or paid trial. No generated AST/parser files edited. The current
evaluated run continues on its immutable old image and records actual results;
it is not silently repaired or restarted. Direct-source/native rebuild is a new
development checkpoint, separate from that image. Preserve other dirty work and
do not create commits.

## Validation

Prerequisites: installed .NET/native prerequisites and cached restore artifacts.
Inspect supported`Makefile`, `Scripts/test.sh`, native project build settings and
existing tests; use Dafny-local commands from this native root. Planned commands:

- `dotnet build Source/Dafny.sln --no-restore -m:1` (or the exact supported owner
  `make exe` target after checking build prerequisites): compiler builds without
  pulling new packages. Report any unrelated project failure separately.
- `dotnet test Source/DafnyCore.Test --no-restore --filter FullyQualifiedName~TriggerBoundVariableScope`
  with the final actual class name: meaningful generic regression passes.
- `make test name=<actual minimal trigger regression> build=false`: focused
  native integration fixture if added; no full benchmark suite or pytest copying.
- `dotnet format whitespace Source/Dafny.sln --no-restore --include <actual changed C# files>`
  and appropriate existing`make format-dfy`scope/check if a Dafny fixture is added.
- Bounded native CLI replay of the private sourceRevision2 with the same
  include/library scope and printed Boogie output. Preserve original diagnostics,
  source/CLI hashes and returned proof outcomes. Any timeout remains incomplete.

Implementation and verification contexts must be independent. First inspect for
the exact cause; add precise file/symbol scope and update status to`in-progress`
before edits. Keep all generated/test artifacts outside Markdown-only plan/wiki
trees and avoid directory-copy/delete tests that caused I/O overload.

## Progress

Initial checkpoint: ready for direct native-source investigation and repair; implementation and validation results follow.

### Inspection finding and exact implementation scope

`CombineSplitQuantifier` groups expressions solely with `HasSameTriggers`, then
conjoins/disjoins their terms under the first expression's `BoundVars`, `Range`
and `Bounds`. Matching-loop rewriting can give each split a distinct fresh bound
variable and equality range. Two empty candidate lists compare equal; merging
those terms loses the second generated variable's binder. Identifier expression
equality itself correctly compares `Var` identity. No cross-method variable
sharing is established by a coincidentally reused printed variable suffix.

The planned minimal repair requires the same binder identities and equivalent
ranges before combination, retaining independently scoped splits otherwise.
Build a generic sequence quantifier with several conjuncts to reproduce the
pre-SMT failure before patching; add a unit regression for resolved free-variable
closure and a native integration fixture as needed. Native fixture and exact
test file names are recorded before creation. Generic scratch:
`/workspace/tmp/dafny-trigger-scope-repair/`.

Baseline generic 7-line sequence precondition reproduced six undeclared generated
identifier errors using the pre-edit local `Binaries/Dafny.dll`. Diagnostics are
under generic scratch `before.stdout.txt`, `before.stderr.txt`, and printed BPL.
The first launch used the nonexistent lowercase wrapper; the actual CLI is
`dotnet Binaries/Dafny.dll`. Native tests will cover both universal and existential
splitting, bound-variable closure, and ordinary same-binder recombination.

### Implementation and local validation completed

Compiler edit: `ComprehensionTriggerGenerator.CombineSplitQuantifier` calls
`CanCombine`, which requires identical binder objects and compatible ranges
before comparing trigger candidates. This retains all independently rewritten
quantifiers, including both universal and existential cases. Same-binder splits
continue to combine. No changes to `ExprSubstituter`, scoring, task inputs or
verification scope were needed.

Local working tree: base `dce5a96612b6516c5b180bb215d6eb3e3b430d5a`, with this
compiler edit and new unit/integration tests; no pre-existing tracked changes
were present. SDK `8.0.131`, test runtime `.NET 8.0.31`. All commands below ran
from `/workspace/cosyn/dafny`. Logs live under
`/workspace/tmp/dafny-trigger-scope-repair/`.

| Command / evidence | Outcome |
| --- | --- |
| Old CLI `dotnet Binaries/Dafny.dll verify /workspace/tmp/dafny-trigger-scope-repair/repro.dfy --allow-warnings --cores=1 --verification-time-limit=10 --bprint=/workspace/tmp/dafny-trigger-scope-repair/before.bpl` | Six undeclared generated-identifier errors; exit 134. Generic seven-line sequence case; `before.stdout.txt` and `before.stderr.txt` |
| `dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~TriggerBoundVariableScope --logger 'console;verbosity=normal'` before compiler patch | Two closure regression failures; one compatible-recombination pass. `unit-before.log` |
| `dotnet test Source/DafnyCore.Test --no-restore -m:1 -p:UseSharedCompilation=false --filter FullyQualifiedName~TriggerBoundVariableScope --logger 'console;verbosity=normal'` after patch | Three passed. `unit-after.log` |
| `dotnet build Source/Dafny.sln --no-restore -m:1 -p:UseSharedCompilation=false` | Succeeded, zero errors, four existing warnings, 19.71 seconds. `build.log` |
| `make test name=triggers/split-matchingloop-bound-variable-scope.dfy build=false` | One integration fixture passed; two methods verified, zero errors. Expected no-trigger warnings retained. `integration-new.log` |
| `dotnet test Source/IntegrationTests --no-build --no-restore --filter 'DisplayName~triggers/nested-matchinglooprewrite-regression.dfy\|DisplayName~triggers/splitting-\|DisplayName~triggers/loop-detection-'` | Seven passed, zero failed/skipped. `integration-related.log` |
| `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyCore/Triggers/ComprehensionTriggerGenerator.cs Source/DafnyCore.Test/TriggerBoundVariableScopeTests.cs` and same command with `--verify-no-changes` | Passed; workspace-loading warnings only. `format.log`, `format-check.log` |
| `dotnet Binaries/Dafny.dll format Source/IntegrationTests/TestFiles/LitTests/LitTest/triggers/split-matchingloop-bound-variable-scope.dfy` and `format --check` on the same fixture | Passed. This scopes the formatting underlying `make format-dfy` to the changed fixture; broad core/standard-library formatting is unrelated |
| `git diff --check` | Passed |

The sandbox initially blocked the .NET test runner's local IPC socket.
The authorized escalation path was approved for focused native tests.
No packages, provider calls or commits were added. Full benchmark suites and
Python copy/delete tests were not run because this is a focused compiler repair.

Rebuilt `Binaries/DafnyCore.dll` SHA256:
`6203565e149a6a05f4dd020b603ad2b60eefe92fa5d2394f140bdf71ae034ebd`.
`Binaries/net8.0/DafnyCore.dll` has the same hash. Entry CLI remains
`dotnet Binaries/Dafny.dll`, whose SHA256 is
`6ee343491e61e9d5e3ca70f8c0d5948bbeea1ed1c195786eb628dbe74146d367`.

Durable finding: [trigger recombination scope invariant](../wiki/trigger-bound-variable-scope.md).
Remaining acceptance: exact private-input replay and fresh independent
verification, owned by the parent integration investigation. Plan remains
`in-progress` pending those results. The evaluated image has not been changed.

The unchanged seven-line generic pre-edit repro also passes on the rebuilt CLI:
`after.stdout.txt` reports one verified, zero errors; stderr is empty and exit
status is zero. `after.bpl` preserves the distinct rewritten binders.
Native plan/wiki recursive file audit found no non-Markdown files.

### Parent-owned exact-input replay update

The parent integration investigation completed the authorized exact private-input
replay using the rebuilt Core SHA256 recorded above, with source, includes,
library scope and automatic-trigger settings unchanged. Ordinary `verify`
reached SMT verification and returned exit 4: 122 verified, 10 actual proof
errors, with no Boogie internal binding error. This is evidence that malformed
translation is repaired; it is not a successful candidate proof.

The three-seed `measure-complexity` replay reached real 132-batch SMT progress
but exceeded the parent's 45-second process deadline. It is explicitly
incomplete (timeout), not a completed complexity result. No internal binding
error was observed. Private provenance and results remain in the authorized
run analysis at `diagnostics/fixed-native-replay.json`; no task proof bodies or
private artifacts were copied into this repository.

Fresh independent native verification is still in progress. No additional
native/benchmark replay is required from the implementation context. Source
and tests remain frozen, and this plan remains `in-progress` until the parent
records the independent acceptance result.

### Independent acceptance — 2026-10-14

Fresh verification context completes its own3unit cases, new integration1/1,
existing automatic-trigger expressivity1/1, generic universal/existential AST
closure and compatible recombination probes, generated-Boogie inspection and
C#/Dafny formatting/diff/documentation hygiene checks. No blocking findings.
Checked source SHA71e87fbabc7d750b3ed28078e4cc1deafbfb3314cdc96df3962b201f6b5cdb5f,
unit4eece685aa69f61445b826083f0a9e19604949bedb5fb07d107434c354b23251,
fixturea4390b4ef148f9f5311869cd1c37052b31def34dae3dcf308452f6c9349fe82f,
expect8057ae540b5046dac3b40ae3b777565ca2ffb5b291e738b346e7b087eb8a589b,
Core6203565e149a6a05f4dd020b603ad2b60eefe92fa5d2394f140bdf71ae034ebd.
It independently checks the exact private replay: all132ordinary obligations
processed,122verified/10proof errors; fixed lexical binding and no internal error.
Three-seed complexity remains externally timed out, not accepted as completed.

The compiler repair criteria are met. Main source/runtime contain the checked
fix; no commits, new dependencies, hidden data, task changes, paid calls or live
image changes. The parent experiment plan remains open for terminal results.
The separate benchmark-native tree receives the same generic repair under
[its own plan](../../../dafnyutils/dafny/plan/2026-10-14-trigger-bound-variable-scope.md).
