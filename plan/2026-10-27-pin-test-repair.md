# Repair native test failures on the commit-pin branch

Status: blocked
Date: 2026-10-27
Parent: [Replace nested Dafny submodules with one commit pin](../../../plan/2026-10-27-dafny-commit-pin.md)

## Objective and acceptance

Branch `pin/2026-10-27` (head `0373531e5`, nine linear commits on `origin/expecto`
`1de66ec5a`) carries 7 `DafnyDriver.Test` and 8 `DafnyTestGeneration.Test` failures
that pass on `1de66ec5a`. Each must be classified with evidence from the commit
intent and the six native plans plus the two Cosyn parent plans
(`../../plan/2026-10-26-pbt-bounded-contract-models.md`,
`../../plan/2026-10-26-pbt-binary-feasibility.md`) as either an intended contract
change (the test then asserts the new observable contract) or a regression (the
code is fixed at its root cause).

- Every listed failure is attributed to its introducing commit by bisection or
  direct diff evidence.
- New focused commits are added on top of `pin/2026-10-27`; history is not rewritten
  and nothing is pushed.
- The full filtered `DafnyCore.Test`, `DafnyDriver.Test` and
  `DafnyTestGeneration.Test` suites pass serially at the final head, with logs in
  `/workspace/tmp/dafny-commit-pin/`.

## Non-goals

No timeout increase, loosened assertion or deleted check to obtain a pass unless the
plans prove the old expectation wrong. No schema, benchmark, evaluator, scoring or
Python change. No push, release or paid run. Generated files stay untouched.

## Failing tests (from the logs in `/workspace/tmp/dafny-commit-pin/`)

`DafnyDriver.Test`: `ContractRuntimeLibraryCommandTests.PrintsEmbeddedRuntimeLibraryBytes`;
`PreCompilationTests.{LocatesGeneratorSyntaxError,RejectsGenericHigherOrderShapeErasure,RejectsGenericShapeFormalCollision}`;
`ClauseDependenciesTests.{ClassifiesEveryBucket,UncertifiedDependencyKeepsCalleeClauseUnchecked(3,...)}`;
`InitialAdmissionTests.ScalarClosedCalleeUsesOriginalSources(2,False)`.

`DafnyTestGeneration.Test`: `ContractRuntimeGeneratorSignatureTests.{RejectsOtherReservedDiagnosticMemberNames x5,TransformsInstanceGeneratorWithoutCapturingCollidingNames}`;
`ContractWitnessQueryTests.ConcreteConcatenationRetainsNativeTarget`;
`ContractQueryTests.ProofOnlyQuantifiersRetainOriginalAssertionAndDefinedness("exists k:int :: result == 2*k")`.

## Suite filters

Reconstructed from the logged totals (306 and 1062 tests, derived from
`--list-tests` of the same assemblies): Driver `FullyQualifiedName~ContractRuntime`
(excludes language-server, formatter, JSON logger, proof-remover and internal-error
tests, 16 in all); TestGeneration `FullyQualifiedName~Contract|FullyQualifiedName~Pbt`
(excludes the legacy test-generation classes `BasicTypes`, `Collections`, `Various`,
`ShortCircuitRemoval`, `WarningTests`, 70 in all); Core unfiltered (357).

## Findings

Attribution used a separate worktree of `1de66ec5a` and of the branch commits, built
with `dotnet build Source/Dafny.sln`. Bisection result: `82c3d3fed` (3 build errors)
and `ef39fa041` (6 errors: it calls members that only `56f18bfc4` adds to the
obligation transformer and heap factory) do not build on their own; the other
branch commits (`2e11f98b7`, `2937f5739`, `6bfdd5fe9`, `2161f6922`, `c2f198e40`,
`56f18bfc4`) build with 0 errors. The observable changes therefore appear together at
`56f18bfc4`, the first buildable commit after them. History was not rewritten.

Z3 selection confound. Dafny uses `z3/bin/z3-<DefaultZ3Version = 4.16.0>` beside the
loaded `DafnyCore.dll` and falls back to the first `z3` on `PATH` (system 4.8.12). The
branch test outputs carry `z3-4.16.0`; the earlier baseline run evidently did not.
On a fresh build of `1de66ec5a` with `z3-4.16.0` present, the same five solver-
dependent tests fail (see the first group); hiding that one file in the test output
makes all of them pass at both `1de66ec5a` and the branch. Durable record:
[`wiki/native-test-solver-selection.md`](../wiki/native-test-solver-selection.md).

| Test(s) | Introducing commit | Decision and evidence |
| --- | --- | --- |
| `ContractRuntimeLibraryCommandTests.PrintsEmbeddedRuntimeLibraryBytes` | `ef39fa041` (`PbtRuntime.dfy` +11 lines; `ContractRuntimeLibraryTests` pin updated, Driver pin missed) | Intended text change; Driver pin updated to `8965d793...6c15`, the digest `ContractRuntimeLibraryTests` pins. The byte comparison with the embedded library stays. |
| `PreCompilationTests.{LocatesGeneratorSyntaxError,RejectsGenericHigherOrderShapeErasure,RejectsGenericShapeFormalCollision}` | `56f18bfc4` (runner catches `NotSupportedException` from source preparation and runs `ContractRuntimeFeasibility.AnalyzeResolved`; added in `ef39fa041`) | Intended. Commit message: "runner and command also report typed terminal failures"; binary-feasibility plan: unsupported targets get a binary false with concrete reasons before any authoring or campaign work. Tests now assert `Status == Unsupported`, the blocker code (`unsupported_generic_reference`, `reserved_diagnostic_name`) or the located syntax diagnostic in `Reason`, and zero generated samples. |
| `ContractRuntimeGeneratorSignatureTests.RejectsOtherReservedDiagnosticMemberNames` x5 | `56f18bfc4` (transformer name gate now runs over `RuntimeExecutionReachable` callables via `UnsupportedDiagnosticNames`) | Intended. Binary-feasibility plan: inspect only relevant selected dependencies, do not reject a library for unrelated declarations; `ContractRuntimeFeasibilityTests.IgnoresUnrelatedUnsupportedDeclarations` covers the unreachable case. The tests declared an unreachable reserved member; `Goal` now calls it, and the rejection is still asserted. |
| `ContractRuntimeGeneratorSignatureTests.TransformsInstanceGeneratorWithoutCapturingCollidingNames` | `56f18bfc4` (commit message: "preserves defaults and named bindings on call-boundary wrappers") | Intended. The wrapper call is `receiver0.Goal__pbt_goal(receiver := receiver)`; test expects the named binding, and the no-capture and resolve checks are unchanged. |
| `ContractQueryTests.ProofOnlyQuantifiersRetainOriginalAssertionAndDefinedness("exists k:int :: result == 2*k")` | None: fails identically on `1de66ec5a` with `z3-4.16.0` (decision `Residual`; `ContractSolver`/`ContractExpressionReducer` untouched by the branch) | Not a branch regression. Passes with system z3 4.8.12 and with `z3-4.12.1` standing in for the default name; fails only on 4.16.0. Left unchanged, unresolved (see Risks). |
| `ContractWitnessQueryTests.ConcreteConcatenationRetainsNativeTarget("!(exists a:seq<int> :: [1,2] == a + a)")` | None: fails on `1de66ec5a` with `z3-4.16.0` | Not a branch regression. Exceeds the 3 s deadline on 4.16.0 and on 4.12.1, passes on system 4.8.12. Deadline not raised. Unresolved. |
| `ClauseDependenciesTests.{ClassifiesEveryBucket,UncertifiedDependencyKeepsCalleeClauseUnchecked(3,...)}`, `InitialAdmissionTests.ScalarClosedCalleeUsesOriginalSources(2,False)` | None: fail identically on `1de66ec5a` with `z3-4.16.0` (3 of 23 in the baseline subset), pass with the fallback solver at both revisions | Not a branch regression and not a callee-count change by any commit. With 4.16.0 the opaque-dependency bucket reports 4 callee violations where the fallback leaves the clause unchecked. Unchanged, unresolved. |

Core: `DafnyCore.Test` unfiltered has 608 tests; the 90 failures are all in
`HelperFunctionInterpreterTest` (reflection on `PartialEvalState` constructor, not
solver dependent) and fail identically on `1de66ec5a` (601 tests, same 90). They are
outside this repair; the earlier 357-test Core filter is not recorded in the logs, so
the Core result below is the unfiltered run plus the run excluding that class.

## Risks and open decision

The five solver-dependent tests are not repaired because no source change of this
branch causes them and every candidate fix changes meaning: raising the 3 s deadline
or forcing `smt.mbqi` for positive existentials would be a timeout/heuristic change
(root `AGENTS.md`: no heuristic without explicit human approval), and selecting the
system 4.8.12 solver in tests would hide the Dafny default. A human must choose
between (a) pinning the test environment solver, (b) revising those expectations for
4.16.0 with proof evidence, or (c) a product change for the 4.16.0 profile. Until
then the default-solver suites show 5 failures that exist on `1de66ec5a` too.

## Validation plan

From `/workspace/cosyn/dafny`, serial, one tmux-free foreground command at a time
with logs redirected to `/workspace/tmp/dafny-commit-pin/`:
`dotnet build Source/Dafny.sln`, then `dotnet test <project> --no-build --no-restore
--filter <filter>` for the three projects. Bisection builds use a separate git
worktree under `/workspace/tmp/dafny-commit-pin/bisect` so the branch working tree
and its `Binaries` stay untouched. Tests added or changed use in-memory data only;
no temporary directories, fsync or live provider calls. The existing
`CampaignFixture` Driver tests are pre-existing real-campaign fixtures and are only
edited, not extended.

## Progress

- 2026-10-27: plan created before any code change.
- 2026-10-27: three test-only commits added on `pin/2026-10-27`: `276440160`
  (Driver library digest), `ddac0b87d` (pre-compilation tests assert unsupported
  results), `61e8525c9` (signature tests: reachable reserved names, named binding).
  No production code changed; production behavior in each case is the planned one.
- 2026-10-27 final runs at source head `61e8525c9` (docs commit added afterwards touches
  only `plan/` and `wiki/`), serial, from `/workspace/cosyn/dafny`, logs in
  `/workspace/tmp/dafny-commit-pin/final-*.log` and `base-*`/`head-nz3-*` logs:
  - `dotnet build Source/Dafny.sln`: 0 errors (`final-build.log`).
  - `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore`:
    608 total, 518 pass, 90 fail (all `HelperFunctionInterpreterTest`, also failing on
    `1de66ec5a`); with `--filter 'FullyQualifiedName!~HelperFunctionInterpreterTest'`:
    511/511 pass.
  - `dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore
    --filter 'FullyQualifiedName~ContractRuntime'`: 306 total, 303 pass, 3 fail (the
    solver-dependent Clause/InitialAdmission tests).
  - `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj
    --no-build --no-restore --filter 'FullyQualifiedName~Contract|FullyQualifiedName~Pbt'`:
    1062 total, 1060 pass, 2 fail (the solver-dependent query tests).
  - Same Driver and TestGeneration commands with `z3-4.16.0` temporarily moved out of
    each test `bin/Debug/net8.0/z3/bin` (Dafny falls back to system z3 4.8.12; file
    restored afterwards): Driver 306/306 pass, TestGeneration 1062/1062 pass.
  - Scoped `dotnet format whitespace --verify-no-changes` on the three edited test
    files exited 0; `git diff --check` clean.
  Skipped checks: no live provider, image or campaign run; legacy test-generation
  classes outside the filters were not run (not touched by the branch).
- Result: all 10 branch-introduced failures are repaired by test updates;
  5 failures remain that are independent of the branch and depend on the selected
  Z3. Status is `blocked` on the solver decision above, not `done`.
