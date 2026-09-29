# Ghost input initial validity

- Status: done; bounded initial-validity support passed owner and fresh independent native checks. Historical outcomes belong to the parent plan.
- Created: 2026-09-29.
- Owner: Dafny fork, `/workspace/cosyn/dafny`; repository maintenance, not an evaluated run.
- Baseline: `060d5ad532f67d5367450689225274fb0a0243e7`, with extensive pre-existing work preserved.
- Parent: [M2 historical follow-up](../../../plan/2026-09-29-pbt-m2-historical-followup.md).
- Related engine work: [runtime query optimization](2026-09-27-runtime-query-optimization.md).

## Objective and acceptance

Admit a captured ghost entry formal only while preparing the original logical
initial-state certificate. The captured value must remain bound to the original
formal name and declared type; original entry requires must already have passed
before the entry heap capture; missing, malformed, type-inconsistent, refined-type
invalid, and non-compilable values must remain rejected or unchecked.

Acceptance:

1. `ContractRuntimeHeapChecking.PrepareInitial` accepts a present supported ghost
   formal and retains it in the request used by `ContractInitialTypeProof`.
2. The normal executable/final-state `ContractHarnessBuilder.Prepare` path still
   rejects ghost formals, so this change cannot synthesize a runtime call with an
   erased input.
3. Exact input-name matching, `ContractModelCodec` validation, supported-type or
   reference checks, original construction scope, exact native carrier assignment,
   and the runtime entry-requires gate remain mandatory.
4. Focused positive and negative tests pass after the coordinated native lane is
   released. No paid provider or benchmark run is part of owner validation.

## Evidence and design

Applicable `/workspace`, Cosyn, and Dafny subtree instructions and `CLAUDE.md`
were read. No local plan instructions or template exist.

- `ContractRuntimeObligationTransformer.Transform` rejects non-compilable goal
  input types, promotes supported ghost formals into the detached executable,
  serializes every goal input in `PbtMain`, and checks original entry type
  constraints and requires before `CaptureHeap("entry", ...)`. Historical h07,
  h08, h09, and h11 artifacts contain their ghost inputs as typed `input` records.
- `ContractRuntimeHeapChecking.PrepareInitial` selects every original formal by
  name and builds an initial-only request. Missing formals already throw before
  preparation; request validation rejects malformed values.
- `ContractInitialTypeProof.RequiredScope` includes every original input type.
  `Plan` pairs every request input with its original resolved formal type, performs
  decisive host checks where possible, and sends residual pure carriers through
  `BuildInitialTypeProof`, which uses native assignments with qualified original
  types and revealed original dependencies.
- The only blocking gate is `ContractHarnessBuilder.ValidateSignature`: its
  `formal.IsGhost` condition applies even when `initialStateOnly` already omits
  outputs and heap-dependent execution restrictions. Restrict that condition to
  the non-initial path. Keep the existing type/reference condition unchanged.
- H13's unqualified `FileSystem`/`Bytes` error occurs in `BuildClosedClause`; this
  bounded change does not touch closed-clause type rendering. Initial native
  carrier queries use `BuildInitialTypeProof.QualifiedType`.

Historical request artifacts are diagnostic evidence authorized by the parent
plan, not new benchmark inputs. No benchmark source, request, evaluator, dataset,
scoring, or report changes are included.

## Exact changes

| File or symbol | Change and reason | Unmet without it | Validation |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs`; `ValidateSignature` | Ignore `formal.IsGhost` only for input formals on `initialStateOnly`; retain supported-type/reference checks and all normal-path checks | Every h07/h08/h09/h11 initial logical certificate fails before exact validation | Focused new unit tests, affected TestGeneration suite after lane release |
| New `Source/DafnyTestGeneration.Test/ContractGhostInitialValidityTests.cs`; `ContractRuntimeHeapQueryTests.InitialPreparationStillRejectsGhostInputs` | Add isolated controls for supported capture, missing input, inconsistent kind, unsupported ghost type, and normal-path rejection; remove the stale blanket-rejection assertion after explicit root/PE-owner coordination | The boundary could broaden silently, bypass exact type checks, or retain a contradictory old expectation | Focused class filter and affected TestGeneration suite |
| This plan and `plan/INDEX.md` | Record scope, evidence, ownership, validation, and handoff without editing the PE owner's shared plan/wiki | Concurrent work and unrun checks would be ambiguous | Diff review |

Implementation and tests are owned by Dafny TestGeneration only. Specification,
proof, evaluator, dataset, scoring, root experiment, and reporting layers are
unchanged. No durable wiki update is planned because the existing contract-testing
topic already owns the broader pipeline and the parent will document final results.

## Validation and handoff

The PE owner currently owns the exclusive native lane. This task will make only
the source/test/plan edits above, then wait for the lane release before running:

```text
cwd: /workspace/cosyn/dafny
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --filter FullyQualifiedName~ContractGhostInitialValidityTests --logger "console;verbosity=minimal" -m:1
dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --logger "console;verbosity=minimal" -m:1
dotnet build Source/Dafny.sln --no-restore -m:1
make format
```

Expected: focused and affected suites pass, the build has no errors, formatting
does not alter behavior, and the final diff contains no benchmark-specific code.
Until those commands run, the plan remains `in-progress`, never `done`. A fresh
independent verification remains owned by the parent workflow.

## Progress

- Read-only design inspection completed at the dirty baseline. Baseline hashes:
  `ContractHarnessBuilder.cs` `e833e1e88db083cda4fa81b54a8370b13cd381a08726f6f7e8b6e3860f07ca2c`;
  existing shared `ContractRuntimeHeapQueryTests.cs`
  `59eec07a3407913be93b62a4cdeb69ab55049690de839cdc9532da76944fdedb`.
- Implementation complete: the initial-only gate admits supported ghost inputs;
  the normal gate is unchanged; a dedicated test class covers supported, missing,
  inconsistent, unsupported, refined-type, requires, and normal-path behavior.
  The stale blanket-rejection test was removed after root authorization and direct
  coordination with the PE owner, who owns a different test file.
- `git diff --check` and equivalent checks for the two untracked new files passed.
  Current hashes: `ContractHarnessBuilder.cs`
  `6f9e9d5e548e94ce8010fdc5b9a9a731fd6962da9d9040243e0ec82829028eb1`;
  `ContractGhostInitialValidityTests.cs`
  `7e450c791cab29fa01520dc9097a2186519a03be882a9925a5cb773e418c958a`.
- No native build, test, format, provider call, or experiment run performed.

## Final validation — 2026-09-29

All8 new controls passed in the owner's157-case affected TestGeneration run.
Fresh independent verification on unchanged final source passed44 affected native
tests,42 Core reducer tests and7 Driver construction/original-source/heap-budget
controls. The root supported build passed with zero warnings/errors, makeformat
passed with its known workspace-load warning, and transport passed4/4.

The planned unfiltered TestGeneration project command is superseded by the
combined affected157-case suite plus independent boundary checks; unrelated
language/test-generation behavior was not changed. No full-project result is
claimed. Raw commands/logs and exact source hashes are retained in
`/workspace/tmp/experiment/pbt-m2-pe-equivalence-20260929/` and the fresh
`/workspace/tmp/experiment/pbt-m2-historical-20260929/independent-review.md`.
All bounded acceptance criteria pass. Root owns unchanged historical reruns.
Reusable conclusions are incorporated in [contract testing](../wiki/contract-testing.md)
under the parent follow-up; no additional topic page is necessary.
