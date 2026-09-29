# Qualify captured closed-clause types

Status: done

Root authorization: [M2 historical follow-up](../../../plan/2026-09-29-pbt-m2-historical-followup.md).
This is engine maintenance using retained public retrospective fixtures; no model
evaluation, provider calls, or hidden inputs. Existing dirty work is preserved.

## Evidence and objective

The h13 baseline `closed-query-10-positive.dfy` captures inferred locals as
`preFs: FileSystem, preStdin: Bytes`. Its result stops at resolution because those
names are unavailable in the insertion module. `BuildClosedClause` prints
`variable.Type` directly, whereas `BuildInitialTypeProof` already qualifies
resolved declarations through `ContractHeapFactory.SourceTypeName`.

Reuse that qualification for captured parameter types, preserving refinements,
generic arguments, collection shape and actual import scope. Keep values,
contracts, proof gates, both truth polarities, limits, and benchmark bytes fixed.
Acceptance: a generic imported inferred-local reproduction reaches native proof
and distinguishes true/false values in both polarities; a definedness violation
remains Error. Existing initial-type and query controls still pass.

| File/symbol | Change and necessity | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractQueryBuilder.cs` | Extract existing local QualifiedType and QualifyValue as reusable private methods; call from BuildClosedClause and existing initial proof | Imported aliases, shadowing, nested/generic types and runtime constructor spellings, existing initial proof tests |
| New `Source/DafnyTestGeneration.Test/ContractClosedClauseTypeTests.cs` | Generic inferred-local closed clause controls | Native results in both polarities and preserved WD failures |
| This plan, `plan/INDEX.md` | Record evidence, commands and results | Diff and root report review |

No specification, evaluator, dataset or scoring changes. Risks: hidden declaration
qualification must fail conservatively; normalizing a subset to its carrier would
erase constraints, so retain NormalizeExpandKeepConstraints exactly as before.

## Validation

Coordinate one native lane with PE/ghost owners. Engine cwd and TMPDIR workspace:
`dotnet build Source/Dafny.sln --no-restore -m:1`; `dotnet test
Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter
'FullyQualifiedName~ContractClosedClauseTypeTests|FullyQualifiedName~ContractQueryTests|FullyQualifiedName~ContractRuntimeHeapQueryTests|FullyQualifiedName~ContractGhostInitialValidityTests'`.
Root final formatting/postformat build and frozen h11/h13 reruns follow. Preserve
baseline owned-file hash and every test result under the root follow-up artifacts.
Independent final review is separate from implementation-owner validation.

## Progress

Ready scope announced; source implementation begins. Existing third-agent slot is unavailable; root owns
this bounded fix. No native commands until PE owner releases the lane.

Independent source-review feedback identifies that captured datatype constructor
names also originate from the declaration's full name, not the local import alias.
Extend the same reuse to existing type-directed QualifyValue before rendering
bindings; use actual runtime-shaped constructor names in the generic fixture.
No new name-guessing rules or value changes are introduced.

Owner validation: build8 passes with zero warnings/errors; all8 new closed-clause
tests pass within the157-case focused TestGeneration pass. Raw log:
`/workspace/tmp/experiment/pbt-m2-pe-equivalence-20260929/testgen-final2.log`.
Final supported packaging build passes51.66s, zero warnings/errors, after
`make format` (exit0, known workspace-load warning). All45 Source hashes remain
identical to the preformat owner manifest. Fresh independent native checks and
the actual h13 rerun remain pending; status stays in-progress.

Actual h13/v1 exposed `nat` resolved declaration identity differing from the
prepared program's NatDecl. Extend QualifiedType's built-in case to compare the
resolved declaration's canonical full name and owning system-module identity,
consistent with SourceTypeName's existing cross-context full-name matching.
Add a native regression with a captured nat type from a separate parse while
retaining the original scope/owner. Keep original refinements and both polarities.
The failed v1 remains immutable; root owns a new v2 freeze/rerun after validation.

The cross-context regression fails4/4 before correction (`nat-before.log`,exit1).
The corrected affected Query/Ghost/RuntimeHeap suite passes191/191
(`nat-after.log`,exit0). Final supported package-v2 build passes28.83s with
zero warnings/errors; makeformat exits0 with the known workspace warning and
transport passes4/4 in20.74s. Fresh independent v2 verification passes12/12
closed-type controls with unchanged pre/post hashes. The v2 Source delta is
exactly QueryBuilder and its dedicated test file; no other source changed.
Final historical v2 reruns remain under the root parent plan.

Closure: final h13/v2 reaches20 closed-query results without the captured-type or
nat name error. It remains inconclusive with no valid samples or violations;
remaining quantified proof timeouts/nonproofs, two Unicode escape parse errors
and post-deadline classification costs are outside this type-qualification slice.
Native positive/negative and WD controls, supported final build, transport and
fresh independent12-case review satisfy this plan's acceptance. Exact historical
receipts and the independent review are linked from the root parent plan.
