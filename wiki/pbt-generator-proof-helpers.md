# Generator-local proof helpers

Status: current authored-contract flow built and memory-tested locally; independent review and actual native controls pending. Date: 2026-10-21. Native base: `b4f683fd85c9764c032346e0367df325f73dd4be` plus the isolated working changes. Originating [current plan](../plan/2026-10-21-pbt-authored-generator-proofs.md); historical [helper plan](../plan/2026-10-20-pbt-generator-proof-helpers.md). Earlier acceptance below concerns the prior mechanism.

## Authoring and placement

Write the selected target's generator in `.top-down-pbt/generators/<TargetFullDafnyName>.dfy`; for `M.Goal`, the file is `.top-down-pbt/generators/M.Goal.dfy`. Put executable statements, assertions and proof statements inside `Generate`. Add new sibling lemmas, functions, predicates or datatypes in that same file when the construction or proof needs them. Source preparation inserts the declarations into the original goal module, so do not wrap them in an extra module or duplicate existing declaration names.

For a target `M.Goal(x: int)` requiring `x >= 0` and `x % 2 == 0`, this file can contain:

```dafny
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int)
  ensures x >= 0
  ensures x % 2 == 0
{
  x := Twice(2);
  TwiceIsNonnegative(2);
  assert x >= 0;
}

lemma TwiceIsNonnegative(value: int)
  requires value >= 0
  ensures Twice(value) >= 0
{
  assert Twice(value) == value + value;
}

function Twice(value: int): int { Add(value, value) }
function Add(left: int, right: int): int { left + right }
```

Keep the exact `Generate(r: PbtRandom.Source)` input and the target's input names/types as generator outputs. State the generated-value properties in authored ensures clauses and prove them with the body and helper calls. Do not author requires clauses on Generate. A sibling lemma may have its own requires, and every call must prove them. Do not edit the original target contract to accommodate generated values.

## Checked helper closure

`ContractRuntimeSourcePreparation.PrepareAsync` already accepts callable and datatype siblings through `AddHelper`; no new merge mechanism is required. It preserves the target contract and maps inserted helper diagnostics back to their original generator-file positions.

The proof source preserves Generate and adds an ordinary lemma whose requires are its authored ensures and whose ensures are all original target requires. Generate and the bridge each need successful native correctness tasks. `ContractSpecificationChecker.AuditedProofScope` supplies the existing reachable method/lemma and transitive function closure; `ContractGeneratorVerification` checks its complete ordinary backend parts. It also checks retained ambient logical definitions, even when unrelated to Generate, because they contribute axioms. A false generator ensure cannot be rescued by a vacuous implication. A correct generator with a weak ensure cannot be rescued by a body that happens to return admissible values. The unrelated target ordinary body remains outside this proof prerequisite; a generator dependency reaching it rejects the attempt.

`ContractGeneratorProofAudit` rejects authored trust attributes such as `{:axiom}`, `{:extern}` and verification skips. An assumption or unchecked `expect` in a retained helper body rejects its audited proof scope. Unsupported top-level siblings, bodyless logical definitions and unsupported proof constructs also fail closed. The exact pinned embedded RNG module has a narrow internal exception; generator-file helpers receive no such exception.

If the optional proof attempt is unsupported, fails or times out, ordinary runtime checking retains the selected entry requirements. Even a successful admission proof preserves declared-type, heap and recursive-call checks. A report or fake coverage object alone cannot authorize omission: production uses the internal source/options-bound certificate.

A reachable bodyless ghost lemma makes proof optimization unsupported. Runtime
source preparation can still proceed because the existing preflight excludes
ghost methods from missing executable drafts and instrumentation erases ghost
lemma calls. Bodyless executable methods and ghost functions remain subject to
their existing draft preflight. This fallback does not pretend the missing
proof body was verified.

## Evidence and limits

Sources: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs`, `ContractGeneratorProof.cs`, `ContractGeneratorProofAudit.cs`, `ContractSpecificationChecker.cs` and `ContractRuntimeObligationTransformer.cs`.

Current focused tests exercise bounded string preparation/resolution, authored
contract preservation, bodyless helpers, ambient scope, source/analyzer drift
and complete ordinary part accounting. The 78-case TestGeneration selection and
nine Driver cases passed with zero skips. Whole analyzer providers are faked;
these tests do not start a solver, prove this sample or mint a production
certificate. The current plan records commands and the test I/O trace.

The helper fixture now crosses the actual preparation/visibility boundary:
runtime snapshots have erased ghost lemma bodies, while authenticated proof
snapshots preserve both nontrivial helper assertions and deliberately false
assertions. Invalid authored ghost proof code is rejected before analyzer use.

## Historical independent and native acceptance, 2026-10-20

Nine helper controls passed within the independently repeated 140-case native selection. Actual public sibling lemma + transitive function proof certifies 10/10; a false helper body fails and keeps entry checks. Fresh independent quantified ghost-predicate/lemma controls certify 9/9 while target assertion, loop invariant, type and postcondition checks remain evaluated. Canonical Cosyn/native end-to-end smoke certifies 10/10 and finds the deliberately wrong target postcondition. Evidence: `/workspace/tmp/experiment/pbt-main-hardening-20261020/r02/`, `r02/independent/`, `canonical-smoke/`, and `/workspace/tmp/pbt-main-hardening-20261020/verify-proof-main.md`. Scoped formatter and Markdown audits pass. No helper insertion production change was necessary; this item closes a regression-coverage and agent-guidance gap. Parent owns the separate requested item-3 commit and main integration.
