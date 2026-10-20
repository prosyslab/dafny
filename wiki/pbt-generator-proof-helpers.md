# Generator-local proof helpers

Status: locally accepted after nine focused memory cases, fresh independent review and actual true/false helper proofs. Verification date: 2026-10-20. Native base: `10dca3ba4a2909c11299176440401fc31413b53d` plus the working-tree proof promotion. Originating [helper plan](../plan/2026-10-20-pbt-generator-proof-helpers.md); related [proof promotion plan](../plan/2026-10-20-pbt-generator-proof-promotion.md).

## Authoring and placement

Write the selected target's generator in `.top-down-pbt/generators/<TargetFullDafnyName>.dfy`; for `M.Goal`, the file is `.top-down-pbt/generators/M.Goal.dfy`. Put executable statements, assertions and proof statements inside `Generate`. Add new sibling lemmas, functions, predicates or datatypes in that same file when the construction or proof needs them. Source preparation inserts the declarations into the original goal module, so do not wrap them in an extra module or duplicate existing declaration names.

For a target `M.Goal(x: int)` requiring `x >= 0` and `x % 2 == 0`, this file can contain:

```dafny
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) {
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

Keep the exact `Generate(r: PbtRandom.Source)` input and the target's input names/types as generator outputs. Do not author `requires` clauses on `Generate`: the proof must establish the original goal requirements for generated outputs without restricting the caller. A sibling lemma may have its own requires, and every call must prove them. Do not edit the original target contract to accommodate generated values.

## Checked helper closure

`ContractRuntimeSourcePreparation.PrepareAsync` already accepts callable and datatype siblings through `AddHelper`; no new merge mechanism is required. It preserves the target contract and maps inserted helper diagnostics back to their original generator-file positions.

The bounded proof adds its own admission wrapper and goal-requirement predicates. `ContractSpecificationChecker.AuditedProofScope` requires the selected generator's reachable method/lemma bodies and transitive function definitions to remain checked. The actual `TwiceIsNonnegative` declaration requires native correctness evidence; `Add`, reached through `Twice`, requires function well-formedness evidence. A helper's ensures clause becomes usable only with the required native check coverage. Missing helper checks or any failed native evidence cannot produce certification, even if admission alone appears successful. The unrelated target implementation is outside this generation closure, and calling back into that target rejects the bounded proof attempt.

`ContractGeneratorProofAudit` rejects authored trust attributes such as `{:axiom}`, `{:extern}` and verification skips. An assumption or unchecked `expect` in a retained helper body rejects its audited proof scope. Unsupported top-level siblings, bodyless logical definitions and unsupported proof constructs also fail closed. The exact pinned embedded RNG module has a narrow internal exception; generator-file helpers receive no such exception.

If the optional proof attempt is unsupported, fails or times out, ordinary runtime checking retains the selected entry requirements. Even a successful admission proof preserves declared-type, heap and recursive-call checks. A report or fake coverage object alone cannot authorize omission: production uses the internal source/options-bound certificate.

## Evidence and limits

Sources: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs`, `ContractGeneratorProof.cs`, `ContractGeneratorProofAudit.cs`, `ContractSpecificationChecker.cs` and `ContractRuntimeObligationTransformer.cs`.

`Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs` exercises bounded string preparation/resolution, unchanged original requirements/postconditions, helper source mapping, exact declaration closure and required checks. Its nine cases passed in the combined 121/121 memory-only proof/runtime/helper run on 2026-10-20; commands and artifacts are in the originating plan. Fake native coverage explicitly tests complete, missing-helper and failed-helper evidence; it does not run a solver, prove the sample or mint a production certificate. Assumption, axiom, authored-generator-requires and unsupported-class controls are separate cases. The subsequent actual true/false helper probes and fresh independent acceptance completed in the parent handoff, as recorded below.

## Final independent and native acceptance

Nine helper controls passed within the independently repeated 140-case native selection. Actual public sibling lemma + transitive function proof certifies 10/10; a false helper body fails and keeps entry checks. Fresh independent quantified ghost-predicate/lemma controls certify 9/9 while target assertion, loop invariant, type and postcondition checks remain evaluated. Canonical Cosyn/native end-to-end smoke certifies 10/10 and finds the deliberately wrong target postcondition. Evidence: `/workspace/tmp/experiment/pbt-main-hardening-20261020/r02/`, `r02/independent/`, `canonical-smoke/`, and `/workspace/tmp/pbt-main-hardening-20261020/verify-proof-main.md`. Scoped formatter and Markdown audits pass. No helper insertion production change was necessary; this item closes a regression-coverage and agent-guidance gap. Parent owns the separate requested item-3 commit and main integration.
