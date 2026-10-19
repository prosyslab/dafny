# Clarify the native proof-input projection boundary

Status: done; source/documentation limits independently accepted, no producer change
Date: 2026-10-16
Owner: Cosyn native Dafny integration
Related: [original integration](2026-10-15-definition-proof-inputs-integration.md),
[proof-input knowledge](../wiki/definition-proof-inputs.md),
[parent iteration](../../../plan/2026-10-16-iterative-shared-ownership.md)

## Objective and acceptance

Document the current producer's raw-translation boundary and the unresolved
requirements for excluding unused procedures. Preserve the distinction between
changed native inputs, different solver behavior and logically invalid proof
reuse. Do not adopt a new producer or weaken proof admission. Acceptance: the
existing topic and index identify these limits, accurately scope historical
verification, link the detailed source study, and pass a fresh independent
documentation/source review. No new native test or manual probe is selected.

## Inspected evidence and existing solutions

Read root, Cosyn and native instructions and native CLAUDE.md; no local plan/wiki
instruction or plan template exists. Native HEAD is
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a` plus extensive pre-existing dirty work.
Preserve it. `DefinitionAnalysis.ProofInputs.cs` hashes a fresh Boogie translation
and excludes foreign eligible ordinary implementations. Existing native tests
and installed manual observations establish particular examples, not completeness
of every preprocessing dependency.

The source-only design study is
`/workspace/tmp/central-verification-20261016/procedure-projection-design.md`,
SHA256 `db60805d8238703219f9aab966b791a97ff6bce188cd3db7a8f07281241c76ef`.
Root read the full study, re-read local frame-lambda and verifier entry paths,
and inspected exact Boogie3.5.5 primary snippets for LambdaHelper, Checker and
ExecutionEngine. Public Git blob identities respectively:
`e9bad4fd021937f2223d5d473aff76cee7a7f56d`,
`9f26352427a565876c527b57fa20eca2ced967a5`,
`7c783fef8738558f439c7080366df5dc951d0082`.
The initial web fetch had a cache miss; the read-only GitHub connector supplied
the exact-tag files. No native program or benchmark input was executed/read.

## Change table

| File | Change, reason and unmet need | Validation |
| --- | --- | --- |
| `wiki/definition-proof-inputs.md` | Describe raw-translation scope and post-translation effects; distinguish source evidence from a false-proof counterexample. Without this note the historical completeness wording can imply a stronger established guarantee than the inspected pipeline supports. | Compare named local and exact-version primary sources; fresh independent review. |
| `wiki/INDEX.md` | Point readers to the same limits without changing historical receipts. | Link and wording review. |
| This plan and `plan/INDEX.md` | Record scope, provenance, open follow-up and validation. | Whitespace, links and Markdown-only record audit. |

Only maintenance knowledge changes. Native/Python implementation, API schema,
test availability, proof semantics, benchmark tasks/evaluator/scoring and live
C7 inputs remain outside scope. The parent retains its two independently accepted
diagnostic fixes as the prospective runtime delta.

## Validation and limits

From `/workspace/cosyn/dafny`, run `git diff --check` and a read-only Python
check of the four records' relative Markdown links, trailing whitespace and
recursive plan/wiki non-Markdown files/symlinks. Check exact native source hashes
before/after to ensure this documentation task did not change the producer.
Fresh `gpt-6.1-sol/high` review starts from these requirements and current source,
with no implementation conversation; it records results in
`/workspace/tmp/proof-input-scope-limits-review-20261016/review.md` and `review.json`.
No test, native build, formatter, solver, container or paid provider call is
appropriate to this documentation-only scope. Source inspection cannot establish
an actual false proof, quantified performance loss, or future pruning correctness.

## Follow-up and authorization

The user authorized harness investigation and improvement; documentation of its
limits needs no new permission. A later implementation needs a separate native
plan selecting the supported verifier/preprocessing boundary and independently
validated dependency footprint. This plan does not authorize call-closure-only
filtering, new heuristics or a duplicated Boogie preparation pipeline.

## Review correction

Fresh review required one wording correction: `Checker.Setup` shuffles the
split's `PrunedDeclarations`, not necessarily every declaration in the original
program. The wiki now states that narrower scope. The producer remains unchanged;
final independent review of the corrected documents was then pending. No execution
validation is implied by this source/documentation correction.

## Independent acceptance and closure

Fresh `gpt-6.1-sol/high` review independently read the local producer/frame/pipeline
sources and exact Boogie3.5.5 files. It accepted the corrected documentation with
no unresolved findings. Report:
`/workspace/tmp/proof-input-scope-limits-review-20261016/review.md`, SHA256
`1fd44ecd91cd230340341c9acac2d6704c5b18e66042e939744a7f438fbd7c36`;
`review.json`, SHA256
`5c1eb818bcb4c470c54febfcd1f4cb99e2441cb7846ba63e53551231548dca8e`.
Root read the full report and matched its four document pins and Markdown report
pin before this plan/index closure. Four-record/23-link, whitespace and recursive
Markdown-only checks passed. Producer SHA256 remained
`6ddff6c9be8be1bd648948331c7b7ad4b2b353bbd455f33a289abb317ecc03ed`,
matching the authorized C7 source-freeze entry. Two initial review discovery
commands used absent paths; actual paths were then located and inspected.

The existing wiki records the reusable boundary and open follow-up. This accepts
the documentation, not a narrower projection algorithm or proof validity claim.
No tests, native/build/container/solver/provider calls or private task evidence
were used. All documentation acceptance criteria are met; the future producer
design remains a separate, unselected implementation requiring its own plan.
