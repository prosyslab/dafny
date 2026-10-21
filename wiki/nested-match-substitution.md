# Nested statement matches in proof-expression substitution

Status: verified locally and independently (2026-10-21), native `b4f683fd8` plus
the focused four-file repair; delivered on the requested `expecto` branch.
Origin: [native substitution plan](../plan/2026-10-21-nested-match-substitution.md).
Integration: [weekly repair/restart plan](../../../plan/2026-10-21-native-match-crash-weekly-restart.md).

## Cause and applicability

Resolved function bodies can contain proof statements inside statement
expressions and let expressions. A forall proof whose body contains a nested
statement-form match reaches `Substituter.SubstStmt`. That method supported
resolved `MatchStmt` but did not support its source-level `NestedMatchStmt`
wrapper, so legal syntax reached the unexpected-statement assertion during
function-axiom translation, before verification-condition execution.

A small public regression with a nested constructor and a case binder shadowing
an enclosing let variable reproduces the original native SIGABRT. No benchmark
solution or evaluator-only evidence is required. The original weekly failure
and later compiler repair are distinct; old scores are not retroactively changed.

## Substitution contract

Rebuild the nested statement match using its substituted source and resolved
flattened statement. Preserve constructor/literal pattern metadata, ghostness,
origin, optional-brace form and substituted root/case attributes. Pattern-bound
variables must be fresh when type substitution requires it, and references in
case bodies and attributes must use the matching case binding. Shadow an existing
mapping for a pattern binder only inside that case. Restore the complete prior
substitution map after each case, including mappings introduced by local
declarations in its body.

This support does not remove the unexpected-statement assertion for other
unsupported forms and does not add proof assumptions, skips or source-shape
rewrites. Ordinary false assertions must continue to fail verification.

## Evidence and limits

The owner regression is
`Source/DafnyCore.Test/NestedMatchSubstitutionTests.cs` (in-memory AST only).
The native LIT case is
`Source/IntegrationTests/TestFiles/LitTests/LitTest/patterns/nested-statement-substitution.dfy`,
with a positive exact-symbol proof and a separately expected failing proof.
Direct weekly-policy checks use Z3-4.16.0, isolated assertions, one core, seed42
and exact declaration filtering. Fresh independent verification reports
4verified/0errors for the positive; the false-proof control exits4 with
2verified/1error and byte-identical expected ordinary assertion output. The
in-memory unit passes, solution build and scoped C#/Dafny formatting pass.

Build/format commands, independent results and delivered revision are recorded
in the plan. Image/runtime attestation is an integration-owned follow-up and
does not follow merely from a successful host build.
