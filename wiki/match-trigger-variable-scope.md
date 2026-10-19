# Match-pattern variables and automatic trigger scope

Status: verified locally and independently; exact-source native repair accepted.
Verified: 2026-10-16 on working tree based on
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a`.
Originating plan: [match trigger scope repair](../plan/2026-10-16-match-trigger-variable-scope.md).
Related invariant: [split-quantifier binder compatibility](trigger-bound-variable-scope.md).

## Invariant and repair

An automatic trigger exported from a match expression to an enclosing quantifier
must mention no variable bound by any match case. Both `NestedMatchExpr` and
flattened `MatchExpr` need this check. A term that omits one local variable can
still mention another; testing that it omits at least one local is insufficient.
The old predicates also discarded valid terms when a match had no local binders.

`TriggersCollector.AnnotateNestedMatchExpr` and `AnnotateMatchExpr` now reject
terms mentioning any local pattern variable. They preserve the candidate object
when all its variables are visible outside the match, including zero/one/multiple
pattern-binder cases. No logical expression, bound variable, specification,
verification scope or trigger setting is changed. The earlier `CanCombine`
split-quantifier repair remains independently necessary and unchanged.

## Evidence and bounded validation

`Source/DafnyCore.Test/MatchTriggerVariableScopeTests.cs` has twelve small
in-memory cases: eight direct collector cases cover both match AST forms,
candidate identity retention for zero/one/two binders, and rejection of a term
mentioning one of two local binders; four parser/resolver cases cover universal
and existential quantifiers, enclosing-scope candidates and constructor-only
matches. Parser/resolver cases alone do not cover `MatchExpr`, since
`MatchFlattener` runs after automatic trigger generation.

`Source/DafnyCore/AssemblyInfo.cs` gives standard friend access to the existing
`DafnyCore.Test` assembly. The tests create only tiny ASTs or parse/resolve short
strings. They do not run a compiler build, native solver, subprocess, filesystem
staging, directory creation or synchronization.

From this native repository root, after an operational native build:

```sh
dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~MatchTriggerVariableScopeTests --verbosity quiet
dotnet test Source/DafnyCore.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~TriggerBoundVariableScopeTests --verbosity quiet
```

The twelve new cases and three existing split-scope cases pass. Vstest needs a
local communication socket, unavailable in the default sandbox; the approved
execution path was used. Focused C# formatting passes. The solution operational
build passes with four warnings in unchanged test-generation source; the later
focused test assembly build passes without warnings.

The unchanged generic eleven-line datatype/existential/match reproducer in
`/workspace/tmp/dafny-match-trigger-scope/generic.dfy` previously produced eight
undeclared match-case identifiers in Boogie before SMT verification. With the
repair, the same native command reaches an ordinary unproved postcondition
(exit 4, zero verified and one proof error), with no internal resolution error.
The source and small before/after logs remain workspace scratch, not repository
fixtures or proof-success evidence.

Fresh independent review accepts both owners on 2026-10-16 at 10:18:52 UTC,
with all ten reviewed source hashes matching the current files. It independently
passes 12 new and 3 preserved cases per owner, focused formatting and diff checks,
and repeats the unchanged generic source via stdin: ordinary exit 4, zero
verified/one proof error, no internal binding error. It confirms both AST forms,
candidate identity and free-variable controls, exact friend-assembly access and
in-memory test paths. Workspace-only receipts are
[acceptance JSON](/workspace/tmp/match-trigger-scope-independent-review-20261016/independent-acceptance.json)
and [review](/workspace/tmp/match-trigger-scope-independent-review-20261016/review.md).

The benchmark-native independent formatter's first default-sandbox attempt times
out after 90 seconds (exit 124). Approved escalated retry passes in 12.334 seconds
with unspecified workspace-load warnings. Both attempts remain recorded.

## Limits

Removing malformed candidates can leave a quantifier without an automatic
trigger and produce the existing warning. This is an expected compiler outcome;
it is not authorization to disable warnings, weaken contracts or claim proof
success. No full proof suite, benchmark evaluation, provider call or image update
was performed by this repair. Private candidate evidence stays in the parent
investigation's authorized run analysis; its incomplete replay is separate from
the generic compiler regression and from independent acceptance.
The reviewer performs no independent solution build or benchmark/private-input
check. Acceptance covers only the exact reviewed source paths/hashes in both
dirty native owners; operational builds remain implementation-owned evidence.
