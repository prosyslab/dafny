# Preserve bound variables when recombining trigger splits

Status: verified locally and independently; direct-source native repair accepted.
Verified: 2026-10-14 on working tree based on
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a`.
Originating plan: [trigger scope repair](../plan/2026-10-14-trigger-bound-variable-scope.md).

## Invariant and applicability

`ComprehensionTriggerGenerator.CombineSplitQuantifier` can combine terms only
when their bound-variable identities and ranges are compatible, as well as their
triggers. Quantifier splitting originally shares binders, but subsequent
automatic matching-loop rewriting introduces distinct generated `BoundVar`
objects in each split and an equality range binding each fresh variable.
Two empty trigger-candidate lists compare equal even when their binders differ.
Combining those terms under only the first split's binders leaves a variable
free and causes a Boogie resolution error before SMT verification. Both
universal and existential quantifiers are affected.

The repair checks `BoundVars.SequenceEqual` and identity or structural equality
of the range before grouping. Distinct binders keep separate quantifiers.
Original compatible splits still recombine. This preserves automatic triggers
and all logical terms/ranges; it does not alpha-rename unrelated binders or
change the substitution mechanism. Printed variable names and numerical suffixes
do not establish declaration identity or cross-method sharing.

## Sources and local evidence

- `Source/DafnyCore/Triggers/ComprehensionTriggerGenerator.cs`: recombination and
  compatibility check.
- `Source/DafnyCore/Triggers/SplitPartTriggerWriter.cs`: matching-loop rewriting
  introduces a fresh variable for a trigger-killing expression.
- `Source/DafnyCore/Triggers/ExprSubstituter.cs`: places the new variable and
  its defining equality in the affected quantifier.
- `Source/DafnyCore.Test/TriggerBoundVariableScopeTests.cs`: universal/existential
  free-variable closure fails on original compiler and passes after repair;
  ordinary same-binder recombination passes both.
- `Source/IntegrationTests/TestFiles/LitTests/LitTest/triggers/split-matchingloop-bound-variable-scope.dfy`:
  generic sequence preconditions exercise the full native translation/proof path.

From the native repository root, use:

```sh
dotnet test Source/DafnyCore.Test --no-restore -m:1 -p:UseSharedCompilation=false --filter FullyQualifiedName~TriggerBoundVariableScope
make test name=triggers/split-matchingloop-bound-variable-scope.dfy build=false
```

The integration command requires a prior native solution build. It passes one
fixture with two verified methods and no errors, retaining expected warnings
where a split has no automatic trigger. The unit command passes three cases.
Seven existing trigger splitting/matching-loop integration tests also pass.
Generic scratch logs and intermediate Boogie files are available in this
workspace at `/workspace/tmp/dafny-trigger-scope-repair/`; they are not committed
or stored in documentation trees.

## Limitations

These are local compiler checks, not benchmark scores or evidence of an improved
paid experiment. The owning integration investigation reports that exact private source replay
now reaches ordinary SMT proof results without the former internal binding
error; the candidate still has proof errors, and the bounded complexity replay
timed out. Fresh independent verification passes its own unit/integration and
generic AST/Boogie scope controls and confirms those private replay limits.
The live image remains immutable.
The fix may retain more split quantifiers and emit more no-trigger warnings
where the old compiler incorrectly merged them. No full benchmark or broad
proof suite was run.
