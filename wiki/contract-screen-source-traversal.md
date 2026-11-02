# Traverse syntactic children before contract-screen resolution

Status: native source patch verified in a development build; publication and
linked pin updates explicitly authorized on 2026-11-02. Deployment validation is
tracked in the integration recovery plan. Verified 2026-11-02 against base
`086ba8b875752dc791bf8dc2da9406d79b6bbae9` plus the current two-file patch.

## Finding

Contract-screen preparation parses a source snapshot with `resolve: false`.
Its declaration and module-option scans must use the syntactic child view.
General `Descendants()` follows `Children`, which may require completed name/type
resolution. An explicitly typed local exposes that distinction:

```dafny
method Child(x: int) returns (y: int)
  requires x >= 0
  ensures y == x + 1
{
  var z: int := 0;
  y := x + 1;
}
```

`LocalVariable` stores its syntactic type at construction, but its separate
resolved type is filled later. Before resolution, `Children` emits that null
resolved type for an explicit local. `PreResolveChildren` emits the syntactic
type. The general descendant recursion dereferences the null and crashes during
source-options checking, before any finite contract decision.

The unchanged base compiler reproduced exit 6 and `NullReferenceException` for
this trusted synthetic input. No benchmark candidate source was read to derive
it. A bodyless method alone is not the established cause; its body traversal is
explicitly guarded by the AST implementation.

## Correction and preserved contracts

`ContractScreenSourcePreparation` uses a local `RawDescendants` over
`PreResolveChildren` in exactly two raw scans:

- `RawDeclarations`, over the default module and parsed file snapshots.
- `CheckSourceOptions`, when it enumerates module definitions.

The global `NodeExtensions.Descendants` and post-resolution `ReferenceIdentity`
traversal remain unchanged. Do not discard nulls globally: that would retain the
wrong phase's view and could omit raw syntax. Source-options rejection remains
mandatory for declarations and modules. Logical projection, method-body omission,
source identity and native wire models are not relaxed.

Source evidence:

- `Source/DafnyTestGeneration/ContractTesting/ContractScreenSourcePreparation.cs`.
- `Source/DafnyCore/Generic/NodeExtensions.cs`.
- `Source/DafnyCore/AST/Statements/Assignment/LocalVariable.cs`.
- `Source/DafnyCore/AST/Statements/Assignment/VarDeclStmt.cs`.

Other AST views also depend on phase: calc lines precede resolved steps, and raw
assignment-or-return syntax precedes resolved statements. These support the
choice of syntactic traversal; they are not separate reproduced failures here.

## Verification and limits

Three new focused tests use in-memory snapshots/AST, null writers and ordinary
resolution. They cover typed-local preparation through the full projection path,
declaration source-options rejection, and module source-options rejection. The
class has no filesystem fixture, native compilation, solver, synchronization or
setup/teardown workload. A fresh reviewer traced and executed the selected
prebuilt class: all three facts passed. VSTest's initial sandbox socket denial
and its approved retry remain separate logs.

The independent native development CLI inspection of the exact typed-local
request now completes with a supported binding. Screening x=0 is admissible and
realizable; x=-1 is precondition-rejected. The reviewer validated binding, source
hash, query identities, solver outcomes and counts. Both stderr streams were
empty. This is a trusted standalone development probe, not validation of a newly
deployed image or evidence of benchmark performance. The separate negative property control also passed: a contradictory postcondition
`y < x && y > x` at x=0 produced admissible/unrealizable with validated query
identities and UNSAT/SAT/UNSAT outcomes. It uses the same typed-local source shape.

The supported reproducible image build requires a clean reachable compiler
commit. The base and current remote expecto head remain the same unpatched
commit. Do not label this dirty development artifact as a clean pinned release.
The user explicitly authorized the commit/publish/pin actions after reviewing
the verified patch. Publication and deployed-image receipts belong to the linked
integration recovery plan. Existing evaluator images remain fixed for comparison;
a linked compiler source pin update does not change the selected grading image.

## Evidence and records

- [Owning plan](../plan/2026-11-02-contract-screen-source-traversal.md).
- [Integration recovery plan](/workspace/plan/2026-11-02-fold-child-screen-comparison.md).
- Patch: `/workspace/tmp/fold-native-screen-recovery/native-traversal.patch`.
- Review: `/workspace/tmp/fold-native-screen-recovery/native-patch-review.json`.
- Independent validation: `/workspace/tmp/fold-native-screen-recovery/native-independent-validation.json`.
- Selected-test retry: `/workspace/tmp/fold-native-screen-recovery/native-independent-tests-retry.log`.

These generated records are local and may not remain available outside this
workspace. Keep them outside plan/wiki. No private task/reference or credential
material is required for this finding.
