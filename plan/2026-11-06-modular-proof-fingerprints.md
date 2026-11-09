# Modular proof-input fingerprints (per implementation, pruned solver input)

Status: in-progress (user approved implementation on 2026-11-06; decisions: include the solver binary in toolchain identity; 2026-11-06 review follow-up: order-insensitive key and native lookup by modular key, see below)
Date: 2026-11-06
Owner: native fork (`/workspace/dafny-optimization`)
Parent: root plan draft `/workspace/tmp/modular-proof-design/root-plan.md`; consumer:
`/workspace/tmp/modular-proof-design/cosyn-plan.md`.
Target location when adopted: `plan/2026-11-0X-modular-proof-fingerprints.md` and `plan/INDEX.md`.

## Objective

Replace the whole-program proof-input fingerprint with a per-target fingerprint that
covers exactly what the solver can see for that target, so that an unrelated merge
leaves earlier proofs reusable. The same per-implementation key binds the native
result-cache checksum and the `proofInputs` document (schema 2) that Cosyn's ledger,
the final gate and the root shared scope consume.

The per-implementation key covers:
- the implementation, after the session's one-shot lambda lifting;
- its own procedure and every called procedure (contracts and where clauses), plus
  bodies of any `{:inline}` callee (or the target is unsupported, see below);
- the Boogie live set from `Pruner.GetLiveDeclarations` (a sorted multiset since 2026-11-06);
- effective options including the seed (`ProofOptionsHash`);
- toolchain identity (assemblies plus the solver binary, which is missing today).

It excludes token positions, `{:id}`, `{:captureState}`, the binding `{:checksum}`,
and counter-generated names (`lambda#N`, plus any others found by the stability test).

## Acceptance criteria

1. On a copy of public plus reference Cat, an edit confined to one declaration changes
   only the keys of targets whose live set or callee contracts contain it. All other
   targets keep identical keys and get native cache hits (0 solver runs).
2. Superset property: for every real split prepared by Boogie for Cat (with
   `--isolate-assertions`), `split.PrunedDeclarations` restricted to the kinds that
   `Checker.Setup` declares is a subset of the computed live set, in the same relative order.
3. Every native verification target gets a proof input, including targets with no
   Boogie implementation (`CatCore.InputDataPiece`, `CatCore.InputFailed`,
   `CatCoreModel.InitState`). By-method, extreme, `{:verify false}` and inline-callee
   cases remain unsupported and are reported, never given a partial certificate.
4. The negative tests below all miss; the metamorphic tests below all hit.
5. The 11-06 identical-bytes second call (smoke) reuses 60 of 60.
6. Cold Cat analysis time increase is measured and recorded. No acceptance threshold
   is set before measuring; above +20 % the user decides.

## Non-goals

No Boogie fork change. No change to one-shot `verify` behavior. No change to the
root scope or Cosyn (separate plans). No paid run. No exclusion policy here (root owns it).

## Evidence

- Current key: `DefinitionAnalysis.ProofInputs.cs::ProofInputsFor` (l.173-266) hashes, per
  definition, every translated top-level declaration of every verifiable module except
  other definitions' modular method/lemma implementations. Any merge that changes any
  function, contract or axiom anywhere changes every fingerprint (diagnosis in
  `cosyn/plan/2026-11-06-single-proof-final-check.md`).
- `BindNativeVerificationChecksums` (l.106-127) binds that per-target fingerprint plus
  `AssertionShape` into every implementation's `{:checksum}`, so native cache hits also
  need whole-program equality.
- Session order (`AnalysisSessionCommand.cs`): `State.PrepareProofInputs` (l.1205-1222)
  hashes fresh unlifted translations, then binds checksums; `SharedVerifier.GetVerificationTasksAsync`
  (l.1380-1386) then calls `LiftLambdasAsOneShot` (l.1318-1343) and Boogie. The
  fingerprint is therefore computed on a program the solver never sees.
- Boogie 3.5.5 (`/workspace/tmp/session-cache-retention-review/boogie`):
  - `Checker.Setup` (VCGeneration/Checker.cs:161-193) declares exactly
    `split.PrunedDeclarations`, limited to TypeCtorDecl, Constant, Function, Axiom and
    GlobalVariable, after `GetReorderedDeclarations`. With seed 42 that is a seeded
    shuffle of the list in program order (l.197-209).
  - `Split.PrunedDeclarations` (Splits/Split.cs:41-57) is
    `Pruner.GetLiveDeclarations(options, program, split.Blocks)`, computed lazily per split.
  - `Pruner.GetLiveDeclarations` (Prune/Pruner.cs:61-97) keeps every non-pruned kind
    (types, globals, procedures, implementations). It keeps a constant, axiom or function
    only when it is reachable from the blocks or `{:keep}` roots over
    `program.DeclarationDependencies`. Merge nodes model trigger tuples: an axiom is live
    only when every term of one of its triggers is reachable (`AxiomVisitor`).
    Function `uses` axioms are outgoing edges (`FunctionVisitor`). `{:include_dep}` adds
    edges. CanHide axioms of hidden functions are cut (`RevealedAnalysis`); merging
    asserts unions the revealed sets.
  - `program.DeclarationDependencies` is computed once, after `ExpandLambdas`
    (ExecutionEngine.cs:597-623), so lifted lambda functions are graph nodes.
  - `VerificationTask` looks up the cache in its constructor (VerificationTask.cs:30-43),
    after `PrepareImplementation` and `ManualSplitFinder` (ExecutionEngine.cs:767-808).
    `VerificationResultCache.Lookup` compares `impl.Id`, the `{:checksum}` attribute and
    the memoized dependency checksum (Absy.cs:1682-1770).
  - `RandomiseNamer` (seed != 0) renames every SMT symbol to `random<n>` by naming order.
    Dafny sets `EmitDebugInformation=false` (DafnyOptions.cs:365), so no `:qid`,
    `:skolemid` or vc-id reaches the solver. The SMT text is invariant under a consistent
    renaming of Boogie symbols.
  - `LambdaHelper.FreshLambdaFunctionName` uses a global counter (`lambda#{lambdaid++}`).
- Dafny: TypeCtorDecl and GlobalVariable come only from the prelude
  (`BoogieGenerator.PredefinedDecls`); `Verifier/` creates none. The never-pruned kinds
  are therefore toolchain-owned.
- Zero-obligation functions: `FunctionWellformednessChecker.Check` emits the
  implementation only when `EmitImplementation` holds (`assertionCount > 0`,
  BoogieGenerator.cs:1797-1804; Functions.Wellformedness.cs:155). The procedure's token
  is `f.Origin`, not a `CanVerifyOrigin`, so `ProofInputsFor` finds no owner and skips
  the definition (l.247-253). The 11-04 public-Cat document
  `/workspace/tmp/incremental-analysis-scope/session-check/05-expanded-roots.stdout`
  (temporary) has 119 proof inputs. `CatCore.InputDataPiece`, `CatCore.InputFailed` and
  `CatCoreModel.InitState` are absent, while the similar `CatCore.InputErrorPiece`, which
  has obligations, is present. Without a certificate, Cosyn never retains these targets
  and re-verifies them (0 obligations, about 0.9 s each). This explains the 3 targets
  re-proved in the 11-06 smoke second call (`final-gate-smoke/summary.json`: 57 reused,
  3 proved, proof coverage 2.8 s). Fingerprint instability does not.

## Design

1. Where it is computed: once per module translation per compilation, before
   `GetVerificationTasks`, on the lambda-lifted program. That is where checksum binding
   happens today, so Boogie's lookup stays the sole cache authority (no lookup hook,
   no change to `VerificationTask`).
   - Resolve, type-check and lift via `LiftLambdasAsOneShot`; make it idempotent with a
     per-program marker so `GetVerificationTasksAsync` does not lift twice.
   - Then call `Pruner.ComputeDeclarationDependencies(options, program)` (public).
2. Live set per implementation: call `Pruner.GetLiveDeclarations(options, program, roots)`
   with `roots = impl.Blocks` plus one synthetic unreachable-safe block of `AssumeCmd`s.
   That block holds the own procedure's requires and ensures, every called procedure's
   requires, ensures and formals' where clauses, and the impl's parameter and local
   where clauses. Keep only the solver-declared kinds.
   - This is a sound superset of each split's set. Splits only rewrite asserts and cut
     blocks, call desugaring only uses those contracts, and the union of revealed
     states over all asserts is a superset.
   - Equality of the superset content, as a multiset, implies equality of every split's
     pruned declaration set. The reachable sub-graph is determined by the contents of
     reachable declarations. (Corrected 2026-11-06: the declared order can still differ,
     because `GetReorderedDeclarations` shuffles the whole pruned list, including
     procedures and implementations. An equal key means a logically identical formula set.)
3. Canonical serialization: reuse `ProofDeclarationHash` (Boogie printer with
   `TokenTextWriter(setTokens:false)`, Boogie lexer, length-framed tokens, `{:id}` and
   `{:captureState}` dropped).
   - Also drop `{:checksum}`.
   - Replace each `lambda#N` by `lambda@<sha256 of the lifted function and its defining
     axiom with the self-name masked>`, computed once per program.
   - Memoize declaration hashes per program in a `ConditionalWeakTable<Declaration,string>`.
   - Key = SHA-256 of JSON `{schema:2, toolchain, optionsHash, impl, ownProcedure,
     callees:[sorted (name, hash)], live:[sorted (kind, hash)], hidden:[sorted]}` (live sorted since 2026-11-06; `hidden` was dropped, see the notes).
4. Target fingerprint (schema 2): the SHA-256 of the sorted `(implName, key)` list of
   implementations owned by the target's `CanVerifyOrigin`. An empty list is valid for a
   zero-obligation target, and the translation itself then certifies that there is
   nothing to prove.
   - Each definition also reports `implementations` (count) and `closureOrigins`: a
     source-path-to-merged-spans map of the Dafny origins of all live declarations and
     callee procedures, plus a `toolchain` bucket for prelude and NoToken declarations.
     Root uses it for the given-declaration rule. It is not part of the key.
5. Checksum binding: `BindNativeVerificationChecksums` uses
   `ProofHash(key + "\0" + AssertionShape)` per implementation. Unsupported
   implementations keep the fresh GUID. The Dafny base checksum is dropped because the
   key contains the implementation text.
6. Toolchain identity: add the solver identity (resolved solver path plus `z3 --version`
   output, or a one-time hash of that binary) to `ProofToolchainHash`.

## Change table

| File / symbol | Change | Why / unmet without it | Test |
| --- | --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` `ProofInputsFor`, `ProofInputsFromTranslations`, records `DafnyProofInputs`/`DafnyDefinitionProofInput` | Schema 2: per-implementation keys from the lifted program's live set; target fingerprint over owned implementation keys; zero-implementation targets certified; add `implementations`, `closureOrigins` | Whole-program key defeats reuse; 3 Cat targets never certified | `DefinitionProofInputsTests` (new cases below) |
| new file `Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs`, `DefinitionAnalysis.ModularProofKeys` (internal, nested) and public `DefinitionAnalysis.LiftLambdasOnce` | `Compute(DafnyOptions, Bpl.Program)`: idempotent lift, dependency graph with quantifier-position restore, synthetic root block, `GetLiveDeclarations`, memoized declaration hashes, lambda content names | Core of the change (moved to its own file during implementation) | `ModularProofKeyTests` (new, DafnyCore.Test) |
| `Source/DafnyCore/DafnyOptions.cs` `ResolveZ3ExecutablePath`, `FindBundledOrSystemZ3` | Resolve the solver binary like `SetZ3ExecutablePath`, without side effects (search extracted, behaviour unchanged) | Solver identity must name the binary that would run | `ModularProofKeyTests.SolverIdentityRequiresAResolvableZ3` |
| same file `ProofDeclarationHash` | Also drop `{:checksum}`; apply lambda canonical names | Generated ids change with unrelated edits | Stability tests |
| same file `ProofToolchainHash` | Add solver identity | A solver change must miss | Fake-boundary unit test (no real binary hashing in tests) |
| same file `BindNativeVerificationChecksums` | Bind per-implementation key plus `AssertionShape` | Cache hits need whole-program equality | `NativeVerificationCacheTests`, `AnalysisSessionRetentionTests` |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs` `State.PrepareProofInputs`, `LiftLambdasAsOneShot`, `SharedVerifier.GetVerificationTasksAsync` | Lift (idempotent) before computing keys; compute keys once per State; share with verify | Fingerprint must describe the solver's program | `AnalysisSessionLambdaLiftingTests`, retention tests |
| `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` (one-shot proof-input path) | No edit needed: `ProofInputsFor(program, uris)` translates, lifts and keys through the same code | One-shot and session documents must be equal | Existing one-shot/session parity tests; real Cat comparison |
| `Source/DafnyDriver.Test/AnalysisSessionRetentionTests.cs` | Cross-compilation reuse after an unrelated edit; session schema-2 zero-obligation row | Session evidence for criteria 1 and 3 | New tests |
| `python/dafny_analysis/models.py` `DafnyProofInputs`, `DafnyDefinitionProofInput` | Accept schema 2, `implementations`, `closureOrigins` (extra still forbidden) | Clients parse with `extra="forbid"` | Python client unit tests |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, `plan/INDEX.md` | Record key definition, superset argument, limits | Durable knowledge | Link review |

## Tests (in-memory programs, no temporary directories, fake solver unless stated)

Negative cases (each must change the key and miss the cache):
- A changed callee contract (requires, ensures, where clause).
- A changed body of a function the target uses (visible function).
- A changed body of an opaque function that the target reveals.
- A changed body of an opaque function that the target does not reveal. This also misses,
  because the body axiom is reachable from the function; record it as conservative.
- A `hide`/`reveal` change.
- A datatype constructor added to a datatype the target uses.
- A changed axiom in a library or module (for example a `{:axiom}` in a library source).
- A changed library source.
- A trigger-tuple axiom whose every trigger term becomes reachable after an edit.
- Changed options or seed, a per-implementation `{:random_seed}`, `{:isolate_assertions}`
  or `{:vcs_split_on_every_assert}`, and changed time or resource limits.
- A changed toolchain (fake identity).
- A changed `{:inline}` callee body, or the target becomes unsupported.
- A zero-obligation function that gains an obligation.

Metamorphic cases (each must keep the key and hit the cache):
- Whitespace changes and position shifts.
- An unrelated function or lemma added anywhere.
- An unrelated lambda added earlier, which renumbers `lambda#N`.
- `{:id}` renumbering.
- A trigger-tuple axiom with only one trigger term reachable.
- Changes inside a sibling lemma body.

Superset property: for every split of a small fixture with `--isolate-assertions`, and
in the real Cat check below, `PrunedDeclarations ⊆ live` with order preserved.

Session: an edit-then-verify sequence shows hits on unaffected implementations and
`AssertionShape` rebasing still holds.

## Validation

Cwd `/workspace/dafny-optimization`. Free local checks only.
- `dotnet build Source/Dafny.sln`.
- `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~DefinitionProofInputs|FullyQualifiedName~ModularProofKey|FullyQualifiedName~ProofInputRepeatability"`.
- `dotnet test Source/DafnyDriver.Test --filter "AnalysisSession|NativeVerificationCache|NativeTaskEntry|LambdaLifting"`.
- Python client tests.
- `dotnet format whitespace --verify-no-changes` on the touched files.

Real-binary check (tmux, after the paid run):
- Build into `/workspace/tmp/modular-proof-fingerprints/bin`.
- Copy public Cat plus the three reference files to `/workspace/tmp/modular-proof-fingerprints/cat`.
- Record the cold analysis time before and after.
- Check the superset property over all Cat splits.
- Run 5 single-declaration edits (CatProof lemma body, CatCore helper body, CatCore
  contract, one function body, one unrelated addition) and record the per-target key
  diffs and the session cache hits.
- Replay the identical-bytes second call and expect 60 of 60 reused.

A fresh independent verifier (Sonnet) runs afterwards from the requirements only.

## Risks and open points

- The superset may be much larger than the exact per-split set, which reduces hits.
  Measure the size ratio on Cat (live set against the union of split sets).
- (Superseded 2026-11-06.) The key was ordered. It is now order-insensitive, because the
  per-split SMT order was never fixed by it. Limit: equal keys can give a different
  declaration order and solver time, so a reused success near the 30 s limit can time out
  when grading proves it again.
- Analysis cost: Boogie resolve, type-check, lift and the dependency graph now run on the
  analysis path. In the session they are shared with verify, but the one-shot path pays them.
- Boogie's own dependency checksum (procedure and function `{:checksum}`) still applies.
  Unstable function checksums would cause spurious misses (a metamorphic test covers this).
- Warnings and resolution are not solver input. Consumers must still check warnings on
  the final bytes (Cosyn and root plans).
- Unknown: whether Dafny ever emits procedure `{:inline}` in these programs. Fail closed.
- Time-limit nondeterminism near 30 s is unchanged. A reused success is sound, but a
  fresh grading proof could still time out.

## Review follow-up: decisions and scope change (2026-11-06)

The independent review accepted the implementation with fixes. The user decided:

1. Order-insensitive key everywhere (replaces the earlier "keep program order" decision).
   - Reason (review): `Checker.GetReorderedDeclarations` shuffles the whole `PrunedDeclarations` list, which
     also contains unrelated procedures and implementations. So an ordered key never guaranteed the same per-split
     SMT order.
   - Change: the live list and the callee list enter the key as sorted multisets of `(kind, canonical hash)`. The
     content-based renaming of lifted lambdas stays.
   - Meaning of an equal key: a logically identical solver formula set. The declaration order, and so solver time,
     can differ.
   - Known limit: a reused success near the 30 s limit can time out when grading proves it again from scratch.
   - Root measured that adding the reference `CatProof.dfy` changed 6 of 7 given `Cat.dfy` method keys only
     through order.
2. The native result cache reuses a Valid result exactly when the modular key, the assertion shape, the
   options/seed and the toolchain match, whatever Boogie's dependency checksum says. Per-split completeness
   (publish only complete Valid rosters) and result rebasing stay.
   - Mechanism: for an implementation with a key, `BindNativeVerificationChecksums` also sets Boogie's dependency
     identity (`MD5DependencyChecksum_`) to a digest of the bound checksum. Boogie's lookup and the session journal
     then compare the key, never the transitive Dafny `{:checksum}` closure. Implementations without a key keep
     Boogie's own dependency checksum and a fresh GUID checksum.
   - Soundness: the key covers a superset of every split's solver input (0 violations over 3447 Cat splits).
3. Solver identity: the hashed Z3 binary must be the one that runs. One resolution rule; fail closed when several
   different `PROVER_PATH` values are present.
4. Info: zero-obligation certificates of one toolchain and options share one digest. Consumers key by source path
   plus full name plus digest (documented in the wiki).

New acceptance criteria (added; criteria 1 to 6 above stay):
7. Program order is not part of the key. A Core regression test: a given declaration in one file keeps its key when
   another file adds or reorders unrelated declarations (the skeleton-to-reference shape).
8. On Cat, all 7 given `Cat.dfy` declarations keep their key from the release skeleton
   (`/workspace/tmp/shared-given-scope/skeleton`) to the reference candidate.
9. In a session, an edit outside a target's live set hits the native cache for that target (0 solver runs). An edit
   inside the live set, and an options, seed or toolchain change, miss.
10. Several conflicting `PROVER_PATH` values give no solver identity (no proof inputs).

Changes (scope update to the change table):

| File / symbol | Change | Test |
| --- | --- | --- |
| `DefinitionAnalysis.ModularProofKeys.cs` `ImplementationContent`, remarks | Sorted live and callee multisets; fix the claim in the remarks | `ModularProofKeyTests` order tests, superset test |
| `DefinitionAnalysis.ProofInputs.cs` `BindNativeVerificationChecksums` | Key-derived dependency identity | `ModularProofKeyTests`, `AnalysisSessionRetentionTests` |
| `DafnyOptions.cs` `ResolveZ3ExecutablePath` | One rule, fail closed on conflicting paths | `SolverIdentityRequiresAResolvableZ3` |
| `wiki/native-analysis-session.md` | Order-insensitive meaning, timing limit, lookup change, zero-obligation digest note | Review |

Validation: the Core and Driver filters, Python tests, format and two mutations as before; superset probe; rebuild
into `/workspace/tmp/session-cache-retention/bin`; Cat re-measurement (stability, unrelated edit key and native
hits, skeleton-to-reference given keys).

## Implementation notes and deviations (2026-11-06)

- Code location: `ModularProofKeys` lives in the new file
  `Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs` (nested internal class of `DefinitionAnalysis`).
  `DefinitionAnalysis.LiftLambdasOnce` is the public, idempotent lift. The session's `LiftLambdasAsOneShot`
  delegates to it, so proof-input preparation and task preparation share one lifted program.
- Revealed state: the synthetic root block starts with `assert true` under the initial all-revealed state, so no
  CanHide edge is cut. This is a larger, still sound superset than the merged revealed state of the plan. The key
  has no `hidden` field. Instead, the unprinted `Axiom.CanHide` flags (and whether a function has a
  `DefinitionAxiom`) are appended to declaration hashes.
- Roots also include the where clauses of all global variables (havoc after calls and modifies).
- Live list kinds: TypeCtorDecl, Constant, Function, Axiom, GlobalVariable, plus TypeSynonymDecl (never pruned,
  can name a type in printed text). Superset checks compare only the kinds `Checker.Setup` declares.
- New finding (Boogie 3.5.5): `AxiomVisitor` sets `Expr.pos` from the previous value of the same object
  (`NegatePosition(n.Args[0].pos)`). A second dependency-graph computation over the same program can differ from
  the first. Positions are read back only for quantifiers of `{:include_dep}` axioms. `Compute` records the
  positions of all quantifiers in axioms and restores them, and it restores `DeclarationDependencies`, so the
  engine's own computation equals a one-shot run. Test: `KeyComputationLeavesTheEngineDependencyGraphUnchanged`;
  Boogie pin: `BoogieDependencyGraphDependsOnEarlierComputations`. Dafny emits no `{:include_dep}` today.
- Fail closed per implementation: missing or ambiguous own or called procedure, a callee with `{:inline}` on its
  procedure or any implementation, or any desugared command other than `call`/`par call`. Fail closed per program:
  lambda expansion off, ill-formed Boogie program, two lifted lambdas with one name or equal content, or cyclic
  lambda references.
- Zero-obligation certificate: issued only if no implementation in any translation lacks a `CanVerifyOrigin`, and
  the scope marker procedure exists (`CheckWellformed$$<f>` for functions, `Impl$$<m>` for methods and lemmas).
  Dafny emits these exactly when the declaration is checked.
- Checksum binding: every implementation with a key gets `ProofHash(key + "\0" + AssertionShape)`, whatever its
  owner. Others get a fresh GUID.
- Toolchain: `ProofToolchainIdentity(options)` = hash of the assembly identity and `z3:<sha256 of the solver
  binary bytes>`. The binary is resolved by the new side-effect-free `DafnyOptions.ResolveZ3ExecutablePath` (last
  `PROVER_PATH`, else the bundled copy, else PATH; non-Z3 solvers give no identity). `ContextToolchainIdentity`
  (transfer, evidence) is unchanged. One-shot proof inputs now need a resolvable Z3 binary; otherwise they are null.
- Dafny drops a method's `{:random_seed}` attribute (it never reaches Boogie), so it is not solver input. The
  per-implementation `{:random_seed}` case is tested at Boogie level.
- An earlier unrelated Dafny lambda misses: Dafny lambdas lift into a body function plus helper functions shared by
  all one-argument lambdas, and the earlier lambda lifts the helpers first. That moves the target's body function
  in program order. This is the fail-safe consequence of keeping program order (user decision). Renumbering
  without reordering hits (Boogie-level test).
- `DefinitionAnalysisCommand.cs` needed no change: the one-shot path translates, lifts and keys through
  `ProofInputsFor`.

## Progress

- 2026-11-06: Implemented the change table (uncommitted, branch `native-session-optimization`, base 650e6db3,
  tree already dirty from the lambda-lifting, response-limit and transfer work).
- Local checks, cwd `/workspace/dafny-optimization`, dotnet 8.0.133, run serially in tmux `modular-fp-checks`
  (logs in `/workspace/tmp/modular-fingerprints/`, temporary):
  - `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q`: rc 0.
  - `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~DefinitionAnalysis|FullyQualifiedName~ProofInput|FullyQualifiedName~DeclarationClone|FullyQualifiedName~Snippet|FullyQualifiedName~Token|FullyQualifiedName~ModularProofKey"`:
    121 passed (55 in the new `ModularProofKeyTests`).
  - `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~AnalysisSession|FullyQualifiedName~NativeVerificationCache|FullyQualifiedName~ParserCacheClone|FullyQualifiedName~CachedParser|FullyQualifiedName~NativeTaskEntry|FullyQualifiedName~LambdaLifting"`:
    167 passed (2 new retention tests).
  - Python client, cwd `python`: `python3 -m pytest -q -p no:cacheprovider tests`: 157 passed, 24 deselected
    (integration marker; not run). 6 new schema-2 model tests.
  - `dotnet format whitespace --folder --verify-no-changes --include <6 touched C# files>`: clean after one
    whitespace fix in `DefinitionAnalysis.ProofInputs.cs`.
  - Mutations, each restored byte-identically (sha256 compared):
    1. Drop `quantifiers.Restore()`: `KeyComputationLeavesTheEngineDependencyGraphUnchanged` fails (1 of 55).
    2. Drop the zero-obligation scope-marker check: `DeclarationOutsideVerificationScopeHasNoProofInput` and
       `LibrarySourceChangesTheKey` fail.
- Real binary on a Cat copy (`/workspace/tmp/modular-fingerprints/cat`, copied from
  `/workspace/tmp/session-verify-mismatch/ws`; flags `--standard-libraries:false --library:bench/core
  --allow-warnings --boogie=/randomSeed:42 --verify-included-files --isolate-assertions
  --verification-time-limit:30 --allow-external-contracts`). Baseline binary: copy of the previous
  `/workspace/tmp/session-cache-retention/bin` (`.../modular-fingerprints/bin-before`, schema 1). Scripts and
  outputs are in `/workspace/tmp/modular-fingerprints/{scripts,probe,out}` (temporary).
  - Superset (`probe`, reflection on the built DLLs, real `ExecutionEngine.GetVerificationTasks`): 9 module
    translations, 154 implementations, 3447 splits, 0 violations (every split's declared list is an ordered
    subsequence of the live set), 0 unsupported, 210 lifted lambdas, no name collisions.
    Live set over a split's declared list: median 1.31, mean 1.86, max 24.1. Live set over the union of the
    implementation's splits: median 1.01, mean 1.50, max 12.5. Mean live 803 declarations; mean declared per split 682.
  - Stability: two one-shot runs, 134 of 134 rows equal; two separate sessions, 134 of 134 rows equal.
    Session and one-shot `optionsSha256` differ (`PROVER_PATH` is in the session's prover options). This was
    already true with the old binary. Consumers must compare within one mode.
  - Coverage: all 60 final-gate targets (Cat.dfy 8, CatCore.dfy 27, CatProof.dfy 25) have a proof input. The old
    binary missed `CatCore.InputDataPiece`, `CatCore.InputFailed` and `CatCoreModel.InitState`, which now have
    `implementations: 0` (also `Cat.CatBenchmarkItem._ctor`).
  - Unrelated merge (`CatCore.InputErrorPiece`: `case Ok(_) => []` to `[] + []`): 46 of 60 final-gate targets keep
    their fingerprint (old: 0 of 60). The 14 that change all reach the helper (`InputErrorPiece`,
    `ObservationErrorFragments`, `InputTraceWitnessRelation`, `CoreSummary`, `RunCore`, four CatProof lemmas, ...).
  - Native reuse after that merge, one session, in-place edit, `--filter-symbol`: untouched
    `CatCore.ExpectedStdinAtExtend` (key unchanged) ran 6 of 6 solver checks again (0 hits). The edited helper
    was proved again, as expected. Cause: Boogie's `DependencyChecksum` combines the Dafny `{:checksum}` of the
    transitive function dependencies collected by `DependencyCollector` (functions mentioned anywhere in
    definition axioms). For this lemma that is 1580 functions, including `InputErrorPiece`, while trigger-gated
    pruning never reaches it. Over all 154 implementations, 133 keep their bound checksum and 94 also keep the
    dependency checksum. The miss is safe, but acceptance criterion 1 (native hits) is not met. A fix changes
    the lookup authority (for example, skip the dependency comparison for key-bound checksums in
    `NativeVerificationCache.Lookup`, or bind the dependency checksum to the key). The design excludes that, so it
    needs a user decision.
  - Cost, cold analysis with proof inputs: one-shot new 30.0 to 31.3 s against old 35.5 to 38.2 s; session new
    32.9 s against old 39.9 s (about 17 % faster: schema 1 serialized the whole translation once per definition).
    In-process split for the new path: lift (resolve, type-check, lift, 9 modules) 6.9 s, key computation 5.4 s.
    On the verify path, the lift moved earlier and is not repeated.
- Final rerun after the whitespace fix and the mutations (tmux `modular-fp-checks2`, same commands): rebuild
  into `/workspace/tmp/session-cache-retention/bin` rc 0 (4.11.1+650e6db3, dirty tree), Core 121 passed,
  Driver 167 passed. Python: `ruff check`, `ruff format --check` and `pyright` on `dafny_analysis/models.py` and
  `tests/test_models.py` clean; pytest 157 passed. The Cat measurements above used the first build, which differs
  only by that whitespace fix.
- Skipped: criterion 5 (replay of the 11-06 harness smoke, 60 of 60 reused) needs the Cosyn and root changes
  and the image. It was not run. Python integration tests (marker `integration`) were not run.
- Status stays in-progress for the independent verifier. Open decision: native hits under Boogie's dependency
  checksum (see above).
- 2026-11-07, review follow-up implemented (decisions 1 to 4 above):
  - `ModularProofKeys`: callee and live lists enter the key as sorted multisets; remarks corrected (equal key =
    logically identical formula set; order and solver time can differ). `ImplementationKey.Live` keeps program order
    for the superset check.
  - `BindNativeVerificationChecksums`: a key-bound implementation gets `MD5DependencyChecksum_ =
    KeyDependencyIdentity(checksum)` (SHA-256 of the bound checksum). Boogie's lookup and the session journal then
    compare key plus assertion shape only. Boogie never resets that field (checked in Absy.cs).
  - `DafnyOptions.ResolveZ3ExecutablePath`: the single distinct `PROVER_PATH`; several distinct values give null.
  - Tests: `ProgramOrderIsNotPartOfTheKey`, `EarlierDafnyLambdaKeepsTheKey` (both inverted),
    `GivenDeclarationKeepsItsKeyWhenProofsAreFilledIn` (skeleton shape: an empty module declared first gains an
    import, so the `Lib` and `Spec` blocks swap order; the test asserts that order differs and the key does not),
    `DependencyIdentityFollowsTheModularKey`, `SolverIdentityRequiresOneResolvableZ3`; Driver
    `NativeLookupFollowsTheModularKey` (datatype, constructor and predicate shape that Boogie's dependency collector
    follows) and `SeedChangeMissesTheNativeCache`.
  - Finding while building the skeleton test: on Cat, filling `CatCore`/`CatProof` adds imports, which moves those
    modules (and `BenchItem` after them) in the module translation order; the given keys' live sets were equal as
    multisets (probe `order` mode, `/workspace/tmp/modular-fingerprints/out/order-*.txt`).
  - Checks (tmux `modular-fp-round2`, logs `/workspace/tmp/modular-fingerprints/round2/`): rebuild into
    `/workspace/tmp/session-cache-retention/bin` rc 0; Core filter 123 passed; Driver filter 169 passed; Python 157
    passed; format clean on the six touched C# files.
  - Mutations, each restored byte-identically (sha256): (1) no position restore: 1 failure; (2) no scope marker:
    2 failures; (3) no key dependency identity: `NativeLookupFollowsTheModularKey` and
    `DependencyIdentityFollowsTheModularKey` fail; (4) ordered live list: `ProgramOrderIsNotPartOfTheKey`,
    `EarlierDafnyLambdaKeepsTheKey` and `GivenDeclarationKeepsItsKeyWhenProofsAreFilledIn` fail.
  - Cat, new binary (scripts `scripts/measure3.py`, `scripts/session_stability.py`, probe):
    - Superset: 3447 splits, 0 violations, 0 unsupported.
    - Stability: two sessions, 134 of 134 rows equal.
    - Given keys, release skeleton (copy of `/workspace/tmp/shared-given-scope/skeleton`) to reference candidate
      (copy of `.../ref`): 7 of 7 kept (old schema-1 binary: 0 of 7; root's measurement with the ordered schema-2
      key: 1 of 7).
    - Unrelated edit (`InputErrorPiece` body): 46 of 60 final-gate targets keep their key. Of 154 implementations,
      133 keep the bound checksum and now all 133 also keep the dependency identity (before: 94).
    - Native cache, one session, whole Cat verified (3451 tasks, 932 s cold, 0 hits), helper edited in place, verified
      again: 2149 hits, 1302 solver runs, 513 s. The implementations with an unchanged checksum own 2931 splits.
      The likely cause of the shortfall is Boogie's 10-minute sliding expiration of result-cache entries
      (`VerificationResultCache.Policy`, mirrored by `NativeSlidingExpiration`): results published early in the
      932 s cold run were idle for more than 10 minutes. Not verified further; existing session behaviour, outside
      this change. It matters for final gates whose proof coverage approaches 10 minutes.
  - Criteria: 7 to 10 met locally; 8 met on Cat. Criterion 1 native part met up to cache expiry. Criterion 5 still
    skipped (needs Cosyn and root). Status stays in-progress for independent verification.

## Scope addition: idle-time expiration of native results (2026-11-07)

Requested by the coordinator under this plan's performance goal; recorded before editing.

- Problem: after the unrelated edit, the whole-Cat session verify hit 2149 tasks, but unchanged implementations own
  2931 splits. Suspected cause: time-based expiry. Boogie's `VerificationResultCache` stores results in a
  `MemoryCache` with a private 10-minute `SlidingExpiration` policy, and `NativeVerificationCache` mirrors it in its
  journal (`NativeSlidingExpiration`, `PruneExpired`). The cold run took 932 s, and final-gate proof coverage and
  idle goal leases come close to or exceed 10 minutes.
- Step 1, evidence: repeat the measurement with a scratch build whose result store never expires, and count hits.
  Also count, in a scratch instrumented copy, which entries were missing at lookup.
- Step 2, if confirmed: `NativeVerificationCache` keeps its results in its own store instead of Boogie's
  `MemoryCache`. Lookup reproduces `VerificationResultCache.Lookup` exactly: keyed by `Implementation.Id`;
  checksum, then dependency checksum, then timed-out-with-diagnostics; same priorities and returned result. The
  store is bounded by entry count with least-recently-used eviction (lookup hits and inserts count as use), not by
  idle time. Clear, dispose and pool semantics stay; the context LRU (4) and the 32-compilation window are unchanged.
- Tests (`NativeVerificationCacheTests`): an entry survives past 10 minutes under the fake clock; the count bound
  evicts the least recently used entry; the lookup priority table matches Boogie's for each case; existing tests pass.
- Validation: Core, Driver and Python tests, format; rebuild; Cat re-measurement (expected about 2931 hits).
- 2026-11-07, scope addition (idle-time expiration) done:
  - Cause located: `VerificationResultCache.Policy` (`SlidingExpiration` 10 minutes, `MemoryCache`) in Boogie, mirrored
    by `NativeVerificationCache.NativeSlidingExpiration`/`PruneExpired` for the transfer journal.
  - Evidence (`scripts/expiry_probe.py`, logs `/workspace/tmp/modular-fingerprints/expiry/`): a small program, one
    session, a comment line added before each later request so it is a new compilation. With identical bytes the
    session reuses its own state and never asks the cache, so the first attempt (`before.log`, `after.log`) could
    not show the effect. Old binary: changed bytes at once 2/2 hits; changed bytes after 660 s idle 0/2 hits, 2
    solver runs. New binary: 2/2 hits in both cases.
  - Fix: `NativeVerificationCache` keeps results in its own `ResultStore` (entry-count bound, default 4096, least
    recently used first; lookups and inserts count as use). `LookupCore` reproduces Boogie's `Lookup` priorities. An
    evicted entry also leaves the journal. Clear, dispose, the context LRU (4) and the 32-compilation window are
    unchanged. The pooled Boogie cache owners and the clock parameter are gone, with their two tests
    (`ExpiredJournalDoesNotResurrectNativeResults`, `RepeatedCloneDisposalReusesNativeTimerOwners`).
  - New tests: `BoogieResultCacheExpiresByIdleTime` (pins the cause), `EntryBoundEvictsLeastRecentlyUsed`,
    `LookupMatchesBoogieResultCache` (6 cases, compared against a real `VerificationResultCache`). Mutation
    (lookups do not refresh recency): `EntryBoundEvictsLeastRecentlyUsed` fails; restored byte-identically.
  - Checks (logs `round3/`): rebuild into `/workspace/tmp/session-cache-retention/bin` rc 0; Core 123, Driver 175,
    Python 157 passed; format clean.
  - Cat, whole-program session verify (`scripts/measure4.py`): cold 3451 tasks, 966 s, 0 hits; after the
    `InputErrorPiece` edit: 2935 hits, 516 solver runs, 274 s (before the fix: 2149 hits, 1302 runs, 513 s). The
    implementations with an unchanged checksum own 2931 of the probe's 3447 splits; the session counts 3451 tasks.

## Re-review follow-ups (2026-11-07)

The independent re-review accepted the native changes and asked for two follow-ups, recorded before editing:
1. Test gap: dropping `journal.Remove(evicted)` in `NativeVerificationCache.Store` passed all tests. Add an
   assertion that the journal shrinks on eviction and never holds an entry missing from the store.
2. Remove the 32-compilation result window clear (`CompilationsPerResultWindow`). The 4096-entry LRU store bound is
   now the memory limit; the window only destroyed valid hits during long goal leases. Keep clear on context
   eviction, clear on shutdown and the 4-context LRU. Change the tests that pinned the window to the new rule (no
   absence-only tests) and update the wiki statements.
Validation: Core, Driver, Python, format; re-apply the journal mutation (must fail), restore; rebuild.
- 2026-11-07, re-review follow-ups done:
  - `NativeVerificationCache.Journal` (test seam: journal size and whether every journal id is in the store);
    `EntryBoundEvictsLeastRecentlyUsed` asserts it before and after eviction. Mutation (keep evicted ids in the
    journal): that test fails; restored byte-identically.
  - Removed the 32-compilation clear, `CompilationsPerResultWindow`, the `Session(int)` seam and the
    `resultCacheClears` evidence field (the Python client keeps it optional for older natives). The
    `ResultRetention.Compilations` count stays, because it is part of the transfer document. The pinning test
    `CompilationWindowClearsOnlyItsOwnContext` became `ResultsSurviveManyCompilationsOfOneContext` (33 new
    compilations in one context, all hits).
- 2026-11-07: Integration review finding fixed:
  `python/tests/test_native_integration.py::test_native_proof_inputs_validate` was stale.
  Schema 2 certifies every target, so the test now expects `Toy.Double` and `Toy.M`
  and asserts the schema-2 fields.

## Scope addition: location-independent options identity (2026-11-07)

Requested by the coordinator; recorded before editing.

- Problem: `ProofOptionsHash` serializes `options.ProverOptions`, which in the session holds
  `PROVER_PATH=<absolute z3 path>` (`SetZ3ExecutablePath`). The proof-input options hash, every modular key and every
  bound native checksum therefore depend on the install location. Evidence (temporary):
  `/workspace/tmp/experiment/cat-topdown-modular/blocker-certificate-path.json` and `diag/out/`: same Binaries bytes,
  options `733ca8ee` at the host artifact path, `cce8fc89` in the images, `d9ac202f` at another host copy; toolchain
  `492ae337` everywhere; 7 of 7 given certificates match only at the certifying path. The solver is already bound by
  content (`z3:<sha256>`) in the toolchain hash.
- Fix:
  - `ProofOptionsHash`: drop prover options that name a host location (`PROVER_PATH`, `LOG_FILE`, `INSPECTOR`, in the
    forms Boogie parses: `=`, `:` or bare) from `ProverOptions` and from the raw `--solver-option` list; drop
    `--solver-path` (bound by content in the toolchain) and `--solver-log` (log destination). `--solver-plugin`
    enters by the content hash of the plugin file, not its path.
  - `ContextOptionsIdentity` (session context, transfer, evidence, contract screening): the path-free options hash
    plus the content hash of every `PROVER_PATH` binary, so a session context still changes when the solver binary
    changes, and stays equal for the same binary at another path. Unhashable files fall back to the raw path.
  - `DafnyOptions.ResolveZ3ExecutablePath`: recognize `PROVER_PATH` in every form Boogie parses, so each dropped
    entry is one the toolchain resolution saw.
  - One shared, cached file-content hash for the solver identity, the context identity and the plugin.
- Audit (no change expected, to confirm): `ResolutionOptionsIdentity` (paths only from `--prelude` and `--plugin`,
  both rejected by `SupportsDiagnosticContext` before the session computes it), library paths (excluded from the
  options hash, represented by translated declarations; the session context's `libraryIdentity` keeps
  `FullName` plus content), modular key content (`{:id}` uses the file base name and is dropped; comments are
  dropped by the lexer), `AssertionShape`, `AssemblyToolchainHash`, native cache lookup (`{:id}` plus checksum).
- Changes:

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` `ProofOptionsHash`, `ContextOptionsIdentity`, `SolverIdentity`, new `FileContentHash`, `IsLocationProverOption` | As above | `ModularProofKeyTests` new cases |
| `Source/DafnyCore/DafnyOptions.cs` `ResolveZ3ExecutablePath`, new `ProverPathValue` | Boogie's `PROVER_PATH` forms | `SolverIdentityRequiresOneResolvableZ3` (extended) |
| `Source/DafnyCore.Test/ModularProofKeyTests.cs` | Solver path only differs: equal options hash, definition hash and bound checksums; same content at another path: equal toolchain and context identity; other content: different toolchain and context identity; no remaining path-typed option in the options hash | New tests, mutation |
| `wiki/native-analysis-session.md` | Options identity is location independent; one-shot/session note | Review |

- Validation: Core filter (`DefinitionAnalysis|ProofInput|DeclarationClone|Snippet|Token|ModularProofKey`), Driver
  filter (`AnalysisSession|NativeVerificationCache|ParserCacheClone|CachedParser|NativeTaskEntry|LambdaLifting`),
  Python unit and integration (`DAFNY_ANALYSIS_NATIVE=<built Dafny>`), `dotnet format whitespace` on touched files,
  one mutation restored byte-identically. Build first into `/workspace/tmp/prover-path-hash/bin` (another agent's
  measurement is using `/workspace/tmp/session-cache-retention/bin`), then rebuild into
  `/workspace/tmp/session-cache-retention/bin` when it is idle. Real binary: two byte copies of the Binaries at
  different directories; session proof inputs for the release skeleton and the reference candidate
  (`/workspace/tmp/session-verify-mismatch/ws`) from each; expect equal options hashes and equal 7 given keys.
  Scratch `/workspace/tmp/prover-path-hash/`.
- 2026-11-07, location-independent options identity done (uncommitted):
  - Code: `DefinitionAnalysis.ProofInputs.cs` `ProofOptionsHash` (now internal; location prover options and
    `--solver-path`/`--solver-log` dropped, plugin by content), new `ProofOptionArguments`, `IsLocationProverOption`,
    `FileContentHash` (shared cache, also used by `SolverIdentity`), `ContentIdentity`; `ContextOptionsIdentity` adds
    the content of each `PROVER_PATH` binary. `DafnyOptions.ProverPathValue`; `ResolveZ3ExecutablePath` uses it.
  - Audit result: `ResolutionOptionsIdentity` unchanged (only `--prelude`/`--plugin` are paths, both rejected by
    `SupportsDiagnosticContext` before the session computes it); session `libraryIdentity` keeps `FullName` plus
    content (resolver retains library URIs; not in any proof key); `AssemblyToolchainHash` and `SolverIdentity` are
    content only; modular key content, `AssertionShape` and the native lookup (`{:id}` = file base name plus
    implementation name, checksum, key-derived dependency identity) name no host path; `sourcePath` and
    `closureOrigins` stay absolute in the document and are in no key. Kept verbatim: `C:` solver arguments and raw
    `--boogie` arguments (proof inputs and sessions admit only `/randomSeed`).
  - Tests (`ModularProofKeyTests`, new): `SolverIdentitySeesEveryProverPathForm`, `SolverLocationDoesNotChangeTheKey`
    (5 cases), `SemanticSolverOptionChangesTheKey`, `SolverBinaryIsIdentifiedByContent`,
    `SolverPluginIsIdentifiedByContent`, `ProofOptionsHaveNoPathTypedArgument`.
  - Checks (cwd `/workspace/dafny-optimization`, dotnet 8.0.133, tmux `prover-path-core`, `prover-path-driver`; logs
    `/workspace/tmp/prover-path-hash/logs/`, temporary): Core filter 133 passed (123 + 10 new); Driver filter 175
    passed; Python 157 passed (24 deselected); Python integration with
    `DAFNY_ANALYSIS_NATIVE=/workspace/tmp/prover-path-hash/bin/Dafny` 24 passed; `dotnet format whitespace --folder
    --verify-no-changes` on the three touched C# files clean; build `dotnet build Source/Dafny/Dafny.csproj -o
    /workspace/tmp/prover-path-hash/bin -m:1` rc 0 (4.11.1+650e6db3, dirty tree).
  - Mutation (restore unfiltered `options.ProverOptions` in `ProofOptionsHash`): 6 failures (5
    `SolverLocationDoesNotChangeTheKey` cases, `SolverBinaryIsIdentifiedByContent`); restored byte-identically (sha256).
  - Real binary (script `/workspace/tmp/prover-path-hash/scripts/cross_location.py`, outputs `out/`, temporary;
    session `definition-analysis --include-proof-inputs` with the final-gate flags; each Binaries copy includes
    `z3/bin/z3-4.16.0`, so the session's `PROVER_PATH` points into the copy):
    - Previous binary (copy of `/workspace/tmp/session-cache-retention/bin`, pre-fix) at two directories: options
      `aaca4fd2` vs `b3f48d53`; 0 of 82 skeleton rows, 0 of 134 reference rows and 0 of 7 given keys equal.
    - New binary at two directories, plus a moved workspace: one options hash `8a51a04c`, one toolchain `db70dc9d`,
      evidence `optionsIdentity` `8cf7a307` everywhere; 82 of 82 and 134 of 134 rows equal; 7 of 7 given keys equal
      across locations and from skeleton to reference.
    - One-shot against session (new binary): toolchain equal, options differ (`4e859ddf` vs `8a51a04c`), so 0 of 82
      rows equal; pre-existing mode difference, likely the session-only Z3 option defaults. Compare within one mode.
  - Not done: rebuild into `/workspace/tmp/session-cache-retention/bin`. At the end of this work it was in use by
    other agents' running jobs (`refstab-*`, `scope-fixed-cost-oneshot`); replacing it would change their binary
    mid-run. Command when idle: `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin
    -m:1 -v:q` (cwd `/workspace/dafny-optimization`). The new artifact and images must be rebuilt and the release
    re-certified before the given certificates can match in the images (root plan).

## Verifier follow-ups: solver identity round 2 (2026-11-07)

Requested by the coordinator after the independent verification of the location-independent options identity;
recorded before editing. Scratch `/workspace/tmp/identity-round2/` (temporary). Builds go to
`/workspace/tmp/identity-round2/bin`, never to `/workspace/tmp/session-cache-retention/bin` (in use by other agents).
Test and native runs are pinned with `taskset -c 0-31` in tmux sessions named `idr2-*`.

Findings to fix:
1. High (false proof reproduced by the verifier): the session context became content-only, so a request with
   `--solver-path B` reused the state whose engine was bound to `PROVER_PATH=A` and ran whatever was at A.
   Fix: `ContextOptionsIdentity` again names the effective absolute solver path of every `PROVER_PATH` entry, next to
   its content hash. Entries are kept in last-occurrence order without duplicates (Boogie applies the last one; the
   `--solver-path` binding and `SetZ3ExecutablePath` add the same entry twice). The session's state, result-cache and
   transfer contexts all use it, so a different solver path never reuses a state, engine or result context of another
   path. `ProofOptionsHash` (`optionsSha256`), modular keys and bound checksums stay path-free.
2. Medium: `AssemblyToolchainHash` covered only DafnyCore and five Boogie assemblies. Fix: hash every `Boogie.*.dll`
   and `Dafny*.dll` in the directories the producer assemblies were loaded from, plus those anchors, by file name and
   content, sorted (location-free). Covers Boogie.Provers.SMTLib, VCGeneration, AbstractInterpretation, Graph,
   BaseTypes, CodeContractsExtender, Houdini, Concurrency, Model, DafnyPipeline, DafnyDriver, DafnyLanguageServer.
3. Low: a relative `PROVER_PATH` was hashed relative to the process cwd while `Process.Start` tries the executable's
   directory first. Fix (fail closed): `ResolveZ3ExecutablePath` returns null for a path that is not fully qualified
   (no proof inputs); the context identity never hashes a relative path; the session rejects a relative
   `PROVER_PATH` (`DAFNY_SESSION_UNSUPPORTED`; `--solver-path` stays supported and is absolutized against the
   request directory). Refinement found during the work: .NET file APIs normalize `.`/`..` lexically while
   `execve` resolves `..` after symlinks, so a fully qualified but unnormalized path (`/a/link/../z3`) can also hash
   one file and start another. Such paths are treated like relative ones (no proof inputs, not read by the context,
   rejected by the session). `ProofToolchainIdentity` gets a content-hash seam so the "same bytes at another path"
   unit test no longer relies on a `dir/./file` alias.
4. Low: the file-hash cache was keyed by path, size and mtime only. Fix: one entry per resolved path whose stamp also
   holds device, inode and ctime from `statx` on Linux (creation time elsewhere); a file changed within the last
   two seconds is not cached (racy stamp). Seams: stamp and reader functions.

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` `ContextOptionsIdentity` (+ overload with a content-hash seam), `SolverIdentity`, `FileContentHash` → `ToolFileHashes`, `AssemblyToolchainHash` → `ToolchainAssemblyFiles`/`ToolchainAssemblyHash` | Items 1, 2, 4 | Core `ModularProofKeyTests` |
| `Source/DafnyCore/DafnyOptions.cs` `ResolveZ3ExecutablePath`, `FindBundledOrSystemZ3` | Item 3: fully qualified paths only | Core `ModularProofKeyTests` |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs` `Session.ToolFileHash` seam, relative `PROVER_PATH` rejection | Items 1, 3 | Driver `AnalysisSessionRetentionTests` |
| `Source/DafnyCore.Test/ModularProofKeyTests.cs`, `Source/DafnyDriver.Test/AnalysisSessionRetentionTests.cs` | New tests; `SolverBinaryIsIdentifiedByContent` keeps toolchain-by-content, context now path-bound | Mutation per item |
| `python/tests/test_native_integration.py` | Relative `PROVER_PATH` gives no proof inputs (one-shot, real binary) | Integration run |
| `wiki/native-analysis-session.md` | Context identity binds path plus content; toolchain covers all Boogie/Dafny assemblies; relative solver paths | Review |

Validation: Core filter (`DefinitionAnalysis|ProofInput|DeclarationClone|Snippet|Token|ModularProofKey`), Driver filter
(`AnalysisSession|NativeVerificationCache|ParserCacheClone|CachedParser|NativeTaskEntry|LambdaLifting`), Python unit and
integration with `DAFNY_ANALYSIS_NATIVE=/workspace/tmp/identity-round2/bin/Dafny`, `dotnet format whitespace` on touched
files, one mutation per item restored byte-identically. Real binary: the verifier's fake-solver chain (A replaced by a
fake that answers unsat, then verify with B) must give `assertion could not be proved`; cross-location rerun (two
install directories plus a moved workspace) must keep one `optionsSha256`, one toolchain and 7 of 7 given Cat.dfy keys.
Expected trade-off: native result transfer between installs at different paths misses again (as before the previous
round); proof inputs and certificates do not.
- 2026-11-07, solver identity round 2 done (uncommitted; cwd `/workspace/dafny-optimization`, dotnet 8.0.133, tmux
  `idr2-*`, every test and native run pinned with `taskset -c 0-31`; logs and outputs in
  `/workspace/tmp/identity-round2/{logs,out}`, temporary):
  - Code: `ContextOptionsIdentity` = path-free options hash plus, per `PROVER_PATH` (`SolverPaths`: as given, last
    occurrence, duplicates collapsed), the path and its content hash; public overload with a content-hash seam.
    `ProofOptionsHash` unchanged. `ToolchainAssemblyFiles`/`ToolchainAssemblyHash` replace the six-assembly list (static
    Boogie/Dafny reference closure from DafnyCore and the execution engine, plus every `Boogie*.dll`/`Dafny*.dll` in their
    directories; file name plus content, sorted). `DafnyOptions.IsExactSolverPath` (fully qualified and normalized) gates
    `ResolveZ3ExecutablePath` and the context's reads; the session rejects inexact paths before and after solver option
    processing (`RejectInexactSolverPaths`). `ToolFileHashes` (stamp with `statx` change time and device:inode, 2 s racy
    window, torn read gives null) replaces the size/mtime cache. `ProofToolchainIdentity` and the session
    (`Session.ToolFileHash`) take content-hash seams.
  - Tests: Core `ContextIdentityBindsSolverPathAndContent`, `InexactSolverPathHasNoIdentity`,
    `ToolchainCoversEveryBoogieAndDafnyAssembly`, `ToolFileHashFollowsInPlaceReplacement`, `ToolFileStampHasInodeOnLinux`;
    `SolverBinaryIsIdentifiedByContent` now uses the seam instead of a `dir/./file` alias (now inexact). Driver
    `AnotherSolverPathNeverReusesTheState` (the verifier's scenario: two bundled Z3 builds with injected equal content;
    new state and context for the other path, same state for the same path, equal `optionsSha256`) and
    `InexactSolverPathIsUnsupported` (2 cases). Python integration `test_native_relative_solver_path_has_no_proof_inputs`.
  - Checks on the final source: `dotnet format whitespace --folder --verify-no-changes` on the five touched C# files
    clean; Core filter 138 passed (133 + 5); Driver filter 178 passed (175 + 3); DafnyTestGeneration
    `ContractScreenService|ContractRuntimeFeasibility` 58 passed; build `dotnet build Source/Dafny/Dafny.csproj -o
    /workspace/tmp/identity-round2/bin -m:1` rc 0 (plus `z3/bin/z3-4.16.0` copied in); Python unit 157 passed (25
    deselected); Python integration with `DAFNY_ANALYSIS_NATIVE=/workspace/tmp/identity-round2/bin/Dafny` 25 passed;
    ruff check and format clean on the touched Python test. The `statx` offsets were checked against `os.stat`
    (inode, ctime ns and device equal).
  - Mutations (`scripts/mutate.py`, each restored byte-identically, sha256 checked; focused filters `ModularProofKey`
    and `AnalysisSessionRetention`): M1 context without path: Core `ContextIdentityBindsSolverPathAndContent` and Driver
    `AnotherSolverPathNeverReusesTheState` fail. M2 toolchain anchors only: `ToolchainCoversEveryBoogieAndDafnyAssembly`
    fails. M3a every solver path exact: 2 Core and 2 Driver failures. M3b normalization not required: 2 Core and 1
    Driver failure. M4 stamp ignores change time: `ToolFileHashFollowsInPlaceReplacement` fails.
  - Real binary, scratch build vs the previous round's build (`/workspace/tmp/prover-path-hash/bin`):
    - Fake chain (`scripts/fake_chain.py`; A and B byte copies of Z3 4.16.0, A swapped for a fake that answers unsat,
      `method Bad(x: int) { assert x > x; }`): new build: verify with B rc 4 (context changed), after restoring A and an
      unrelated edit rc 4 again (1 hit for Good, Bad proved again), fake started 0 times; deleted A: verify with B rc 4.
      Previous build: rc 0 with the fake started at A, then rc 0 with 2 hits and 0 solver runs; deleted A: rc 6.
    - In-place replacement keeping inode, size and mtime (ctime changes) inside one session (`scripts/inplace.py`): new
      build reports another toolchain and context; previous build kept both.
    - Toolchain completeness (`scripts/tamper.sh`, one-shot proof inputs): appending bytes to Boogie.Provers.SMTLib,
      AbstractInterpretation, Houdini, DafnyPipeline, DafnyDriver or DafnyLanguageServer changes the toolchain each time;
      options hash unchanged.
    - Relative `PROVER_PATH` in a real session (cwd = install, so the relative file exists): `DAFNY_SESSION_UNSUPPORTED`;
      the absolute path verifies normally.
    - Cross location (`scripts/cross_location.py`, Cat release skeleton and reference candidate, two install copies at
      `loc-a/Binaries` and `loc-b/x/y/Binaries`, plus a moved workspace): options `8a51a04c` and toolchain `d76812c8`
      everywhere; 82 of 82 skeleton rows, 134 of 134 reference rows and 7 of 7 given `Cat.dfy` keys equal across
      installs and the moved workspace; 7 of 7 given keys equal skeleton to reference. Evidence `optionsIdentity` is
      per install now (`05f3ea40` vs `a1fbb3cf`), as intended.
  - Not done: rebuild into `/workspace/tmp/session-cache-retention/bin` (in use by other agents; command above). No
    Docker image build, re-certification or criterion 5 replay. Native transfer between installs at different paths
    now misses again (context names the path); not measured this round.
