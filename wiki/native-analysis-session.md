# Persistent native analysis and verification

Status: native source/local checks accepted; parent records artifact/image/runtime acceptance
Verified: 2026-11-03, editable developer source based on
0776df27c2449bad68e9a28e687bb6c70bf4b401, committed 2026-11-09 on branch `native-session-optimization` after that base.
Plan: [native implementation](../plan/2026-11-02-native-analysis-session.md).
Parent: [integration implementation](../../plan/2026-11-02-verifier-optimization-implementation.md).

`Dafny analysis-session` is a host-owned JSONL process. It accepts ordinary
`resolve`, `definition-analysis` and `verify` argument arrays and returns the
existing captured stdout, stderr and exit code, with typed native evidence.
One-shot commands retain their existing path. The Python adapter lives in
`python/dafny_analysis/session.py` and implements the existing DafnyInvocation
runner boundary:

```python
from pathlib import Path
from dafny_analysis.runner import DafnyInvocation
from dafny_analysis.session import NativeDafnySession

workspace = Path("/absolute/workspace")
with NativeDafnySession(["/absolute/Dafny"], cwd=workspace,
                       context_id="one-owned-run") as session:
    result = session.run(DafnyInvocation(
        ("resolve", "--standard-libraries:false", "Example.dfy"),
        workspace, "resolve", 10,
    ))
    assert result.returncode == 0
    assert result.native_evidence.completed
```

## Candidate inputs that ended session requests (2026-11-15)

Status: local source repair on `expecto` base `87dcbe557`, independently reviewed; not yet
pinned or in an image. Plan: [candidate native crashes](../plan/2026-11-15-candidate-native-crashes.md).
Parent: [weekly FAIL:F classification](../../plan/2026-11-15-weekly-fail-f-native-classification.md).

Two candidate programs from weekly run `weekly-20261114t015031z-a6d430c1b660` ended a session
request as an operational failure instead of returning a diagnostic.

- Message-less related locations. Some resolver errors attach a related location with no text
  of its own: `Duplicate module name` (`LiteralModuleDecl.cs`) and duplicate top-level names
  (`ModuleDefinition.cs`) report `new NestedOrigin(Origin, other.Origin)`, and
  `ErrorReporterExtensions` turns that into related information with `MessageParts = [null]`.
  When the request's source root differs from its logical root, `RemapDiagnostic` remapped every
  part and threw a NullReferenceException (exit 6). It now keeps a null part as null. Requests
  with equal roots and the one-shot CLI never remap and were not affected.
- hide/reveal arguments inside a `match`. `HideRevealStmt.GenResolve` resolves only the callee
  name (`applySuffix.Lhs`); the arguments are accepted and never resolved. Match flattening clones
  the case body with resolved fields (`new Cloner(false, true)`). Two clone constructors then read
  resolution state the arguments never got: `BinaryExpr` read `ResolvedOp`, whose
  `Debug.Assert` ends the Debug-built process ("Process terminated. Assertion failed.", return
  code -6, seen as `hide P(x + y);`), and `UserDefinedType` looked up a null `ResolvedClass`
  (`Value cannot be null. (Parameter 'key')`, exit 6, for example `x is Mode`, `n as Small` or a
  typed lambda). `HideRevealStmt.CloneTarget` now clones the arguments of a hidden or revealed
  call as unresolved syntax and keeps the resolved callee, `OffsetMembers` and
  `ResolvedStatements`. Post-resolution readers of `Exprs` only count them or skip unresolved
  expressions. One loss: `ContractReductionCloner` does not run its cancellation check inside the
  (small) argument subtrees.
- Upstream behavior kept as is: hide/reveal arguments have no effect, and without
  `--isolate-assertions` a `reveal` in one branch of a method also cancels a `hide` in its other
  branches. The LIT test `ast/reveal/hideArgumentsInMatch.dfy` keeps its reveals in a separate
  method and runs with `--isolate-assertions`.
- Evidence: Driver test `MessagelessRelatedLocationIsRemapped` and the LIT test fail without the
  repair and pass with it. Sweeps of argument forms inside a match against the same statement in
  if/else (212 files locally; 379 pairs in the independent review, with dotted, static, instance
  and constant callees, wildcards, auto-reveal and the old resolver) give equal results and no
  internal failure; the pinned build crashes in 166 of the reviewed match cases. A live session
  returns exit 2 with `Duplicate module name` and the related location on the physical path.
- Limits: revealing a labeled assert or requires label inside a match still aborts (exit 134, on
  the pinned build too): the clone creates new `AssertLabel` objects whose `E` is never set, and a
  fix needs a label map in the cloner. Native Dafny is still built in Debug configuration, so
  other `Debug.Assert`s reachable from candidate input remain possible. The Python client and Cosyn keep such a crash from
  wedging a run (see [client close](python-analysis-client.md)). The weekly image uses the pinned
  commit until the parent moves the pin.

## Boogie validation before verification (2026-11-12)

Status: local source repair, final archived-input replay and independent review
accepted on 2026-11-12. Plan: [native verification failure](../plan/2026-11-12-native-verification-oom.md).
Base native commit `466072769`; changes were uncommitted when checked.

Proof-input preparation resolves and typechecks the same Boogie program that the
session later verifies. Boogie resolution mutates that program even when reporting
an error. A malformed user trigger exposed a defect: proof-key computation treated
the first validation failure as an unsupported key, and subsequent preparation
accepted the partially resolved object. A tiny reproduction reached a solver and
raised `ProverDiedException` although one-shot Boogie preparation rejected it.

Validation now records each original Boogie diagnostic and remembers the failure
on that program object. The session reports source locations and messages as a
completed candidate failure before starting verification; repeated preparation
cannot reinterpret the mutated program as valid. Ordinary proof-key analysis keeps
its unsupported-key fallback. The normal verifier entry point also reports these
diagnostics for seeded one-shot and language-server verification; the session's
direct translation entry point leaves request-local reporting to the session.
A completed successful result cache entry is now
stored in the existing detached snapshot representation, so the cache does not
retain its original verification graph; ordinary native inserts remain unchanged.

The archived cold request before the change started 164 batches and returned
native code 6; the host process itself exited zero. A solver-observation replay
reported 18 launches including version checks, 13 exit-code-1 processes, no
signals, and at most 37.03 MiB per solver. Managed heap was about 0.8 GiB under a
10 GiB cap. After the source repair the same request returned native code 2,
completed, with zero tasks and zero solver runs. The misleading out-of-memory
message did not establish actual exhaustion. Redacted observations are temporary
under `/workspace/tmp/native-verification-oom/`; source snapshots remain isolated.

Focused source regressions cover invalid and corrected triggers, repeated
requests, proof-input analysis, proof failure, successful reuse, and retained
object lifetimes. The archived replay checks this request's rejection only; it
does not show that the corrected candidate verifies or that a running image has
been rebuilt or deployed.

Independent checks passed Driver 83 and Core proof-key 75 cases before the final
CLI follow-up; final affected Driver 26 and stable-seed 14 cases passed after it,
with no skips. The external seeded stdin negative returns 2 with its original
source diagnostic and its positive control returns 0. Final compiled-artifact R4
replay again reports completed rejection and zero solver work. The plan records
commands, formatter limits and delivery boundaries.

## Stable seeded order (2026-11-08)

Plan: [stable seeded randomization](../plan/2026-11-08-stable-seeded-randomization.md) (design B1,
fork only; Boogie stays the 3.5.5 package). Status: implemented and checked locally in the
worktree `/workspace/tmp/dafny-stable-seed-wt` (base 650e6db3; committed 2026-11-09 on `native-session-optimization`). Not
adopted: the native artifact, `dafny-version.toml`, re-certification, reference re-checks and
Cosyn's accepted proof-input schemas are a separate approved step.

Problem. With Boogie's own `/randomSeed:N`, `Checker.GetReorderedDeclarations` runs a
Fisher-Yates shuffle over a split's whole pruned list, which also holds every procedure,
implementation, type and global of the program, and `RandomiseNamer` names symbols by the
order of the draws. A target's SMT text then depends on unrelated declarations anywhere in the
program. On Cat, two programs that differed only in sibling declarations gave 0 of 183
textually identical RenderData VCs and different outcomes (183 verified vs 2 time outs).

What `--boogie=/randomSeed:N` (N not 0) now means:
- `DafnyOptions.ParseBoogieArguments` (the `--boogie` binding) sets
  `DafnyOptions.StableRandomSeed = N`, clears Boogie's `RandomSeed`, turns
  `NormalizeDeclarationOrder` off and puts `O:smt.random_seed=N` and `O:sat.random_seed=N`
  first in the prover options. Per VC they follow the time and resource limits, where Boogie
  sent its own seed lines; they also appear in the option block Boogie sends after every full
  reset. A later
  `--solver-option` for the same name still wins.
- `DefinitionAnalysis.ApplyStableSeededOrder` (from `DafnyProgramVerifier` before tasks are
  prepared, and from `DafnyMain.BoogiePipelineWithRerun` for build/run/test) lifts lambdas
  once and reorders type constructors, constants, functions and axioms in place by
  `(SHA-256(seed, key), key)`. The key is the kind plus the position-free declaration hash of
  the modular keys, with lifted lambdas named by content and, for the order only, the names of
  bound variables, let-bound names, function formals and type parameters replaced by their
  first occurrence. Other declarations keep their places.
- Boogie then sees seed 0 and takes `TopLevelDeclarations` order, so names are
  `$generated@@k` in first-use order and depend on the seed only through the order.
- The JSON, CSV/TRX and text loggers report the split's Boogie seed or else the stable seed
  (`VerificationResultLogger.TaskRandomSeed`); Cosyn reads the optional JSON `randomSeed`.

Two Boogie details that the order must respect:
- `Checker.Target` numbers the basic types (type tags 0-2) in the order a `BasicTypeVisitor`
  first meets them over the whole program. Boogie never reorders `TopLevelDeclarations`, so
  this came from the prelude. The reorder keeps the leading run up to the last first meeting
  of a basic type in place (for Dafny, the prelude up to `LitReal`); without it, seed 42 gave
  `int, bool, real` instead of `bool, int, real`.
- Boogie's lambda lifter shares one function between alpha-equivalent lambdas and keeps the
  bound names of the first one it meets, which can be a sibling's (`$l#4#y#0` vs
  `$l#7#z#0`). Normalized solver names never show them, so the order key ignores them; with
  the exact text, a sibling with the same lambda changed 5 of 9 target VCs.

Guarantee and its limits:
- Under a stable seed, a split's solver input is a function of its live declarations (as
  keyed), the seed, the options and the toolchain. An equal modular key (exact text) implies
  equal order keys, so equal key, seed, options and toolchain give byte-identical SMT.
- Without a seed, Boogie still orders by `ContentHash` with ties in program order; that SMT
  can change with unrelated declarations (the tied-handles case).
- Boogie's own seeded randomization is unchanged and never keyed: an implementation's
  `{:random_seed N}` (Dafny never emits it) keeps Boogie's shuffle and namer and gets
  `{:smt_option}` entries so that Z3 still ends with N; `/randomizeVcIterations` above 1 keeps
  the seed with Boogie and gives no proof inputs. measure-complexity (`--random-seed`,
  `--mutations`, `task.FromSeed`) is unchanged; combining it with `--boogie /randomSeed` is
  unsupported. test-contracts' verification seed is also Boogie's.
- Names from translation-wide counters other than lifted lambdas (Dafny's `$let#N`) are in
  both keys: renumbering them misses reuse and can change the order.
- Proof inputs are schema 3 (`ModularProofKeys.SchemaVersion`). The fork's Python client
  accepts modular rows for every schema from 2. Cosyn's `SUPPORTED_PROOF_INPUT_SCHEMAS`
  must accept 3 at adoption.
- Seed-42 outcomes change for every proof (new order, names and tags), so references and
  given certificates must be re-checked before adoption. Cat RenderData now verifies all 183
  VCs in both contexts (61.6 s and 63.3 s, host build, one core).

Evidence (2026-11-08, worktree build, CPUs 56-63, z3 4.16.0 behind the tee wrapper; outputs
temporary in `/workspace/tmp/dafny-stable-seed/out/`): Cat RenderData validated vs candidate at
seed 42 183 of 183 VCs byte-identical; synthetic unrelated block before/after 5 of 5, shared
handle and lambda sibling before/after 9 of 9, tied handles 3 of 3; seed 7 vs 42 differs in all
5 VCs beyond the seed lines. Unit tests: `StableSeedTests` (DafnyCore.Test) capture the exact
solver input from a no-op solver (`CreateSolver`), so no solver process or file is used; with
the order disabled four of them fail, without the basic-type prefix one fails.

## Modular proof-input fingerprints (2026-11-06)

Plan: [modular proof-input fingerprints](../plan/2026-11-06-modular-proof-fingerprints.md).
Status: native source and local checks done, real Cat measurements done; first independent
review accepted with fixes (order-insensitive key, native lookup by key, solver path rule),
fixes implemented 2026-11-07; second review pending. Options hash made
location independent on 2026-11-07 (see the key bullets); session context bound to the
solver path again, toolchain widened to all Boogie/Dafny assemblies the same day. Base 650e6db3; committed 2026-11-09 on `native-session-optimization`. Consumers:
[root shared scope](../../plan/2026-11-06-shared-given-declaration-scope.md),
[Cosyn reuse key](../../cosyn/plan/2026-11-06-modular-proof-reuse-key.md).

Proof inputs are schema 2 (schema 3 since the [stable seeded order](#stable-seeded-order-2026-11-08)).
Each Boogie implementation gets a key over what the solver
can see for it, and a definition's `sha256` hashes the sorted `(implementation name,
key)` list of the implementations it owns (owner: the `CanVerifyOrigin`, as for
session tasks). Code: `Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs` and
`DefinitionAnalysis.ProofInputs.cs`.

Key, computed once per module translation on the program the engine will verify:
- The translation is lifted first (`DefinitionAnalysis.LiftLambdasOnce`, idempotent per
  program, VerifySnapshots 0 semantics). The session's pre-engine lift reuses it.
- Content: the printed implementation, its own procedure, the sorted multiset of called
  procedures, and the sorted multiset of `(kind, hash)` of the live list from
  `Pruner.GetLiveDeclarations` over one synthetic block (order-insensitive since the
  2026-11-06 review follow-up). That block holds `assert true` (initial all-revealed state, so no CanHide edge
  is cut), every implementation command except scope push/pop, and assumes of the own
  and called contracts, formal and local where clauses and all global where clauses.
- Hashing is token-based (Boogie lexer, length-framed) and drops `{:id}`,
  `{:captureState}` and `{:checksum}`. Lifted `lambda#N` names become
  `lambda@<hash of the function and its defining axiom, own name masked>`. The unprinted
  `Axiom.CanHide` flags are appended.
- Final key: `{schema 2, toolchain, optionsHash, content}`. Toolchain = producer
  assemblies plus `z3:<sha256 of the solver binary>`, resolved by
  `DafnyOptions.ResolveZ3ExecutablePath`: the single distinct `PROVER_PATH`, else the
  bundled copy, else PATH. Several distinct `PROVER_PATH` values (Boogie runs the last,
  Dafny checks the first), a missing file, a path that is not absolute and normalized
  (2026-11-07, `DafnyOptions.IsExactSolverPath`: a relative path is read against the current
  directory but `Process.Start` tries the executable's directory first; .NET file APIs collapse
  `..` lexically while the kernel resolves it after symbolic links) or a non-Z3 solver give no
  proof inputs.
  `PROVER_PATH` is recognized in every form Boogie parses (`=`, `:`, bare).
- Producer assemblies (2026-11-07, `DefinitionAnalysis.ToolchainAssemblyFiles`): the Boogie
  and Dafny assemblies statically reachable from DafnyCore and Boogie's execution engine,
  plus every `Boogie*.dll` and `Dafny*.dll` in the directories they load from, named by file
  name and content (sorted, location-free). This covers Boogie.Provers.SMTLib (SMT text, Z3
  defaults, answer parsing), AbstractInterpretation, Houdini, Graph, Model, Concurrency and
  the install's DafnyDriver, DafnyLanguageServer and DafnyPipeline. Before, only DafnyCore and
  five Boogie assemblies were hashed, so a changed SMTLib kept certificates valid.
- Tool file hashes (`ToolFileHashes`) are cached per resolved path while the stamp (size,
  write time, change time, device and inode from Linux `statx`; creation time elsewhere) is
  unchanged. An in-place rewrite that keeps size and write time (`cp -p`, `touch -r`) changes
  the change time, so it is read again; a file changed in the last 2 s is not cached.
- The options hash names no host location (2026-11-07). Before, the session's
  `ProverOptions` carried `PROVER_PATH=<absolute z3 path>`, so the same Binaries bytes at
  another directory gave another `optionsSha256`, other keys and other bound checksums
  (Cat certificates matched only at the certifying path:
  `/workspace/tmp/experiment/cat-topdown-modular/blocker-certificate-path.json`, temporary).
  `ProofOptionsHash` now drops `PROVER_PATH`, `LOG_FILE` and `INSPECTOR` from the prover
  options and from `--solver-option`, and drops `--solver-path` and `--solver-log`;
  `--solver-plugin` enters by file content. `ContextOptionsIdentity` (session state,
  result-cache and transfer context, evidence `optionsIdentity`, contract screening) is that
  hash plus, for each `PROVER_PATH` (last occurrence order, duplicates collapsed), its
  normalized absolute path and its content hash. The path is required (2026-11-07 review):
  a content-only context let a request with `--solver-path B` reuse a state whose engine
  started `PROVER_PATH=A`; with A swapped for a fake that answers unsat, `assert x > x`
  verified and the false result was then served from the native cache. So native result
  transfer between installs at different paths misses again, while proof keys and
  certificates stay location-free. Sessions reject a relative or unnormalized `PROVER_PATH`
  (`DAFNY_SESSION_UNSUPPORTED`); `--solver-path` is absolutized against the request
  directory. Real-binary check (`/workspace/tmp/identity-round2/out/chain-*.json`, temporary):
  the fake chain now fails `assert x > x` (rc 4) and never starts the fake; the previous
  build returned rc 0 and then served the false result from the cache (2 hits). Test `ProofOptionsHaveNoPathTypedArgument` rejects any new
  file-typed option in the hash. Not changed, by design: the session context's library
  identity (library `FullName` plus content; the resolver retains library URIs),
  `ResolutionOptionsIdentity` (its only path options, `--prelude` and `--plugin`, are
  rejected by `SupportsDiagnosticContext`), and the absolute `sourcePath`/`closureOrigins`
  paths in the document, which are not part of any key. Implementation `{:id}` uses the
  file base name and is dropped from keys.
- Fail closed (no key): a callee with `{:inline}`, a missing or ambiguous procedure,
  any other desugared command, ill-formed Boogie, or lambda name/content collisions.

Superset argument. A split's solver declarations are `Pruner.GetLiveDeclarations` of
its blocks. Reachability is monotone in the roots and in the revealed set, and the
roots above contain everything preparation adds. So the live list contains every
split's declared list. Equal content of the reachable declarations, as a multiset, then
fixes every split's declaration set, since the reachable sub-graph and its edges are
functions of that content. Checked on Cat: 3447 real splits of 154 implementations,
0 violations.

An equal key means a logically identical solver formula set, not identical SMT text
(stale for seeded runs since 2026-11-08: under the [stable seeded order](#stable-seeded-order-2026-11-08)
an equal key gives identical SMT). `Checker.GetReorderedDeclarations` shuffles the whole pruned list (it also holds
unrelated procedures and implementations), so the declaration order, and solver time,
can differ. A success reused near the 30 s limit can time out when grading proves it
again. Program order was in the key at first; root measured that filling the release
skeleton's empty proof modules changed 6 of 7 given `Cat.dfy` keys only through order.
Filling a module adds imports, which changes the module translation order, so the
blocks of unchanged modules swap places.

Pitfall (Boogie 3.5.5). `AxiomVisitor` computes `Expr.pos` from the previous value of
the same object, so a second dependency-graph computation over one program can differ
(it matters for quantifiers in `{:include_dep}` axioms). Key computation records and
restores quantifier positions and `DeclarationDependencies`. Without that, the engine
could declare an axiom the key never saw.

Zero-obligation targets. Dafny emits no implementation when a declaration has no
obligations. All such rows of one toolchain and options share one digest, so consumers
must key by source path plus full name plus digest. Such a target gets a row with `implementations: 0` only if every
implementation has a known owner and the translation contains its scope marker
(`CheckWellformed$$<f>` or `Impl$$<m>`). This covers `CatCore.InputDataPiece`,
`CatCore.InputFailed` and `CatCoreModel.InitState`, which schema 1 never certified.

Document fields for consumers, per definition: `sourcePath`, `fullName`, `sha256`,
`implementations` (count; 0 = certified), `closureOrigins` (`sources[{sourcePath,
spans[{start,end}]}]`, `toolchain` count). Spans use the offsets that definitions
report and cover the whole origin range of each implementation, procedure and live
declaration. They are not part of any key. Top level: `schemaVersion` 2,
`toolchainSha256`, `optionsSha256`.

Measured on a Cat copy (outputs temporary in `/workspace/tmp/modular-fingerprints/out`):
- Stability: 134 of 134 rows equal across two one-shot runs and across two sessions.
  Session and one-shot `optionsSha256` differ. Since 2026-11-07 this is no longer the
  prover path; the likely remaining cause is the Z3 option defaults that only the session
  adds (`SetZ3Options`; the one-shot skips the solver-version subprocess). Compare within
  one mode.
- Install location (2026-11-07, session, Cat release skeleton and reference candidate,
  outputs temporary in `/workspace/tmp/prover-path-hash/out`): two byte copies of one
  Binaries tree (with bundled z3) at different directories, and a moved workspace, give one
  `optionsSha256`, one toolchain, 82 of 82 skeleton rows and 134 of 134 reference rows equal,
  and 7 of 7 given `Cat.dfy` keys equal (also skeleton to reference). The previous binary
  gave two options hashes and 0 equal rows across the two copies. Rechecked after the
  path-bound context and the wider toolchain (2026-11-07, `/workspace/tmp/identity-round2/out`,
  temporary): options `8a51a04c` and toolchain `d76812c8` at both copies and with a moved
  workspace, 82 of 82 and 134 of 134 rows, 7 of 7 given keys; evidence `optionsIdentity`
  now differs per install (`05f3ea40`, `a1fbb3cf`).
- Unrelated merge (one `CatCore.InputErrorPiece` body edit): 46 of 60 final-gate targets
  keep their fingerprint (schema 1: 0). All 60 targets have a proof input. With native
  lookup by key and the bounded store below, a whole-Cat session verify after the edit hit
  2935 of 3451 tasks (274 s against 966 s cold; unchanged implementations own 2931 splits).

Idle expiration (2026-11-07). Boogie's `VerificationResultCache` keeps results in a
`MemoryCache` with a fixed 10-minute sliding expiration. Results of a long cold run, or of
a session idle during a long model turn, were dropped by idle time alone (a session with
changed bytes after 660 s idle: 0 of 2 hits). `NativeVerificationCache` now keeps its own
store, bounded by entry count (4096) with least-recently-used eviction, and reproduces
Boogie's lookup priorities exactly (differential test). Evicted entries leave the
transfer journal. Context LRU, clear on eviction and dispose are unchanged. The former
32-compilation window, which cleared a context's whole cache, was removed on 2026-11-07:
the entry bound limits entry count rather than bytes, and a goal lease easily makes more than 32
compilations in one turn. A context now keeps hits across 33+ compilations (test
`ResultsSurviveManyCompilationsOfOneContext`).
Pitfall: with identical bytes the session reuses its own compilation state and never asks
the cache, so cache experiments must change the bytes.
- Release skeleton to reference candidate: all 7 given `Cat.dfy` keys stay equal
  (schema 1: 0; ordered schema 2: 1).
- Live list over the union of an implementation's split lists: median 1.01, max 12.5.
- Cold analysis with proof inputs got faster: one-shot 30 to 31 s against 36 to 38 s.
  The key itself costs about 5.4 s plus 6.9 s of lifting, which the verify path already paid.

Limits:
- Native lookup follows the key (2026-11-06 decision). Boogie's result cache compares
  the checksum and a dependency identity. Boogie's own dependency identity combines the
  Dafny `{:checksum}` of transitively mentioned functions; it reaches, for example, a
  datatype's constructor functions and every predicate they appear in (1580 functions
  for `CatCore.ExpectedStdinAtExtend`). It therefore missed after unrelated edits. For a
  key-bound implementation, `BindNativeVerificationChecksums` now sets
  `MD5DependencyChecksum_` to a digest of the bound checksum, so lookup and insert
  compare key plus assertion shape only. Implementations without a key keep Boogie's
  identity and a fresh checksum. Completeness rules and rebasing are unchanged.
- Retention bound: 4096 results per verifier context; a larger working set evicts the
  least recently used results (safe misses).
- Dafny does not translate a method's `{:random_seed}`. Per-implementation limits that reach
  Boogie are in the implementation text; since schema 3 a Boogie `{:random_seed}` makes the
  implementation unsupported.
- A reuse is for a solver input equal up to the dropped labels and the lambda renaming
  (Dafny sets `NormalizeNames`, so symbol names do not reach the SMT text).

## Independent native branch cache cloning (2026-11-05)

Status: local implementation and fresh independent verification accepted. Verified
on dirty native base0776df27c2449bad68e9a28e687bb6c70bf4b401. Owner plan:
[native cache cloning](../plan/2026-11-05-native-cache-cloning.md); parent:
[Cosyn session cloning](../../cosyn/plan/2026-11-05-native-session-cloning.md).

One daemon routes `sessionId` separately from the existing role `contextId`.
`clone` keeps its parent registered and creates a new branch epoch. Its versioned
receipt binds daemon, parent/child ids and epochs and counts actual inherited
parser/native-proof entries. `close-session` disposes only one branch; final
client transport ownership alone shuts down/reaps the daemon. Pending jobs validate
branch/context/epoch/generation and source hashes. Clone errors have no replay or
cold-success fallback. Root legacy responses may omit sessionId; cloned branches
require it.

Parser clone copies cache maps, keys and pruning markers and reconstructs private
parsed templates solely from retained immutable source strings/URIs with detached
child options. It performs syntax work, not filesystem reads or resolve/analysis/
verify command replay. Tokens/options/includes/builtin delegate captures are
branch-owned. Resolver/fact caches and live compilation/engine/tasks are fresh.
A shared compiler safety gate protects process-static preparation; reader waits
release that gate, and solver owners remain independent. Cancellation reaches
per-file parser and native result snapshot loops.

`NativeVerificationCache` journals only complete successful native task rosters.
Transfer data retains original implementation id/checksum/dependency bytes,
scalar split stats and assertion shape descriptions, without parent AST/task/
counterexample/tracked-component graphs. A child builds its own native result
shells; Boogie's native lookup remains the sole reuse authority. Reused assertions
are matched and rebound to the child's actual split before reporting. Result
contexts, library/options identity, native expiry and current source keys remain
conservative.

Boogie's sealed cache cannot dispose its private timer owners. Drained wrappers
therefore return explicitly reset backing caches to an exclusive process-local
pool; allocations grow to peak concurrent owners, not every historical clone.
Explicit key removal avoids Trim/periodic-flush races. Disposed wrappers reject
late access and double return; VerifySnapshots1 rejects unused program-AST cache
insertion. No reflection or dependency change is used.

Client normal admission jointly bounds jobs and clones; cancellation and branch
close use separate bounded lanes. Original terminal responses, not cancellation
ACKs, establish drainage. A late cancelled clone is disposed before ownership
releases. Fatal daemon failure explicitly fails all shared handles.

Evidence: final independent native subset27passed/0skipped with freshly built
LanguageServer/Driver/Test, plus59client units/17memory integrations and separate
client saturation/close probes. Native cases exercise real parser/native lookup,
with fake solver completions and bounded fixed assembly reads; no native solver
process, hidden task, provider or paid run. Commands, build dependency limits and
source audits are in the plan. No end-to-end proof, speedup, image/pinned-install
or process-crash-isolation claim is made.

## Cross-process session transfer (2026-11-05)

Status: implemented and locally tested; independent verification and the host side
pending. Verified 2026-11-05 on dirty native base `650e6db3`. Owner plan:
[cross-process session transfer](../plan/2026-11-05-cross-process-session-transfer.md);
host plan: [cross-process child sessions](../../cosyn/plan/2026-11-05-cross-process-child-sessions.md).

In-process clones share one daemon, and the process-static compiler gate serializes
their compilations. `export-session` and `import-session` move the same detached cache
data into a new process instead. Both run at the clone's drained boundary (admission,
preparation, readers drained); neither takes the compiler gate, because nothing is parsed.

Protocol, version 1 (Python: `NativeDafnySession.export_session` and `import_session`):
- `export-session` returns, as stdout, one JSON document: `schemaVersion`, `daemonEpoch`,
  `sessionId`, `sessionEpoch`, `toolchain` (the native toolchain identity of result
  checksums), `resolvers[]` (`key`, `optionsIdentity`, `entries[{uri, text}]`) and
  `results[]` (`key`, `compilations`, `entries[]` of detached successful snapshots with
  base64 dependency bytes and scalar split and assertion shapes). `nativeEvidence` is null.
- `import-session` carries that exact string in the request field `payload` and returns
  a receipt (`schemaVersion`, `daemonEpoch`, `sessionId`, `sessionEpoch`, `parsedEntries`,
  `verificationEntries`).
- Import validates strictly (no unknown members, required fields, toolchain equal, 64-hex
  keys, canonical absolute URIs, unique entries, bounded dependency bytes and counts,
  named enum values, at most two resolver and four result contexts) and installs nothing
  on failure (code 2, `DAFNY_SESSION_TRANSFER_REJECTED`). It needs a fresh branch.
- A response line may be at most 128 MiB (`ResponseLimit`, newline excluded; the Python
  client's `MAX_RESPONSE_BYTES`); a longer one becomes a code-6 response, never truncated.
  Requests stay at 8 MiB. The payload must fit the 8 MiB import request frame (binding) and
  the 128 MiB export response
  frame, each with a 4096-byte reserve; otherwise code 6,
  `DAFNY_SESSION_TRANSFER_TOO_LARGE`. Never truncated.

Limits and a deviation from the contract text: a fresh process has no `DafnyOptions` for
a retained resolver context and cannot rebuild them from an identity. Parser sources are
parked at import and parsed with the first request that creates the matching resolver
context, only if its `ResolutionOptionsIdentity` equals the exported one; otherwise they
are dropped and that request parses cold. Result caches are built at import time and
remain authoritative only through native checksum lookup. `clone` is unchanged except
that it also carries parked sources.

Evidence: 49 new driver cases (real solver on a tiny program for the session-level round
trip, a fake solver for the wire-level one) and 22 + 3 new Python cases; a real check on
copies of public Cat with the rebuilt binary: payload 1.41 MB, export 0.15 s, import 0.7
s, two fresh processes with 3 of 3 hits and 0 solver runs, resolves overlapping 7.8 s,
wall 50.9 s against 91.7 s for two in-process clones. Children still need about 41 s to
prepare the compilation. One workload, one run; no speedup claim beyond it.

## Request-local diagnostic locations (2026-11-05)

Status: local source checks and independent source review accepted. Owner: [diagnostic repair](../plan/2026-11-05-review-diagnostic-locations.md);
parent: [Cosyn review fixes](../../cosyn/plan/2026-11-05-optimization-review-fixes.md).
Applies to the dirty native source based on `0776df27c2449bad68e9a28e687bb6c70bf4b401`.

A session retains logical token URIs for compilation/cache identity and captured
source lookup. It now installs `DafnyOptions.PrintPathMapper` on each request's
response options after compilation selection. `GetPrintPath` and
`TokenExtensions.GetRelativeFilename` apply it only while presenting filenames;
JSON diagnostic file URIs use the same full-path mapping independently of basename
formatting. Original ranges, token chains, positions and captured excerpt keys
remain logical. Unchanged URIs retain their components, and changed file paths
preserve URI query/fragment components.

Mapping rendered filenames rather than source ranges avoids ambiguous inverse
URI lookup when an external file already lives under the physical root. The
excerpt view also recognizes retained captured inputs when the physical source
is no longer present; that read-only check does not change consumed-input capture
or cache freshness. Message-part mapping remains request-local as before.

Verified 2026-11-05: 18/18 cases pass against freshly built core, driver and test
assemblies. Other dependency DLLs were retained; a whole dependency rebuild was
blocked by the Gradle lock in a read-only home. Fresh source review accepted the
current patch; that independent reviewer ran no runtime tests.

The new `AnalysisSessionDiagnosticLocationTests` class uses synthetic diagnostics,
StringWriter and memory-backed source readers; no temporary directory or native
process lifecycle. Final validation commands, dependency-build limits and fresh
review are recorded in the owner plan. This repair makes no proof-cache soundness,
performance, image adoption or benchmark claim.

## Reported analysis scope (2026-11-04)

Plan: [analysis scope reuse](../plan/2026-11-04-analysis-scope-reuse.md).

`definition-analysis --analysis-source <file>` (repeatable) reports facts for
those sources from a compilation of the unchanged roots, includes and
libraries. Validation lives in `DefinitionAnalysisCommand.SelectAnalysisSources`
and is shared by one-shot and session paths: every analyzed root must be listed,
each added file must be a parsed `.dfy` source in the compilation's verified URIs
(`ShouldCompileOrVerify.VerifiedUris`, so library-reachable files are rejected),
and a non-root file with proof inputs or verification facts requires
`--verify-included-files`, because otherwise root status changes translation.
`--spans-only` rejects a selection. Rejections exit with PREPROCESSING_ERROR (1).
The session remaps selection paths through the logical root like roots; the
option is not part of any context or state key, so changing only the reported
scope keeps the native State, its translation and prepared proof inputs.
Proof inputs use `identitiesOnly` and are already independent of the reported
scope.

`DefinitionAnalysis.SessionCache` now keeps up to four analysis profiles
(reported sources plus statements flag, LRU). Each profile owns its own
declaration nodes, so cross-module call facts never mix profiles. Modules the
resolver replaced in the analyzed program are pruned from every profile.

Limit: Dafny's precedence (indentation) linter is silent in included files, so a
selection reports the diagnostics of the fixed-root compilation. A warning that
only appears when an included file is a root is not reported; verification of
the same roots never reported it either. Selection and expanded-root documents
are equal as values; list order can differ because root order changes
declaration order in the default module.

Evidence (local, 2026-11-04, public Cat sources under
`bench/dafny/dafnyutils/bench`, uncommitted source based on 0776df27, executable
built into `/workspace/tmp/incremental-analysis-scope/bin`, outputs temporary in
[session-check](/workspace/tmp/incremental-analysis-scope/session-check/summary.json)):
cold proof-input analysis 42.1 s; the same compilation reporting six reachable
files 0.48 s; filtered verify on the root 8.2 s with 15 solver runs and no new
compilation; repeated root and selected analyses 0.035 s and 0.195 s with 22/22
module hits; the old expanded-root request 33.2 s. Selection and expanded-root
documents match after order normalization, including 119 proof inputs by key
and stderr. The first run exposed a session bug (verify requests carry no
`--analysis-source` option and the remap dereferenced null, retiring the State);
it is fixed and the second run is the one above. Memory checks: Core 86/86
(two new profile tests), Driver 28/28 (seven new selection tests), Python
client 104 passed. This is not an image, benchmark or paid-run result.

## Warning path remap (2026-11-05)

Plan: [session warning path remap](../plan/2026-11-05-session-warning-path-remap.md).
Status: native source/local checks done; Cosyn adoption and image identity are separate.

Diagnostics are queued when a compilation is created and replayed to every request that
reuses it, possibly with another `source_root`. `Session.Execute` therefore maps the
logical root to the request's physical root at replay (`RemapDiagnostic`,
`RemapOutputText` in `AnalysisSessionCommand.cs`), on `MessageParts` and related
information, with the exact root-prefix rule of `RemapPrefix` at path boundaries; it is
not a regex over rendered output. This fixes `CLI: Warning: The file '<path>' was passed
to --library` (and "file X not found" text) for resolve, definition-analysis and verify,
and `--analysis-source` rejection text. Equal or absent roots leave text unchanged.
Limits: diagnostic location prefixes are relative to the process cwd and are not mapped (source
excerpts are covered by [the next section](#diagnostic-excerpt-source-2026-11-05));
JSON documents keep logical paths natively and rely on the client remap; one-shot
`resolve` prints no library warning while the session does (and returns 2 without
`--allow-warnings`).

## Diagnostic excerpt source (2026-11-05)

Plan: [session snippet source](../plan/2026-11-05-session-snippet-source.md).
Status: native source/local checks done; independent review, Cosyn adoption and image
identity are separate.

The `NN | code` excerpt under a diagnostic is not part of the message text.
`HumanReadableOutputWriter.WriteDiagnostic` (main range and each related location) calls
`Snippets.WriteSourceCodeSnippet`, whose `GetFileLine` read the file from
`OnDiskFileSystem` at the diagnostic's URI (`Snippets.cs`). A session parses logical URIs
through `CapturedFileSystem`, so with `source_root != logical_root` that read opened the
stale logical-root file (smoke finding F6: header right, excerpt line wrong, caret length
from the wrong line). Equal roots only matched by accident.

Fix: `DafnyOptions.SnippetFileSystem` (null by default, so one-shot is unchanged) is the
file system `GetFileLine` reads through. `Session.Execute` sets it, on the request's own
options, to `ExcerptFileSystem`, a read-only view of the request's `CapturedFileSystem`
(`responseFiles`, the consumed closure copied from the possibly reused State): captured
text first, else the supplied snapshot or the physical file without capturing. It records
nothing, so consumed-input identity and freshness checks are unchanged. The hook is a
property of one options instance and the line cache is per options instance, so no state
is shared between concurrent requests. A reused State is only selected when every captured
input's fingerprint equals the new request's, so the copied bytes are the new request's
bytes. Diagnostics are rendered when each request writes them, so queued compilation
diagnostics and verification results replayed from a reused State also render the
request's bytes. Failing verification results are not inserted into the Boogie result
cache (only `Valid` outcomes), so cross-compilation replay of failures does not exist; the
reuse case is the same State.

Tests: `AnalysisSessionSnippetSourceTests` (12 cases). Excerpt blocks are compared with the
one-shot output of the same file in a clean directory; headers are not compared (cwd
relative path, unchanged). Limit: Dafny verification order differs between session and
one-shot, so verify excerpts are compared as sorted blocks. A diagnostic location in a
file the session never captured and that does not exist still prints no excerpt, as before.

## Session cache retention (2026-11-04)

Plan: [session cache retention](../plan/2026-11-04-session-cache-retention.md).
Status: native source/local checks and free local reproduction done; independent
review, artifact/image identity and any live use are separate. The source is
uncommitted and based on 0776df27.

Retention. `Session` keeps `(parser, resolver, DefinitionAnalysis.SessionCache)`
per resolver context (LRU, 2) and one `VerificationResultCache` per verifier
context (LRU, 4), instead of recreating them and clearing results whenever the
options differ. Cosyn alternates option sets (`certificates` omits
`--allow-external-contracts`; isolated verifies add or drop `--extract-counterexample`),
so a single slot was cold on every request. An evicted result cache is cleared and
its instance recycled. `resultCacheClears` counted the per-context 32-compilation
window (stale since 2026-11-07: the window and the field were removed; the client still
accepts it from older natives). `resultCacheEvictions` and `resolverEvictions` count LRU
evictions; they are optional fields of `NativeEvidence`. State replacement still waits for
readers to drain, and error/faulted/cancelled compilations and library identity
behave as before. The compilation `State` (resolution, translation, prepared tasks)
is still single and is rebuilt when the context changes.

Position-free key. `BindNativeVerificationChecksums` no longer hashes token
coordinates. `AssertionShape` lists, without positions, each `AssertCmd` (type name,
success and failure text, ordinal), each non-free `requires` of a called procedure,
and the non-free `ensures` of the implementation's own procedure. A fresh
translation has unresolved callees and procedures, so contracts are found by name in
the translated program. Boogie desugars call preconditions and postconditions into
assertions only later, which is why they are listed from their contracts. The
fresh-GUID checksum for implementations without a certificate owner is unchanged.
Superseded 2026-11-06: the base checksum and owner fingerprint were replaced by the
per-implementation modular key; see
[modular proof-input fingerprints](#modular-proof-input-fingerprints-2026-11-06).

Rebasing. `NativeTaskEntry` rebases every result of a task whose `CacheStatus` was
`Completed` (whether Boogie hands it back with no stream or through one) with
`cached with { Asserts = task.Split.Asserts }`. `ManualSplit.Asserts` is public in
Boogie 3.5.5. `RebaseCachedResult` requires equal count, assertion type and
success/failure text per ordinal; otherwise it throws, the request fails with a
native error and the state is retired. `Start`, `RunTime` and `ResourceCount` stay
as cached. `DeclarationsAfterPruning` and `CoveredElements` also stay as cached;
neither is used by the session loggers (coverage reports are unsupported).

Evidence (local, 2026-11-04, built into
`/workspace/tmp/session-cache-retention/bin`, outputs temporary under
`/workspace/tmp/session-cache-retention/out/`; public Cat sources, Dafny
4.11.1+0776df27 dirty tree). Confirmed by the runs:

| Sequence | Before (diagnosis, same flags) | After |
| --- | --- | --- |
| S,A,S,A | 22/22 module misses on every request, 20-24 s | requests 3 and 4: 21/22 module hits, 15.5-16.6 s |
| S,V,S,V | 0 result hits, 3 solver runs on each V, 22 s | second V: 3/3 hits, 0 solver runs, 16.9 s |
| Cosyn flow, old image roots, second prove | 69 s, 0 hits | 63 s, verify 3/3 hits |
| Cosyn flow, current tree, second prove | 1.1 s | 1.7 s (unchanged) |
| Shift above, whitespace inside (verify) | location change forced verification | 3/3 hits, 0 solver runs |
| Changed assertion (verify) | miss | miss, 3 solver runs |

After a shift or whitespace hit, the JSON, text and TRX logs equal a cold one-shot
`verify` of the same source after timestamp, GUID and ordering normalization (the
one-shot run logs `vcResults` in completion order, so they are compared by
`vcNum`).

Limit: the time of a context-alternating request is still 15-18 s, because a new
compilation re-translates and re-fingerprints the whole program; only the
resolution caches, the facts and the verification results are retained. A reused
verify after a shift took 18 s in the session against 11 s for a cold one-shot run.
Retaining one `State` per context would be a separate change.

## Cached export ownership (2026-11-03)

The generic ProgramResolver declaration-pointer setter captured a fresh parsed
module. After resolution reused a cached literal module, processing its export
retargeted the cached export to the unresolved parsed owner. Signature.ModuleDef
still identified the resolved owner, so BodyVisibility correctly returned null.
This was a real metadata loss, not a warning or context-hash difference.

The setter now preserves ModuleExportDecl's established owner. Export resolution
already belongs to its literal module; its graph node is a dependent no-op.
Other alias/literal handling and resolved/error flags stay unchanged. Two real
memory regressions cover fresh/reused analysis facts, resolution-only warming,
root changes, dependency/importer edits, empty exports, failed-cache reuse and
repair. Strict whole-document equality and owner/signature/object containment
are asserted. Core84/Driver21 pass with0skips and fresh independent source review.

These are source/local gates. The [parent plan](../../plan/2026-11-02-verifier-optimization-implementation.md)
records actual v5artifact/image/strict recorded-document controls and experiment
acceptance. This page is part of the frozen build source, not a mutable image
status receipt. The immutable-source-index proposal is still unimplemented;
finite regressions do not prove that every future AST/semantic field is covered.

## Proof-input diagnostic channels (2026-11-03)

The parent captured a real session-only failure on the recorded Cat candidate.
Both one-shot modes parsed complete proof-input documents; the session returned
rc0 with2758bytes of nine library warnings before JSON and empty stderr. Those
bytes exactly match one-shot stderr. Forensic suffix validation establishes the
routing cause; production does not strip prefixes. These controls establish
analysis success, not candidate proof correctness.

`AnalysisSessionCommand.RouteAnalysisDiagnostics` sends proof-input diagnostics
to request stderr before solver-option processing/CLI replay. Serialization
still uses independent captured stdout. Warning policy/counts, proof options
and one-shot behavior are unchanged. Other requests retain their writer.
Six real reporter/StringWriter cases plus13existing Driver controls pass19/19
with0skips; builds and scoped whitespace pass. First formatting failure and
successful retry remain under `/workspace/tmp/experiment/verifier-optimization-v4/`.
Actual retry tmux session is `proof-input-output-checks-20261103-r2`; raw helper
metadata retains the base session name.

Fresh independent source review finds no narrow routing blocker. New-image
library-warning allow/deny and exact recorded-source controls remain required.
Broader preexisting limits remain: malformed option-binding failures can write
a failure status on stdout, solver-option setup differs from one-shot
proof-input-only setup, and translation exceptions can omit queued diagnostics.
The bounded successful-document routing fix does not resolve those cases.
Parent measurement stays tied to frozen v3; v4 requires a fresh artifact identity.

A request may supply `source_snapshots` with exact source text and
`source_root`/`logical_root` together. The native parser owns root and relative
library resolution against invocation.cwd. Stable logical URIs permit reuse
across immutable host snapshot directories; report paths, structured source
locations and message text that names a file map to the physical request snapshot
(see [warning path remap](#warning-path-remap-2026-11-05)). The client forwards argv without
suffix heuristics. It preserves lexical and canonical source aliases and rejects
conflicting supplied bytes. No Python include parser is involved.

The native filesystem captures actual parser/include/library reads and exact raw
SHA256 byte identities, checks them at completion, and reports the consumed
closure. Native library directory expansion supplies membership, which is checked
again before completion. This is a freshness check; hosts still own immutable
snapshots and explicit context/toolchain binding. Standard input, project-file discovery, arbitrary
plugins/Boogie switches, alternate input decoding, legacy Unicode mode, compiler
dumps and proof-dependency coverage reports are explicitly unsupported. Fixed
`--boogie=/randomSeed:42` and source libraries are supported. `source-fingerprint`
remains an explicit host one-shot operation. Errors do not silently restart or
fall back to another proof path.

The session explicitly enables the server-only UseCaching option; CLI parsing
otherwise leaves Get<bool> false even though the option declares a true default.
Existing CachingParser/CachingResolver reuse parsed and resolved native module
objects. DefinitionAnalysis.SessionCache keys expensive extraction and local
analysis by those resolved objects and rebuilds current graph/source metadata.
A changed dependency replaces its module identity; unused and empty modules are
pruned. Resolver identity includes effective manual-trigger, time/resource and
rewriter settings. Output/report destinations and target filters do not partition
semantic state. Error, faulted and cancelled compilations are retired before reuse; a missing
include created later must be discovered on the immediately following request
even when the main file has not changed.
Source-library bytes conservatively partition native state because
not all library axioms appear in Boogie's dependency collector.

Proof-input analysis and verification share a native translation per resolved
compilation/module. Effective verifier settings must match, including seed; an
analysis using seed0 and verify using seed42 intentionally have different verifier
contexts. Unchanged resolver modules may still reuse across those contexts.
Fingerprinting calls the existing five-argument Boogie TokenTextWriter with
setTokens=false. The default constructor mutates origins, destroying resolved
verification ownership; memory and real-native controls cover this boundary.

The native VerificationTask API reads Boogie's VerificationResultCache but does
not insert into it. The session registers every prepared split before applying a
request's assertion filter. It inserts only an implementation whose complete,
contiguous native split roster has drained with SolverOutcome.Valid, preserving
native index order and actual result metadata. Partial, cancelled, invalid,
unknown and bounded outcomes cannot publish success. Existing complete native
proof-input fingerprints strengthen implementation checksums before preparation,
covering arbitrary translated axioms omitted by native dependency traversal.
Native result checksums are position-free (2026-11-04, see
[session cache retention](#session-cache-retention-2026-11-04)): the base checksum
and the proof-input fingerprint are combined with `AssertionShape`, a hash of the
ordered assertion kinds and descriptions. Cached results retain the assertion
objects of the compilation that produced them, so a cache hit is rebased onto the
current split's assertions before it is reported.
Unsupported certificate owners get a fresh checksum, disabling cross-compilation
replay while preserving same-state completed task reuse. (Stale since 2026-11-06:
checksums now bind each implementation's modular key; implementations without a key
get the fresh checksum. See
[modular proof-input fingerprints](#modular-proof-input-fingerprints-2026-11-06).) Boogie's own cache
remains the result store and checksum/dependency lookup authority. The session
keeps one cache per verifier context (at most four, least recently used first).
A context's cache is cleared when it is evicted and at shutdown (the 32-compilation
clear was removed on 2026-11-07); another context's requests never clear it. Its size is
bounded by 4096 results, least recently used first.

Requests share prepared native task futures, with independent subscribers and
cancellation. The last cancelled subscriber retires the state, cancels the actual
native producer and awaits terminal stream drain. A completed status before
stream termination does not publish success. Native preparation finishes under serialized admission before concurrent readers
are admitted; queued callers cannot join a live request-owned preparation.
Same-generation verification requests may overlap, with one solver core per
session and eight pending requests. A queued source writer blocks new admissions
while existing readers drain. The client uses a dedicated POSIX process group;
if bounded cancellation cannot drain, it fails all owners and terminates the
group. It never restarts the session silently.

TRX uses a process-global console sink. The session captures its original
protocol writer once and suppresses other Console.Out output for the entire
session, avoiding per-request global swaps. Each request owns and disposes its
report logger, queue and streams. Reporting of shared native results is serialized
because native counterexample formatting sorts a shared list.

Local evidence is temporary under
[/workspace/tmp/native-analysis-session](/workspace/tmp/native-analysis-session).
The source build passed with a fresh Java runtime in a network-none container.
Focused memory checks pass Core12, Driver10 and broader affected Core82; Python
client fake checks pass45 with Ruff/Pyright. Tiny public native controls under
tmux demonstrate real JSON/TRX protocol output, same-state and cross-compilation
hits with no solver producer, native module extraction reuse, independent request
cwd/library semantics, missing-file and identical-root missing-include recovery, concurrent target verification,
weakened modular contracts, changed ordinary axioms, current assertion locations
after source movement, and partial assertion scope
followed by failing full scope after a compilation boundary. These are compiler
and synthetic lifecycle checks, not benchmark throughput, statistical or paid
experiment results. Final separately attested artifact and live experiment claims
belong to the parent integration plan.

Historical synthetic-control acceptance on 2026-11-03 (withdrawn for broad source-shape claims by the strict saved-model pilot) is recorded in
[summary](/workspace/tmp/native-analysis-session-review/third/summary.json),
[provenance](/workspace/tmp/native-analysis-session-review/third/provenance.json)
and [exit status](/workspace/tmp/native-analysis-session-review/third/exit.json).
Exact root flags without warning suppression pass warm/cross cache, real edited
module reuse, constant/partial-scope negatives, real alias overlays, concurrency,
seed partition, identical-root include recovery and fresh one-shot position parity.
That historical review found no blocker within its synthetic-control scope; broad
source-shape acceptance was subsequently withdrawn. It does not establish current
artifact/image or experiment acceptance.

## Clone source-shape correction, 2026-11-03

Canonical declaration/function clones and authored module copies now preserve
BodyStartTok. Parser-specific cloning additionally retains authored function
SignatureEllipsis; generic transformed-cloner refinement behavior is unchanged.
Authored module names and mutable attribute graphs are independently cloned,
so resolving @Options cannot mutate the cached parsed source. Synthetic default
module names have a separate existing reuse convention; do not generalize this
ownership claim to every synthetic node.

Strict dictionary-memory regressions cover every affected declaration/function
kind, parse spans, actual CachingParser misses/hits/includes/root replacement,
CachingResolver and module-fact reuse, full source/semantic/verifier-target models,
body movement, @Options ownership and refining function parse/resolution metadata.
The ordinary full-analysis exporter has a preexisting null-owner limitation for
the refinement source roster; that fixture explicitly covers authored shape and
resolution, while the main full-document parity assertion remains strict.

Focused current checks passed Core84/84 and Driver13/13,0skipped; whitespace and
focused builds pass. Raw logs and exact commands are in
[/workspace/tmp/native-analysis-session/clone-final-results-2.json](/workspace/tmp/native-analysis-session/clone-final-results-2.json).
Two independent source reviewers accepted the corrected source for fresh artifact
construction. Current compiler source is frozen. Parent-owned corrected-image
saved3/full30 exact model equality and elapsed-time measurements remain required;
no accepted speedup or paid-run result is established by these source checks.
