# Make seeded verifier randomization depend only on each target's own inputs

Status: in-progress (phase 2: B1 implemented and checked locally in the worktree on 2026-11-08; independent review and the separate adoption approval are open)
Record location: the main session copied this plan from the research worktree back into the owner repo on 2026-11-08.
The code work stays in `/workspace/tmp/dafny-stable-seed-wt`.
Date: 2026-11-08
Owner: native fork maintenance (dafny-optimization).
Parallel Cosyn safety fix: `/workspace/cosyn/plan/2026-11-08-final-gate-exact-program-reuse.md`.
Incident record: `/workspace/plan/2026-11-07-cat-topdown-modular.md`.
Evidence: `/workspace/tmp/cat-renderdata-diagnosis/summary.md`, section "Mechanism".

## Problem

With `--boogie=/randomSeed:42`, Boogie renames symbols to `random<N>`. Strings and type
names in Boogie.VCExpr 3.5.5 include `RandomiseNamer` and `SetRandom`. It also orders and
groups axioms and numbers type tags in a way that depends on the whole program.

In the Cat incident:
- 180 of the 183 RenderData VCs were logically identical across two programs that differed
  only in unrelated sibling declarations. The other 3 differed only in Boogie's follow-ups
  after `unknown`.
- Z3 still went from about 1-2 s to more than 30 s on two of them.

A target's outcome is therefore a function of the whole program and the seed, not of its
own live inputs. This makes modular proof reuse unsound as a predictor of grading.

## Goal

Under a fixed seed, the SMT text sent for a target's VC depends only on:
- the target's pruned live inputs;
- the seed;
- the options and toolchain.

The symbol names, declaration order, axiom grouping and tag numbering must not change when
unrelated declarations are added, removed or moved.

## Phases

1. Research (read-only, then a written design in this plan):
   - Locate the exact mechanism in Boogie 3.5.5. Check whether `make boogie`, a submodule
     or `customBoogie.patch` gives buildable source. Find where the shuffle, namer and
     tag numbering get their order and RNG draws.
   - Confirm with a minimal experiment that adding an unrelated declaration changes a
     target's SMT. Use the tee-wrapper method from the evidence summary.
   - Design per-declaration stable derivation: for example, names and order from
     `hash(seed, stable declaration identity)` and tags by a stable key.
   - List what it changes for grading. Seed-42 outcomes of existing proofs will change, so
     references and given certificates must be re-checked before any adoption.
2. Implementation in an isolated worktree, `/workspace/tmp/dafny-stable-seed-wt`. Prefer
   changes in the fork's own code over patching Boogie. If Boogie must change, record the
   patch and how it is built.
3. Verification:
   - the SMT for a target is identical before and after unrelated sibling edits (Cat
     RenderData case, plus a synthetic case);
   - existing native and unit test suites pass;
   - seed sensitivity still exists, so the seed still changes the SMT.

## Constraints (the weekly paid experiment runs at the same time)

- Do not change `/workspace/dafny-optimization` (main checkout, branch
  `native-session-optimization`), the native artifact, `dafny-version.toml`, images,
  `/workspace/src`, `/workspace/cosyn` or `/workspace/bench`.
- Work only in a separate git worktree under `/workspace/tmp/`.
- Local builds and tests run only on CPUs 56-63 (`taskset -c 56-63 nice -n 19`), with one
  heavy job at a time. Use no Docker image builds and no `--cpuset` outside 56-63.
- Make no provider calls. Make no commits unless the user asks.
- Adoption requires a separate approved step: native artifact, re-certification,
  reference re-check, then Cosyn re-enables modular final-gate reuse.

## Planned changes

Phase 1 findings and the design. No code was edited.

### Source used

- Boogie source: `git clone --depth 1 --branch v3.5.5 https://github.com/boogie-org/boogie` into
  `/workspace/tmp/dafny-stable-seed/boogie-v3.5.5` (temporary, read only). Its commit
  `d90c6c9ef7e0e244cef55ddd0557e28a1a1301d8` equals the `repository commit` in
  `~/.nuget/packages/boogie.vcexpr/3.5.5/boogie.vcexpr.nuspec`. It also equals the read-only checkout
  `/workspace/tmp/session-cache-retention-review/boogie` (tag v3.5.5).
- `strings` on the 3.5.5 DLLs finds the cited members, so no decompilation was needed: `GetReorderedDeclarations`,
  `Shuffle`, `GetLiveDeclarations`, `BasicTypeVisitor`, `GetNamer`, `ResetNamer`, `RandomiseNamer`, `NormalizeNamer`,
  `KeepOriginalNamer`, `SetRandom` and `GetModifiedName`.
- The fork has no `boogie/` checkout or submodule. `make boogie` (`Makefile:33,52-53`) and `customBoogie.patch`
  (project references to `../boogie/Source/...`) assume one. The build uses the NuGet package `Boogie.ExecutionEngine`
  3.5.5 (`Source/DafnyCore/DafnyCore.csproj:41`).
- Boogie paths below are relative to `Source/` at that commit.

### Mechanism

1. Seed and random generators.
   - `/randomSeed:N` sets `CommandLineOptions.RandomSeed` (`ExecutionEngine/CommandLineOptions.cs:201,1293-1296`).
   - Each split takes `randomSeed ?? Implementation.RandomSeed ?? Options.RandomSeed ?? 0`
     (`VCGeneration/Splits/Split.cs:103`). `Implementation.RandomSeed` is `{:random_seed}` (`Core/AST/Absy.cs:673-684`).
   - `Checker.Setup` copies the seed into the prover options: `SolverOptions.RandomSeed = split.RandomSeed`, or
     `split.NextRandom()` when `/randomizeVcIterations` > 1 (`VCGeneration/Checker.cs:164`; `Split.cs:104,1070-1073`).
   - Shuffle generator: a new `new Random(randomSeed)` per split in `Checker.GetReorderedDeclarations`
     (`Checker.cs:207-208`).
   - Name generator: whenever the seed is not 0, `GetNamer` returns
     `RandomiseNamer.Create(new Random(options.RandomSeed), namer)`
     (`Provers/SMTLib/SMTLibProcessTheoremProver.cs:75-83`).
     - The interactive prover drops its namers at every `FullReset` (`SMTLibInteractiveTheoremProver.cs:164-185`).
       `Checker.Target` calls `FullReset` for every split (`Checker.cs:143`).
     - It then creates the common namer lazily (`:33`) and copies it for each VC with a fresh `Random(seed)`
       (`ResetNamer`, `:95-99`).
   - Z3 seeds: `smt.random_seed` and `sat.random_seed` are sent with every VC (`SMTLibProcessTheoremProver.cs:441-444`).
2. What is shuffled.
   - `Split.PrunedDeclarations` is `Pruner.GetLiveDeclarations` (`Split.cs:41-57`), which returns
     `program.TopLevelDeclarations.Where(d => d is not Constant && d is not Axiom && d is not Function ||
     reachable.Contains(d))` (`VCGeneration/Prune/Pruner.cs:79-80`).
   - So the list keeps every procedure, implementation, type declaration, type synonym and global variable of the whole
     program, in program order, plus the reachable constants, functions and axioms.
   - With a non-zero seed, `GetReorderedDeclarations` runs a Fisher-Yates shuffle over this whole list
     (`Checker.cs:198-210`; `Core/Generic/Util.cs:8-14`). The permutation depends on the list length and on every
     position.
   - Procedures and implementations emit nothing, but they still take part in the shuffle. Adding or removing any method,
     lemma or function anywhere in the program adds procedures and implementations. That reorders the live declarations
     of every VC. Moving a declaration changes positions in the same way.
   - With seed 0, the same method sorts by `ContentHash` when `NormalizeDeclarationOrder` is on (default true,
     `CommandLineOptions.cs:609`; `Checker.cs:200-204`).
     - Only `Axiom` overrides `ContentHash` (`Core/AST/Absy.cs:276` returns 1 for every declaration; `:590`), and
       `IdentifierExpr` hashes to 1 (`Core/AST/Expression/AbsyExpr.cs:1275`). The hash is structural and ignores names.
     - Ties keep program order (stable `OrderBy`).
3. What the order controls. `Checker.Setup` feeds the list in order (`Checker.cs:172-194`). Only these calls produce
   solver input:
   - `AddAxiom` appends to `axiomConjuncts`, and `DeclareConstant` of a unique constant appends to `distincts`
     (`Provers/SMTLib/ProverContext.cs:210-240`).
   - `DeclareFunction` of a `{:define}` function and `DeclareType` of a Boogie datatype
     (`SMTLibProcessTheoremProver.cs:1588-1609`).
   - Plain functions, type declarations and global variables are declared later, on first use.

   From there:
   - The context axiom is `(and (distinct <unique constants in order>) (and <axioms in order>))`
     (`ProverContext.cs:242-259`).
   - `SetupAxioms` linearises each conjunct in that order (`SMTLibProcessTheoremProver.cs:400-416`).
   - For each conjunct, `VCExpr2String` erases types, collects declarations in first-use order, and emits the type
     axioms that this conjunct needs first as one `and` chunk in front of it (`:973-1038`, chunk at `:1014-1021`).
   - The VC follows (`SMTLibInteractiveTheoremProver.cs:101-107`).
4. Names.
   - `RandomiseNamer.GetModifiedName` returns `random{random.Next()}` (`VCExpr/RandomiseNamer.cs:38-41`).
   - `ScopedNamer.GetName` draws once per new global symbol (`VCExpr/ScopedNamer.cs:165-196`), and `GetLocalName`
     draws once per bound or local variable (`:200-212`). Clashes get an `@@k` suffix (`:102-130`).
   - So a symbol's name is the k-th value of `Random(seed)`, where k is the point at which it was named in this VC. The
     inherent name is not used. If the order is stable, the names are stable without any namer change.
   - `SetRandom` (`:28-31`) only replaces the generator. It cannot give a per-symbol draw.
5. Type tags and axiom grouping. Dafny uses the arguments type encoding (`Source/DafnyCore/DafnyOptions.cs:363`).
   - `TypeAxiomBuilder` numbers types with the running counter `CurrentCtorNum` in first-encounter order
     (`VCExpr/TypeErasure/TypeAxiomBuilder.cs:70-81,171-184,195-220`) and accumulates the new type axioms (`:48-64`).
     It is rebuilt at every `FullReset` (`SMTLibProcessTheoremProver.cs:105-121`).
   - `Setup(usedTypes)` numbers the basic types first (`TypeAxiomBuilder.cs:401-406`). `usedTypes` comes from a
     `BasicTypeVisitor` over the whole program except other implementations (`Checker.cs:133-142`;
     `Core/BasicTypeVisitor.cs`), in a `HashSet` in first-encounter order.
   - All other tags (3, 4, ...) and the `and` chunks follow the axiom order.
6. Whole-program inputs left once the order is fixed.
   - `usedTypes`: it holds only Boogie basic types, not bit-vector or float types. Dafny emits `int`, `bool` and `real`
     from the prelude (`rmode`, `string` and `regex` are not emitted), so the set and its order are constant for Dafny
     programs. Tags 0-2 were identical in E1.
   - Lifted lambda functions are named `lambda#N` from one counter over the whole program
     (`Core/LambdaHelper.cs:151,157-160`). No namer prints inherent names under a seed or with `/normalizeNames`, so
     lambda names matter only if an order key is built from names.

Conclusion: under a fixed seed, the names, tag numbers, `and` grouping and `distinct` order are deterministic functions
of four things: the order of the live solver declarations, the VC, the seed and the options. The only whole-program
input is the order, which comes from the shuffled list (its length and positions). The fork already documents this gap
for modular keys (`Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs:32-35`).

### Experiments (free, local, host build in the worktree)

Setup:
- Worktree `/workspace/tmp/dafny-stable-seed-wt` at `650e6db3` plus the main checkout's uncommitted diff (sha256
  `0d1a2cb1...`, saved as `/workspace/tmp/dafny-stable-seed/wt-base.diff`) and its untracked files. After the copy, the
  status and the diff hash are identical to the main checkout, which is unchanged.
- Build in `/workspace/tmp/dafny-stable-seed-wt`: `taskset -c 56-63 nice -n 19 dotnet build
  Source/DafnyDriver/DafnyDriver.csproj -c Debug -m:8 -nodeReuse:false -p:UseSharedCompilation=false`.
  - Result: 0 errors, 51.6 s, .NET SDK 8.0.133 (MSBuild 17.8.60). Log: `/workspace/tmp/dafny-stable-seed/build-baseline.log`.
- Solver: a private copy of z3 4.16.0 (sha256 `bf8484ec...`, the same bytes as the main checkout's
  `Binaries/z3/bin/z3-4.16.0`), behind a tee wrapper (`--solver-path`) that appends the exact solver input to
  `out/z3in-<label>-<pid>.smt2`. This is the method of the diagnosis `scripts/z3tee.sh`.
- All runs use `--cores:1 --isolate-assertions --verification-time-limit:30` on CPUs 56-63.
- Scripts are in `/workspace/tmp/dafny-stable-seed/scripts/`: `synthetic-run.sh`, `cat-run.sh` and `smtcmp.py`.
  - `smtcmp.py` compares VC by VC, cut at the first `(check-sat)`.
  - "canonical" is the diagnosis measure: names mapped to N, numerals to K, and nested `and` flattened into a multiset.
- Outputs are in `/workspace/tmp/dafny-stable-seed/out/` (temporary).

| case | contexts | seed path | VCs | textually identical | canonically identical |
| --- | --- | --- | --- | --- | --- |
| E1 synthetic `Target` | A vs B (unrelated datatype, function, lemma, method before) | `/randomSeed:42` | 5 | 0 | 5 |
| E1 | A vs C (same, after the target) | `/randomSeed:42` | 5 | 0 | 5 |
| E2 | A vs B, A vs C | seed 0 (default normalization) | 5 | 5 | 5 |
| E3 Cat `CatCore.RenderData` | validated vs candidate (graded argv) | `/randomSeed:42` | 183 | 0 | 183 |
| E3 | validated vs candidate | seed 0 | 183 | 183 | 183 |
| E4 | validated vs candidate | seed 0, `/normalizeDeclarationOrder:0` (program order) | 183 | 183 | 183 |
| E5 synthetic handles and lambdas | H1 vs H2 (sibling before target uses the same handle and a lambda) | seed 0 / program order / 42 | 9 | 9 / 4 / 0 | 9 / 9 / 9 |
| E5 | H1 vs H3 (sibling after) | seed 0 / program order / 42 | 9 | 9 / 9 / 0 | 9 / 9 / 9 |
| E6 synthetic tied handles | T1 vs T2 (sibling before target uses only `Dec`; target uses `Inc` then `Dec`) | seed 0 / program order / 42 | 3 | 0 / 0 / 0 | 3 / 3 / 3 |

Observations:
- E1 confirms the mechanism on the host build. Under seed 42, an unrelated declaration either before or after the target
  changes all of the target's VCs, which stay logically identical.
  - The first draws (the `Ctor` function and the tags 0-2 of the basic types) get the same names in A and B. After that
    the names diverge.
  - Tag 3 goes to a different type constructor in A and in B.
- E3 reproduces the incident on the host build. Seed 42 gives validated 183 verified (40.6 s) and candidate 181 verified
  with 2 time outs (100.8 s).
  - At seed 0 the 183 VCs are byte-identical and both contexts verify all 183 (42.9 s and 42.4 s).
  - In program order (E4) they are also byte-identical. Both contexts then time out on the same invariant (line 336 and
    line 318; RenderData starts 18 lines apart, at 299 and 281). Identical SMT gave an identical outcome.
- E5 and E6 show that Dafny's program order itself depends on the context. Function handles and lifted lambdas are
  emitted on demand, at the first declaration that uses them.
  - In E6, Boogie's own seed-0 path (`ContentHash` order, ties in program order) changes all 3 target VCs. The handle
    axioms of `Inc` and `Dec` have the same structure, so `ContentHash` ties and program order decides.
  - Therefore neither "use Boogie's seed-0 path" nor "pre-sort by `ContentHash`" is sufficient. The order key must be
    canonical and independent of position.
- Not done: counting declaration kinds in the two Cat Boogie programs. `--bprint` printed nothing in this CLI path, and
  the mechanism did not need it.

### Design

Requirement: the order of the live solver declarations must be a function of their own canonical content and the seed.
The names, tags, grouping and `distinct` order then follow without other changes. This was checked in the code above;
RandomiseNamer needs no change.

Order key:
- The key must not depend on program position or on whole-program counters such as `lambda#N`.
- The fork already has such a hash: `DeclarationHasher` (`DefinitionAnalysis.ModularProofKeys.cs:306-...`) hashes the
  printed declaration with lifted lambda names canonicalised by content, and the modular key is built from it.
- Using it as the order key makes the per-split SMT a function of exactly what the modular key covers, plus the seed,
  options and toolchain.
- Declarations the hasher cannot key (its `Unsupported` cases, or Boogie-added declarations) need a fallback key. Those
  implementations have no modular key anyway, so reuse stays off for them.

Order function:
- Sort by `(H(seed, key), key)`, where H is a deterministic hash (SHA-256, never `string.GetHashCode`).
- This is position-free per declaration. Declarations that emit nothing (procedures, implementations, type synonyms,
  globals, non-datatype types) can sit anywhere without moving the others.
- Fisher-Yates over a key-sorted list of only the emitting kinds would also work, but adding one live declaration then
  reshuffles all the others.

Options (only one is needed):

| option | where | change | keeps Boogie's meaning of the seed | ships as | assessment |
| --- | --- | --- | --- | --- | --- |
| A2 (recommended if a patched Boogie can ship) | Boogie `VCGeneration/Checker.cs` `GetReorderedDeclarations` (seed != 0 branch); `VCGenOptions` plus `CommandLineOptions` get `Func<Declaration, string> DeclarationOrderKey`; fork sets it from `DeclarationHasher` keys computed once per program | about 15 Boogie lines, 40-60 fork lines plus tests | yes: random names, seed-driven order, Z3 seeds, `split.RandomSeed` reporting, `FromSeed` and `{:random_seed}` unchanged | patched Boogie packages (see below) | canonical; one source of truth for declaration identity |
| A1 | Boogie only: filter to the emitting kinds, stable-sort by `ContentHash`, then the existing shuffle | about 5 Boogie lines | yes | patched Boogie packages | not sufficient: E6 shows `ContentHash` ties falling back to context-dependent program order |
| B1 (recommended if Boogie must stay unpatched) | fork only: Boogie gets seed 0 and `NormalizeDeclarationOrder = false`; the fork re-sorts the solver-input declarations in `TopLevelDeclarations` by `(H(seed, key), key)` in place (procedures and implementations keep their slots), adds `O:smt.random_seed=S` and `O:sat.random_seed=S`, and keeps reporting `S` in CSV, JSON and text logs | 80-120 fork lines plus tests | no: names become `$generated@@k` in first-use order, which depends on the seed only through the order; Boogie no longer sees the seed | fork commit only | canonical; changes what `--boogie=/randomSeed:42` means; `FromSeed` (measure-complexity), `{:random_seed}` and `/randomizeVcIterations` need their own handling; `SupportedProofBoogieArguments` and proof identity must keep binding S |
| B1' | B1 plus a `Factory` subclass whose prover overrides the protected `Namer` to draw names from `H(seed, k)` | B1 plus about 80 lines | closer (random names) | fork commit only | fragile: re-implements the private `commonNamer`/`finalNamer`/`hasReset` lifecycle (`SMTLibInteractiveTheoremProver.cs:19-20,33,65,95-99,120-124,137-153,164-173,663-668`); not recommended |
| B0 | fork only: Boogie's seed-0 path, seed only to Z3 options | 30-50 fork lines | no: order and names no longer depend on the seed | fork commit only | not sufficient (E6), and weakest randomization |
| C | fork only: one Boogie program per target, containing only its closure | large | yes | fork commit only | rejected: the engine would process shared, mutable AST objects once per program |

Planned changes for A2 (owner of each change in brackets; layers: code and evaluator toolchain, no spec or proof change):

| file / symbol | change | why | missing today | test |
| --- | --- | --- | --- | --- |
| [Boogie patch] `VCGeneration/VCGenOptions.cs`; `ExecutionEngine/CommandLineOptions.cs` | add `DeclarationOrderKey` (default null) | lets the host supply a canonical key | no hook | Boogie builds; Dafny compiles against it |
| [Boogie patch] `VCGeneration/Checker.cs` `GetReorderedDeclarations` | for seed != 0, order by `(H(seed, key), key)`, with key = hook or a printed-text fallback; seed 0 unchanged | removes the whole-program shuffle input | Fisher-Yates over the whole pruned list | E1/E3/E5/E6 at seed 42 become byte-identical; seed 7 differs from 42 |
| [fork] `DefinitionAnalysis.ModularProofKeys.cs`, `DafnyOptions` wiring | compute `DeclarationHasher` keys for the solver-input kinds of every translated program the engine verifies (one-shot verify and session), and install the hook | canonical key shared with the modular key | keys exist only for proof inputs | new unit test: keys and order are unchanged by an unrelated sibling and by the E6 handle case |
| [fork] `ModularProofKeys` remarks (`:32-35`) and `SchemaVersion` | state that an equal key now means identical SMT under a fixed seed; bump the schema | documentation and fail-closed keys | remark says the opposite | existing `ModularProofKeyTests` |
| [fork] wiki `native-analysis-session.md` | record the mechanism and guarantee | reusable lesson | none | none |

B1 has the same fork key work. It adds seed interception in `DafnyOptions` (or `BoogieOptionBag`), the in-place
re-sort before verification, prover options, logger seed fields and proof-identity binding instead of the Boogie patch.

### Planned changes for B1 (chosen 2026-11-08)

Owner: the fork (worktree `/workspace/tmp/dafny-stable-seed-wt`). Layers: code, evaluator toolchain, the fork's
Python client and wiki. No spec, proof, dataset or scoring change. Boogie stays the unpatched 3.5.5 package.

Two design details found while planning (both read in Boogie 3.5.5 source):
- `Checker.Target` numbers the basic types (tags 0-2) in the order a `BasicTypeVisitor` first meets them over the
  whole program in `TopLevelDeclarations` order (`Checker.cs:133-142`). Boogie never reorders `TopLevelDeclarations`,
  so this order always comes from the start of the prelude. An in-place re-sort that moved a different declaration
  to the front could change the tags with unrelated declarations. The re-sort therefore leaves the leading run of
  declarations up to the last first meeting of a basic type in place (for Dafny: the prelude up to `LitReal`), and
  reorders only after it.
- Global variables stay in place: their order is not solver-list order but the order of the where-clause assumptions
  in every VC (`VerificationConditionGenerator.cs:675`). Dafny's globals are all in the prelude.
- Dafny's translator never emits `{:random_seed}` (it is not in `ExpressionTranslator` attribute copy lists), so that
  attribute only comes from raw Boogie or plugins, which proof inputs already reject.

| file / symbol | change | why | missing today | test |
| --- | --- | --- | --- | --- |
| `Source/DafnyCore/DafnyOptions.cs`: new `StableRandomSeed`, new `ParseBoogieArguments` | a non-zero `/randomSeed:N` given in `--boogie`, with `/randomizeVcIterations` at most 1, sets `StableRandomSeed = N`, clears Boogie's `RandomSeed`, sets `NormalizeDeclarationOrder = false` and puts `O:smt.random_seed=N`, `O:sat.random_seed=N` first in `ProverOptions` (so per VC they come right after `rlimit`, where Boogie sent them, and a user `--solver-option` still wins); a seed from another option (measure-complexity, test-contracts) stays Boogie's; a later application replaces or removes these | Boogie must not see the seed (no shuffle, no `RandomiseNamer`); Z3 must still get it; the graded argv text stays `--boogie=/randomSeed:42` | no interception | new `StableSeedTests` (DafnyCore.Test): activation, `/randomizeVcIterations`, seed 0, re-application |
| `Source/DafnyCore/Options/BoogieOptionBag.cs` `BoogieArguments` binding | call `ParseBoogieArguments` instead of `BaseParse` | single entry for CLI, project files, session and language server | none | same |
| `Source/DafnyCore/DefinitionAnalysis.ModularProofKeys.cs`: new `OrderBySeed`, `BasicTypePrefix`, `LocalNames`, an alpha-invariant mode of `DeclarationHasher` (`globalNames`); wrapper `DefinitionAnalysis.ApplyStableSeededOrder` | lift lambdas once (as the session already does), then re-sort type constructors, constants, functions and axioms after the basic-type prefix into their own slots by `(SHA-256(seed, key), key)`, key = kind plus `DeclarationHasher` hash with lifted lambdas named by content and (order key only, changed during implementation) bound, let-bound, formal and type-parameter names replaced by first occurrence unless they name a global; procedures, implementations, globals and synonyms keep their places; ties keep program order (tied declarations give the same solver text, except content-equal lifted lambdas, which already make the program's keys unsupported); an implementation with `{:random_seed N}` gets one `{:smt_option}` attribute per seed name for N so that Z3 still ends with N | canonical, position-free solver order; an equal modular key implies equal order keys | order is program order or the whole-program shuffle | `StableSeedTests` capture the exact solver input from a no-op solver (`CommandLineOptions.CreateSolver`): equal with an unrelated block before/after, a shared-lambda sibling before/after and the E6 tied handles; seed 7 differs from 42 beyond the seed lines; basic-type order kept; own `{:random_seed}` keeps random names and Z3 ends with its seed; a control test pins Boogie's own seed changing with the sibling |
| `ModularProofKeys`: `SchemaVersion` 2 -> 3, remarks (`:32-35`), `{:random_seed}` implementations unsupported | state the new guarantee (equal key, stable seed, options and toolchain give identical SMT) and its limits; fail closed for Boogie's own seeded randomization | decision 3 default | remark says the SMT differs | updated `ImplementationSolverAttributesChangeTheKey`; new random-seed and iterations tests |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs`: `SupportedProofBoogieArguments`, `ProofInputsFor`, `ProofOptionsHash`, schema doc comments | compare `/randomSeed:N` with `StableRandomSeed ?? RandomSeed`; no proof inputs when `RandomizeVcIterations > 1`; hash `StableRandomSeed` | keys keep binding the seed; fail closed | seed moved out of `RandomSeed` would drop proof inputs | `ModularProofKeyTests.OptionChangesChangeTheKey("stable-seed")` (proof inputs exist under `--boogie /randomSeed:42` and differ from no seed); `RandomizedIterationsHaveNoProofInputs` |
| `Source/DafnyLanguageServer/Language/DafnyProgramVerifier.cs` `GetVerificationTasksFromTranslationAsync` | apply the order (on the large-stack factory) before printing and `engine.GetVerificationTasks` | one-shot `verify`, `measure-complexity`, the session and the language server all pass here | none | phase-2 E1/E3/E5/E6 runs; session test |
| `Source/DafnyCore/DafnyMain.cs` `BoogiePipelineWithRerun` | apply the order after resolution | `build`, `run`, `test`, `translate` verify through this legacy pipeline | none | `translate cs` on E1 A and B: every VC of A verbatim among B's |
| `Source/DafnyDriver/VerificationResultLogger.cs` (new `TaskRandomSeed`), `JsonVerificationLogger.cs`, `TextVerificationLogger.cs` | report the split's Boogie seed, else the stable seed | Cosyn reads optional JSON `randomSeed`; CSV/TRX/text logs | seeds vanish under B1 | session JSON test (DafnyDriver.Test) |
| `Source/DafnyCore.Test/ModularProofKeyTests.cs`, `Source/DafnyDriver.Test/AnalysisSessionRetentionTests.cs` | schema asserts follow the bump; seeded session reports `randomSeed` | follow the change | none | themselves |
| `python/dafny_analysis/models.py` `DafnyProofInputs._schema_fields`; `python/tests/test_models.py`, `python/tests/test_native_integration.py` | modular rows for every schema >= 2 | the fork's client would reject schema 3 | client knows only 2 | python unit tests (integration test not run) |
| worktree `wiki/native-analysis-session.md` | record the mechanism, guarantee, limits and adoption steps | durable lesson | none | none |

Out of scope (documented, unchanged): measure-complexity (`--random-seed`, `--mutations`, `task.FromSeed`) keeps
Boogie's per-iteration seeds, and combining it with `--boogie /randomSeed:N` is unsupported; test-contracts'
verification seed; seed 0 keeps Boogie's `ContentHash` order, whose ties follow program order (E6), so identical SMT
is guaranteed only with a non-zero `--boogie /randomSeed`; translation-wide counter names other than lifted lambdas
(Dafny's `$let#N`) are in the key, so an unrelated edit that renumbers them changes the key (reuse fails closed) and
may change the order. Adoption also needs Cosyn's `SUPPORTED_PROOF_INPUT_SCHEMAS` to accept schema 3 (Cosyn-owned).

Commands (worktree root, CPUs 56-63, one job at a time):
- Build: `taskset -c 56-63 nice -n 19 dotnet build Source/DafnyDriver/DafnyDriver.csproj -c Debug -m:8 -nodeReuse:false -p:UseSharedCompilation=false`.
- Format: `dotnet format whitespace --folder --verify-no-changes --include <touched files>` (the `make format`
  rule is whitespace only).
- Unit tests: `taskset -c 56-63 nice -n 19 dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~StableSeed|FullyQualifiedName~ModularProofKey" -- RunConfiguration.MaxCpuCount=1`,
  then `Source/DafnyDriver.Test` with `NativeVerificationCache|AnalysisSession|JsonVerificationLogger`.
- Python: `python3 -m pytest -q python/tests/test_models.py`.
- Phase-2 solver checks as listed below, with the new build.

### Shipping a patched Boogie (A1 or A2)

1. Keep the patch in the fork outside `plan/` and `wiki/`, for example `Scripts/boogie/stable-seeded-order.patch`. It
   applies to Boogie tag v3.5.5 (`d90c6c9e`). Optionally upstream it to boogie-org/boogie and later replace the local
   build with a released package.
2. Build: check out v3.5.5, apply the patch, then
   `dotnet pack Source/Boogie.sln -c Release -p:Version=3.5.5.1 -o <feed>`. Repack all Boogie packages at one version
   so that the dependency graph stays consistent.
3. Reference it with a repository-local `nuget.config` that adds `<feed>`, and with `Boogie.ExecutionEngine` 3.5.5.1 in
   `DafnyCore.csproj`. The feed is either committed or produced by a new Make target before restore.
4. Root build: `scripts/build-dafny-runtime.sh` and `src/utils/dafny_build.py` run `dotnet build Dafny.sln` on the
   pinned fork. They must produce or find the feed. The NuGet configuration digest in the build identity changes, and
   `dafny-version.toml`, the native artifact and the images that pre-warm NuGet packages (`docker/task/Dockerfile`)
   must follow. These are root changes and need their own approval.
5. Alternative: the existing `customBoogie.patch` route, with a `boogie/` checkout and project references. It changes
   the solution and the root build more than a package feed does.

### Grading implications (all options)

- Seed-42 outcomes change.
  - Every VC gets a new presentation (order, names, tags, grouping), so existing proofs can flip in either direction at
    seed 42 and 30 s.
  - The graded argv `--boogie=/randomSeed:42` stays the same text. With B1 the fork reinterprets it.
  - Per-target results before and after adoption are not comparable. Record the toolchain change in experiment records.
- References and given certificates must be re-checked.
  - Reference solutions must be re-verified under the new toolchain with the graded argv before adoption.
  - Given certificates and ledger entries are bound to the old toolchain hash and must be regenerated.
- The toolchain hash changes.
  - `AssemblyToolchainHash` covers the content of every `Boogie*.dll` and `Dafny*.dll`
    (`DefinitionAnalysis.ProofInputs.cs:612-616`). A2 changes both, and B1 changes `DafnyCore.dll`.
  - Every modular key therefore changes and old certificates fail closed. Bumping `SchemaVersion` makes this explicit.
- New property:
  - With an equal modular key, seed, options and toolchain, every split's SMT is byte-identical.
  - Z3 is deterministic on identical input: 6 of 6 runs in the diagnosis, and E4 above.
  - Modular reuse then predicts the graded solver run, except for wall-clock variance near the 30 s limit under load.
  - Cosyn can re-enable modular final-gate reuse only after the separate adoption step.
  - The native result-cache replay by key (`BindNativeVerificationChecksums`) becomes consistent with seeded SMT for the
    same reason.
- B1 only: Boogie-reported seeds disappear unless the fork re-adds them. Cosyn reads an optional JSON `randomSeed`
  (`cosyn/src/cosyn/dafny/verification.py:403`), and the CSV logger writes `RandomSeed`.

### Decisions needed

1. A2 (patched Boogie 3.5.5.1 from a local feed, keeps Boogie's seeded randomization) or B1 (fork only, the fork
   re-implements seeded order, names become normalized and Boogie no longer sees the seed).
2. With A2: how the feed is shipped (committed packages or a build step), and whether to upstream the patch.
3. With B1: whether `measure-complexity` (`task.FromSeed`), `{:random_seed}` and `/randomizeVcIterations` keep Boogie's
   old whole-program shuffle or move to the new scheme.
4. Adoption (native artifact, `dafny-version.toml`, re-certification, reference re-check, Cosyn reuse) stays a separate
   approved step, as stated in the constraints.

### Phase 2 verification (after the decision; all free and local, CPUs 56-63, serial)

- Cat RenderData: `scripts/cat-run.sh` on validated and candidate with `--boogie=/randomSeed:42`, then `smtcmp.py`.
  Expect 183 of 183 textually identical, and report both outcomes.
- Synthetic: A/B/C, H1/H2/H3 and T1/T2 at seed 42. Expect all VCs textually identical.
- Seed sensitivity: A at seed 42 and at seed 7. Expect different SMT beyond the `set-option` lines (order and names).
- Unit tests, filtered and run one at a time:
  `taskset -c 56-63 nice -n 19 dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ModularProofKey" -- RunConfiguration.MaxCpuCount=1`.
  Do the same for the new order-key tests and for `Source/DafnyDriver.Test` with the filters `NativeVerificationCache`
  and `AnalysisSession`.
- A2 only: build the patched Boogie feed under `/workspace/tmp/dafny-stable-seed/` and reference it only from the
  worktree. No Docker image builds.

## Progress

- 2026-11-08: Plan written; phase 1 delegated to an Opus agent.
- 2026-11-08: Phase 1 done (Opus agent).
  - Created the worktree `/workspace/tmp/dafny-stable-seed-wt`, detached at `650e6db3`, with the main checkout's
    uncommitted diff and untracked files copied in. The main checkout is unchanged.
  - Cloned Boogie v3.5.5 for reading and located the mechanism (above).
  - Built the host driver in the worktree.
  - Ran E1-E6 on CPUs 56-63, one job at a time, while host load was 0.7-4.
  - Findings: the seed-42 dependence comes only from the shuffle input. Boogie's own seed-0 path is not enough either,
    because program order depends on the context (E6). A canonical, position-free order key is required.
  - Blocked on the user's choice between A2 (Boogie patch) and B1 (fork only).
  - No code edits, commits, Docker builds or provider calls. Not touched: `dafny-version.toml`, the native artifact,
    `/workspace/src`, `/workspace/cosyn`, `/workspace/bench` and `/workspace/tmp/experiment/`.
  - No durable wiki finding was written yet. The mechanism will go to `wiki/native-analysis-session.md` with the
    phase-2 change, because before the decision there is no settled guarantee to document.
- 2026-11-08: User decision: B1 (fork-only; Boogie stays the unpatched 3.5.5 package).
  Defaults chosen by the main session for decision 3, open to user override:
  - `{:random_seed}` and `/randomizeVcIterations` keep Boogie's old behavior. The grader does
    not use them.
  - Modular proof keys must fail closed (no reuse) whenever either is in effect.
  - Measure-complexity is out of scope and documented.

  Phase 2 is delegated to an implement-and-verify workflow in the worktree (CPUs 56-63). An
  independent three-lens check of the phase-1 claims (source, experiment, design) is running in
  parallel. Its findings will be folded in.
- 2026-11-08: Phase 2 implemented and checked locally (implement-and-verify workflow agent, worktree
  `/workspace/tmp/dafny-stable-seed-wt`, base `650e6db3` plus the copied dirty tree; .NET SDK 8.0.133; z3 4.16.0
  private copy behind the tee wrapper; CPUs 56-63, `nice -n 19`, one heavy job at a time, host load 1.9-4.2).
  - Code as in "Planned changes for B1". Changes made during implementation, each found by a check:
    - The order key ignores local names. With the exact modular hash, H1 vs H2 stayed at 4 of 9 identical VCs:
      Boogie's lambda lifter shares one function between alpha-equivalent lambdas and keeps the bound names of
      the first it meets (`$l#4#y#0` from the sibling vs `$l#7#z#0` from the target). The modular key stays exact,
      so an equal modular key still implies equal order keys. The per-program shared hasher planned first was
      dropped, since the two keys now differ.
    - The `{:random_seed}` repeat must be one `QKeyValue` per option: Boogie's `AddAttribute` appends parameters
      to an existing `smt_option`, which `GetExtraSMTOptions` then ignores (caught by the new unit test).
    - `locals.ExceptWith(globalNames)` was quadratic; `RemoveWhere` cut the key and sort time on Cat from 3.1 s to
      1.1 s.
  - Build (worktree root): `taskset -c 56-63 nice -n 19 dotnet build Source/DafnyDriver/DafnyDriver.csproj -c Debug -m:8 -nodeReuse:false -p:UseSharedCompilation=false`:
    0 errors (log `/workspace/tmp/dafny-stable-seed/build-b1.log`, temporary). Format:
    `dotnet format whitespace --folder --verify-no-changes --include <12 touched C# files>`: no changes. Python:
    `ruff check` and `ruff format --check` on the touched files: clean. `dotnet format style` was not run (not part of
    `make format`).
  - Phase-2 solver checks with the final build (scripts in `/workspace/tmp/dafny-stable-seed/scripts/`, outputs in
    `/workspace/tmp/dafny-stable-seed/out/`, all temporary), all with `--boogie=/randomSeed:42`:

    | case | command | VCs | textually identical | outcome |
    | --- | --- | --- | --- | --- |
    | E3 Cat RenderData validated vs candidate | `cat-run.sh fc42-valid validated ...`, `cat-run.sh fc42-final candidate ...`, `smtcmp.py` | 183 | 183 (was 0) | both 183 verified, 59.7 s and 59.4 s (were 183 verified / 2 time outs) |
    | E1 A vs B, A vs C | `synthetic-run.sh f42-<ctx> synthetic/<ctx>.dfy ...` | 5 | 5, 5 (were 0) | all verified |
    | E5 H1 vs H2, H1 vs H3 | same | 9 | 9, 9 (were 0) | all verified |
    | E6 T1 vs T2 | same | 3 | 3 (was 0) | all verified |
    | seed 7 vs 42 on A | `synthetic-run.sh f7-A synthetic/A.dfy --boogie=/randomSeed:7` | 5 | 0 apart from the seed lines; 0 equal assert sequences | all verified |
    | legacy pipeline A vs B | `dafny translate cs synthetic/<ctx>.dfy ...` | 9 / 16 | all 9 of A verbatim among B's | all verified |

    The final-build Cat stream also equals the earlier build's (183 of 183). Per VC the seed lines sit after
    `rlimit`, where Boogie sent them; no `random<N>` names remain.
  - Unit tests (serial, `-- RunConfiguration.MaxCpuCount=1`, CPUs 56-63):
    - `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ProofInput|FullyQualifiedName~DefinitionAnalysis|FullyQualifiedName~StableSeed|FullyQualifiedName~ModularProofKey|FullyQualifiedName~Options"`:
      153 of 153 passed (log `test-core-final.log`). New: 14 `StableSeedTests` cases, `BoogieSeededImplementationIsUnsupported`,
      `RandomizedIterationsHaveNoProofInputs`, `OptionChangesChangeTheKey("stable-seed")`.
    - `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~NativeVerificationCache|FullyQualifiedName~AnalysisSession|FullyQualifiedName~JsonVerificationLogger"`:
      156 of 156 passed (log `test-driver-final.log`). The first run failed only
      `AnotherSolverPathNeverReusesTheState` at its file precondition: the worktree had no `Binaries/z3/bin`
      (ignored by git, not copied with the dirty tree). The two bundled Z3 builds were copied from the main checkout
      into the worktree's ignored `Binaries/z3/bin`; the test and the full filter then passed.
    - `python3 -m pytest -q python/tests/test_models.py`: 27 passed. `test_native_integration.py` (marked
      integration, needs a native build) was updated but not run.
    - Mutation checks: with `ApplyStableSeededOrder` disabled, 4 `StableSeedTests` fail (shared lambda before,
      tied handles, seed order, basic-type order); the unrelated-block cases pass, as program order already keeps
      them (E4). Without the basic-type prefix, seed 42 numbers `int, bool, real` instead of `bool, int, real` and
      `OrderKeepsTheBasicTypeOrder` fails. Both mutations were reverted (file compared with the kept copy).
  - Cost (temporary stopwatch, reverted): on Cat's CatCore module (11363 declarations, 71 kept as the prefix, 11202
    reordered) the step takes about 2.6 s in the Debug build: lambda lifting 1.4 s (one extra Boogie resolve and type
    check; Boogie lifts anyway), prefix 0.08 s, keys and sort 1.1 s. It runs once per verified module. A cheap
    CatCore target (62 VCs) took 42.1-42.5 s at seed 42 vs 38.2-38.4 s at seed 0 before the quadratic fix. Release
    timing was not measured.
  - Wiki (worktree): new section "Stable seeded order (2026-11-08)" in `wiki/native-analysis-session.md`, the
    order-insensitive "not identical SMT text" claim marked stale for seeded runs, schema 3 noted, `{:random_seed}`
    note updated, `wiki/INDEX.md` entry added. The main checkout's wiki is unchanged.
  - The B1-only change against the phase-1 base (main checkout files vs worktree files, 17 files) is saved as
    `/workspace/tmp/dafny-stable-seed/b1.patch` (temporary).
  - Not done or not run: LIT integration tests, language server tests, a Release build, an independent review,
    adoption (native artifact, `dafny-version.toml`, reference re-checks, certificate regeneration, Cosyn's
    `SUPPORTED_PROOF_INPUT_SCHEMAS` accepting 3). No commits, Docker builds or provider calls. Not touched:
    `dafny-version.toml`, the native artifact, images, `/workspace/src`, `/workspace/cosyn`, `/workspace/bench`,
    `/workspace/tmp/experiment/` and the main checkout's code.
