- [Native validation before verification](native-analysis-session.md#boogie-validation-before-verification-2026-11-12) — preserved validation diagnostics and detached successful caches; final archived replay and independent native checks accepted; existing images unchanged. [Plan](../plan/2026-11-12-native-verification-oom.md).

- [Native session execution timings](execution-profiling.md) — negotiated request-local timing evidence, cache and overlapping-work semantics; source verified locally and independently 2026-11-12. [Plan](../plan/2026-11-12-native-phase-profiling.md).

- [Stable seeded order](native-analysis-session.md#stable-seeded-order-2026-11-08) — a non-zero `--boogie=/randomSeed:N` hides the seed from Boogie, orders the solver declarations by `(SHA-256(seed, key), key)` over the modular declaration hash (bound names ignored, basic-type prefix kept) and sends N to Z3; equal key, seed, options and toolchain give byte-identical SMT (Cat RenderData 183/183, synthetic cases); schema 3; `{:random_seed}`, `/randomizeVcIterations` and measure-complexity keep Boogie's randomization; not adopted. [Plan](../plan/2026-11-08-stable-seeded-randomization.md).

- [Modular proof-input fingerprints](native-analysis-session.md#modular-proof-input-fingerprints-2026-11-06) — schema-2 proof inputs key each Boogie implementation over its pruned solver input (superset of every split, 0 violations over 3447 Cat splits); order-insensitive (equal key = equal formula set); zero-obligation certificates; solver binary in the toolchain; native lookup by key instead of Boogie's dependency checksum; results bounded by count (LRU) instead of a 10-minute idle expiry; Boogie `Expr.pos` pitfall; Cat: 7 of 7 given keys stable skeleton to reference; options hash and keys independent of the install path (solver bound by content), while the session context binds the solver path and content (a content-only context reused an engine bound to another path); toolchain covers every Boogie/Dafny assembly; relative solver paths fail closed. [Plan](../plan/2026-11-06-modular-proof-fingerprints.md).

- [Cross-process session transfer](native-analysis-session.md#cross-process-session-transfer-2026-11-05) — `export-session`/`import-session` move detached parser sources and proof results to a fresh native process; strict validation, frame bound, parked parser seeds; real Cat check with 0 solver runs in two concurrent processes. [Plan](../plan/2026-11-05-cross-process-session-transfer.md).

- [Independent native branch cache cloning](native-analysis-session.md#independent-native-branch-cache-cloning-2026-11-05) — retained parent/multiple child epochs, private parser templates and detached authoritative proof caches;59client units/17fake integrations/27native cases and independent reviews. [Plan](../plan/2026-11-05-native-cache-cloning.md).

- [Request-local diagnostic locations](native-analysis-session.md#request-local-diagnostic-locations-2026-11-05) — logical cached ranges and captured excerpts stay unchanged; request-local filename/JSON URI presentation maps to physical sources. [Plan](../plan/2026-11-05-review-diagnostic-locations.md).

- [Persistent native analysis and verification](native-analysis-session.md) — 2026-11-04 session cache retention (per-context result/resolver caches, position-free result key, rebased cache hits) and reported analysis scope (`--analysis-source`) keeps one compilation across scope changes, per-profile facts cache; 2026-11-05 session warning/diagnostic text maps logical root to physical per request (Driver59 incl. 16 new); 2026-11-05 diagnostic source excerpts read the request's captured bytes through `DafnyOptions.SnippetFileSystem` instead of the logical-root file on disk (smoke F6; 12 new Driver tests); source/local phase accepted: clone metadata, diagnostic channels and cached export ownership, Core84/Driver21/fresh review. Parent records image/runtime/experiment acceptance; invalid artifacts remain separate.

- [One Python client for native Dafny analysis](python-analysis-client.md) — `python/dafny_analysis` merges the Cosyn and Dafnyutils clients; injected command runner, strict Path/SHA-256 models, tests and limits.

- [Native tests depend on which Z3 Dafny selects](native-test-solver-selection.md) — five contract tests differ between `z3-4.16.0` and the PATH fallback on both base and pin branch; comparison procedure and limits.

- [Native PBT delivery and validation boundaries](pbt-main-delivery.md) — reviewed runtime closure, checked helper screening, verifier-seed forwarding and explicit matching-source/canonical-build limits.

- [Nested statement matches in proof expressions](nested-match-substitution.md) — independently accepted compiler substitution, local scope and ordinary proof rejection; source delivery on expecto, image and weekly outcomes tracked by the parent.

- [Generator proof helpers](pbt-generator-proof-helpers.md) — authored ensures, ordinary implication lemma and complete helper/ambient closure; current refactor memory-tested, independent/native controls pending.

- [Exact generator admission proof boundary](pbt-generator-proof-integrity.md) — authored contracts, analyzer identities and ordinary verifier tasks; accepted public diagnostic identifies helper definition-input drift. Core memory regression reproduces repeat-translation drift; scoped naming repair retains exact evidence gates, with fresh review and operational acceptance pending.

2026-10-19: [PBT trusted source snapshots](pbt-trusted-sources.md) records exact source/digest trust binding and retained runtime/type/heap admission; combined-tree source independently accepted on base `29da48b6`, focused tests15/15; see the [owner plan](../plan/2026-10-19-pbt-trusted-sources.md). The [2026-10-26 arithmetic follow-up](pbt-trusted-sources.md#ambient-integer-constants-2026-10-26) preserves that trust policy and admits closed total integer arithmetic; independent28memory cases and formatting pass, image/live adoption pending.

# Native Dafny knowledge

- [Diagnostic treatment of unrelated bodyless declarations](pbt-unreachable-bodyless.md) — method/constructor and iterator transformation accepted locally; actual R07 exposes generated Valid draft before transformation. [Execution-only draft correction](pbt-unreachable-bodyless.md#iterator-types-and-implementation-draft-discovery-2026-10-23) independently accepts3builds/4real memory cases and exact5source/4payload bindings. Public proof/fingerprint closure and conservative iterator capability remain; full new image/tool acceptance is unmet.
- [Binary PBT feasibility before authoring](pbt-trusted-sources.md#binary-feasibility-before-authoring-2026-10-26) — independently verified; shared source-only binary analysis before templates, exact binding and operational errors preserved;109 memory checks and three project builds pass.



- [PBT random source bounds and Unicode scalar intervals](pbt-random-api.md) — size contract, deterministic constructor seam and scalar-gap mapping; 23 selected pure-memory cases and fresh independent review pass on 2026-10-20; exact normalized resource pin updated.

- [Match-pattern variables and automatic trigger scope](match-trigger-variable-scope.md) — exact sources independently accepted; both AST forms preserve valid candidate identity and reject local binders, 12 new plus 3 preserved cases per owner and generic compiler recovery confirmed; formatter timeout/retry warnings retained.

- [Native proof-input projection integration](definition-proof-inputs.md) — historical 2026-10-15 five-file source match, local build/format, and independent Core21/Driver6/interface acceptance; on 2026-10-16 the command-test path was removed, leaving four of five manifest paths. Prior Driver6/6 is not current validation; see the [cleanup plan](../plan/2026-10-16-remove-proof-input-tempdir-tests.md). The [scope-limits review](../plan/2026-10-16-proof-input-scope-limits.md) distinguishes raw translation from later preprocessing; unused-procedure filtering is not selected. Historical binary freeze and four build warnings retained; image/paid gates parent-owned.

- [Aggregate JSON verification resource counts outside the 32-bit range](json-verification-resource-count.md) — superseded for active modern reports 2026-10-15; prior overflow repair receipts remain historical, while legacy/internal counters stay outside the reporting removal.

- [Preserve bound variables when recombining trigger splits](trigger-bound-variable-scope.md) — compiler invariant and generic regressions, verified locally on 2026-10-14; independent review and private replay tracked in the originating plan.

- [Native internal compiler exit contract](internal-compiler-exit-contract.md) — explicit code 6, typed event priority and terminal mutation behavior; local native checks pass, independent acceptance pending.

- [Resolved function body visibility](function-body-visibility.md) — effective opacity and conservative resolved dependency/reveal closure, independently22-case verified.

- [Unified native Dafny runtime](unified-dafny-runtime.md) — 2026-10-19 source independently verified (90 native checks); combined metadata retains trust/proof behavior; parent pins/build metadata separate.
- [Installed draft provenance](pbt-installed-draft-evidence.md) — actual substitutions govern runtime evidence and callee attribution; strict unused-draft validation and native proof bindings preserved, independently verified 20 memory cases.
- [Diagnostic generator names](pbt-generator-formal-names.md) — response-authoritative public names plus canonical-snapshot two-hop runtime binding; exact formal/member/runtime identities and include-first named/default/cross-file controls independently accepted.

2026-10-18: [Resolved verification target facts](verification-target-facts.md) — opt-in actual compiler target inventory and authored declaration attributes; build, seven in-memory tests, generic native proof/attribute controls and fresh independent review accepted; baseline style limitations recorded.

2026-10-15: [Modern native verification logging](verification-json-logging.md) — reporting removal independently accepted; solver limits/outcomes retained, implementation25unique LIT and independent33focused checks pass. Standalone probe limits and historical overflow/campaign receipts preserved; no image or experiment claim.
- [Generator proof value domain](pbt-generator-value-domain.md) — independently accepted2026-10-25; empty premises, finite collections and immutable/refined-map projections, native127/independent69 memory checks and formatting pass; actual solver/sample/image efficacy remains separate.

2026-10-26: [Immutable field identity aliases](pbt-trusted-sources.md#immutable-field-identity-aliases-2026-10-26) adds exact finite fresh-class construction with unchanged trust, scope and concrete-heap checks; independent40memory cases pass. Full-public/image adoption remains separate.

2026-10-26: [Post-preparation sampling budget](pbt-trusted-sources.md#post-preparation-sampling-budget-2026-10-26) assigns half of the remaining post-compilation campaign budget to one fixed sampling cutoff; independent review, bounded build, 9/9 pure tests and scoped format/diff checks pass. CLI/image/live campaign effects remain separate.

2026-10-26: [Preparation and compilation reuse](pbt-trusted-sources.md#preparation-and-compilation-reuse-2026-10-26) records cohesive resolved-program reuse, source-edit/default semantics, a smaller PBT-only C# backend, typed terminal feedback and unchanged admission/deadlines. Independent111 memory cases and pinned CLI publication pass; latest exact-input compiler worker51.380→21.339s; valid-sample/counterexample efficacy remains unestablished.

2026-10-26: [Old-state capture admission](pbt-trusted-sources.md#old-state-capture-admission-2026-10-26) defers capture emission until the final consuming decision and validates inputs first; independent44 memory cases and scoped formatting pass. Exact-input r03 reaches64 target calls, then external ghost-state errors and classification timeout; no valid classified sample or counterexample.
- [Bounded contract models](pbt-trusted-sources.md#bounded-contract-models-2026-10-26) — explicit generator policy, finite bool/int state and joint extern transition search, preserved checks and no-evidence exhaustion; independent145 memory checks and three project builds pass. No Csplit or real native IO correctness claim.

- [Traverse syntactic children before contract-screen resolution](contract-screen-source-traversal.md) — verified development patch; publication authorized; downstream deployment tracked in integration recovery plan.

- [Contract screen omitted-body identities](contract-screen-omitted-body-identity.md) — native resolution lifecycle verified in development; not deployed or pinned.
