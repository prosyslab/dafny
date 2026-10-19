2026-10-19: [PBT trusted source snapshots](pbt-trusted-sources.md) records exact source/digest trust binding and retained runtime/type/heap admission; combined-tree source independently accepted on base `29da48b6`, focused tests15/15; see the [owner plan](../plan/2026-10-19-pbt-trusted-sources.md).

# Native Dafny knowledge

- [Match-pattern variables and automatic trigger scope](match-trigger-variable-scope.md) — exact sources independently accepted; both AST forms preserve valid candidate identity and reject local binders, 12 new plus 3 preserved cases per owner and generic compiler recovery confirmed; formatter timeout/retry warnings retained.

- [Native proof-input projection integration](definition-proof-inputs.md) — historical 2026-10-15 five-file source match, local build/format, and independent Core21/Driver6/interface acceptance; on 2026-10-16 the command-test path was removed, leaving four of five manifest paths. Prior Driver6/6 is not current validation; see the [cleanup plan](../plan/2026-10-16-remove-proof-input-tempdir-tests.md). The [scope-limits review](../plan/2026-10-16-proof-input-scope-limits.md) distinguishes raw translation from later preprocessing; unused-procedure filtering is not selected. Historical binary freeze and four build warnings retained; image/paid gates parent-owned.

- [Aggregate JSON verification resource counts outside the 32-bit range](json-verification-resource-count.md) — superseded for active modern reports 2026-10-15; prior overflow repair receipts remain historical, while legacy/internal counters stay outside the reporting removal.

- [Preserve bound variables when recombining trigger splits](trigger-bound-variable-scope.md) — compiler invariant and generic regressions, verified locally on 2026-10-14; independent review and private replay tracked in the originating plan.

- [Native internal compiler exit contract](internal-compiler-exit-contract.md) — explicit code 6, typed event priority and terminal mutation behavior; local native checks pass, independent acceptance pending.

- [Resolved function body visibility](function-body-visibility.md) — effective opacity and conservative resolved dependency/reveal closure, independently22-case verified.

- [Unified native Dafny runtime](unified-dafny-runtime.md) — 2026-10-19 source independently verified (90 native checks); combined metadata retains trust/proof behavior; parent pins/build metadata separate.
