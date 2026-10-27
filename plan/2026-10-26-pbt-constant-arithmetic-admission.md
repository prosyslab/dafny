# Admit closed integer arithmetic in PBT global construction

Status: done
Date: 2026-10-26

## Objective and evidence

Repair the false rejection of fully defined integer constant arithmetic during
PBT initial-state construction. The public R10 support probe compiled and ran
four samples, but global construction rejected `nat := 64 * 1024`, forcing four
full-premise SMT queries which timed out. The exact public set has 46 static
globals; existing literal, conversion, datatype and collection branches cover
all other defined RHS shapes. The bodyless extern remains under the existing
abstract-global structural check. No benchmark candidate or hidden data is used.

The existing `ConstantFolder.TryFoldInteger` implements integer arithmetic, but
is internal to DafnyCore. General partial reduction can discard undefined
operands, and unrestricted constant folding admits unrelated syntax. Reuse the
folder through a narrow total-integer-arithmetic syntax gate: BigInteger literal
leaves and resolved integer Add/Sub/Mul trees only. Keep all other syntax on its
existing path. The parent is
[Cosyn extern runtime plan](../../plan/2026-10-26-pbt-extern-runtime.md).

## Acceptance and boundaries

- Positive closed integer arithmetic permits global construction after the
  existing complete declaration scope is accepted.
- Built-in nat still requires a nonnegative value. Other subsets/newtypes,
  undefined operands, calls, conversions, noninteger arithmetic and residual
  expressions remain conservatively rejected by the new path.
- The small fold helper computes a value only; `IsIntegerType` normalizes
  refinements. Subset/newtype membership rejection belongs to the unchanged
  expected-type admission boundary and is tested there, not asserted for the
  helper alone.
- Keep existing reference recursion/cycle checks and literal/datatype/collection
  handling. Do not expand trust, filter ambient declarations, change preconditions,
  remove original proof checks, increase timeouts or change source snapshots.
- Preserve all concrete input/receiver/heap/frame checks, trust/source ownership,
  schema and cache identities. No benchmark source or evaluation change.
- Independent source/memory checks precede rebuilt-product and R11 readiness.

## Change table

| Files / symbols | Change, need and validation |
| --- | --- |
| `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs` | Expose a small static integer-arithmetic fold helper. Internally reject all but resolved integer literal/Add/Sub/Mul trees, then delegate to existing ConstantFolder. No new evaluator or public access to the whole internal folder. Memory positive/exclusion/domain cases. |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeHeapChecking.cs`, `ClosedConstantValue` | Reuse the folded value only for expected plain int or built-in nat, with nat range preserved. Keep every other gate unchanged. Positive construction and negative membership checks. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeGlobalAdmissionTests.cs` | New bounded in-memory owner using SnapshotFileSystem parse, direct AbstractGlobalsInhabited and RequiredScope; optional exact trusted source with check-free accepted scope and TryPrepare. No fabricated certificates, CheckModuleAsync, solver, process, filesystem writes, temp directories or synchronization. |
| This plan, native plan index, existing `wiki/pbt-trusted-sources.md` and wiki index | Record unchanged trust policy, actual source/test evidence and limits. No new wiki topic needed. |
| Parent Cosyn plans/index and existing goal-PBT wiki | Link native repair and distinguish local evidence from image/live outcomes. |

## Validation and execution

Audit the complete new test helper path before execution. Cover arithmetic
construction; a negative computed nat; direct reference chains; preserved full
scope/native requirements for untrusted constants; and rejection of division
(including under multiplication by zero), calls, conversions, strings/sequence
operations, conditionals, bitvectors and constrained domains in the new helper.
Use a one-line intention comment for each scenario. Existing broad heap-query
and Driver admission classes invoke native/disk workloads and will not run.

From `/workspace/cosyn/dafny`, build separately as an operator in recorded tmux:
`dotnet msbuild Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj -nologo -t:Build -verbosity:minimal -maxCpuCount:1 -nodeReuse:false -p:SkipFocusedTestAssets=true`.
Retain bounded log under `/workspace/tmp/pbt-constant-arithmetic-20261026/`.
Then run `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractRuntimeGlobalAdmissionTests|FullyQualifiedName~ContractTrustedSourcesTests' -v:minimal`.
No native compilation occurs in tests. Scoped whitespace checking uses the
repository's `dotnet format whitespace` command with only the three named files,
`--no-restore --verify-no-changes`; avoid broad formatting mutations.
Review `git diff --check` and independently run the safe selected memory tests.
Parent owns separate bounded CLI product publication and a fresh R11 PBT image.

## Risks and non-goals

Broadening reduction could hide undefined expressions or constrained values.
The explicit total-arithmetic syntax gate and final expected-type checks prevent
that expansion. Full global dependency/native certification remains unchanged;
host computation is not a replacement for declaration proof. Preserve ongoing
user commits/pre-commit temporary stashes without restoration or overwrites.
No dependencies, commits, paid calls or benchmark edits are introduced here.

## Progress

Independent read-only review rejected an ambient trusted-global exemption as a
trust-contract expansion. That approach is abandoned. Source implementation,
memory tests, publication, installed-image acceptance and real Csplit evidence
remain pending.

Implementation began with the frozen three-file source and memory-test scope.
The guarded fold seam, expected-type admission and bounded in-memory regression
owner are implemented, including accepted-scope ownership/no-native-proof checks
and distinct constrained subset and newtype controls. Static diff and call-path
review found no filesystem, process, solver or synchronization operation in the
selected tests. Build, test, publication and runtime validation remain owned by
the parent operator workflow and have not run yet.

## Independent source gate and operator dispatch

Independent review accepted the two production changes and traced the complete
new test path as memory-only. Test refinements explicitly retain the constant in
scope, require RequiresNativeProof=false on positive construction, and reject
newtype arithmetic separately. Frozen production hashes are
`e02f3387a051ab63b2fcd9e74643eacffebc1d171aab8b91be3beb5cd61e53e6`
and `d50ec3312c5ffd5aeef5a9b22de9a1bdfc4c50ba11bad7e3ffe8f9b66aa45c23`;
new test hash is `bce56ad2136390792ba596f7a72d12586c2ab3e3b48f6d9ad10072ac5c6f0cd2`.
Root bound these exact current bytes into the independently reviewed stdlib-only
worker and launched tmux/socket `pbt-constant-arithmetic-test-build-20261026`.
Worker hash `1bc4ea410603b628f66f9e4452d51bba3a8e4049c8f07d9566880ddd0b4a14c2`;
launch/log/result live under `/workspace/tmp/pbt-constant-arithmetic-20261026/`.
Actual build/test outcomes remain pending. No provider or container was launched.

Operator syntax and actual root-config Ruff checks pass with cwd `/workspace`
and `--no-cache --no-force-exclude`. Earlier checks from Cosyn cwd classified
imports differently; the ordinary root invocation excluded scratch entirely,
and the first no-force-exclude attempt hit a read-only cache. None of those is
counted as a pass. No helper source was changed to address those invocation issues.

## First matching memory validation and formatting retry

The bounded test-project build exited 0, all fifteen source pins matched, and
independent `--no-build --no-restore` tests passed 28/28 with zero skips (312 ms;
.NET SDK 8.0.131, VSTest 17.8.0). Test assembly SHA256 was
`0ec00e92693928a428dee98b5add09263594ee9ddc9c2011721fbd5c662fa43c`.
Independent scoped formatting found two whitespace diagnostics in the new
BinaryExpr property pattern. The scoped formatter fixed only that layout;
new reducer hash is `1faa59617c56c48f51e999ea6f9aad3ea3555307b1283a17434073a2bd8ca4c6`.
Heap/test hashes remain unchanged. Preserve the initial build and test records.

Ready retry scope: derive `native-test-build-format.py` from the accepted worker,
change only its reducer pin and unique `native-test-build-format` output names,
and launch tmux `pbt-constant-arithmetic-test-build-format-20261026`. Rebind the
same reducer pin in the unexecuted R11 builder/publication worker. Repeat the
same narrow memory/format validation to establish final matching-source evidence;
no broader tests, changed semantics, trust, trial policy or data scope.

Final formatted-source build and independent verification pass: 28/28 memory
cases, zero skips, 539 ms; exact source/test and fresh testhost Core/TG dependency
hashes bound. Scoped three-file whitespace check exits 0 (only workspace-load
warning), diff check clean. Final logs are `independent-memory-tests-final-format.log`
and `independent-format-check-final-format.log` under the named arithmetic scratch.
Binaries TG was still the old publication after the test-project build; do not
confuse testhost success with CLI product freshness. Root has now dispatched
`pbt-csplit-native-publication-20261026-r11`, guarded by all fourteen current
source hashes, to refresh the actual four CLI products. Source/trust policy will
be recorded in native wiki/pbt-trusted-sources.md; installed-image/live evidence
is still pending.

## R11 actual outcome: additional initial-construction limitation remains

R11 image `86ce2b8172a4fef05e34e00c672a5aece2068d40a9464977c25b32d889db9470`
contains the exact newly published products. Independent actual audit confirms
all current fourteen source/four product/nine helper/public/delivery/Cosyn/latest
identities, original base ancestry, typed authoring/proof controls, corrected
call origin, default extern four valid samples and missing-link CS0103 control.
Full public support still executes four samples with clean runtime postconditions
but zero valid samples: all initial admissions report closed_query_timeout.
Build exit1/transport0; owned container was removed and absence independently
queried by exact name/CID. No accepted image identity or live trial exists.
R11 artifacts are now immutable. Arithmetic source/local regression and CLI
publication evidence remain valid, but do not establish full-support admission.

Before any further image attempt, inspect the remaining constructive-admission
failure directly. A bodyless nonnull global also requires a structural witness
for its class; public IO contains initialized ghost readonly state in that class.
No next production repair is approved by this observation alone. Preserve trust,
timeouts, complete public sources, fixture contract and sample classifications.
The single authorized fresh model trial remains unconsumed.

## Closure

Done for the bounded arithmetic repair: all its source, memory, formatting and
matching-product criteria pass. R11 installed products also match the repaired
source. Full-support admission and the Csplit objective remain incomplete under
the parent plans; the separately diagnosed immutable alias gap is covered by
[its own plan](2026-10-26-pbt-immutable-alias-admission.md). Durable findings were
recorded in [trusted-source semantics](../wiki/pbt-trusted-sources.md).
