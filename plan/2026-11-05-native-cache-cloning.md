# Clone reusable native caches into independent sessions

Status: done
Date: 2026-11-05
Parent: [Cosyn session cloning](../../cosyn/plan/2026-11-05-native-session-cloning.md).

## Scope and pass criteria

User explicitly requests parent-to-two-child cloning instead of adoption/replay.
Maintenance work; preserve the dirty native base 0776df27 and existing changes.
Copy parser seeds and complete successful native proof-result data, then create
independent branch-local resolver/facts/compilation/engine/task/cancellation and
filesystem owners. Parent stays usable and can clone multiple times. No command
replay, unsafe full resolved-graph clone, OS process fork, new dependency, external
success import, protocol fallback, paid run or commit.

This is cache-snapshot inheritance, with actual copied-entry receipts; it does not
claim full resolved-program/state copying. Current Program resolved cloning throws;
translation mutates scope/name/dependency scratch. Compiler preparation is guarded
across in-process branches until static-state concurrency is established.

## Existing code inspected

Native AGENTS/CLAUDE and root maintenance/test rules, protocol Session/State,
CachingParser/ParsedSourceCloner, pruning cache, resolver/facts ownership, matching
Boogie 3.5.5 source at temporary session-cache-retention-review (d90c6c9),
VerificationResultCache/ImplementationRunResult/VerificationRunResult, Python
transport and memory-backed tests. No plan/wiki rules/templates exist.

## Protocol and ownership

Use exactly the branch/clone/close-session contract in the parent plan. Existing
contextId role remains cache-key input; sessionId is separate branch routing.
Clone receipt stdout is a strict versioned JSON object with daemonEpoch, parentId,
parentEpoch, sessionId, sessionEpoch, parsedEntries and verificationEntries.
Root id defaults to `default`; existing jobs/cancel/shutdown remain compatible.
Clone/dispose cannot block the protocol reader from receiving cancellation.
Closing one branch drains only its work; final transport owner reaps the daemon.

## Planned changes

| Exact files/symbols | Change and need | Validation |
| --- | --- | --- |
| `Source/DafnyLanguageServer/Caching/PruneIfNotUsedSinceLastPruneCache.cs`: explicit snapshot/copy; `Language/{CachingParser,DafnyLangParser}.cs`: parser cache clone | Independent maps/pruning markers and branch-private parsed templates reconstructed solely from retained immutable source text/URI with child options; no filesystem or command replay | In-memory parent/two-child cache membership, different mutation/prune owners, unchanged parse seed |
| `Source/DafnyDriver/NativeVerificationCache.cs` (new) | Small IVerificationResultCache wrapper delegates native priority/lookup; detached successful aggregate snapshots; exclusively rent/reset native cache instances from process-local drained-owner reuse pool to bound non-disposable native timer owners; copy original id/checksum/dependency bytes and split/scalar/shape metadata, never child-request-derived identity | Complete-success-only snapshot, independent clear/expiry, checksum/dependency misses, no parent AST/task references, repeated clone/close allocation bounded by peak owners |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: protocol registry, Session clone, RetentionMap snapshot, ResultRetention, NativeTaskEntry rebase, completion insertion | Branch-addressed independent owners; copied caches, strict receipts, native lookup sole reuse authority, detached assertion metadata rebased to actual current assertions | Native branch clone, close/cancel, invalid control, source/option change miss and current locations |
| `python/dafny_analysis/session.py`: transport/branch lifetime, typed receipt, clone and close-session controls, pending validation | Share process transport with reference-counted branch handles; each branch has own epoch and closure; final owner shuts down | Memory process/pipe controls, two children, each close order, cancelled clone cleanup, stale/wrong branch/epoch receipts |
| `python/tests/test_session.py` | Extend fake daemon for branch protocol and lifecycle regressions | Serial memory-only pytest; no dirs/sync/native/provider |
| New `Source/DafnyDriver.Test/{AnalysisSessionCloneTests,NativeVerificationCacheTests,ParserCacheCloneTests}.cs` | Pure in-memory clone/cache regression coverage; native pipeline checks use injected bounded source snapshots | No tempdirs/native process/real builds inside test bodies; fake solver/cache seams where appropriate |
| `wiki/native-analysis-session.md`, `wiki/INDEX.md`, this plan and `plan/INDEX.md` | Record cache family guarantees, protocol and exact limits/evidence | Source/schema/link review |

Do not edit a broader AST or Boogie dependency to add generic serialization. If a
new exact source file is necessary, update this plan before editing it.

## Validation commands

From `/workspace/dafny-optimization`, first run affected Python client units after
I/O audit: `PYTHONDONTWRITEBYTECODE=1 PYTEST_ADDOPTS=--capture=sys python3 -m pytest
-q -n 0 -p no:cacheprovider python/tests/test_session.py` with correct local source
path. Do not run opt-in native process tests. Run scoped Ruff/typing as available.

Build edited LanguageServer/Core only as needed, then Driver/Test projects offline
and serially with `dotnet build <project> --no-restore --verbosity minimal
--disable-build-servers -m:1 -p:BuildProjectReferences=false`; test project also
`-p:SkipFocusedTestAssets=true`. Existing runtime/test-generation references are
retained; do not trigger blocked Gradle restoration/runtime work. Run only new
audited in-memory classes with `dotnet test ... --no-build --no-restore --filter
FullyQualifiedName~<new class> --verbosity minimal -m:1`. VSTest local socket may
need the approved execution path. Expected: inherited native entries reuse only
matching inputs; changed checksum/dependencies/options/includes miss; parent and
two children cancel/close independently. Source-only checks never count as native
proofs or performance evidence. No benchmark suites, live providers or paid work.

Run scoped `dotnet format whitespace . --folder --include <edited files>
--verify-no-changes --verbosity minimal` and `git diff --check`. Fresh independent
verification starts from requirements/current source. Scratch/logs/manifests belong
to `/workspace/tmp/native-session-cloning/`, never plan/wiki.

## Progress

Implementation in progress. User explicitly selected independent session state
with shared daemon processes. Parser audit found that cloning existing AST nodes
alone leaves tokens/options/attributes/includes/builtin-modifier captures shared.
Use branch-private template reconstruction from retained immutable source text
and URI instead of a generic graph clone. This costs one in-memory syntax parse
per inherited file at clone, then normal child cache hits apply; it performs no
resolve/analysis/verify command or filesystem read. Completed native results are
copied as detached success metadata with original native identity.

Fresh review found Boogie VerificationResultCache owns non-disposable private
MemoryCache timer owners; Clear alone cannot release a historical child's timer
resources. Adjust cache ownership before final acceptance: rent reset cache
instances exclusively from a process-local pool and return exactly once after a
drained owner's Dispose. Session disposal returns every retained cache; eviction
and clear reset only the owning wrapper's data. Native session VerifySnapshots=1
never uses CachedProgram/SetProgram (matching Boogie source guards at >1); this
session-specific wrapper rejects unsupported program-snapshot insertion rather
than retain unremovable parent program graphs. No private-field reflection or
Boogie package change. Tests must bound repeated clone/close native cache creation,
prove no cross-owner result leakage and exercise double disposal.

## Final implementation and evidence

Implemented 2026-11-05 on dirty base 0776df27c2449bad68e9a28e687bb6c70bf4b401.
Native/parser/client coding and fresh native/client reviews used separate
contexts; model settings are recorded in the parent plan. No dependencies or
commits were added. Root integration pins/gitlinks were not changed.

Native branch registry preserves the source branch and publishes only a complete
child clone receipt. Role context is separate from branch id. Close/cancel control
admission stays responsive at normal-job capacity; cancel targets must belong to
the same branch. Closing/cancelled branch cleanup remains owned until drained.
Compiler lock ordering is branch admission -> compiler gate -> branch preparation;
reader waits release compiler/preparation gates so unrelated branches can prepare.
Parser token checks reach each inherited template and the underlying parse.

Transferred native result data contains only original checksums/ids/dependency
bytes and detached scalar split/assertion shapes. Native inner Lookup is the sole
reuse authority; task rebasing validates shapes and installs current assertions.
Cache wrappers exclusively rent/reset/return native backing instances. Explicit
RemoveMatchingKeys clears results before reuse (native Clear/Trim alone can skip
a concurrent timer flush); disposed wrappers reject late operations and return
exactly once. The pool holds empty backing caches up to peak simultaneous owners;
it does not dispose sealed Boogie private timers. Program snapshot insertion is
unsupported under the existing forced VerifySnapshots=1 policy.

Client shared transport owns the daemon while independent branch handles own
generation/epoch/closure. Final owner alone shuts down/reaps. Fresh review found
that clone controls had consumed cancellation quota; corrected joint normal
job+clone admission and separate bounded cancel/close lanes, including writer
queue capacity and admission notifications. A fixture that returned success0
for cancelled/incomplete evidence was corrected to130, keeping the production
evidence guard unchanged.

Final Python checks, cwd owner root, Python3.12.3 with explicit native source path:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/dafny-optimization/python PYTEST_ADDOPTS=--capture=sys python3 -m pytest -q -n 0 -p no:cacheprovider -m 'not integration' python/tests/test_session.py
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/dafny-optimization/python PYTEST_ADDOPTS=--capture=sys python3 -m pytest -q -n 0 -p no:cacheprovider -m integration python/tests/test_session.py
python3 -m pyright --project /workspace/tmp/verifier-optimization-cosyn/pyrightconfig.json python/dafny_analysis/session.py python/tests/test_session.py
```

Results: 59 units passed/17 deselected; 17 fake integrations passed/59 deselected;
configured typing0errors/warnings and scoped Ruff/format pass. Plain Pyright
dependency discovery was unavailable and is not counted as a pass. Fresh client
review independently reran five affected integration controls and a stronger
saturation probe (full normal lane/eight close controls/ninth queued close), with
successful child cancel and unrelated clone/branch survival.

Final native commands from owner root, SDK8.0.133, VSTest17.8.0, serial/offline:

```sh
dotnet build Source/DafnyLanguageServer/DafnyLanguageServer.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false
dotnet build Source/DafnyDriver/DafnyDriver.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false
dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-restore --verbosity minimal --disable-build-servers -m:1 -p:BuildProjectReferences=false -p:SkipFocusedTestAssets=true
dotnet test Source/DafnyDriver.Test/DafnyDriver.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~AnalysisSessionCloneTests|FullyQualifiedName~NativeVerificationCacheTests|FullyQualifiedName~ParserCacheCloneTests' --verbosity minimal -m:1
```

Fresh LanguageServer build passed0warnings/errors (4.46s). Driver passed with seven
existing CS8632 warnings (6.25s); test build passed with one existing VSTHRD103
warning (5.50s). Existing core/runtime/test-generation dependencies were retained;
this is not a whole dependency rebuild. New API dependency builds were ordered
LanguageServer -> Driver -> Test; an earlier test compile against stale Driver
failed before this coordinated refresh. No runtime/Gradle/dependency restore ran.
Scoped dotnet whitespace verification and git diff checks pass.

Fresh independent native review executed the single final subset: 27 passed,
0 skipped, 704ms (session/protocol6, parser5, native-cache16). This uses actual
native parser and cache-lookup code, but fake solver completions; it demonstrates
copied native reuse with zero extra fake solver starts, exact checksum/dependency
misses, current child assertions and independent lifecycle. Source snapshots are
in memory; existing native toolchain identity reads six fixed producer assemblies
on first use. No recursive/runtime-tree hashing or tempdirs/sync/native subprocess
test bodies were run. Default sandbox VSTest required the approved local socket
execution path; earlier blocked attempts were not passes.

Intermediate failures corrected before final acceptance: parser's synthetic hash
fixture initially used too-short keys; native private Priority type was replaced
with the documented pinned native skip constant; native memory-cache timer owner
growth, preparation-gate waits and parser clone cancellation were independently
reviewed and repaired. Earlier22-case passes predate those fixes and are not final
evidence. No unresolved native/client review finding remains.

Temporary evidence: `/workspace/tmp/native-session-cloning/final-*.log`, parser
build/format logs and bounded source/task-diff manifests. Durable findings:
[independent native branches](../wiki/native-analysis-session.md#independent-native-branch-cache-cloning-2026-11-05).
This completes the requested local cache cloning scope. No real solver proof,
performance/benchmark, image publication, clean pinned install or process-crash
isolation is claimed; no paid/provider run or commit occurred.
