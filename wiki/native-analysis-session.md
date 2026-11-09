# Persistent native analysis and verification

Status: native source/local checks accepted; parent records artifact/image/runtime acceptance
Verified: 2026-11-03, editable developer source based on
0776df27c2449bad68e9a28e687bb6c70bf4b401, intentionally uncommitted.
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
replay while preserving same-state completed task reuse. Boogie's own cache
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
