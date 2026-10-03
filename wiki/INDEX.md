# Implementation knowledge

2026-10-03: [legacy fixed-input removal](contract-testing.md#legacy-fixed-input-removal-2026-10-03-implementation-checks) leaves `test-contracts --runtime-check` as the only mode; fixed-input, generation and symbolic sections are marked STALE. Implementation checks only, independent verification pending.

2026-10-02: [static runtime library](contract-testing.md#static-runtime-library-2026-10-02-implementation-checks) moves the PBT Dafny/C# runtime text into checked-in, ahead-of-time-checked files with pinned byte identity; implementation checks only, independent review pending.

2026-10-01: [invocation-bound callee heaps, successful fact reuse and profiles](contract-testing.md#invocation-bound-callee-heaps-fact-reuse-and-profiles-2026-10-01) pass independent native49/Driver16 plus corrective10/5 and artifact13 controls. Original P/type/WD/frame/dependency and finite-prefix gates remain; root all15/six logical cases/seven exact replays and package closure are independently accepted.

2026-09-29 heap construction: [recursive and nested heap construction](contract-testing.md#recursive-and-nested-heap-construction-2026-09-29) accepts `object`-typed representation sets and cyclic fixed-state heaps, and nested `pbt_heap_constructor` paths with default object allocation; M2 cat with a one-annotation generator matches the existing generator.

2026-09-29 sequential stage4: [runtime classification deadline boundaries](contract-testing.md#runtime-classification-deadline-boundaries-2026-09-29) independently pass23 Driver controls, h11 deadline/result audit and exact h13 sentinel replay. h11 returns a result while expired initial states remain unchecked; goal coverage limits remain.

2026-09-29 sequential stage3b: [ordered runtime check fragments](contract-testing.md#ordered-runtime-check-fragments-2026-09-29) independently pass22 controls and6 raw byte-prefix comparisons. Exact h11 runtime ordinals complete under5s; campaign/proof outcomes remain separate.

2026-09-29 sequential stage3a: [exact native membership proof reuse](contract-testing.md#exact-native-membership-proof-reuse-2026-09-29) independently passes21 campaign controls, raw artifact audit and cancellation-during-hit control. State admission remains separate from reusable pure proofs.

2026-09-29 sequential stage2: [captured ghost goal heap observations](contract-testing.md#captured-ghost-goal-heap-observations-2026-09-29) independently pass native133/Driver12. Actual h15 return capture is available; its original dependency proof still blocks Q. At this historical stage per-callee capture was unsupported; the bounded 2026-10-01 extension above supersedes that limitation.

2026-09-29 bounded follow-up: [captured ghost inputs and closed-clause names](contract-testing.md#captured-ghost-inputs-and-closed-clause-names-2026-09-29) and quantified heap reduction boundaries pass fresh independent44 native/42 Core/7 Driver/12 final type checks. Historical reruns are complete with no additional counterexamples; general existential support and full M2 acceptance remain open.

| Page | Status | Verified | Scope |
| --- | --- | --- | --- |
| [Contract testing](contract-testing.md) | bounded entry heap implementation independently verified | 2026-09-27 | Diagnostic source, partial logical heaps, fixed/runtime query boundaries; TestGeneration313/313, Driver168/168 and ten independent raw probes pass. Original contracts and conservative omitted-state support remain intact. Root r5 M1 detection6/6 and spurious0/5 are historical; new r6 populations pending, public M2 probe06 valid0 |

Current development extension: [runtime query optimization](contract-testing.md#runtime-query-optimization-2026-09-28-development), 2026-09-28. Native construction/cancellation15/15 and Driver admission/cache12/12 pass; subsequent compiled-membership provenance/construction29/29 and actual Driver8/8 pass; frozen all-four/full64 acceptance and independent review remain pending. See the [owner plan](../plan/2026-09-27-runtime-query-optimization.md).

Latest development: frozen11 recording preserves18 complete traces byte-for-byte;
sequence checked-step focus passes61+9 native cases and7 Driver cases. Original
CatSpec passes7.128s after actual initial certificates reuse its frontend, while
cold checks still exceed10s. Logical/execution roles are now separated with
98/98 native-focused and14/14 Driver checks; original CoreSummary campaign,
all-four detection and final suites remain pending. This is implementation-owned
evidence, not independent review.

Latest development checks: pre-final-guard complete Contract suites pass451/451
TestGeneration and188/188 Driver; final admission/query-visibility focus passes
10/10 native and7/7 Driver. Final-source complete suites and frozen M1/M2 probes
remain pending; these results do not establish all-four/full64 acceptance.

M1 compatibility follow-up: independent source-bound global certificates and
input-only initial preparation pass native focus10/10 and Driver13/13, including
20 distinct structured inputs with one source proof under a three-query limit.
Successor public64-sample probes and final complete suites are pending.

Final bounded follow-up: same-sample prepared-state reuse retains exact request,
source and checker binding; confirmed hidden initializer dependencies now fail
closed. Native145/145 plus four visibility controls and Driver13/13 pass. Frozen10
timings/full suites/populations and unresolved original CoreSummary detection are
still pending.

Final-source update (2026-09-28): supported package10 and complete Contract suites
pass486/486 TestGeneration and195/195 Driver, no skips; Cosyn transport4/4 passes.
Frozen10 full64 M1 probes retain64valid/63violating and64valid/33violating with
measured reuse savings, still slower than r6. One-sample M2 stdin detects; exit
remains CoreSummary-unchecked. Actual r7-dev populations are underway and fresh
independent review remains unavailable. The owner plan stays in-progress;
logical/by-method certificate separation is design-only and HelpTextSpec's
original result-type proof remains an unresolved blocker.

Full r7-dev M1 now completes36 rows/12 variants:6/6 mutant detection,0/5 spurious
reports,704 valid samples and zero errors/unchecked/timeouts. Wall1441.192s
regresses versus r6's670.248s. Root mechanical audit2754 checks/117 summary fields
passes; it is not independent verification. Full M2 is running; the plan remains
in-progress with all-four acceptance and fresh review pending.

Full frozen10 M2 completes24 rows/eight variants:3/4 detection,0/4 spurious,
159valid/54violating and eight sample timeouts;159 CoreSummary clause evaluations
remain unchecked. Root mechanical audit2582/117 passes, not independently reviewed.
Recording-only draft build and focused9+13 tests pass; successor measurements and
final-source full suites remain pending. Sequence proof steps are planned only;
all-four detection remains unmet.

Recording-only handoff: build and focused9+13+4 cases pass; format/diff clean.
Exact33-file source manifest preserves all frozen10 source hashes except the two
planned production files and new recording test file. Root owns freeze11 timing
and record-conservation checks; no successor speedup/full-suite result is claimed.

State-aware reduction follow-up: frozen12 logical/observed certificates pass but
negative CoreSummary proof times out. First bounded heap-aware reducer and native
checked equivalence are implemented; Core98/98, native141/141 and Driver15/15 focus
pass. Frozen13 residual/timing evidence, final full suites and independent review
remain pending; all-four M2 detection is not complete.

2026-09-29 development: frozen13 actual iff failure is reproduced in a generic
unbounded-existential fixture. Resolved import scope is corrected; heap-aware
finite-domain unrolling now preserves unknown quantified bodies/ranges/triggers.
[Boundary and evidence](contract-testing.md#checked-heap-equivalence-boundary-2026-09-29-development);
owner Core100/100 and native157/157 pass; Q28 checked iff succeeds with original
target nonproof, Q29 remains timeout. Final root validation, broader existential
support and all-four detection remain open.

2026-09-29 continued optimization: [exact reduction and finite-prefix counterexamples](contract-testing.md#exact-reduction-and-finite-prefix-counterexamples-2026-09-29). Fresh v3 independent Driver32/Core62/query83 and v4 Core33/query21/Driver14 scopes pass; six-case execution and representative replay are complete, with remaining historical coverage limits recorded separately in the parent plan.

2026-09-29 sequential stage1: [ordered native proof composition](contract-testing.md#ordered-native-proof-composition-2026-09-29) passes independent Core93/query87 and retained h07 gates under unchanged budgets. Ordinary reduction stays unchanged; certificates publish atomically on success, and negated/unknown-length sequence coverage limits remain explicit. The later goal heap/ghost and runtime stages are recorded separately above.
