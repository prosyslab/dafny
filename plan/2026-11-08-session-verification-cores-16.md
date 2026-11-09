# Fix analysis-session verification cores at 16

Status: in-progress
Date: 2026-11-08
Owner: native fork. Parent: `/workspace/plan/2026-11-08-verify-cores16-codex-cache.md`.

## Problem

`dafny analysis-session` forced `options.VcsCores = 1` and `BoogieOptionBag.Cores = 1` on every
request, so isolated batches ran serially.

## Change

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`, `SessionVerificationCores` | New constant 16, used for both `VcsCores` and `BoogieOptionBag.Cores`. One value serves agent goal checks, agent task scripts and grading. | DafnyDriver.Test `AnalysisSession` and `NativeVerificationCache`; B1 `StableSeed` and `ModularProofKey`; a Cat RenderData CPU-use and outcome comparison against 1 core |

No test or doc asserted 1 core, except the historical timing note in `wiki/native-analysis-session.md`
(a measured "one core" run), which stays as history.

## Non-goals

No change to proof keys, the cache, or seeds. Core count does not enter the cache key.

## Results

See the parent plan; filled in after the run.
- 2026-11-09: committed as "[Session] fix verification cores at 16" on branch `native-session-optimization`.
