# Raise the analysis-session response limit to 128 MiB

Status: done, local scope (user approved the small native fix on 2026-11-06)
Date: 2026-11-06
Parent: [Cat topdown single proof](../../plan/2026-11-06-cat-topdown-single-proof.md).

## Problem and evidence

The paid Cat trial's final gate failed with `Native session response exceeds the output
limit` at 16 MiB
(`/workspace/tmp/experiment/cat-topdown-single-proof/blocker-native-response-limit.json`).
A one-shot measurement of the evaluator-style `definition-analysis` over Cat plus the
`bench/core` reported scope is 24.3 MB of compact JSON
(`/workspace/tmp/response-size-probe/out-core.json`); Cat alone is 5.3 MB.

## Goals and pass criteria

- Response frames up to 128 MiB pass on both ends; larger ones are rejected cleanly
  (server: code 6 response with the existing message; client: `SessionProtocolError`).
  Nothing is truncated.
- The Cat plus `bench/core` analysis succeeds through the real session binary.

## Non-goals

- The request limit stays 8 MiB; the evidence shows requests are not the constraint
  (sources travel as snapshots well under 8 MiB).
- No streaming or chunked responses, no change to Cosyn, root or Dafnyutils.

## Existing code reviewed

- `AnalysisSessionCommand.ResponseLimit` (serialize, `GetByteCount`, replace by a code-6
  response) and `ReadBoundedLine` (request side only; request limit).
- `NativeSessionTransfer.CheckFrame`: the export payload must fit the import request frame
  (8 MiB, binding) and the export response frame (was 16 MiB). It derives the response
  bound from `ResponseLimit`.
- `python/dafny_analysis/session.py`: `MAX_RESPONSE_BYTES`, `_read_loop` reads with
  `readline(limit + 1)` on the binary pipe, so the buffer is bounded by the limit.
- Pre-existing off-by-one: the server accepts a line of exactly `ResponseLimit` bytes and
  then writes the newline, so the client's `readline(limit + 1)` check rejects it. The
  limit is meant to bound the JSON line, not the newline.

## Decisions

- Response limit: 128 MiB (`134217728`), in the server constant and the client constant.
  It covers the measured 24.3 MB with more than 5x headroom (more scope sources can be
  added) while bounding memory: the server holds the serialized string (UTF-16, about
  2x) and its UTF-8 byte count is computed without a second copy; the client reads one
  bounded line.
- Transfer semantics: the import request frame (8 MiB) remains the binding side. The
  response frame carries the same string escaped by the protocol options (at most 3x
  growth for quotes), so a payload that fits the request frame always fits 128 MiB.
  The response check in `CheckFrame` stays as a defensive bound and now takes an
  injectable `responseLimit` so a test can exercise it without huge allocations.
- `RunProtocol` gets an optional `responseLimit` (default `ResponseLimit`) as a test
  seam for the server boundary.
- Client frame bound excludes the newline: it reads at most `limit + 2` bytes and rejects
  a frame longer than `limit + 1` bytes or without a newline.

## Planned changes

| File / symbol | Change | Why | Test |
| --- | --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs` `ResponseLimit`, `RunProtocol` | 128 MiB; optional `responseLimit` parameter | evidence above; test seam | new protocol boundary test |
| `Source/DafnyDriver/Commands/NativeSessionTransfer.cs` `CheckFrame`, doc comment | optional `responseLimit`; comment no longer says sixteen MiB | coherent transfer bound | updated `FrameAccountingCoversBothFramesAndIsExactAtTheLimit` |
| `python/dafny_analysis/session.py` `MAX_RESPONSE_BYTES`, `_read_loop` | 128 MiB; newline excluded from the bound | same limit; fix off-by-one | new exact-limit and limit+1 tests |
| `Source/DafnyDriver.Test/AnalysisSessionCloneTests.cs`, `AnalysisSessionTransferTests.cs`, `python/tests/test_session.py` | boundary tests | no huge allocations (injected small limits) | below |
| `wiki/native-analysis-session.md` | update the frame limits | durable record | review |

Layers: native session protocol and Python client only.

## Verification (free, local)

From `/workspace/dafny-optimization`:
- `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~AnalysisSession|NativeVerificationCache|ParserCacheClone|CachedParser|NativeTaskEntry"`
- `python -m pytest python/tests` (client tests)
- `dotnet format whitespace Source/DafnyDriver.Test --verify-no-changes` and the same for `Source/DafnyDriver`
- Rebuild the binary into `/workspace/tmp/session-cache-retention/bin`, then run
  `/workspace/tmp/response-size-probe/probe.py` adapted to the session client with Cat plus
  `bench/core`; record the response size. No LLM calls, no Docker.

## Results

Run 2026-11-06 on branch `native-session-optimization` (uncommitted tree, HEAD unchanged):
- `dotnet test Source/DafnyDriver.Test --filter "AnalysisSession|NativeVerificationCache|ParserCacheClone|CachedParser|NativeTaskEntry"`: 159 passed, 0 failed, including the new
  `ProtocolRejectsOnlyResponsesAboveTheLimit` (injected 4096-byte limit: exactly at the limit passes, one byte more is code 6, then the protocol still serves) and the updated frame accounting test.
- `python -m pytest python/tests` (in `python/`): 151 passed, 24 deselected (opt-in native); new exact-limit and constant tests; `ruff check` and `ruff format --check` clean.
- `dotnet format whitespace --verify-no-changes` on `Source/DafnyDriver` and `Source/DafnyDriver.Test`: clean.
- Rebuild: `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q`: 0 errors, version 4.11.1+650e6db3d8249d41e6f6f189a840920ab9e76963 (dirty tree).
- Real session (`/workspace/tmp/response-size-probe/session_probe.py`, `NativeDafnySession` with that binary, 16 Cat plus `bench/core` sources as roots and reported scope, `--include-verification-facts`): succeeded in 10.6 s, 1115 definitions; the response frame was 25,003,273 bytes (23.8 MiB, above the old 16 MiB limit, 19% of the new one). Temporary output location: `/workspace/tmp/response-size-probe/`.
- Not run: paid or Docker runs; the full native suite.

Found and fixed: the client rejected a frame of exactly `limit` bytes because the newline counted against the bound while the server's bound excludes it.

Memory: the client reads one bounded line (`readline(limit + 2)`, no preallocation); the server holds one serialized string per reply and replaces an oversize reply with a short code-6 response. No truncation anywhere.

Durable finding: recorded in `wiki/native-analysis-session.md` (frame limits).
