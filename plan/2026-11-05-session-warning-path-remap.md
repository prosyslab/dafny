# Remap logical-root paths in native session warning text

Status: done (local source scope; independent review accepted 2026-11-05)
Date: 2026-11-05
Parent: [goal-owned native sessions](../../cosyn/plan/2026-11-04-goal-owned-native-sessions.md).
Related: [native analysis session](2026-11-02-native-analysis-session.md),
[session cache retention](2026-11-04-session-cache-retention.md),
[wiki](../wiki/native-analysis-session.md).
Evidence: lab note `/workspace/lab-notebook/2026-11-05/goal-owned-native-smoke.md`
(finding F1); outputs `/workspace/tmp/experiment/goal-owned-native-smoke-20261105/out/`
(`s2/run.log`, `s3/result.json`, `s4/result.json`), temporary.

## Problem and evidence

A host may bind a snapshot with `source_root != logical_root` (stable logical URIs,
immutable physical snapshot directory). The session parses logical paths, so the
warning `CLI: Warning: The file '<logical path>' was passed to --library. ...` shows
the logical root. The one-shot CLI, run in the physical directory, shows the physical
path, and the Cosyn warning filter (`without_expected_dafny_library_warnings`) accepts
only paths under the physical workspace. Result in the smoke: every lease proof-input
analysis raised `NativeProofInputWarning` (27 logical-root mentions per case, 0
physical).

Root cause. The message text is built where the file is opened:
`DafnyFile.CreateAndValidate` (`Source/DafnyCore/DafnyFile.cs:154`) formats
`options.GetPrintPath(uri.LocalPath)` into a `DafnyDiagnostic` (error id
`UnverifiedLibrary`, `MessageParts = [path]`) and queues it in the resolved
compilation's diagnostics. `AnalysisSessionCommand.Session.Execute` replays queued
diagnostics through `cli.ReportDiagnostic` unchanged. Only the verification logger
(`RemapOutputPath`), the Python JSON remap (`_remap_analysis`, keys
`sourcePath` and similar) and the request parser (`Logical`) knew the two roots.

Why not remap at production. A `State` is reused across requests whose
`source_root` differs (same logical URIs, same bytes, different immutable snapshot
directory). The message would carry the physical root of the request that built the
State. The mapping must therefore be applied per request when diagnostics are
replayed, which is also where the per-request writers are bound.

Other places the session emits text with logical paths (inspected in
`AnalysisSessionCommand.cs`, `DefinitionAnalysisCommand.cs`, `DafnyFile.cs`,
`DooFile.cs`, `TranslationRecord.cs`):

| Producer | Text | Status before |
| --- | --- | --- |
| `DafnyFile.CreateAndValidate` library warning (`UnverifiedLibrary`) | path in message part | logical (bug) |
| `DafnyFile` "file X not found" (include, library, doo) | path interpolated into the format string | logical (bug) |
| `DooFile`/`TranslationRecord` "cannot load X", "malformed doo" | path in message | logical; doo libraries are unsupported by the session (`.dfy` only), same path as above if reached |
| `SelectAnalysisSources` errors (`--analysis-source X ...`, `X is missing`) written to request stderr | `LocalPath` of logical URIs | logical (bug) |
| Diagnostic location prefix `path(line,col)` | token path made relative to the process cwd | not changed, see limits |
| `ParseOptions` command-line errors | echo of the host's own argument text | host-supplied argv, not a logical-root mapping problem |
| Verification loggers (json, trx, text) | `RemapOutputPath` | already remapped |
| Native exceptions from file reads | `ActualPath` (physical) | already physical |

All three commands (resolve, definition-analysis, verify) replay diagnostics through
the same code path (two `ReportDiagnostic` loops in `Execute`), to the options'
`OutputWriter`/`ErrorWriter` that the request parser bound to the request's
captured stdout and stderr. Routing (proof-input analysis sends them to stderr) is
unchanged.

## Goals and pass criteria

- With `source_root != logical_root`, library warning lines in the captured stdout or
  stderr of resolve, definition-analysis (with and without proof inputs) and verify
  show the physical path, byte-equal to the one-shot text for the same files in the
  physical directory.
- `--analysis-source` rejection messages show physical paths.
- Without roots, or with equal roots, output is unchanged; one-shot code paths are
  unchanged.
- A State built for one `source_root` and reused for another prints the second
  request's physical root.

## Non-goals

- Remapping diagnostic location prefixes (they are relative to the process cwd,
  which is host-chosen; changing that rule would alter the existing byte equality
  of `bench/...` lines with a one-shot run in the attempt directory).
- Python-side text remapping (the host passes through native text).
- Any change to one-shot `DafnyOptions.GetPrintPath`.

## Design

Remap structured message parts, not whole rendered text.
`DafnyDiagnostic.MessageParts` holds the format and arguments as separate strings, so
the library warning argument is exactly the path. A helper
`RemapDiagnostic(DafnyDiagnostic, Request)` in `AnalysisSessionCommand` returns a copy
whose parts have the logical root replaced by the physical root, with an exact prefix
rule at a path boundary (the root must start the part or follow a character that cannot
belong to a path, and must be followed by `/`, end of text or a non-path character).
This is `RemapPrefix` generalised to a root embedded in a message part, needed for
"file X not found" where the path is interpolated into the format string; it is not a
regex over rendered output. If a part is the format string, braces in the replacement
are escaped. Error id, range, level, source and related information are kept.
`RelatedInformation` messages are remapped the same way. The same text helper maps
`selectionError` before it is written to request stderr.

## Planned changes

| File / symbol | Change | Test |
| --- | --- | --- |
| `Source/DafnyDriver/Commands/AnalysisSessionCommand.cs`: new `RemapDiagnostic`, `RemapText` beside `RemapPrefix`; the two `cli.ReportDiagnostic` loops and the solver-reporter loop in `Session.Execute`; `selectionError` write | Apply logical to physical mapping per request | New Driver tests below |
| `Source/DafnyDriver.Test/AnalysisSessionPathRemapTests.cs` (new) | Supplied snapshots, `SourceRoot != LogicalRoot`, a `--library` file; resolve, definition-analysis, proof-inputs, verify; equals one-shot; State reuse with another source root; no-op when roots are absent or equal; `--analysis-source` rejection text; embedded not-found path | `dotnet test --filter AnalysisSession` |
| `wiki/native-analysis-session.md` | Replace the statement that only report paths and structured locations map; record warning text mapping and the location-prefix limit | link review |
| `plan/INDEX.md` | Register this plan at the top | |

Layers: native evaluator/session code only. No spec, proof, dataset, scoring or
reporting layer changes. No Cosyn edits (another agent works there).

## Validation

Free, local, serial (no LLM or provider calls, no Docker). Long runs in tmux.
- `cd /workspace/dafny-optimization && dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj -m:1 -v:q`
- `dotnet test Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSession"` and
  `FullyQualifiedName~AnalysisSourceSelection|CachedParser|NativeTaskEntry`
- `cd python && python3 -m pytest -q`
- `dotnet format whitespace Source/DafnyDriver/DafnyDriver.csproj --verify-no-changes --include <touched files>`
- Rebuild `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q`,
  record time and `Dafny --version`, then one real session check with `source_root !=
  logical_root` and `--library` (scratch `/workspace/tmp/session-warning-path-remap/`).

## Risks

- Replacing text in message parts could rewrite an unrelated string equal to the logical
  root. The boundary rule limits this to path-shaped occurrences, and these messages
  contain host-supplied paths only.
- A path containing braces in a format string: escaped on replacement.

## Progress and validation log

Implemented 2026-11-05. Tool versions: dotnet 8.0.133, Python 3.12, Dafny
4.11.1+0776df27 (dirty tree; other uncommitted work preserved, nothing reset, stashed or
committed). Change as planned, plus `RelatedInformation` and the solver-reporter loop and
the verification-diagnostic loop use the same helper. Design check: with the helper
bypassed (temporary env switch, reverted), 6 of the 16 new tests fail (all four
`LibraryWarningShowsPhysicalPath` cases, `ReusedStateReportsTheCurrentSourceRoot`,
`FormatStringPathsRemapWithoutBreakingFormatting`).

| Command (cwd `/workspace/dafny-optimization`) | Result |
| --- | --- |
| `dotnet build Source/DafnyDriver.Test/DafnyDriver.Test.csproj -m:1 -v:q` | 0 errors |
| `dotnet test Source/DafnyDriver.Test --no-build --filter "FullyQualifiedName~AnalysisSessionPathRemap"` | 16 passed, 0 failed, 0 skipped |
| `dotnet test ... --filter "FullyQualifiedName~AnalysisSession\|AnalysisSourceSelection\|CachedParser\|NativeTaskEntry"` (tmux `warn-remap-tests`, log `/workspace/tmp/session-warning-path-remap/driver-tests.log`) | 59 passed, 0 failed, 0 skipped (includes the 16 new) |
| `cd python && python3 -m pytest -q` | 105 passed, 12 deselected (opt-in native) |
| `dotnet format whitespace ... --verify-no-changes --include` on `AnalysisSessionCommand.cs` and `AnalysisSessionPathRemapTests.cs` | exit 0 both |
| `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/session-cache-retention/bin -m:1 -v:q` (tmux `warn-remap-build`) | 0 errors, 27 s (2026-11-05T01:16:06Z to 01:16:33Z), `Dafny --version` 4.11.1+0776df27c2449bad68e9a28e687bb6c70bf4b401 (dirty tree) |
| Real session check `/workspace/tmp/session-warning-path-remap/real/check.py` (log `check.log`) | `NativeDafnySession` with `logical_root` = session cwd and `source_root` = another directory, `--library lib/Lib.dfy`: resolve, definition-analysis and verify print `The file '<physical>/lib/Lib.dfy' was passed to --library`, 0 logical-root mentions in the warnings (return code 2 on all three, because the library warning fails without `--allow-warnings`, as in one-shot verify) |

Observations kept out of scope:
- One-shot `resolve` prints no library warning and returns 0, while the session prints it
  and returns 2 (lab note F3). The new tests compare text and return code with one-shot
  only for definition-analysis and verify.
- JSON documents keep logical paths natively; `_remap_analysis` in the Python client maps
  them. Message text is now mapped natively.
- Diagnostic location prefixes `path(line,col)` use the token path relative to the process
  cwd and stay as before (see Non-goals).

Skips: no Core tests (Core untouched), no Cosyn tests (not edited), no Docker, no LLM or
provider calls, no independent verification agent (small change; not requested).

## Independent review and close (2026-11-05)

A fresh verifier (Sonnet, high effort) accepted the change.
- Binary built 10:16:33, after the last source edit at 10:13:33.
- Real-binary runs on public Cat copies, all Cosyn-shaped argv modes:
  - logical-root mentions: 0;
  - library warnings showed the request's physical root, including on a reused
    State with another root;
  - Cosyn's `without_expected_dafny_library_warnings` removed 9 of 9 and nothing else.
- Driver filters 59 passed (16 new), Python 105 passed, format clean.
- Test gaps: mutations removing the remap in the proof-input replay loop, in
  RelatedInformation, and in verify-result diagnostics survived (low).
- Session `resolve` printing library warnings is pre-existing and harmless:
  Cosyn always pairs `--library:bench/core` with `--allow-warnings`.
- Pre-existing issue found, not fixed here: error source snippets are read from
  the logical path on disk, not from the request's physical file. With a stale
  logical directory, a candidate diagnostic shows the logical file's line.
  Follow-up needed.

Evidence: `/workspace/tmp/session-warning-path-remap-review/out/` (temporary).
