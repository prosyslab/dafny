# Separate the compilation input from the reported analysis scope

Status: done (native source/local checks; no image, benchmark or paid run)
Date: 2026-11-04
Parent: [incremental analysis implementation](../../plan/2026-11-04-incremental-analysis-implementation.md)
Design: [Korean design](../../docs/incremental-definition-analysis.ko.md)

## Problem

In the saved Cat reproduction (`/workspace/tmp/experiment/cat-verifier-regression-profile/paired-04/v7/b01-full/unchanged.json`),
the `candidate-verification` session receives identical options and identical
sources, but the root list alternates between `Cat.dfy` and six reachable files.
The session keys its single `State` on the root list, so each alternation
discards the compilation and repeats translation (18–20 s each, 56.3 s total).
`DefinitionAnalysis.SessionCache.Begin` also clears all module facts when the
reported source set changes, so every request reports 0/22 module hits.
The saved 1-root and 6-root documents have identical stderr and identical proof
inputs (72/72 equal hashes); only the reported source-fact scope differs.

## Goals and pass criteria

1. A definition-analysis request can name the reported sources separately from
   the compilation roots (`--analysis-source`). Roots, includes and libraries,
   and therefore the verification scope, stay those of the compilation.
2. In the session, changing only the reported scope reuses the same native
   State (no new compilation or translation).
3. Module facts are cached per analysis profile (reported scope plus
   statements flag), so alternating profiles hit both; a request never mixes
   node objects of two profiles.
4. Reported output for a selection equals the output of a compilation that lists
   the same files as roots, apart from the documented diagnostic limit below.
5. Invalid selections are rejected with a clear error instead of returning a
   partial or differently-scoped document.

Selection rules: the selection must contain every analyzed (non-library) root;
every selected file must be a parsed `.dfy` source the compilation would verify
(`UrisToVerify`, so library-reachable files are excluded); and selecting a
non-root file together with proof inputs or verification facts requires
`--verify-included-files`, because otherwise root status changes which
declarations are translated. `--spans-only` does not accept a selection.

Known limit: the precedence (indentation) linter does not warn in included
files. A selection reports the diagnostics of the fixed compilation, so an
indentation warning that only appears when an included file is a root is not
reported. This matches the diagnostics of the verification that uses the same
roots.

Non-goals: declaration-level resolution, cross-compilation reuse of Boogie
translations or prepared tasks, changes to proof-input composition, result
cache policy, concurrency admission, or benchmark sources.

## Existing code reviewed

`AnalysisSessionCommand.Session.Execute` (state identity, facts, proof-input
preparation), `DefinitionAnalysisCommand.AnalysisSourceUris`,
`DefinitionAnalysis.AnalyzeDocument/Analyze/SourceDefinitions/LegacySourceFacts/ImportedModuleNames`,
`DefinitionAnalysis.ProofInputsFor` (uses `identitiesOnly`, so it does not depend
on the reported scope), `ShouldCompileOrVerify`, `ProgramParser.ParseFiles`,
`Compilation.DetermineRootFiles`, `PrecedenceLinter`, `CachingParser`,
`CachingResolver`, the Python client and the existing memory tests.

## Planned changes

| Files / symbols | Change and why | Test |
| --- | --- | --- |
| Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs: `AnalysisSources`, `SelectAnalysisSources`, `Execute` | New repeatable option; shared validation that returns the reported URI set or an error; one-shot uses it | Driver memory tests for parity and each rejection |
| Source/DafnyCore/AST/ShouldCompileOrVerify.cs: `UrisToVerify` | Expose the existing verified-URI computation for validation | Covered by selection tests |
| Source/DafnyCore/DefinitionAnalysis.cs: `ImportedModuleNames` | Dropped during implementation: its root check only feeds the unused legacy `SourceFacts.ImportedModules` list (per-definition imports come from structured facts), so the change had no output effect; reverted | Mutation run showed no output effect |
| Source/DafnyCore/DefinitionAnalysis.Session.cs: `SessionCache` | Bounded per-profile caches (4 profiles, LRU); dead modules pruned from every profile | Core memory tests: alternating profiles hit, results equal fresh analysis, edits still invalidate |
| Source/DafnyDriver/Commands/AnalysisSessionCommand.cs: `ParseOptions`, `Execute` | Remap selection paths through the logical root; use the selection for definition-analysis without touching the state key | Built-binary session check on public Cat sources |
| python/dafny_analysis/client.py: `definition_analysis_details_from_paths`; python/tests | Optional `analysis_sources` argument emitting `--analysis-source` | Python unit tests, Ruff, Pyright |
| wiki/native-analysis-session.md, wiki/INDEX.md, plan/INDEX.md | Record the scope separation, profile cache and limit | Markdown review |

## Commands

Working directory `/workspace/dafny-optimization`, dotnet 8.0.133. Free local checks only:

- `dotnet build Source/DafnyDriver/DafnyDriver.csproj -m:1 -v:q`
- `dotnet build Source/DafnyCore.Test/DafnyCore.Test.csproj -m:1 -v:q`, then
  `dotnet test ... --no-build --filter FullyQualifiedName~DefinitionAnalysisSessionTests|...`
- Same for `Source/DafnyDriver.Test` with the cached-parser and new selection tests.
- `dotnet format whitespace` verification on touched files.
- `python -m pytest python/tests -q`, `ruff check python`, `pyright python` (serial).
- Session timing on public Cat sources (read-only), outputs under
  `/workspace/tmp/incremental-analysis-scope/`.

No paid runs, image builds or benchmark experiments.

## Log

Tool versions: dotnet 8.0.133, Python 3.12, Z3 4.12.1 (`Binaries/z3/bin`).
Source: uncommitted worktree on 0776df27c2449bad68e9a28e687bb6c70bf4b401 with
pre-existing unrelated changes; this task only touched the files in the table.
Logs: `/workspace/tmp/incremental-analysis-scope/` (temporary).

- Driver/Core/test builds pass. The default test build output refreshed
  `Binaries/DafnyCore.dll`; the executable for real checks was built with
  `dotnet build Source/Dafny/Dafny.csproj -o /workspace/tmp/incremental-analysis-scope/bin`.
- Core focused tests 86/86 (two new profile tests); Driver focused tests 28/28
  (seven new selection tests); `dotnet format whitespace --verify-no-changes` on
  touched files passes.
- First selection parity attempt failed only because the in-memory test did not
  supply source snapshots for semantic facts; fixed in the test.
- Python client: `pytest tests` 104 passed (12 opt-in deselected), Ruff, Ruff
  format and Pyright clean.
- Real session check (`session_check.py`, public Cat sources read in place):
  run 1 found that `verify` requests raised a null reference in the new
  selection remap (option absent on `verify`), retiring the State; fixed with a
  guard. Run 2: cold 42.1 s, widened scope 0.48 s, verify 8.2 s (15 solver runs,
  same State), repeats 0.035 s and 0.195 s with 22/22 module hits, expanded-root
  form 33.2 s; normalized documents, 119 keyed proof inputs and stderr equal.
- One-shot CLI: missing root and non-root proof inputs without
  `--verify-included-files` exit 1 with the expected messages; a structural
  selection reports both files.
- Independent Sonnet review (fresh context, requirements and repository only):
  no confirmed defects. Noted gaps: no xUnit test of session State reuse or
  logical-root remapping (covered only by the local session check above, which
  did not use a logical root), and possible symlink spelling mismatch because the
  client resolves paths while native compares `GetFullPath` URIs.

Result: done for the planned scope. Wiki updated in
[native-analysis-session](../wiki/native-analysis-session.md#reported-analysis-scope-2026-11-04).
Remaining work belongs to later stages: cross-compilation module translation
reuse and declaration-level resolution.
