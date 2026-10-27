# Provide one Python analysis client package in the native fork

Status: done
Date: 2026-10-27
Parent: [Move the Dafny evaluator to root and keep one analysis client](../../../plan/2026-10-27-evaluator-to-root.md) (Phase A)

## Objective and acceptance

Cosyn (`cosyn/src/dafny/analysis`) and Dafnyutils (`dafnyutils/src/analysis`) each
carry a diverged copy of the Python client for `dafny definition-analysis` and
`dafny source-fingerprint`. The native fork owns that wire format, so it also owns
one installable client. Phase A adds the package here; consumers switch in later
phases (not in this plan).

1. `python/dafny_analysis/` (installable through `python/pyproject.toml`, setuptools,
   Python >= 3.11, runtime dependency `pydantic` only) provides every public symbol
   and behavior that a caller in Cosyn, Dafnyutils or the root package uses.
2. The package imports neither Cosyn nor Dafnyutils. Host process policy (executable
   name, environment, cancellation, process groups) enters through one injected
   command runner; library-warning policy enters through an explicit parameter.
3. Every difference between the two copies is resolved with recorded evidence
   (table below).
4. `python/tests/` passes with `python -m pytest -q python/tests` using in-memory JSON
   payloads and fake runners; an opt-in integration test runs the built native
   `definition-analysis` at the same commit.
5. Work stays on branch `analysis-package`; nothing is pushed.

## Non-goals

No change to native C# code, wire formats, Cosyn, Dafnyutils or root files. No
schema-versioning beyond what tests need, no evaluator or scoring change, no consumer
import switch, no pin bump (Phase A follow-up in the parent plan).

## Inspected evidence

- Cosyn copy: `cosyn/src/dafny/analysis/{client,kinds,models,queries,source_fingerprints}.py`
  (1151 lines), host imports `cosyn.dafny.cli`, `cosyn.dafny.standard_library`,
  `cosyn.shared.utils.SHA256`. Dafnyutils copy: `dafnyutils/src/analysis/*` (816 lines),
  host imports `dafny_cli`, `standard_library`. All five files differ.
- Callers (`grep` over `cosyn/src`, `dafnyutils/src`, `/workspace/src`, scripts, and both
  test trees): Cosyn imports models (`DafnyAnalysisResult`, `DefinitionInfo`,
  `DafnyProject`, `DafnyProofInputs`, `DafnyFingerprint*`, `DefinitionAnalysis*`,
  `DafnyDefinitionSemanticFingerprint`), `DefinitionKind`, queries
  (`definition_semantic_fingerprint`, `source_semantic_fingerprint`,
  `source_byte_span_text`, `definition_text`, `normalized_signature`), client
  (`definition_analysis_{document,details,infos}_from_paths`,
  `definition_analysis_infos_from_stdin`, the error classes,
  `DefinitionAnalysisDetails`) and `dafny_source_fingerprints`. Dafnyutils imports
  `DefinitionAnalysisDocument`, `DefinitionSourceFacts`, `DefinitionVerificationTarget`,
  `definition_analysis_document_from_paths(include_verification_facts=True)`,
  `spec_dependency_closure`, `definition_dependency_closure`,
  `dafny_source_fingerprints`. The root package imports no analysis module directly.
- Native contract at `cb1a6437f` (`Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs`,
  `Source/DafnyCore/DefinitionAnalysis*.cs`): the options `--spans-only`,
  `--include-source-facts`, `--include-semantic-facts`, `--include-verification-facts`,
  `--include-proof-inputs`, `--include-statements`; `--stdin` reads the source from
  standard input and reports `sourcePath` `"/"` (observed with the build at
  `/workspace/cosyn/_build/dafny`, version `4.11.1+cb1a6437f`); semantic facts require a
  file source (stdin fails with exit 6); `SourcePath()` yields `""` only for nodes
  without a filename; hashes are lowercase hexadecimal.

## Design

- Modules mirror the old layout: `kinds`, `models`, `queries`, `client`,
  `source_fingerprints`, plus `runner` (the injected-process contract).
- `DafnyInvocation` (dataclass) carries the arguments after the executable, `cwd`,
  operation label, optional stdin text, timeout, optional cancellation event and optional
  environment. `DafnyCommandRunner` is a `Protocol` `(DafnyInvocation) -> CompletedProcess[str]`.
  The consumer builds `[its_dafny_command(), *invocation.arguments]` and calls its own
  process helper, so Cosyn keeps process-group cancellation and Dafnyutils keeps
  `TMPDIR=/tmp`. Contract: on timeout the runner raises `RuntimeError` caused by
  `subprocess.TimeoutExpired` (both hosts already do), which the client turns into
  `DefinitionAnalysisTimeout`; other exceptions (for example cancellation) propagate.
- The client is a set of module functions taking a required keyword `runner`. Consumers
  bind it once with `functools.partial`, so callbacks such as `DefinitionAnalyzer`
  keep their signature. No global configuration.
- Moved into the package: `DAFNY_STANDARD_LIBRARY_OPTION` (`--standard-libraries:false`),
  `DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC` (300, equal to both hosts' tool timeout),
  `SHA256` (same pattern as Cosyn's alias), `has_dafny_warning`. Taken as a parameter:
  `expected_warning_filter` (the Cosyn `bench/core` raw-library warning filter used only
  with `proof_input_options`; default keeps every warning). Dropped: the
  `is_allowed_dafny_standard_library_symbol` call (constant `False` in both hosts, so
  the branch never ran).

## Difference table

Legend: C = Cosyn copy, D = Dafnyutils copy.

| Symbol | C | D | Merged decision | Reason / evidence |
| --- | --- | --- | --- | --- |
| Path-bearing model fields (`source_path`, `target_path`, `resolved_target_source_path`, `included_files`) | `Path`, strict (Python mode requires `Path`; JSON accepts strings) | `StrictStr` | `Path`, strict (C) | Cosyn's tests pin strict `Path` (`test_path_models.py`) and Cosyn code compares and resolves `Path`; D mostly wraps with `Path(...)` but also compares `source_path` to `str(...)` and builds models from strings. Those D call sites must pass and compare `Path` when they switch. |
| `DefinitionInfo.source_path` empty value | rejected (`field_validator`) | accepted, default `""` | reject (C) | Native emits `""` only for nodes without a filename; stdin yields `"/"`. Rejecting avoids `Path("")` becoming the current directory. D's empty-path fallback and "omitted source path" check become unreachable. |
| `DafnyFingerprintResult.sha256`, `DafnySourceSemanticFingerprint.*sha256`, `DafnyDefinitionSemanticFingerprint.*sha256`, `DafnyProofInputs.*sha256` | `SHA256` (64 lowercase hex) | `StrictStr` | `SHA256` (C) | Native emits `ToLowerInvariant()` hex (`DefinitionAnalysis.ProofInputs.cs:192,256`); integration test validates real output. |
| `DafnyProject` / `DefinitionSourceFacts` | has `proof_inputs` | lacks it | `DafnyProject` with `proof_inputs`; alias `DefinitionSourceFacts = DafnyProject` | `proofInputs` is a native optional field (`--include-proof-inputs`); extra=forbid in D would reject it. Alias keeps D names until switch. |
| `DafnyAnalysisResult` / `DefinitionAnalysisDocument` | `DafnyAnalysisResult` | `DefinitionAnalysisDocument` | `DafnyAnalysisResult`; alias `DefinitionAnalysisDocument = DafnyAnalysisResult` | Same fields (`definitions`, `sourceFacts`); the C name is imported throughout Cosyn. |
| `DafnyDefinitions` / `StructuredDefinitionInfo` | `DafnyDefinitions` | `StructuredDefinitionInfo` | `DafnyDefinitions` | Same required-field set; D name has no caller outside its module. |
| `DefinitionSourceSpan` vs `DafnyFingerprintSpan` for `children`/`sourceGroup` | `DefinitionSourceSpan` | `DafnyFingerprintSpan` | `DefinitionSourceSpan` (C) | Same two strict ints; separate type keeps fingerprint request spans distinct from analysis output. |
| `DefinitionAnalysisModule` field order | `start,end,bodyStart,bodyEnd` | `bodyStart,bodyEnd,start,end` | C order | Order is not observable on the wire. |
| `DefinitionVerificationTarget` | docstring only differs | | C | Identical fields. |
| `DafnyDefinitionProofInput`, `DafnyProofInputs` | present | absent | keep (C) | Used by Cosyn proof reuse (`DafnyProofInputs` import). |
| `DefinitionInfo` remaining fields, defaults and aliases | same | same | unchanged | Field-by-field diff shows no other difference. |
| `DefinitionKind` | same 20 members | same | unchanged | Docstring wording only. |
| `DefinitionAnalysisError`, `...Timeout`, `...ProcessError` (`operational`), `...ProtocolError` | present | absent (plain `RuntimeError`) | keep (C) | All are `RuntimeError` subclasses, so D `except RuntimeError` handlers still apply. |
| `DefinitionAnalysisDetails`, `definition_analysis_details_from_paths` | present (`env`, `cancel_event`, `proof_input_*`, `cwd`, `include_verification_facts`) | absent | keep (C) | Used by Cosyn proof reuse/shared proofs. |
| `definition_analysis_document_from_paths` parameters | `timeout_seconds`, `include_semantic_facts`, `cancel_event`, `proof_input_options`, `proof_input_allow_warnings`, `cwd` | `timeout_seconds`, `include_semantic_facts`, `include_verification_facts` | union | D passes `include_verification_facts=True` (entry contract); C lacked it on this function. |
| Omitted verification facts when requested | not checked | `RuntimeError` | raise `DefinitionAnalysisError` | D behavior; strictly safer, still a `RuntimeError`. |
| Omitted semantic facts when requested | `DefinitionAnalysisError` | `RuntimeError` | `DefinitionAnalysisError` | Subclass of D's type. |
| Output validation order | validate JSON, then fill call text on models | `json.loads`, patch dicts, then validate | validate, then fill (C) | Pydantic errors become `DefinitionAnalysisProtocolError`; D's raw `JSONDecodeError`/`ValidationError` were unhandled. |
| Call-text source lookup | exact `Path` key, then read file | string key, empty-path fallback, then read file | exact `Path` key, then read file (C) | Empty source path is rejected by the model, so D's fallback is unreachable. |
| `definition_analysis_infos_from_stdin` | keys text by emitted path | keys text by `<stdin>` | emitted path (C) | Native reports `"/"` for stdin; D's `<stdin>` key never matched. Covered by an in-memory test. |
| Process execution (`run_dafny_command`, `dafny_command()`, env) | `dafny` from PATH, process-group cancel, optional env | `DAFNY_BENCHMARK`/`dafny-benchmark`, `TMPDIR=/tmp` | injected `DafnyCommandRunner` | Each host keeps its process policy. |
| Timeout translation | `RuntimeError` caused by `TimeoutExpired` becomes `DefinitionAnalysisTimeout` | plain `RuntimeError` | translate (C) | Runner contract above. |
| `DAFNY_TOOL_TIMEOUT_SEC` | 300 | 300 | `DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC = 300` in the package | Equal values; hosts keep their own constant for other tools. |
| `spec_dependency_closure` callable kinds | 4 kinds | 6 kinds (adds `least predicate`, `greatest predicate`) | 6 kinds (D) | C has no caller; D accepts them for benchmark specifications; both kinds are native `DefinitionKind` values. |
| `spec_dependency_closure` ordering | sort key `(as_posix, name)` | sort key `(str, name)` | `(as_posix, name)` | Equivalent for resolved absolute paths. |
| `definition_dependency_closure` (`boundary_symbols`) | absent (closure inlined) | present | present (D) | Used by D entry contract. |
| `is_allowed_dafny_standard_library_symbol` in closure | called (constant `False`) | called (constant `False`) | not called | Never true in either host; no parameter added for a feature nobody uses. |
| `source_semantic_fingerprint`, `definition_semantic_fingerprint` | `Path.resolve()` | `Path(str).resolve()` | `Path.resolve()` | Follows the path type decision. |
| `dafny_source_fingerprints` | `mode="json"` dump, `SHA256` result | plain dump, `str` result | `mode="json"` (needed for `Path`), `SHA256` | Same request file; same completeness check. |
| `without_expected_dafny_library_warnings`, `has_dafny_warning` | host module, bench-core specific | `without_expected_library_warnings(libraries)` | `has_dafny_warning` moved; filter injected as `expected_warning_filter` | Library layout is a benchmark/host policy. |
| `definition_analysis_infos_from_path`, `definition_analysis_infos`, `span_definitions` | present | absent | dropped | No caller in `cosyn/src`, `dafnyutils/src`, root `src`, scripts or tests; they only wrapped the retained functions or created temporary files. |
| `callable_spec_definitions`, `definitions_in_enclosing_name`, `definitions_by_full_name`, `definition_dependency_map`, `reachable_definition_names`, `datatype_definitions`, `constant_definitions`, `definition_map`, `implementation_declaration_violation` | present | absent | dropped | No caller anywhere (grep over all three source trees, tests and scripts). |
| `definition_text`, `source_byte_span_text`, `normalized_signature` | present | absent | keep (C) | Used by Cosyn bottom-up and top-down code. |

## Validation plan

Local only, no provider calls, serial. From `/workspace/dafny`:
`python -m pytest -q python/tests` in a venv that inherits system site packages and
installs the package editable (`pip install --no-build-isolation -e python`); then the
opt-in integration test with `DAFNY_ANALYSIS_NATIVE` pointing to the native executable
built at `cb1a6437f` (`/workspace/cosyn/_build/dafny/Binaries/Dafny`; the fork's own
`Binaries/` is empty and a rebuild is not required) and `python -m pytest -q -m integration
python/tests`. Tests use in-memory JSON and fake runners; the only file read is one
checked-in read-only fixture. No temporary directories, no fsync. No scratch artifacts
are stored in `plan/` or `wiki/`; scratch lives in `/workspace/tmp/python-analysis-client/`.

## Results

Environment: Python 3.12.3 (the only interpreter available), pydantic 2.13.5 and pytest
9.1.1 from the system site packages, ruff 0.15.x and pyright from `/usr/local/bin`.
`python3 -m venv` cannot create a pip-enabled venv here (no `ensurepip`), so the venv
`/workspace/tmp/python-analysis-client/venv` was made with `--without-pip
--system-site-packages` and the package was installed with
`/usr/bin/pip --python <venv>/bin/python install --no-build-isolation --no-deps -e python`
(nothing went into system site-packages).

- `python -m pytest -q python/tests` (from `/workspace/dafny`, venv interpreter): 65 passed,
  4 deselected (integration).
- `DAFNY_ANALYSIS_NATIVE=/workspace/cosyn/_build/dafny/Binaries/Dafny python -m pytest -q
  -m integration python/tests`: 4 passed in 4.4 s. That executable reports
  `4.11.1+cb1a6437f23cca667f007d3284c23b925e01c96d`, the commit of this branch's base; the
  fork's own `Binaries/` is empty and no native rebuild was needed. Without the variable
  the 4 tests skip. They cover stdin definitions, stdin span-only definitions, the full
  document with semantic and verification facts and queries over it, and proof inputs.
- `ruff check`/`ruff format --check` and `pyright` (standard mode) from `python/`: clean.
- Manual probe (scratch, not committed): `dafny_source_fingerprints` with a real native
  runner returned digests for a whole-file and a partial region; the whole-file digest equals
  the native `fullSha256` of the same file. No committed fingerprint integration test: the
  command only reads a request file and the client writes that file with
  `NamedTemporaryFile`, which the test I/O policy does not allow in tests. Only the response
  validation and empty-request paths are unit-tested.
- Not verified: Python 3.11 (interpreter unavailable), pydantic below 2.13.5 (the
  `>=2.7,<3` range is a declared lower bound, not a tested one), consumer test suites
  (consumers are not switched in this plan).

## Open items for the consumer phases

- Hosts must supply a `DafnyCommandRunner`; consumer tests that monkeypatched the private
  `_run_definition_analysis` should inject a fake runner instead.
- Dafnyutils call sites and tests that pass string paths to analysis models or compare
  `source_path` with `str(...)` must use `Path`.
- Each host should assert that its own tool timeout equals
  `DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC` or pass `timeout_seconds` explicitly.
- Cosyn keeps its `bench/core` warning filter and passes it as `expected_warning_filter`.

## Progress

- 2026-10-27: branch `analysis-package` created from `cb1a6437f`; both copies diffed and
  the table above recorded before writing the package.
- 2026-10-27: package, tests and wiki page added in focused commits; all checks above pass.
  Documentation: [wiki/python-analysis-client.md](../wiki/python-analysis-client.md).
