# One Python client for native Dafny analysis

Status: current; checked 2026-10-27 on branch `analysis-package` (base `cb1a6437f`). Originating plan: [Python analysis client](../plan/2026-10-27-python-analysis-client.md).

`python/dafny_analysis` is the single Python client for `dafny definition-analysis` and `dafny source-fingerprint`; it replaces the diverged copies in Cosyn and Dafnyutils. It depends only on pydantic and imports no consumer code. Install with `pip install -e python` (Python >= 3.11); run unit tests with `python -m pytest -q python/tests`, and the opt-in native checks with `DAFNY_ANALYSIS_NATIVE=<Binaries/Dafny> python -m pytest -q -m integration python/tests`.

Modules: `models` (strict camel-case wire models; paths decode to `Path`, hashes are lowercase SHA-256, unknown fields are rejected), `kinds` (`DefinitionKind`), `queries` (fingerprint lookup, specification/definition dependency closures, byte-span helpers), `client` (analysis entry points and typed errors), `source_fingerprints`, `runner` (the process boundary). `DefinitionAnalysisDocument` and `DefinitionSourceFacts` remain as aliases of `DafnyAnalysisResult` and `DafnyProject` for former Dafnyutils callers.

Process boundary: every client function takes a keyword-only `runner`, a `DafnyCommandRunner` called with a `DafnyInvocation` (arguments after the executable, `cwd`, operation label, timeout, optional stdin text, cancellation event and environment). The host prepends its own Dafny command and applies its own process policy. On timeout the runner raises `RuntimeError` caused by `subprocess.TimeoutExpired`, which becomes `DefinitionAnalysisTimeout`; other exceptions propagate; a non-zero exit is returned and becomes `DefinitionAnalysisProcessError` (`operational` for signals and exit codes >= 6). The Cosyn raw-library warning filter used with proof inputs is passed as `expected_warning_filter(stderr, cwd)`; without it every warning drops the proof inputs.

```python
from functools import partial
from dafny_analysis.client import definition_analysis_document_from_paths

analyze = partial(definition_analysis_document_from_paths, runner=my_runner)
document = analyze([Path("Spec.dfy")], include_verification_facts=True)
```

Limits: the fingerprint request still goes through a temporary file written by the client, so it has no committed native test; Python 3.11 and older pydantic releases are untested. The merge decisions per symbol are in the plan's difference table; the native wire contract is `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` and `Source/DafnyCore/DefinitionAnalysis*.cs`.
