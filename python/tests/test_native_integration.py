"""Opt-in checks of the schema against the built native Dafny executable.

Set ``DAFNY_ANALYSIS_NATIVE`` to the ``Binaries/Dafny`` built from the same commit and run
``python -m pytest -q -m integration python/tests``.  The tests read only checked-in
fixtures and stdin, and write no files.
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from subprocess import CompletedProcess

import pytest

from dafny_analysis.client import (
    definition_analysis_document_from_paths,
    definition_analysis_infos_from_stdin,
)
from dafny_analysis.kinds import DefinitionKind
from dafny_analysis.queries import definition_semantic_fingerprint, source_semantic_fingerprint
from dafny_analysis.runner import DafnyInvocation
from support import TOY_SOURCE

pytestmark = pytest.mark.integration

_NATIVE = os.environ.get("DAFNY_ANALYSIS_NATIVE", "")
_SOURCE = """function Id(x: int): int { x }
method M(x: int) returns (r: int)
  ensures r == Id(x)
{ r := x; }
"""


@pytest.fixture(scope="module")
def native_runner():
    """Return a runner that executes the native executable named by the environment."""

    if not _NATIVE or not Path(_NATIVE).is_file():
        pytest.skip("DAFNY_ANALYSIS_NATIVE does not name a built Dafny executable")

    def run(invocation: DafnyInvocation) -> CompletedProcess[str]:
        return subprocess.run(
            [_NATIVE, *invocation.arguments],
            cwd=invocation.cwd,
            input=invocation.source_text,
            text=True,
            capture_output=True,
            check=False,
            timeout=invocation.timeout_seconds,
        )

    return run


# Native stdin output validates against the strict schema and keeps call text.
def test_native_stdin_infos_validate(native_runner) -> None:
    definitions = definition_analysis_infos_from_stdin(
        _SOURCE, source_dir=TOY_SOURCE.parent, runner=native_runner
    )

    by_name = {definition.name: definition for definition in definitions}
    assert by_name["Id"].kind is DefinitionKind.FUNCTION
    assert by_name["M"].kind is DefinitionKind.METHOD
    assert by_name["M"].direct_postcondition_calls[0].text == "Id(x)"


# Native span-only stdin output validates against the same definition schema.
def test_native_stdin_spans_only_validate(native_runner) -> None:
    definitions = definition_analysis_infos_from_stdin(
        _SOURCE, source_dir=TOY_SOURCE.parent, runner=native_runner, spans_only=True
    )

    assert {definition.name for definition in definitions} == {"Id", "M"}


# The full native document, with semantic and verification facts, validates and is queryable.
def test_native_document_with_all_facts_validates(native_runner) -> None:
    document = definition_analysis_document_from_paths(
        [TOY_SOURCE], runner=native_runner, include_verification_facts=True
    )

    facts = document.source_facts
    method = next(item for item in document.definitions if item.name == "M")
    assert method.source_path == TOY_SOURCE.resolve()
    assert source_semantic_fingerprint(facts, TOY_SOURCE).full_sha256
    assert definition_semantic_fingerprint(facts, method).body_sha256
    assert facts.verification_targets is not None
    assert {target.full_name for target in facts.verification_targets} == {"Toy.Double", "Toy.M"}


# Native proof inputs validate and survive when Dafny emits no warning.
def test_native_proof_inputs_validate(native_runner) -> None:
    document = definition_analysis_document_from_paths(
        [TOY_SOURCE], runner=native_runner, proof_input_options=()
    )

    proof_inputs = document.source_facts.proof_inputs
    assert proof_inputs is not None
    assert [item.full_name for item in proof_inputs.definitions] == ["Toy.M"]
