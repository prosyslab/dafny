"""Client behavior against a fake command runner and in-memory native output."""

from __future__ import annotations

import json
import threading
from pathlib import Path
from subprocess import CompletedProcess, TimeoutExpired

import pytest

from dafny_analysis import client
from dafny_analysis.client import (
    DAFNY_STANDARD_LIBRARY_OPTION,
    DefinitionAnalysisError,
    DefinitionAnalysisProcessError,
    DefinitionAnalysisProtocolError,
    DefinitionAnalysisTimeout,
    definition_analysis_details_from_paths,
    definition_analysis_document_from_paths,
    definition_analysis_infos_from_paths,
    definition_analysis_infos_from_stdin,
    has_dafny_warning,
)
from dafny_analysis.runner import DafnyInvocation
from support import (
    HEX_A,
    HEX_B,
    TOY_SOURCE,
    FakeRunner,
    completed,
    definition_payload,
    document_payload,
    json_completed,
)

STRUCTURED = {
    "parameterDetails": [],
    "returnDetails": [],
    "directPreconditionCalls": [],
    "directPostconditionCalls": [],
    "contractHeaderWithoutAxiom": "",
    "contractHeaderWithAxiom": "",
}
SEMANTIC_FACTS = {
    "sources": [
        {
            "sourcePath": str(TOY_SOURCE),
            "fullSha256": HEX_A,
            "declarationScaffoldSha256": HEX_B,
            "scaffoldSha256": HEX_B,
        }
    ],
    "definitions": [],
}
PROOF_INPUTS = {
    "schemaVersion": 1,
    "toolchainSha256": HEX_A,
    "optionsSha256": HEX_B,
    "definitions": [],
}
WARNING = "Warning: something noteworthy\n"


def _definition(**updates: object) -> dict[str, object]:
    defaults = {"sourcePath": str(TOY_SOURCE.resolve()), **STRUCTURED}
    return definition_payload(**{**defaults, **updates})


def _document(**facts: object) -> dict[str, object]:
    return document_payload([_definition()], **facts)


# The path client sorts inputs, runs from the first parent, and asks for statement facts.
def test_infos_from_paths_builds_deterministic_command() -> None:
    runner = FakeRunner(lambda _: json_completed([]))
    other = TOY_SOURCE.parent / "Zeta.dfy"

    definition_analysis_infos_from_paths([other, TOY_SOURCE], runner=runner)

    (invocation,) = runner.invocations
    assert invocation.arguments == (
        "definition-analysis",
        "--format",
        "json",
        "--allow-warnings",
        "--suppress-warnings",
        DAFNY_STANDARD_LIBRARY_OPTION,
        "--reads-clauses-on-methods",
        "--include-statements",
        str(TOY_SOURCE.resolve()),
        str(other.resolve()),
    )
    assert invocation.cwd == TOY_SOURCE.resolve().parent
    assert invocation.operation == "dafny definition-analysis"
    assert invocation.timeout_seconds == client.DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC
    assert invocation.source_text is None


# Span-only analysis omits the resolver-dependent flags.
def test_infos_from_paths_spans_only_omits_statement_flags() -> None:
    runner = FakeRunner(lambda _: json_completed([]))

    definition_analysis_infos_from_paths([TOY_SOURCE], runner=runner, spans_only=True)

    arguments = runner.invocations[0].arguments
    assert "--spans-only" in arguments
    assert "--include-statements" not in arguments
    assert "--reads-clauses-on-methods" not in arguments


# Empty source selections are a caller error before any process starts.
def test_empty_source_selection_is_rejected_before_running() -> None:
    runner = FakeRunner(lambda _: json_completed([]))

    with pytest.raises(ValueError):
        definition_analysis_infos_from_paths([], runner=runner)
    with pytest.raises(ValueError):
        definition_analysis_details_from_paths([], runner=runner)
    assert runner.invocations == []


# Cancellation event and environment reach the runner unchanged.
def test_details_forward_cancellation_environment_and_cwd() -> None:
    runner = FakeRunner(lambda _: json_completed(_document(semanticFacts=SEMANTIC_FACTS)))
    event = threading.Event()
    env = {"TMPDIR": "/tmp"}
    cwd = TOY_SOURCE.parent

    definition_analysis_details_from_paths(
        [TOY_SOURCE], runner=runner, cancel_event=event, env=env, cwd=cwd, timeout_seconds=7
    )

    invocation = runner.invocations[0]
    assert invocation.cancel_event is event
    assert invocation.env == env
    assert invocation.cwd == cwd
    assert invocation.timeout_seconds == 7


# Empty contract-call text is filled from the reported byte span.
def test_infos_fill_empty_call_text_from_source_span() -> None:
    call = {"targetFullName": "Toy.Double", "start": 127, "end": 136, "text": "", "arguments": []}
    kept = {**call, "text": "kept"}
    payload = [
        _definition(directPostconditionCalls=[call], directPreconditionCalls=[kept]),
    ]
    runner = FakeRunner(lambda _: json_completed(payload))

    (info,) = definition_analysis_infos_from_paths([TOY_SOURCE], runner=runner)

    assert info.direct_postcondition_calls[0].text == "Double(x)"
    assert info.direct_precondition_calls[0].text == "kept"


# A non-zero exit keeps its status; signals and internal errors are operational.
@pytest.mark.parametrize(
    ("code", "operational"), [(1, False), (2, False), (5, False), (6, True), (-9, True)]
)
def test_process_failure_reports_operational_exit(code: int, operational: bool) -> None:
    runner = FakeRunner(lambda _: completed("out", returncode=code, stderr="err"))

    with pytest.raises(DefinitionAnalysisProcessError) as raised:
        definition_analysis_infos_from_paths([TOY_SOURCE], runner=runner)

    assert raised.value.returncode == code
    assert raised.value.operational is operational
    assert "out\nerr" in str(raised.value)


# Output that is not the expected JSON becomes a protocol error with the schema cause.
@pytest.mark.parametrize("stdout", ["not json", "{}", json.dumps([{"name": "only"}])])
def test_malformed_output_is_a_protocol_error(stdout: str) -> None:
    runner = FakeRunner(lambda _: completed(stdout))

    with pytest.raises(DefinitionAnalysisProtocolError):
        definition_analysis_infos_from_paths([TOY_SOURCE], runner=runner)
    with pytest.raises(DefinitionAnalysisProtocolError):
        definition_analysis_document_from_paths([TOY_SOURCE], runner=runner)


# A runner timeout surfaces as the typed timeout with the subprocess cause preserved.
def test_runner_timeout_becomes_analysis_timeout() -> None:
    cause = TimeoutExpired(["dafny"], 3)

    def respond(_: DafnyInvocation) -> CompletedProcess[str]:
        raise RuntimeError("dafny definition-analysis timed out after 3 seconds") from cause

    with pytest.raises(DefinitionAnalysisTimeout) as raised:
        definition_analysis_infos_from_paths([TOY_SOURCE], runner=FakeRunner(respond))

    assert raised.value.__cause__ is cause
    assert isinstance(raised.value, DefinitionAnalysisError)


# Other runner failures and cancellation signals are not rewritten by the client.
def test_other_runner_failures_propagate() -> None:
    class Stopped(Exception):
        pass

    def stop(_: DafnyInvocation) -> CompletedProcess[str]:
        raise Stopped

    def broken(_: DafnyInvocation) -> CompletedProcess[str]:
        raise RuntimeError("process did not complete cleanly")

    with pytest.raises(Stopped):
        definition_analysis_infos_from_paths([TOY_SOURCE], runner=FakeRunner(stop))
    with pytest.raises(RuntimeError, match="did not complete") as raised:
        definition_analysis_infos_from_paths([TOY_SOURCE], runner=FakeRunner(broken))
    assert not isinstance(raised.value, DefinitionAnalysisError)


# The document request asks for semantic facts by default and verification facts on demand.
def test_document_flags_follow_requested_facts() -> None:
    facts = {"semanticFacts": SEMANTIC_FACTS, "verificationTargets": []}
    runner = FakeRunner(lambda _: json_completed(_document(**facts)))

    definition_analysis_document_from_paths(
        [TOY_SOURCE], runner=runner, include_verification_facts=True
    )
    definition_analysis_document_from_paths(
        [TOY_SOURCE],
        runner=FakeRunner(lambda _: json_completed(_document())),
        include_semantic_facts=False,
    )

    arguments = runner.invocations[0].arguments
    assert {
        "--include-source-facts",
        "--include-semantic-facts",
        "--include-verification-facts",
    } <= set(arguments)
    assert "--include-proof-inputs" not in arguments


# Missing semantic facts that were requested are an analysis error.
def test_document_requires_requested_semantic_facts() -> None:
    runner = FakeRunner(lambda _: json_completed(_document()))

    with pytest.raises(DefinitionAnalysisError, match="semantic facts"):
        definition_analysis_document_from_paths([TOY_SOURCE], runner=runner)


# Missing verification facts that were requested are an analysis error.
def test_document_requires_requested_verification_facts() -> None:
    runner = FakeRunner(lambda _: json_completed(_document(semanticFacts=SEMANTIC_FACTS)))

    with pytest.raises(DefinitionAnalysisError, match="verification facts"):
        definition_analysis_document_from_paths(
            [TOY_SOURCE], runner=runner, include_verification_facts=True
        )


# Proof-input mode keeps caller order and warning policy, and appends caller options.
def test_proof_input_mode_uses_caller_order_and_options() -> None:
    runner = FakeRunner(
        lambda _: json_completed(_document(semanticFacts=SEMANTIC_FACTS, proofInputs=PROOF_INPUTS))
    )
    second = TOY_SOURCE.parent / "Zeta.dfy"

    definition_analysis_details_from_paths(
        [second, TOY_SOURCE], runner=runner, proof_input_options=("--solver-option:a=b",)
    )

    arguments = runner.invocations[0].arguments
    assert "--allow-warnings" not in arguments and "--suppress-warnings" not in arguments
    assert "--reads-clauses-on-methods" not in arguments
    flag = arguments.index("--include-proof-inputs")
    assert arguments[flag : flag + 2] == ("--include-proof-inputs", "--solver-option:a=b")
    assert arguments[-2:] == (str(second.resolve()), str(TOY_SOURCE.resolve()))


# An unexpected warning discards proof inputs and is retained for the caller.
def test_unfiltered_warning_discards_proof_inputs() -> None:
    runner = FakeRunner(
        lambda _: json_completed(
            _document(semanticFacts=SEMANTIC_FACTS, proofInputs=PROOF_INPUTS), stderr=WARNING
        )
    )

    details = definition_analysis_details_from_paths(
        [TOY_SOURCE], runner=runner, proof_input_options=()
    )

    assert details.document.source_facts.proof_inputs is None
    assert details.warning_diagnostic == WARNING


# A host filter that removes every warning keeps the proof inputs.
def test_filtered_warning_keeps_proof_inputs_and_receives_directory() -> None:
    seen: list[tuple[str, Path]] = []

    def drop(output: str, directory: Path) -> str:
        seen.append((output, directory))
        return ""

    runner = FakeRunner(
        lambda _: json_completed(
            _document(semanticFacts=SEMANTIC_FACTS, proofInputs=PROOF_INPUTS), stderr=WARNING
        )
    )

    details = definition_analysis_details_from_paths(
        [TOY_SOURCE], runner=runner, proof_input_options=(), expected_warning_filter=drop
    )

    assert details.document.source_facts.proof_inputs is not None
    assert details.warning_diagnostic is None
    assert seen == [(WARNING, TOY_SOURCE.resolve().parent)]


# Warnings never discard proof inputs when the caller allows them.
def test_allowed_warnings_keep_proof_inputs() -> None:
    runner = FakeRunner(
        lambda _: json_completed(
            _document(semanticFacts=SEMANTIC_FACTS, proofInputs=PROOF_INPUTS), stderr=WARNING
        )
    )

    details = definition_analysis_details_from_paths(
        [TOY_SOURCE], runner=runner, proof_input_options=(), proof_input_allow_warnings=True
    )

    assert details.document.source_facts.proof_inputs is not None


# The stdin client sends the text, resolves call text against the reported path.
def test_stdin_client_sends_source_and_fills_call_text() -> None:
    source = "function F() : int { 1 }\n"
    call = {"targetFullName": "Toy.F", "start": 0, "end": 8, "text": "", "arguments": []}
    payload = [_definition(sourcePath="/", directPostconditionCalls=[call])]
    runner = FakeRunner(lambda _: json_completed(payload))

    (info,) = definition_analysis_infos_from_stdin(
        source, source_dir=TOY_SOURCE.parent, runner=runner
    )

    invocation = runner.invocations[0]
    assert invocation.source_text == source
    assert invocation.arguments[-1] == "--stdin"
    assert "--reads-clauses-on-methods" in invocation.arguments
    assert info.direct_postcondition_calls[0].text == "function"


# Warning detection matches Dafny's diagnostic prefix on any line.
def test_has_dafny_warning_matches_any_line() -> None:
    assert has_dafny_warning("ok\nfile.dfy(1,2): Warning: careful\n")
    assert not has_dafny_warning("file.dfy(1,2): Error: no\n")
