"""Client for the native Dafny ``definition-analysis`` command.

Every entry point takes the host's :class:`~dafny_analysis.runner.DafnyCommandRunner`
as the keyword-only ``runner`` argument; bind it once with ``functools.partial``.
"""

from __future__ import annotations

import threading
from collections.abc import Callable, Collection, Mapping
from dataclasses import dataclass
from pathlib import Path
from subprocess import CompletedProcess, TimeoutExpired
from typing import TypeVar

from pydantic import ValidationError

from .models import (
    DEFINITION_INFO_LIST,
    DafnyAnalysisResult,
    DefinitionInfo,
    DefinitionPostconditionCall,
    DefinitionPreconditionCall,
)
from .runner import DafnyCommandRunner, DafnyInvocation

DAFNY_STANDARD_LIBRARY_OPTION = "--standard-libraries:false"
DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC = 300

_DefinitionInfoT = TypeVar("_DefinitionInfoT", bound=DefinitionInfo)


class DefinitionAnalysisError(RuntimeError):
    """Report an expected failure from the native definition-analysis boundary."""


class DefinitionAnalysisTimeout(DefinitionAnalysisError):
    """Identify a native analyzer timeout while preserving its subprocess cause."""


class DefinitionAnalysisProcessError(DefinitionAnalysisError):
    """Retain a failed native analyzer process exit for typed caller policy."""

    def __init__(self, diagnostic: str, *, returncode: int) -> None:
        super().__init__(diagnostic)
        self.returncode = returncode

    @property
    def operational(self) -> bool:
        """Return whether the exit is a signal, internal error, or unknown status."""

        return self.returncode < 0 or self.returncode >= 6


class DefinitionAnalysisProtocolError(DefinitionAnalysisError):
    """Report malformed or schema-invalid output from a successful analyzer process."""


@dataclass(frozen=True)
class DefinitionAnalysisDetails:
    """Retain host-observed strict warnings independently of the native document schema."""

    document: DafnyAnalysisResult
    warning_diagnostic: str | None = None


ExpectedWarningFilter = Callable[[str, Path], str]
"""Remove a host's expected diagnostics from ``(stderr, working_directory)``."""


def has_dafny_warning(output: str) -> bool:
    """Return whether Dafny output still contains a warning diagnostic."""

    return any("Warning:" in line for line in output.splitlines())


def _run_definition_analysis(
    arguments: tuple[str, ...],
    *,
    runner: DafnyCommandRunner,
    cwd: Path,
    source_text: str | None = None,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
    cancel_event: threading.Event | None = None,
    env: Mapping[str, str] | None = None,
) -> CompletedProcess[str]:
    invocation = DafnyInvocation(
        arguments=("definition-analysis", *arguments),
        cwd=cwd,
        operation="dafny definition-analysis",
        timeout_seconds=timeout_seconds,
        source_text=source_text,
        cancel_event=cancel_event,
        env=env,
    )
    try:
        return runner(invocation)
    except RuntimeError as exc:
        if not isinstance(exc.__cause__, TimeoutExpired):
            raise
        raise DefinitionAnalysisTimeout(str(exc)) from exc.__cause__


def _checked_stdout(completed: CompletedProcess[str], subject: str) -> str:
    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        raise DefinitionAnalysisProcessError(
            f"dafny definition-analysis failed for {subject}:\n{detail}",
            returncode=completed.returncode,
        )
    return completed.stdout


def _parse_definition_infos(stdout: str) -> list[DefinitionInfo]:
    try:
        return DEFINITION_INFO_LIST.validate_json(stdout)
    except ValidationError as exc:
        raise DefinitionAnalysisProtocolError(
            "dafny definition-analysis returned malformed or unusable JSON"
        ) from exc


def _parse_analysis_document(stdout: str) -> DafnyAnalysisResult:
    try:
        return DafnyAnalysisResult.model_validate_json(stdout)
    except ValidationError as exc:
        raise DefinitionAnalysisProtocolError(
            "dafny definition-analysis returned malformed or unusable JSON"
        ) from exc


def _basic_arguments(*, spans_only: bool) -> list[str]:
    arguments = [
        "--format",
        "json",
        "--allow-warnings",
        "--suppress-warnings",
        DAFNY_STANDARD_LIBRARY_OPTION,
    ]
    if spans_only:
        arguments.append("--spans-only")
    return arguments


def definition_analysis_infos_from_paths(
    source_paths: Collection[Path],
    *,
    runner: DafnyCommandRunner,
    spans_only: bool = False,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
    cancel_event: threading.Event | None = None,
) -> list[DefinitionInfo]:
    """Analyze source files and enrich empty contract-call text from their byte spans."""

    if not source_paths:
        raise ValueError("definition analysis requires at least one source path")
    sorted_paths = sorted(path.resolve() for path in source_paths)
    arguments = _basic_arguments(spans_only=spans_only)
    if not spans_only:
        arguments.extend(("--reads-clauses-on-methods", "--include-statements"))
    arguments.extend(str(path) for path in sorted_paths)
    completed = _run_definition_analysis(
        tuple(arguments),
        runner=runner,
        cwd=sorted_paths[0].parent,
        timeout_seconds=timeout_seconds,
        cancel_event=cancel_event,
    )
    stdout = _checked_stdout(completed, ", ".join(str(path) for path in sorted_paths))
    return _populate_specification_call_text(
        _parse_definition_infos(stdout),
        {path: path.read_text(encoding="utf-8") for path in sorted_paths},
    )


def definition_analysis_document_from_paths(
    source_paths: Collection[Path],
    *,
    runner: DafnyCommandRunner,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
    include_semantic_facts: bool = True,
    include_verification_facts: bool = False,
    cancel_event: threading.Event | None = None,
    proof_input_options: tuple[str, ...] | None = None,
    proof_input_allow_warnings: bool = False,
    expected_warning_filter: ExpectedWarningFilter | None = None,
    cwd: Path | None = None,
) -> DafnyAnalysisResult:
    """Analyze source structure, optionally requesting semantic facts in the same run."""

    return definition_analysis_details_from_paths(
        source_paths,
        runner=runner,
        timeout_seconds=timeout_seconds,
        include_semantic_facts=include_semantic_facts,
        include_verification_facts=include_verification_facts,
        cancel_event=cancel_event,
        proof_input_options=proof_input_options,
        proof_input_allow_warnings=proof_input_allow_warnings,
        expected_warning_filter=expected_warning_filter,
        cwd=cwd,
    ).document


def definition_analysis_details_from_paths(
    source_paths: Collection[Path],
    *,
    runner: DafnyCommandRunner,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
    include_semantic_facts: bool = True,
    include_verification_facts: bool = False,
    env: Mapping[str, str] | None = None,
    cancel_event: threading.Event | None = None,
    proof_input_options: tuple[str, ...] | None = None,
    proof_input_allow_warnings: bool = False,
    expected_warning_filter: ExpectedWarningFilter | None = None,
    cwd: Path | None = None,
) -> DefinitionAnalysisDetails:
    """Analyze once and retain the filtered warnings that suppress strict proof inputs.

    With ``proof_input_options`` the source order and warning flags are the caller's and
    proof inputs are dropped when Dafny reports a warning that ``expected_warning_filter``
    does not remove; without a filter every warning counts.
    """

    if not source_paths:
        raise ValueError("definition analysis requires at least one source path")
    resolved_paths = [path.resolve() for path in source_paths]
    sorted_paths = sorted(resolved_paths) if proof_input_options is None else resolved_paths
    arguments = [
        "--format",
        "json",
        *(("--allow-warnings", "--suppress-warnings") if proof_input_options is None else ()),
        DAFNY_STANDARD_LIBRARY_OPTION,
        *(("--reads-clauses-on-methods",) if proof_input_options is None else ()),
        "--include-statements",
        "--include-source-facts",
    ]
    if include_verification_facts:
        arguments.append("--include-verification-facts")
    if include_semantic_facts:
        arguments.append("--include-semantic-facts")
    if proof_input_options is not None:
        arguments.extend(("--include-proof-inputs", *proof_input_options))
    arguments.extend(str(path) for path in sorted_paths)
    working_directory = cwd or sorted_paths[0].parent
    completed = _run_definition_analysis(
        tuple(arguments),
        runner=runner,
        cwd=working_directory,
        timeout_seconds=timeout_seconds,
        cancel_event=cancel_event,
        env=env,
    )
    stdout = _checked_stdout(completed, ", ".join(str(path) for path in sorted_paths))
    document = _parse_analysis_document(stdout)
    warning_diagnostic = None
    if proof_input_options is not None and not proof_input_allow_warnings:
        diagnostics = completed.stderr
        if expected_warning_filter is not None:
            diagnostics = expected_warning_filter(diagnostics, working_directory)
        if has_dafny_warning(diagnostics):
            warning_diagnostic = diagnostics
            document = document.model_copy(
                update={
                    "source_facts": document.source_facts.model_copy(update={"proof_inputs": None})
                }
            )
    document = document.model_copy(
        update={
            "definitions": tuple(
                _populate_specification_call_text(
                    document.definitions,
                    {path: path.read_text(encoding="utf-8") for path in sorted_paths},
                )
            )
        }
    )
    if include_semantic_facts and document.source_facts.semantic_facts is None:
        raise DefinitionAnalysisError("dafny definition-analysis omitted requested semantic facts")
    if include_verification_facts and document.source_facts.verification_targets is None:
        raise DefinitionAnalysisError(
            "dafny definition-analysis omitted requested verification facts"
        )
    return DefinitionAnalysisDetails(document, warning_diagnostic)


def definition_analysis_infos_from_stdin(
    source_text: str,
    *,
    source_dir: Path,
    runner: DafnyCommandRunner,
    spans_only: bool = False,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
) -> list[DefinitionInfo]:
    """Analyze source text through Dafny's stdin mode and return typed definitions."""

    arguments = _basic_arguments(spans_only=spans_only)
    if not spans_only:
        arguments.append("--reads-clauses-on-methods")
    arguments.append("--stdin")
    completed = _run_definition_analysis(
        tuple(arguments),
        runner=runner,
        cwd=source_dir.resolve(),
        source_text=source_text,
        timeout_seconds=timeout_seconds,
    )
    definitions = _parse_definition_infos(_checked_stdout(completed, "stdin"))
    return _populate_specification_call_text(
        definitions,
        {definition.source_path: source_text for definition in definitions},
    )


def _source_text_for_definition(
    source_path: Path,
    sources: dict[Path, str],
) -> str | None:
    source = sources.get(source_path)
    if source is None:
        if source_path.is_file():
            source = source_path.read_text(encoding="utf-8")
            sources[source_path] = source
    return source


def _populate_specification_call_text(
    definitions: Collection[_DefinitionInfoT],
    sources: dict[Path, str],
) -> list[_DefinitionInfoT]:
    """Fill omitted contract-call text from source spans emitted by Dafny."""
    enriched: list[_DefinitionInfoT] = []
    for definition in definitions:
        source = _source_text_for_definition(definition.source_path, sources)
        if source is None:
            enriched.append(definition)
            continue
        enriched.append(
            definition.model_copy(
                update={
                    "direct_precondition_calls": tuple(
                        _call_with_source_text(call, source)
                        for call in definition.direct_precondition_calls
                    ),
                    "direct_postcondition_calls": tuple(
                        _call_with_source_text(call, source)
                        for call in definition.direct_postcondition_calls
                    ),
                }
            )
        )
    return enriched


def _call_with_source_text(
    call: DefinitionPreconditionCall | DefinitionPostconditionCall,
    source: str,
) -> DefinitionPreconditionCall | DefinitionPostconditionCall:
    if call.text:
        return call
    text = source.encode("utf-8")[call.start : call.end].decode("utf-8")
    return call.model_copy(update={"text": text})
