"""Process boundary through which the analysis client reaches the native Dafny tool.

The client never chooses the executable or the process policy.  A host supplies a
:class:`DafnyCommandRunner` that prepends its own Dafny command to the invocation
arguments and applies its own environment, cancellation and process-group handling.
"""

from __future__ import annotations

import threading
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from subprocess import CompletedProcess
from typing import Protocol


@dataclass(frozen=True)
class DafnyInvocation:
    """One native Dafny process request, without the executable."""

    arguments: tuple[str, ...]
    cwd: Path
    operation: str
    timeout_seconds: float
    source_text: str | None = None
    cancel_event: threading.Event | None = None
    env: Mapping[str, str] | None = None


class DafnyCommandRunner(Protocol):
    """Run a Dafny invocation and return its captured text output.

    On timeout an implementation raises ``RuntimeError`` whose ``__cause__`` is
    ``subprocess.TimeoutExpired``; the client reports that as
    :class:`dafny_analysis.client.DefinitionAnalysisTimeout`.  Any other exception,
    such as a cancellation signal, propagates unchanged.  A non-zero exit status is
    returned, not raised.
    """

    def __call__(self, invocation: DafnyInvocation) -> CompletedProcess[str]:
        """Execute the invocation with the host's Dafny executable and process policy."""
        ...
