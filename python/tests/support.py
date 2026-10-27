"""Shared in-memory payload builders and a recording fake command runner."""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from subprocess import CompletedProcess

from dafny_analysis.runner import DafnyInvocation

FIXTURES = Path(__file__).parent / "fixtures"
TOY_SOURCE = FIXTURES / "Toy.dfy"
HEX_A = "a" * 64
HEX_B = "b" * 64


def definition_payload(**updates: object) -> dict[str, object]:
    """Return a minimal valid `definition-analysis` definition object with overrides."""

    payload: dict[str, object] = {
        "name": "M",
        "fullName": "Toy.M",
        "kind": "method",
        "enclosingName": "Toy",
        "line": 3,
        "column": 10,
        "start": 0,
        "bodyStart": 20,
        "end": 40,
        "sourcePath": "/workspace/Toy.dfy",
        "ghost": False,
        "hasByMethod": False,
        "hasLoop": False,
        "worldRelated": False,
        "returns": [],
        "returnNames": [],
        "requires": [],
        "ensures": [],
        "modifies": [],
        "recursive": False,
        "recursiveGroup": [],
        "callees": [],
        "references": [],
    }
    payload.update(updates)
    return payload


def document_payload(
    definitions: list[dict[str, object]] | None = None, **source_facts: object
) -> dict[str, object]:
    """Return a `--include-source-facts` document with overridable source facts."""

    facts: dict[str, object] = {"modules": [], "imports": [], "includes": []}
    facts.update(source_facts)
    return {"definitions": definitions or [], "sourceFacts": facts}


def completed(stdout: str = "", *, returncode: int = 0, stderr: str = "") -> CompletedProcess[str]:
    """Build a captured process result."""

    return CompletedProcess(["dafny"], returncode, stdout, stderr)


def json_completed(payload: object, *, stderr: str = "") -> CompletedProcess[str]:
    """Build a successful process result whose stdout is the JSON payload."""

    return completed(json.dumps(payload), stderr=stderr)


@dataclass
class FakeRunner:
    """Record invocations and answer them from a callback instead of a process."""

    respond: Callable[[DafnyInvocation], CompletedProcess[str]]
    invocations: list[DafnyInvocation] = field(default_factory=list)

    def __call__(self, invocation: DafnyInvocation) -> CompletedProcess[str]:
        self.invocations.append(invocation)
        return self.respond(invocation)
