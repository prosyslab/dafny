"""Client for the native Dafny ``source-fingerprint`` command."""

from __future__ import annotations

import json
import tempfile
from collections.abc import Collection
from pathlib import Path
from subprocess import CompletedProcess

from .client import DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC
from .models import (
    SHA256,
    DafnyFingerprintDocument,
    DafnyFingerprintRegion,
    DafnyFingerprintRequest,
)
from .runner import DafnyCommandRunner, DafnyInvocation


def dafny_source_fingerprints(
    regions: Collection[DafnyFingerprintRegion],
    *,
    cwd: Path,
    runner: DafnyCommandRunner,
    timeout_seconds: float = DAFNY_DEFINITION_ANALYSIS_TIMEOUT_SEC,
) -> dict[str, SHA256]:
    """Hash source regions natively and return the digest of every region id."""

    request = DafnyFingerprintRequest(regions=tuple(regions))
    if not request.regions:
        raise ValueError("Dafny source fingerprinting requires at least one region")
    with tempfile.NamedTemporaryFile(
        "w",
        suffix=".json",
        encoding="utf-8",
    ) as handle:
        json.dump(request.model_dump(by_alias=True, mode="json"), handle, ensure_ascii=False)
        handle.flush()
        completed = runner(
            DafnyInvocation(
                arguments=("source-fingerprint", handle.name),
                cwd=cwd,
                operation="Dafny source fingerprinting",
                timeout_seconds=timeout_seconds,
            )
        )
    return fingerprints_from_completed(request, completed)


def fingerprints_from_completed(
    request: DafnyFingerprintRequest,
    completed: CompletedProcess[str],
) -> dict[str, SHA256]:
    """Validate a ``source-fingerprint`` process result against its request."""

    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        raise RuntimeError(f"Dafny source fingerprinting failed:\n{detail}")
    document = DafnyFingerprintDocument.model_validate_json(completed.stdout)
    result = {item.id: item.sha256 for item in document.fingerprints}
    expected = {region.region_id for region in request.regions}
    if set(result) != expected or len(result) != len(document.fingerprints):
        raise RuntimeError("Dafny source fingerprinting returned incomplete region results")
    return result
