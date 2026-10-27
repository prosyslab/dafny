"""Fingerprint response validation against its request, using in-memory process results."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from dafny_analysis.models import DafnyFingerprintRegion, DafnyFingerprintRequest
from dafny_analysis.source_fingerprints import (
    dafny_source_fingerprints,
    fingerprints_from_completed,
)
from support import HEX_A, HEX_B, FakeRunner, completed, json_completed


def _request(*ids: str) -> DafnyFingerprintRequest:
    return DafnyFingerprintRequest(
        regions=tuple(
            DafnyFingerprintRegion(
                id=region_id, sourcePath=Path("/workspace/Toy.dfy"), excludedSpans=()
            )
            for region_id in ids
        )
    )


# Every requested region id maps to its digest.
def test_fingerprints_map_region_ids_to_digests() -> None:
    result = fingerprints_from_completed(
        _request("a", "b"),
        json_completed(
            {"fingerprints": [{"id": "a", "sha256": HEX_A}, {"id": "b", "sha256": HEX_B}]}
        ),
    )

    assert result == {"a": HEX_A, "b": HEX_B}


# A failed process reports its combined output.
def test_fingerprint_failure_reports_output() -> None:
    with pytest.raises(RuntimeError, match="failed:\nout\nerr"):
        fingerprints_from_completed(_request("a"), completed("out", returncode=2, stderr="err"))


# Missing, extra or duplicated region ids are rejected as incomplete.
@pytest.mark.parametrize(
    "ids",
    [["a"], ["a", "b", "c"], ["a", "a", "b"]],
)
def test_incomplete_region_results_are_rejected(ids: list[str]) -> None:
    payload = {"fingerprints": [{"id": region, "sha256": HEX_A} for region in ids]}

    with pytest.raises(RuntimeError, match="incomplete region results"):
        fingerprints_from_completed(_request("a", "b"), json_completed(payload))


# A digest that is not lowercase SHA-256 hexadecimal fails validation.
def test_fingerprint_digest_must_be_sha256_hex() -> None:
    payload = json.dumps({"fingerprints": [{"id": "a", "sha256": "xyz"}]})

    with pytest.raises(ValueError):
        fingerprints_from_completed(_request("a"), completed(payload))


# An empty region set is a caller error before any process starts.
def test_empty_regions_are_rejected_before_running() -> None:
    runner = FakeRunner(lambda _: completed("{}"))

    with pytest.raises(ValueError, match="at least one region"):
        dafny_source_fingerprints([], cwd=Path("/workspace"), runner=runner)
    assert runner.invocations == []
