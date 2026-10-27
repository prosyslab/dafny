"""Pure query behavior over in-memory analysis models."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from dafny_analysis.models import DafnyProject, DefinitionInfo
from dafny_analysis.queries import (
    definition_dependency_closure,
    definition_semantic_fingerprint,
    definition_text,
    normalized_signature,
    source_byte_span_text,
    source_semantic_fingerprint,
    spec_dependency_closure,
)
from support import HEX_A, HEX_B, definition_payload

SOURCE = Path("/workspace/Toy.dfy")
OTHER = Path("/workspace/Other.dfy")


def _info(name: str, **updates: object) -> DefinitionInfo:
    payload = definition_payload(
        name=name.split(".")[-1], fullName=name, sourcePath=str(SOURCE), **updates
    )
    return DefinitionInfo.model_validate_json(json.dumps(payload))


def _project(
    sources: list[dict[str, object]], definitions: list[dict[str, object]]
) -> DafnyProject:
    return DafnyProject.model_validate_json(
        json.dumps(
            {
                "modules": [],
                "imports": [],
                "includes": [],
                "semanticFacts": {"sources": sources, "definitions": definitions},
            }
        )
    )


def _source_fact(path: Path) -> dict[str, object]:
    return {
        "sourcePath": str(path),
        "fullSha256": HEX_A,
        "declarationScaffoldSha256": HEX_B,
        "scaffoldSha256": HEX_B,
    }


def _definition_fact(path: Path, name: str, kind: str = "method") -> dict[str, object]:
    return {
        "sourcePath": str(path),
        "fullName": name,
        "kind": kind,
        "declarationSha256": HEX_A,
        "contractSha256": HEX_A,
        "bodySha256": HEX_B,
    }


# A unique source fingerprint is found by its path.
def test_source_fingerprint_lookup_returns_unique_match() -> None:
    project = _project([_source_fact(SOURCE)], [])

    assert source_semantic_fingerprint(project, SOURCE).full_sha256 == HEX_A


# Missing or duplicated source fingerprints fail instead of choosing one.
@pytest.mark.parametrize("sources", [[], [_source_fact(SOURCE), _source_fact(SOURCE)]])
def test_source_fingerprint_lookup_rejects_non_unique(sources: list[dict[str, object]]) -> None:
    with pytest.raises(ValueError, match="not unique"):
        source_semantic_fingerprint(_project(sources, []), SOURCE)


# A project without semantic facts reports the missing facts.
def test_source_fingerprint_lookup_requires_semantic_facts() -> None:
    project = DafnyProject.model_validate_json('{"modules": [], "imports": [], "includes": []}')

    with pytest.raises(ValueError, match="missing"):
        source_semantic_fingerprint(project, SOURCE)


# A definition fingerprint is keyed by path, full name and kind.
def test_definition_fingerprint_lookup_matches_key() -> None:
    project = _project([], [_definition_fact(SOURCE, "Toy.M")])

    assert definition_semantic_fingerprint(project, _info("Toy.M")).body_sha256 == HEX_B
    with pytest.raises(ValueError, match="not unique"):
        definition_semantic_fingerprint(project, _info("Toy.N"))


# The closure follows dependencies and references in sorted order.
def test_closure_follows_dependencies_and_references() -> None:
    infos = [
        _info("Toy.Spec", kind="function", dependencies=["Toy.Helper"]),
        _info(
            "Toy.Helper",
            kind="predicate",
            references=[
                {
                    "targetFullName": "Toy.Leaf",
                    "targetModule": "Toy",
                    "targetKind": "function",
                    "isPattern": False,
                    "start": 0,
                    "end": 1,
                }
            ],
        ),
        _info("Toy.Leaf", kind="function"),
        _info("Toy.Unused", kind="function"),
    ]

    closure = spec_dependency_closure(
        infos, source_paths=[SOURCE], spec_entries=[(SOURCE, "Toy.Spec")]
    )

    assert [info.full_name for info in closure] == ["Toy.Helper", "Toy.Leaf", "Toy.Spec"]


# Least and greatest predicates are valid specification entries.
@pytest.mark.parametrize("kind", ["least predicate", "greatest predicate"])
def test_closure_accepts_extreme_predicate_entries(kind: str) -> None:
    closure = spec_dependency_closure(
        [_info("Toy.Spec", kind=kind)], source_paths=[SOURCE], spec_entries=[(SOURCE, "Toy.Spec")]
    )

    assert [info.full_name for info in closure] == ["Toy.Spec"]


# A method is not a specification entry, so the closure fails closed.
def test_closure_rejects_non_callable_entry() -> None:
    with pytest.raises(RuntimeError, match="callable specification"):
        spec_dependency_closure(
            [_info("Toy.Spec", kind="method")],
            source_paths=[SOURCE],
            spec_entries=[(SOURCE, "Toy.Spec")],
        )


# An empty entry set and an entry outside the selected sources both fail closed.
def test_closure_rejects_empty_and_foreign_entries() -> None:
    infos = [_info("Toy.Spec", kind="function")]

    with pytest.raises(RuntimeError, match="empty"):
        spec_dependency_closure(infos, source_paths=[SOURCE], spec_entries=[])
    with pytest.raises(RuntimeError, match="outside selected sources"):
        spec_dependency_closure(infos, source_paths=[SOURCE], spec_entries=[(OTHER, "Toy.Spec")])


# A dependency declared in an unselected source is rejected.
def test_closure_rejects_dependency_outside_selected_sources() -> None:
    foreign = DefinitionInfo.model_validate_json(
        json.dumps(
            definition_payload(
                name="Leaf", fullName="Toy.Leaf", kind="function", sourcePath=str(OTHER)
            )
        )
    )
    infos = [_info("Toy.Spec", kind="function", dependencies=["Toy.Leaf"]), foreign]

    with pytest.raises(RuntimeError, match="outside selected sources"):
        definition_dependency_closure(infos, source_paths=[SOURCE], root_symbols=["Toy.Spec"])


# Unknown dependencies and duplicate full names are reported rather than skipped.
def test_closure_rejects_unresolved_and_duplicate_symbols() -> None:
    infos = [_info("Toy.Spec", kind="function", dependencies=["Toy.Missing"])]

    with pytest.raises(RuntimeError, match="unresolved definition dependency"):
        definition_dependency_closure(infos, source_paths=[SOURCE], root_symbols=["Toy.Spec"])
    with pytest.raises(RuntimeError, match="duplicate full name"):
        definition_dependency_closure(
            [_info("Toy.Spec"), _info("Toy.Spec")], source_paths=[SOURCE], root_symbols=["Toy.Spec"]
        )


# Boundary symbols stop the closure without being included or resolved.
def test_closure_stops_at_boundary_symbols() -> None:
    infos = [_info("Toy.Spec", kind="function", dependencies=["Toy.Retained"])]

    closure = definition_dependency_closure(
        infos,
        source_paths=[SOURCE],
        root_symbols=["Toy.Spec"],
        boundary_symbols=["Toy.Retained"],
    )

    assert [info.full_name for info in closure] == ["Toy.Spec"]


# Byte offsets from Dafny slice UTF-8 text, not Python characters.
def test_byte_span_text_uses_utf8_offsets() -> None:
    source = "// é\nfunction F()"

    assert source_byte_span_text(source, 6, 14) == "function"
    info = _info("Toy.F", kind="function", start=6, end=18, bodyStart=None)
    assert definition_text(source, info) == "function F()"


# Signature normalization drops a leading ghost keyword and collapses whitespace.
def test_normalized_signature_drops_ghost_and_collapses_whitespace() -> None:
    source = "ghost   function  F(x: int)\n  : int { x }"
    info = _info("Toy.F", kind="function", start=0, end=len(source), bodyStart=source.index("{"))

    assert normalized_signature(source, info) == "function F(x: int) : int"
    assert (
        normalized_signature("ghostly()", _info("Toy.G", start=0, end=9, bodyStart=None))
        == "ghostly()"
    )
