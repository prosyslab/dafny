"""Wire-format contracts of the analysis models, checked against in-memory JSON."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from pydantic import ValidationError

from dafny_analysis.kinds import DefinitionKind
from dafny_analysis.models import (
    DEFINITION_INFO_LIST,
    DafnyAnalysisResult,
    DafnyFingerprintRegion,
    DafnyFingerprintSpan,
    DafnyProject,
    DefinitionAnalysisDocument,
    DefinitionInfo,
    DefinitionSourceFacts,
)
from support import HEX_A, HEX_B, definition_payload, document_payload


# A JSON source path decodes to a native Path and encodes back to its wire spelling.
def test_definition_info_decodes_paths_and_round_trips() -> None:
    payload = definition_payload(includedFiles=["/workspace/Dep.dfy"])

    info = DefinitionInfo.model_validate_json(json.dumps(payload))

    assert info.source_path == Path("/workspace/Toy.dfy")
    assert info.included_files == (Path("/workspace/Dep.dfy"),)
    wire = info.model_dump(mode="json", by_alias=True)
    assert wire["sourcePath"] == "/workspace/Toy.dfy"
    assert DefinitionInfo.model_validate_json(info.model_dump_json(by_alias=True)) == info


# Dafny reports twostate predicates as their own definition kind.
def test_definition_list_accepts_twostate_predicate_kind() -> None:
    payload = [definition_payload(kind="twostate predicate", declarationKind="twostate predicate")]

    definitions = DEFINITION_INFO_LIST.validate_json(json.dumps(payload))

    assert definitions[0].kind is DefinitionKind.TWOSTATE_PREDICATE


# An empty or missing source path is rejected instead of becoming the current directory.
@pytest.mark.parametrize("update", [{"sourcePath": ""}, {"sourcePath": None}, {"sourcePath": 7}])
def test_definition_info_rejects_invalid_source_path(update: dict[str, object]) -> None:
    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(definition_payload(**update)))


# Python-mode construction requires a Path and does not coerce strings.
def test_definition_info_requires_native_python_source_path() -> None:
    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate(definition_payload())


# Unknown native fields fail the schema so that a wire change is noticed.
def test_definition_info_rejects_unknown_field() -> None:
    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(definition_payload(surprise=1)))


# Optional native fields keep their documented defaults when absent.
def test_definition_info_defaults_optional_fields() -> None:
    info = DefinitionInfo.model_validate_json(json.dumps(definition_payload()))

    assert info.body_visibility is None
    assert info.children == ()
    assert info.source_group is None
    assert info.attributes == ()
    assert info.direct_precondition_calls == ()


# Span children and source groups decode as byte ranges.
def test_definition_info_decodes_children_and_source_group() -> None:
    payload = definition_payload(
        children=[{"start": 1, "end": 2}], sourceGroup={"start": 3, "end": 9}
    )

    info = DefinitionInfo.model_validate_json(json.dumps(payload))

    assert (info.children[0].start, info.children[0].end) == (1, 2)
    assert info.source_group is not None and info.source_group.end == 9


# A boolean flag must be a real JSON boolean, never a coerced string.
def test_definition_info_rejects_coerced_boolean() -> None:
    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(json.dumps(definition_payload(ghost="false")))


# Body visibility decodes with its camel-case names and rejects unknown members.
def test_body_visibility_decodes_and_rejects_extra_field() -> None:
    visibility = {
        "referencedDeclarations": ["Toy.M"],
        "isOpaque": True,
        "revealedFunctions": [],
        "revealsAllFunctions": False,
    }
    info = DefinitionInfo.model_validate_json(
        json.dumps(definition_payload(bodyVisibility=visibility))
    )
    assert info.body_visibility is not None and info.body_visibility.is_opaque is True

    with pytest.raises(ValidationError):
        DefinitionInfo.model_validate_json(
            json.dumps(definition_payload(bodyVisibility={**visibility, "extra": True}))
        )


# The full document accepts semantic facts, proof inputs and verification targets together.
def test_document_accepts_all_optional_source_facts() -> None:
    facts: dict[str, object] = {
        "semanticFacts": {
            "sources": [
                {
                    "sourcePath": "/workspace/Toy.dfy",
                    "fullSha256": HEX_A,
                    "declarationScaffoldSha256": HEX_B,
                    "scaffoldSha256": HEX_B,
                }
            ],
            "definitions": [
                {
                    "sourcePath": "/workspace/Toy.dfy",
                    "fullName": "Toy.M",
                    "kind": "method",
                    "declarationSha256": HEX_A,
                    "contractSha256": HEX_A,
                    "bodySha256": HEX_B,
                }
            ],
        },
        "proofInputs": {
            "schemaVersion": 1,
            "toolchainSha256": HEX_A,
            "optionsSha256": HEX_B,
            "definitions": [
                {"sourcePath": "/workspace/Toy.dfy", "fullName": "Toy.M", "sha256": HEX_A}
            ],
        },
        "verificationTargets": [
            {
                "fullName": "Toy.M",
                "sourcePath": "/workspace/Toy.dfy",
                "attributes": [{"name": "timeLimit", "arguments": ["5"], "start": 1, "end": 2}],
            }
        ],
    }
    definition = definition_payload(
        parameterDetails=[{"name": "x", "type": "int", "ghost": False}],
        returnDetails=[],
        directPreconditionCalls=[],
        directPostconditionCalls=[],
        contractHeaderWithoutAxiom="",
        contractHeaderWithAxiom="",
    )

    result = DafnyAnalysisResult.model_validate_json(
        json.dumps(document_payload([definition], **facts))
    )

    project = result.source_facts
    assert project.semantic_facts is not None and project.proof_inputs is not None
    assert project.verification_targets is not None
    assert project.verification_targets[0].attributes[0].name == "timeLimit"
    assert project.proof_inputs.definitions[0].full_name == "Toy.M"


# The strict document type requires the parameter and contract-header fields.
def test_document_requires_structured_definition_fields() -> None:
    with pytest.raises(ValidationError):
        DafnyAnalysisResult.model_validate_json(
            json.dumps(document_payload([definition_payload()]))
        )


# Digests must be 64 lowercase hexadecimal characters.
@pytest.mark.parametrize("digest", ["A" * 64, "a" * 63, "g" * 64])
def test_semantic_fingerprint_rejects_malformed_digest(digest: str) -> None:
    facts = {
        "sources": [
            {
                "sourcePath": "/workspace/Toy.dfy",
                "fullSha256": digest,
                "declarationScaffoldSha256": HEX_A,
                "scaffoldSha256": HEX_A,
            }
        ],
        "definitions": [],
    }

    with pytest.raises(ValidationError):
        DafnyProject.model_validate_json(
            json.dumps({"modules": [], "imports": [], "includes": [], "semanticFacts": facts})
        )


# Fingerprint regions serialize with wire aliases and string paths in JSON mode.
def test_fingerprint_region_serializes_wire_names() -> None:
    region = DafnyFingerprintRegion(
        id="r1",
        sourcePath=Path("/workspace/Toy.dfy"),
        includedSpan=DafnyFingerprintSpan(start=0, end=5),
        excludedSpans=(),
    )

    assert region.model_dump(by_alias=True, mode="json") == {
        "id": "r1",
        "sourcePath": "/workspace/Toy.dfy",
        "includedSpan": {"start": 0, "end": 5},
        "excludedSpans": [],
    }


# Fingerprint regions reject a string path in Python mode like the other strict models.
def test_fingerprint_region_rejects_string_path() -> None:
    with pytest.raises(ValidationError):
        DafnyFingerprintRegion(
            id="r1",
            sourcePath="/workspace/Toy.dfy",  # type: ignore[arg-type]
            excludedSpans=(),
        )


# The Dafnyutils names are aliases of the merged models, not second schemas.
def test_dafnyutils_names_are_aliases() -> None:
    assert DefinitionAnalysisDocument is DafnyAnalysisResult
    assert DefinitionSourceFacts is DafnyProject
