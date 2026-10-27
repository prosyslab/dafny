"""Pydantic models used by the Dafny analysis adapters.

This module intentionally has no subprocess or Dafny-tool imports.  Datatype
consumers can import :class:`DefinitionKind` without importing the external
analysis client.  Every model mirrors the camel-case JSON that the native
``definition-analysis`` and ``source-fingerprint`` commands emit; unknown wire
fields are rejected so a native schema change fails loudly.
"""

from __future__ import annotations

from functools import cached_property
from pathlib import Path
from typing import Annotated

from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    Strict,
    StrictBool,
    StrictInt,
    StrictStr,
    TypeAdapter,
    field_validator,
)

from .kinds import DefinitionKind

# Complete SHA-256 values use the canonical lowercase hexadecimal JSON form.
SHA256 = Annotated[
    StrictStr,
    Field(min_length=64, max_length=64, pattern=r"^[0-9a-f]{64}$"),
]


class DafnyFingerprintSpan(BaseModel):
    """Half-open byte range of one source region in a fingerprint request."""

    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    start: StrictInt
    end: StrictInt


class DafnyFingerprintRegion(BaseModel):
    """One source file region, minus excluded spans, that the native tool hashes."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True, strict=True)

    region_id: StrictStr = Field(alias="id")
    source_path: Path = Field(alias="sourcePath")
    included_span: DafnyFingerprintSpan | None = Field(default=None, alias="includedSpan")
    excluded_spans: tuple[DafnyFingerprintSpan, ...] = Field(alias="excludedSpans")


class DafnyFingerprintRequest(BaseModel):
    """Request document accepted by the native `source-fingerprint` command."""

    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    regions: tuple[DafnyFingerprintRegion, ...]


class DafnyFingerprintResult(BaseModel):
    """Digest of one requested region, keyed by the request region id."""

    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    id: StrictStr
    sha256: SHA256


class DafnyFingerprintDocument(BaseModel):
    """Response document of the native `source-fingerprint` command."""

    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    fingerprints: tuple[DafnyFingerprintResult, ...]


class DefinitionAnalysisInclude(BaseModel):
    """One `include` directive and the resolved target it names."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: Path = Field(alias="sourcePath", strict=True)
    target_path: Path = Field(alias="targetPath", strict=True)
    start: StrictInt
    end: StrictInt


class DefinitionAnalysisModule(BaseModel):
    """One module declaration with its full and body byte ranges."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    name: StrictStr
    source_path: Path = Field(alias="sourcePath", strict=True)
    start: StrictInt
    end: StrictInt
    body_start: StrictInt = Field(alias="bodyStart")
    body_end: StrictInt = Field(alias="bodyEnd")


class DefinitionAnalysisImport(BaseModel):
    """One module import with its resolved target and alias facts."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    module_name: StrictStr = Field(alias="moduleName")
    alias: StrictStr
    has_alias: StrictBool = Field(alias="hasAlias")
    resolved_target: StrictStr = Field(alias="resolvedTarget")
    resolved_target_source_path: Path = Field(alias="resolvedTargetSourcePath", strict=True)
    opened: StrictBool
    source_path: Path = Field(alias="sourcePath", strict=True)
    start: StrictInt
    end: StrictInt


class DafnySourceSemanticFingerprint(BaseModel):
    """Whole-source digests that ignore comments and layout."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: Path = Field(alias="sourcePath", strict=True)
    full_sha256: SHA256 = Field(alias="fullSha256")
    declaration_scaffold_sha256: SHA256 = Field(alias="declarationScaffoldSha256")
    scaffold_sha256: SHA256 = Field(alias="scaffoldSha256")


class DafnyDefinitionSemanticFingerprint(BaseModel):
    """Declaration, contract and body digests for one definition."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: Path = Field(alias="sourcePath", strict=True)
    full_name: StrictStr = Field(alias="fullName")
    kind: DefinitionKind
    declaration_sha256: SHA256 = Field(alias="declarationSha256")
    contract_sha256: SHA256 = Field(alias="contractSha256")
    body_sha256: SHA256 = Field(alias="bodySha256")


class DafnySemanticFacts(BaseModel):
    """Semantic digests for the analyzed sources and their definitions."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    sources: tuple[DafnySourceSemanticFingerprint, ...]
    definitions: tuple[DafnyDefinitionSemanticFingerprint, ...]

    @cached_property
    def sources_by_path(self) -> dict[Path, tuple[DafnySourceSemanticFingerprint, ...]]:
        """Group source fingerprints by resolved absolute path."""

        found: dict[Path, list[DafnySourceSemanticFingerprint]] = {}
        for source in self.sources:
            found.setdefault(source.source_path.resolve(), []).append(source)
        return {path: tuple(items) for path, items in found.items()}

    @cached_property
    def definitions_by_key(
        self,
    ) -> dict[
        tuple[Path, str, DefinitionKind],
        tuple[DafnyDefinitionSemanticFingerprint, ...],
    ]:
        """Group definition fingerprints by resolved path, full name and kind."""

        found: dict[
            tuple[Path, str, DefinitionKind],
            list[DafnyDefinitionSemanticFingerprint],
        ] = {}
        for definition in self.definitions:
            key = (
                definition.source_path.resolve(),
                definition.full_name,
                definition.kind,
            )
            found.setdefault(key, []).append(definition)
        return {key: tuple(items) for key, items in found.items()}


class DafnyDefinitionProofInput(BaseModel):
    """Identify the complete native translation inputs for one declaration's proof."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: Path = Field(alias="sourcePath", strict=True)
    full_name: StrictStr = Field(alias="fullName")
    sha256: SHA256


class DafnyProofInputs(BaseModel):
    """Bind native proof-input fingerprints to their producer and translation policy."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    toolchain_sha256: SHA256 = Field(alias="toolchainSha256")
    options_sha256: SHA256 = Field(alias="optionsSha256")
    definitions: tuple[DafnyDefinitionProofInput, ...]


class DefinitionAttribute(BaseModel):
    """One authored attribute with its arguments and byte range."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    name: StrictStr
    arguments: tuple[StrictStr, ...]
    start: StrictInt
    end: StrictInt


class DefinitionVerificationTarget(BaseModel):
    """One native verification unit, including targets outside authored worklist goals."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    full_name: StrictStr = Field(alias="fullName")
    source_path: Path = Field(alias="sourcePath", strict=True)
    attributes: tuple[DefinitionAttribute, ...]


class DafnyProject(BaseModel):
    """Source-level facts emitted next to the definitions of one analysis run."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    modules: tuple[DefinitionAnalysisModule, ...]
    imports: tuple[DefinitionAnalysisImport, ...]
    includes: tuple[DefinitionAnalysisInclude, ...]
    semantic_facts: DafnySemanticFacts | None = Field(default=None, alias="semanticFacts")
    proof_inputs: DafnyProofInputs | None = Field(default=None, alias="proofInputs")
    verification_targets: tuple[DefinitionVerificationTarget, ...] | None = Field(
        default=None, alias="verificationTargets"
    )


class DefinitionFormal(BaseModel):
    """One formal parameter or return value with its type and ghost flag."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    name: StrictStr
    type: StrictStr
    ghost: StrictBool


class DefinitionStatement(BaseModel):
    """One resolved statement span with its kind and direct call targets."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    start: StrictInt
    end: StrictInt
    direct_call_targets: tuple[StrictStr, ...] = Field(alias="directCallTargets")


class DefinitionControlContext(BaseModel):
    """One enclosing control construct of a call site."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    start: StrictInt
    end: StrictInt
    branch_index: StrictInt = Field(alias="branchIndex")
    branch_count: StrictInt = Field(alias="branchCount")
    other_branch_statement_count: StrictInt = Field(alias="otherBranchStatementCount")
    guard: StrictStr
    invariants: tuple[StrictStr, ...]
    decreases: tuple[StrictStr, ...]


class DefinitionCallSite(BaseModel):
    """One resolved call with its arguments, assigned names and control path."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    arguments: tuple[StrictStr, ...]
    assigned_names: tuple[StrictStr, ...] = Field(alias="assignedNames")
    control_path: tuple[DefinitionControlContext, ...] = Field(alias="controlPath")


class DefinitionContractClause(BaseModel):
    """One requires or ensures clause with its syntactic facts."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    index: StrictInt
    text: StrictStr
    has_existential: StrictBool = Field(alias="hasExistential")
    has_old: StrictBool = Field(alias="hasOld")
    referenced_variables: tuple[StrictStr, ...] = Field(alias="referencedVariables")
    referenced_members: tuple[StrictStr, ...] = Field(alias="referencedMembers")
    index_selections: tuple[StrictStr, ...] = Field(alias="indexSelections")
    index_selection_count: StrictInt = Field(alias="indexSelectionCount")


class DefinitionMemberAssignment(BaseModel):
    """One assignment to a member of an object."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    start: StrictInt
    end: StrictInt
    target_full_name: StrictStr = Field(alias="targetFullName")
    receiver_type: StrictStr = Field(alias="receiverType")
    target_is_ghost: StrictBool = Field(alias="targetIsGhost")


class DefinitionPostconditionCall(BaseModel):
    """One call inside a postcondition, with the text of its source span."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    text: StrictStr
    arguments: tuple[StrictStr | None, ...]


class DefinitionPreconditionCall(BaseModel):
    """One call inside a precondition, with the text of its source span."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    text: StrictStr
    arguments: tuple[StrictStr | None, ...]


class DefinitionReference(BaseModel):
    """One resolved reference from a definition to another declaration."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    target_module: StrictStr = Field(alias="targetModule")
    target_kind: DefinitionKind = Field(alias="targetKind")
    is_pattern: StrictBool = Field(alias="isPattern")
    start: StrictInt
    end: StrictInt


class DefinitionSourceSpan(BaseModel):
    """Preserve a native declaration's half-open source byte range."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    start: StrictInt
    end: StrictInt


class DefinitionBodyVisibility(BaseModel):
    """Describe effective opacity and revealed bodies in a resolved proof context."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    referenced_declarations: tuple[StrictStr, ...] = Field(alias="referencedDeclarations")
    is_opaque: StrictBool = Field(alias="isOpaque")
    revealed_functions: tuple[StrictStr, ...] = Field(alias="revealedFunctions")
    reveals_all_functions: StrictBool = Field(alias="revealsAllFunctions")


class DefinitionInfo(BaseModel):
    """Resolved metadata of one Dafny declaration as reported by `definition-analysis`."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    name: StrictStr
    full_name: StrictStr = Field(alias="fullName")
    kind: DefinitionKind
    enclosing_name: StrictStr = Field(alias="enclosingName")
    line: StrictInt
    column: StrictInt
    start: StrictInt
    body_start: StrictInt | None = Field(alias="bodyStart")
    end: StrictInt
    source_path: Path = Field(alias="sourcePath", strict=True)
    ghost: StrictBool
    has_by_method: StrictBool = Field(alias="hasByMethod")
    has_loop: StrictBool = Field(alias="hasLoop")
    world_related: StrictBool = Field(alias="worldRelated")
    declaration_kind: StrictStr = Field(default="", alias="declarationKind")
    has_axiom_attribute: StrictBool = Field(default=False, alias="hasAxiomAttribute")
    has_extern_attribute: StrictBool = Field(default=False, alias="hasExternAttribute")
    has_verify_false_attribute: StrictBool = Field(
        default=False,
        alias="hasVerifyFalseAttribute",
    )
    attributes: tuple[DefinitionAttribute, ...] = ()
    has_assume_statement: StrictBool = Field(default=False, alias="hasAssumeStatement")
    has_var_declaration: StrictBool = Field(default=False, alias="hasVarDeclaration")
    statements: tuple[DefinitionStatement, ...] = ()
    member_assignments: tuple[DefinitionMemberAssignment, ...] = Field(
        default=(), alias="memberAssignments"
    )
    call_sites: tuple[DefinitionCallSite, ...] = Field(default=(), alias="callSites")
    contract_clauses: tuple[DefinitionContractClause, ...] = Field(
        default=(), alias="contractClauses"
    )
    body_shape: StrictStr = Field(default="", alias="bodyShape")
    has_broad_exit_range_disjunct: StrictBool = Field(
        default=False,
        alias="hasBroadExitRangeDisjunct",
    )
    type_parameters: tuple[StrictStr, ...] = Field(default=(), alias="typeParameters")
    type_parameter_names: tuple[StrictStr, ...] = Field(
        default=(),
        alias="typeParameterNames",
    )
    parameters: tuple[StrictStr, ...] = ()
    parameter_names: tuple[StrictStr, ...] = Field(default=(), alias="parameterNames")
    returns: tuple[StrictStr, ...]
    return_names: tuple[StrictStr, ...] = Field(alias="returnNames")
    requires: tuple[StrictStr, ...]
    ensures: tuple[StrictStr, ...]
    modifies: tuple[StrictStr, ...]
    parameter_details: tuple[DefinitionFormal, ...] = Field(default=(), alias="parameterDetails")
    return_details: tuple[DefinitionFormal, ...] = Field(default=(), alias="returnDetails")
    reads: tuple[StrictStr, ...] = ()
    decreases: tuple[StrictStr, ...] = ()
    source_modules: tuple[StrictStr, ...] = Field(default=(), alias="sourceModules")
    included_files: tuple[Annotated[Path, Strict()], ...] = Field(default=(), alias="includedFiles")
    local_included_modules: tuple[StrictStr, ...] = Field(
        default=(),
        alias="localIncludedModules",
    )
    imported_modules: tuple[StrictStr, ...] = Field(default=(), alias="importedModules")
    local_includes: tuple[DefinitionAnalysisInclude, ...] = Field(
        default=(),
        alias="localIncludes",
    )
    recursive: StrictBool
    recursive_group: tuple[StrictStr, ...] = Field(alias="recursiveGroup")
    callees: tuple[StrictStr, ...]
    call_sequence: tuple[StrictStr, ...] = Field(default=(), alias="callSequence")
    call_names: tuple[StrictStr, ...] = Field(default=(), alias="callNames")
    direct_precondition_callees: tuple[StrictStr, ...] = Field(
        default=(),
        alias="directPreconditionCallees",
    )
    direct_precondition_calls: tuple[DefinitionPreconditionCall, ...] = Field(
        default=(), alias="directPreconditionCalls"
    )
    direct_postcondition_callees: tuple[StrictStr, ...] = Field(
        default=(),
        alias="directPostconditionCallees",
    )
    direct_postcondition_calls: tuple[DefinitionPostconditionCall, ...] = Field(
        default=(), alias="directPostconditionCalls"
    )
    contract_header_without_axiom: StrictStr = Field(default="", alias="contractHeaderWithoutAxiom")
    contract_header_with_axiom: StrictStr = Field(default="", alias="contractHeaderWithAxiom")
    references: tuple[DefinitionReference, ...]
    dependencies: tuple[StrictStr, ...] = ()
    body_visibility: DefinitionBodyVisibility | None = Field(default=None, alias="bodyVisibility")
    children: tuple[DefinitionSourceSpan, ...] = ()
    source_group: DefinitionSourceSpan | None = Field(default=None, alias="sourceGroup")
    yield_requires: tuple[StrictStr, ...] = Field(default=(), alias="yieldRequires")
    yield_ensures: tuple[StrictStr, ...] = Field(default=(), alias="yieldEnsures")
    header_dependencies: tuple[StrictStr, ...] = Field(default=(), alias="headerDependencies")

    @field_validator("source_path", mode="before")
    @classmethod
    def _reject_empty_source_path(cls, value: object) -> object:
        """Reject an empty source spelling before Path normalizes it to the current directory."""

        if value == "":
            raise ValueError("sourcePath must not be empty")
        return value


DEFINITION_INFO_LIST = TypeAdapter(list[DefinitionInfo])


class DafnyDefinitions(DefinitionInfo):
    """Definition metadata from a run that always reports parameter details and contract headers."""

    parameter_details: tuple[DefinitionFormal, ...] = Field(alias="parameterDetails")
    return_details: tuple[DefinitionFormal, ...] = Field(alias="returnDetails")
    reads: tuple[StrictStr, ...] = ()
    decreases: tuple[StrictStr, ...] = ()
    direct_precondition_calls: tuple[DefinitionPreconditionCall, ...] = Field(
        alias="directPreconditionCalls"
    )
    direct_postcondition_calls: tuple[DefinitionPostconditionCall, ...] = Field(
        alias="directPostconditionCalls"
    )
    contract_header_without_axiom: StrictStr = Field(alias="contractHeaderWithoutAxiom")
    contract_header_with_axiom: StrictStr = Field(alias="contractHeaderWithAxiom")


class DafnyAnalysisResult(BaseModel):
    """Wrap definitions with the resolved source structure of one analysis run."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    definitions: tuple[DafnyDefinitions, ...]
    source_facts: DafnyProject = Field(alias="sourceFacts")


# Names used by the former Dafnyutils copy; both denote the Cosyn-derived models above.
DefinitionAnalysisDocument = DafnyAnalysisResult
DefinitionSourceFacts = DafnyProject
