"""Pure queries over Dafny analysis models."""

from __future__ import annotations

from collections.abc import Collection
from pathlib import Path

from .kinds import DefinitionKind
from .models import (
    DafnyDefinitionSemanticFingerprint,
    DafnyProject,
    DafnySourceSemanticFingerprint,
    DefinitionInfo,
)


def source_semantic_fingerprint(
    source_facts: DafnyProject,
    source_path: Path,
) -> DafnySourceSemanticFingerprint:
    """Return the unique source fingerprint for a path or raise ``ValueError``."""

    semantic_facts = source_facts.semantic_facts
    if semantic_facts is None:
        raise ValueError("Dafny source semantic fingerprints are missing")
    resolved = source_path.resolve()
    matches = semantic_facts.sources_by_path.get(resolved, ())
    if len(matches) != 1:
        raise ValueError(f"Dafny source semantic fingerprint is not unique: {source_path}")
    return matches[0]


def definition_semantic_fingerprint(
    source_facts: DafnyProject,
    definition: DefinitionInfo,
) -> DafnyDefinitionSemanticFingerprint:
    """Return the unique semantic fingerprint of a definition or raise ``ValueError``."""

    semantic_facts = source_facts.semantic_facts
    if semantic_facts is None:
        raise ValueError("Dafny definition semantic fingerprints are missing")
    source_path = definition.source_path.resolve()
    matches = semantic_facts.definitions_by_key.get(
        (source_path, definition.full_name, definition.kind),
        (),
    )
    if len(matches) != 1:
        raise ValueError(
            f"Dafny definition semantic fingerprint is not unique: {definition.full_name}"
        )
    return matches[0]


def _definition_infos_by_full_name(
    infos: Collection[DefinitionInfo],
) -> dict[str, DefinitionInfo]:
    by_full_name: dict[str, DefinitionInfo] = {}
    for info in infos:
        if info.full_name in by_full_name:
            raise RuntimeError(f"definition analysis emitted duplicate full name: {info.full_name}")
        by_full_name[info.full_name] = info
    return by_full_name


def spec_dependency_closure(
    infos: Collection[DefinitionInfo],
    *,
    source_paths: Collection[Path],
    spec_entries: Collection[tuple[Path, str]],
) -> tuple[DefinitionInfo, ...]:
    """Resolve configured specification dependency closures or fail closed."""
    allowed_paths = {path.resolve() for path in source_paths}
    resolved_entries = tuple(
        sorted(
            ((path.resolve(), full_name) for path, full_name in spec_entries),
            key=lambda item: (item[0].as_posix(), item[1]),
        )
    )
    if not resolved_entries:
        raise RuntimeError("specification entry set is empty")
    by_full_name = _definition_infos_by_full_name(infos)
    callable_kinds = {
        DefinitionKind.FUNCTION,
        DefinitionKind.PREDICATE,
        DefinitionKind.TWOSTATE_FUNCTION,
        DefinitionKind.TWOSTATE_PREDICATE,
        DefinitionKind.LEAST_PREDICATE,
        DefinitionKind.GREATEST_PREDICATE,
    }
    roots: list[DefinitionInfo] = []
    for source_path, full_name in resolved_entries:
        if source_path not in allowed_paths:
            raise RuntimeError(
                f"specification entry source is outside selected sources: {source_path}"
            )
        root = by_full_name.get(full_name)
        if root is None or root.source_path != source_path or root.kind not in callable_kinds:
            raise RuntimeError(
                "configured specification entry does not resolve to a callable specification "
                f"definition in its source: {full_name}"
            )
        roots.append(root)

    return definition_dependency_closure(
        infos, source_paths=source_paths, root_symbols={root.full_name for root in roots}
    )


def definition_dependency_closure(
    infos: Collection[DefinitionInfo],
    *,
    source_paths: Collection[Path],
    root_symbols: Collection[str],
    boundary_symbols: Collection[str] = (),
) -> tuple[DefinitionInfo, ...]:
    """Follow authored declarations up to already-retained source boundaries."""
    allowed_paths = {path.resolve() for path in source_paths}
    by_full_name = _definition_infos_by_full_name(infos)
    boundaries = set(boundary_symbols)
    closure: dict[str, DefinitionInfo] = {}
    pending = sorted(set(root_symbols), reverse=True)
    while pending:
        full_name = pending.pop()
        if full_name in closure or full_name in boundaries:
            continue
        info = by_full_name.get(full_name)
        if info is None:
            raise RuntimeError(f"unresolved definition dependency: {full_name}")
        if info.source_path not in allowed_paths:
            raise RuntimeError(f"definition dependency outside selected sources: {full_name}")
        closure[full_name] = info
        pending.extend(sorted(info.dependencies, reverse=True))
        pending.extend(
            sorted(
                {
                    reference.target_full_name
                    for reference in info.references
                    if reference.target_full_name in by_full_name
                },
                reverse=True,
            )
        )
    return tuple(closure[name] for name in sorted(closure))


def definition_text(source_text: str, info: DefinitionInfo) -> str:
    """Return a definition's source text with trailing whitespace removed."""

    return source_byte_span_text(source_text, info.start, info.end).rstrip()


def source_byte_span_text(source_text: str, start: int, end: int) -> str:
    """Slice source text by the UTF-8 byte offsets that Dafny reports."""

    return source_text.encode("utf-8")[start:end].decode("utf-8")


def normalized_signature(source_text: str, info: DefinitionInfo) -> str:
    """Return a definition header with the leading ``ghost`` keyword and spacing normalized."""

    end = info.body_start if info.body_start is not None else info.end
    header = source_byte_span_text(source_text, info.start, end).strip()
    if header.startswith("ghost"):
        rest = header[len("ghost") :]
        if not rest or rest[0].isspace():
            header = rest.lstrip()
    return " ".join(header.split())
