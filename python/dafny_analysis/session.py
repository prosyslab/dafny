"""Execution-owned, bounded JSONL transport for native Dafny analysis sessions.

The native process owns source discovery and all reuse decisions. This client
correlates requests, validates provenance, and preserves the existing runner API.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import queue
import signal
import subprocess
import sys
import threading
import time
import uuid
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path
from typing import Annotated, Any, Literal

from pydantic import BaseModel, ConfigDict, Field, StrictBool, StrictInt, StrictStr, field_validator

from .models import SHA256
from .runner import DafnyInvocation

MAX_REQUEST_BYTES = 8 * 1024 * 1024
# Bounds one response JSON line, newline excluded (matches the native ResponseLimit).
MAX_RESPONSE_BYTES = 128 * 1024 * 1024
MAX_PENDING_REQUESTS = 8
_STDERR_BYTES = 64 * 1024
_POLL_SECONDS = 0.02
_CLOSE_SECONDS = 1.0


class NativeSessionError(RuntimeError):
    """Identify an operational failure of the native session boundary."""


class SessionUnsupportedError(NativeSessionError):
    """Identify an operation the native session explicitly does not support."""


class SessionProtocolError(NativeSessionError):
    """Identify malformed, stale, or inconsistent native session evidence."""


class SessionClosedError(NativeSessionError):
    """Identify use of a closed session or an unexpectedly closed transport."""


class SessionCancelledError(NativeSessionError):
    """Identify cancellation of one caller's request."""


class NativeOutcome(StrEnum):
    COMPLETED = "completed"
    CANCELLED = "cancelled"
    ERROR = "error"


_Count = Annotated[StrictInt, Field(ge=0)]
_SNAPSHOT_OPERATIONS = ("clone", "export-session", "import-session")


class NativeTimings(BaseModel):
    """Request-local measured durations; absent phases were not observed."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    compilation_reused: StrictBool | None = Field(alias="compilationReused")
    durations_seconds: dict[Literal["admission_wait", "compiler_wait", "parse", "resolve",
                                   "proof_input_preparation", "analysis", "translation",
                                   "vc_preparation", "solver_runtime"], float] = Field(alias="durationsSeconds")

    @field_validator("schema_version")
    @classmethod
    def _supported_schema(cls, value: int) -> int:
        if value != 1:
            raise ValueError("unsupported timing schema version")
        return value

    @field_validator("durations_seconds", mode="before")
    @classmethod
    def _valid_durations(cls, value: Any) -> Any:
        if not isinstance(value, dict) or any(
            type(duration) not in (int, float)
            or duration < 0
            or duration > sys.float_info.max
            or not math.isfinite(duration)
            for duration in value.values()
        ):
            raise ValueError("timing durations must be finite nonnegative numbers")
        return value


class NativeEvidence(BaseModel):
    """Native provenance and observed reuse counters, without host inference."""

    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    session_epoch: StrictStr = Field(alias="sessionEpoch", min_length=1)
    session_id: StrictStr | None = Field(default=None, alias="sessionId", min_length=1)
    generation: _Count
    source_identity: SHA256 = Field(alias="sourceIdentity")
    context_id: StrictStr = Field(alias="contextId")
    options_identity: SHA256 = Field(alias="optionsIdentity")
    toolchain_identity: SHA256 | None = Field(alias="toolchainIdentity")
    consumed_inputs: dict[StrictStr, SHA256] = Field(alias="consumedInputs")
    completed: StrictBool
    outcome: NativeOutcome
    task_count: _Count = Field(alias="taskCount")
    cache_hit_count: _Count = Field(alias="cacheHitCount")
    solver_run_count: _Count = Field(alias="solverRunCount")
    analysis_module_hits: _Count = Field(alias="analysisModuleHits")
    analysis_module_misses: _Count = Field(alias="analysisModuleMisses")
    timings: NativeTimings | None = None
    # Session-cumulative retention counters; absent from older native executables.
    result_cache_clears: _Count | None = Field(default=None, alias="resultCacheClears")
    result_cache_evictions: _Count | None = Field(default=None, alias="resultCacheEvictions")
    resolver_evictions: _Count | None = Field(default=None, alias="resolverEvictions")

    @field_validator("schema_version")
    @classmethod
    def _supported_schema(cls, value: int) -> int:
        if value != 1:
            raise ValueError("unsupported native evidence schema version")
        return value

    @field_validator("session_epoch")
    @classmethod
    def _valid_epoch(cls, value: str) -> str:
        uuid.UUID(value)
        return value


class CloneReceipt(BaseModel):
    """Native observations from one completed cache snapshot."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    daemon_epoch: StrictStr = Field(alias="daemonEpoch")
    parent_id: StrictStr = Field(alias="parentId", min_length=1)
    parent_epoch: StrictStr = Field(alias="parentEpoch")
    session_id: StrictStr = Field(alias="sessionId", min_length=1)
    session_epoch: StrictStr = Field(alias="sessionEpoch")
    parsed_entries: _Count = Field(alias="parsedEntries")
    verification_entries: _Count = Field(alias="verificationEntries")

    @field_validator("schema_version")
    @classmethod
    def _supported_schema(cls, value: int) -> int:
        if value != 1:
            raise ValueError("unsupported clone receipt schema version")
        return value

    @field_validator("daemon_epoch", "parent_epoch", "session_epoch")
    @classmethod
    def _valid_epoch(cls, value: str) -> str:
        uuid.UUID(value)
        return value


class ImportReceipt(BaseModel):
    """Native observations from one completed session import."""

    model_config = ConfigDict(extra="forbid", frozen=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    daemon_epoch: StrictStr = Field(alias="daemonEpoch")
    session_id: StrictStr = Field(alias="sessionId", min_length=1)
    session_epoch: StrictStr = Field(alias="sessionEpoch")
    parsed_entries: _Count = Field(alias="parsedEntries")
    verification_entries: _Count = Field(alias="verificationEntries")

    @field_validator("schema_version")
    @classmethod
    def _supported_schema(cls, value: int) -> int:
        if value != 1:
            raise ValueError("unsupported import receipt schema version")
        return value

    @field_validator("daemon_epoch", "session_epoch")
    @classmethod
    def _valid_epoch(cls, value: str) -> str:
        uuid.UUID(value)
        return value


class _ExportHeader(BaseModel):
    """The identity fields of an export document the client checks before handing it on.

    The rest of the document is validated by the importing native process.
    """

    model_config = ConfigDict(extra="allow", frozen=True)

    schema_version: StrictInt = Field(alias="schemaVersion")
    daemon_epoch: StrictStr = Field(alias="daemonEpoch")
    session_id: StrictStr = Field(alias="sessionId", min_length=1)
    session_epoch: StrictStr = Field(alias="sessionEpoch")
    toolchain: SHA256

    @field_validator("schema_version")
    @classmethod
    def _supported_schema(cls, value: int) -> int:
        if value != 1:
            raise ValueError("unsupported export document schema version")
        return value

    @field_validator("daemon_epoch", "session_epoch")
    @classmethod
    def _valid_epoch(cls, value: str) -> str:
        uuid.UUID(value)
        return value


@dataclass
class _Branch:
    session_id: str
    context_id: str
    epoch: str | None = None
    generation: int = 0
    closed: bool = False
    close_done: threading.Event = field(default_factory=threading.Event)
    close_error: NativeSessionError | None = None


@dataclass
class _Control:
    operation: str
    branch: _Branch
    target: _Branch | None = None
    ready: threading.Event = field(default_factory=threading.Event)
    response: _Response | None = None
    receipt: CloneReceipt | ImportReceipt | None = None
    exported: str | None = None
    error: NativeSessionError | None = None


class _Response(BaseModel):
    model_config = ConfigDict(extra="forbid")

    id: StrictStr
    returncode: StrictInt
    stdout: StrictStr
    stderr: StrictStr
    nativeEvidence: NativeEvidence | None


class NativeSessionCompletedProcess(subprocess.CompletedProcess[str]):
    """A runner-compatible result with required, validated native evidence."""

    native_evidence: NativeEvidence

    def __init__(self, arguments: Sequence[str], response: _Response, stdout: str) -> None:
        super().__init__(list(arguments), response.returncode, stdout, response.stderr)
        if response.nativeEvidence is None:
            raise SessionProtocolError("native job response omitted evidence")
        self.native_evidence = response.nativeEvidence


@dataclass
class _Pending:
    branch: _Branch
    generation: int
    snapshot_hashes: dict[str, str]
    ready: threading.Event = field(default_factory=threading.Event)
    finished: threading.Event = field(default_factory=threading.Event)
    response: _Response | None = None
    error: NativeSessionError | None = None
    abandoned: bool = False


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


class _SessionTransport:
    """Own one native process; share it between callers until ``close``.

    ``command`` is the executable prefix, without ``analysis-session``. A timeout
    raises ``NativeSessionError`` caused by ``subprocess.TimeoutExpired``, matching
    ``DafnyCommandRunner``. Timeout and cancellation target only the owned request.
    Admission, frames, queued writes, diagnostics, and shutdown waits are bounded.
    ``max_pending`` may lower the native eight-request admission limit.
    """

    def __init__(
        self,
        command: Sequence[str],
        *,
        cwd: Path,
        env: Mapping[str, str] | None = None,
        max_pending: int = 8,
        source_root: Path | None = None,
        logical_root: Path | None = None,
        branch: _Branch,
    ) -> None:
        if not command or isinstance(command, str):
            raise ValueError("command must be a nonempty executable sequence")
        if type(max_pending) is not int or not 1 <= max_pending <= MAX_PENDING_REQUESTS:
            raise ValueError(f"max_pending must be between 1 and {MAX_PENDING_REQUESTS}")
        if (source_root is None) != (logical_root is None):
            raise ValueError("source_root and logical_root must be supplied together")
        self._command = (*command, "analysis-session")
        self._cwd = Path(os.path.abspath(cwd))
        self._env = None if env is None else dict(env)
        self._max_pending = max_pending
        self._source_root = None if source_root is None else Path(os.path.abspath(source_root))
        self._logical_root = None if logical_root is None else Path(os.path.abspath(logical_root))
        self._condition = threading.Condition()
        self._pending: dict[str, _Pending] = {}
        self._controls: dict[str, _Control] = {}
        self._branches = {branch.session_id: branch}
        self._daemon_epoch: str | None = None
        self._failure: NativeSessionError | None = None
        self._closed = False
        self._stopped = threading.Event()
        self._close_done = threading.Event()
        self._close_error: NativeSessionError | None = None
        self._stderr = b""
        self._writes: queue.Queue[bytes | None] = queue.Queue(
            maxsize=2 * max_pending + MAX_PENDING_REQUESTS + 2
        )
        try:
            self._process = subprocess.Popen(
                self._command,
                cwd=self._cwd,
                env=self._env,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=-1,
                start_new_session=os.name == "posix",
            )
        except OSError as exc:
            raise NativeSessionError("could not start native Dafny session") from exc
        self._threads = (
            threading.Thread(target=self._write_loop, daemon=True, name="dafny-session-write"),
            threading.Thread(target=self._read_loop, daemon=True, name="dafny-session-read"),
            threading.Thread(target=self._stderr_loop, daemon=True, name="dafny-session-stderr"),
        )
        for thread in self._threads:
            thread.start()

    def run(
        self,
        branch: _Branch,
        invocation: DafnyInvocation,
        *,
        source_snapshots: Mapping[Path, str] | None = None,
        generation: int | None = None,
        source_root: Path | None = None,
        logical_root: Path | None = None,
    ) -> NativeSessionCompletedProcess:
        """Submit one native job; never replace native errors with one-shot execution."""

        if not invocation.arguments or invocation.arguments[0] not in {
            "definition-analysis",
            "verify",
            "resolve",
        }:
            raise SessionUnsupportedError(
                "native session supports definition-analysis, resolve, verify"
            )
        if invocation.source_text is not None or "--stdin" in invocation.arguments:
            raise SessionUnsupportedError("native session requires path-based source snapshots")
        if invocation.env is not None and dict(invocation.env) != self._env:
            raise SessionUnsupportedError("native session cannot change its process environment")
        if generation is not None and (type(generation) is not int or generation < 0):
            raise ValueError("generation must be a nonnegative integer")
        if (source_root is None) != (logical_root is None):
            raise ValueError("source_root and logical_root must be supplied together")
        roots = (
            self._source_root if source_root is None else Path(os.path.abspath(source_root)),
            self._logical_root if logical_root is None else Path(os.path.abspath(logical_root)),
        )
        deadline = time.monotonic() + invocation.timeout_seconds
        snapshots = (
            None
            if source_snapshots is None
            else self._snapshot_aliases(source_snapshots, invocation.cwd)
        )
        snapshot_hashes = {
            path: hashlib.sha256(text.encode("utf-8")).hexdigest()
            for path, text in (snapshots or {}).items()
        }
        request_id = uuid.uuid4().hex
        with self._condition:
            while self._normal_count() >= self._max_pending:
                self._check_open(branch)
                self._check_wait(invocation, deadline)
                self._condition.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic())))
            self._check_open(branch)
            self._check_wait(invocation, deadline)
            if generation is None:
                branch.generation += 1
                generation = branch.generation
            else:
                branch.generation = max(branch.generation, generation)
            pending = _Pending(branch, generation, snapshot_hashes)
            frame = self._frame(
                {
                    "id": request_id,
                    # Native option arities distinguish roots from filter,
                    # report, and solver values that resemble source filenames.
                    "arguments": list(invocation.arguments),
                    "cwd": os.path.abspath(invocation.cwd),
                    "contextId": branch.context_id,
                    "sessionId": branch.session_id,
                    "sourceSnapshots": snapshots,
                    "generation": generation,
                    "profileTimings": True,
                    "sourceRoot": None if roots[0] is None else str(roots[0]),
                    "logicalRoot": None if roots[1] is None else str(roots[1]),
                }
            )
            self._pending[request_id] = pending
            self._enqueue(frame)
        try:
            while not pending.ready.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic()))):
                self._check_wait(invocation, deadline)
            if pending.error is not None:
                raise pending.error
            response = pending.response
            if response is None:
                raise SessionProtocolError("native request finished without a response")
            if response.returncode == 7 and "DAFNY_SESSION_UNSUPPORTED:" in response.stderr:
                raise SessionUnsupportedError(response.stderr)
            stdout = response.stdout
            if invocation.arguments[0] == "definition-analysis":
                stdout = self._remap_analysis(stdout, roots)
            return NativeSessionCompletedProcess(invocation.arguments, response, stdout)
        except (NativeSessionError, subprocess.TimeoutExpired):
            if not pending.finished.is_set():
                try:
                    if not pending.ready.is_set():
                        self._cancel(request_id, pending)
                finally:
                    # Transport failure can clear the request between the ready
                    # check and _cancel. Always await physical cleanup in that race.
                    if not pending.finished.is_set():
                        if self._failure is not None:
                            self.close()
                        elif not pending.finished.wait(_CLOSE_SECONDS):
                            self._fail(
                                NativeSessionError("native request did not physically drain")
                            )
                            self.close()
            raise

    @staticmethod
    def _absolute(path: Path, cwd: Path) -> Path:
        return Path(os.path.abspath(path if path.is_absolute() else cwd / path))

    @staticmethod
    def _canonical(path: Path) -> str:
        try:
            return str(path.resolve())
        except (OSError, RuntimeError) as exc:
            raise SessionProtocolError("could not resolve native source snapshot identity") from exc

    @classmethod
    def _snapshot_aliases(cls, sources: Mapping[Path, str], cwd: Path) -> dict[str, str]:
        snapshots: dict[str, str] = {}
        for path, text in sources.items():
            absolute = cls._absolute(path, cwd)
            # Native Path.GetFullPath preserves lexical symlink aliases. Keep
            # those keys as well as the canonical fallback for other native reads.
            for alias in (str(absolute), cls._canonical(absolute)):
                if alias in snapshots and snapshots[alias] != text:
                    raise SessionProtocolError(
                        "conflicting source snapshots refer to the same file"
                    )
                snapshots[alias] = text
        return snapshots

    @staticmethod
    def _map_path(
        value: str, roots: tuple[Path | None, Path | None], *, reverse: bool = False
    ) -> str:
        source, target = roots
        if reverse:
            source, target = target, source
        if source is None or target is None or not Path(value).is_absolute():
            return value
        try:
            relative = Path(value).relative_to(source)
        except ValueError:
            return value
        return str(target / relative)

    def _remap_analysis(self, stdout: str, roots: tuple[Path | None, Path | None]) -> str:
        if roots[0] is None:
            return stdout
        try:
            document = json.loads(stdout)
        except (ValueError, RecursionError):
            return stdout

        def remap(value: Any, key: str = "") -> Any:
            if isinstance(value, dict):
                return {name: remap(item, name) for name, item in value.items()}
            if isinstance(value, list):
                return [remap(item, key) for item in value]
            if isinstance(value, str) and key in {
                "sourcePath",
                "targetPath",
                "resolvedTargetSourcePath",
                "includedFiles",
            }:
                return self._map_path(value, roots, reverse=True)
            return value

        return json.dumps(remap(document), ensure_ascii=False)

    @staticmethod
    def _frame(document: dict[str, Any]) -> bytes:
        frame = (json.dumps(document, ensure_ascii=False, separators=(",", ":")) + "\n").encode(
            "utf-8"
        )
        if len(frame) > MAX_REQUEST_BYTES:
            raise SessionProtocolError("native request exceeds the JSONL byte limit")
        return frame

    def _enqueue(self, frame: bytes) -> None:
        try:
            self._writes.put_nowait(frame)
        except queue.Full as exc:
            error = NativeSessionError("native session write queue is full")
            self._fail(error)
            raise error from exc

    def _check_open(self, branch: _Branch) -> None:
        if self._failure is not None:
            raise self._failure
        if self._closed or branch.closed:
            raise SessionClosedError("native session is closed")

    @staticmethod
    def _check_wait(invocation: DafnyInvocation, deadline: float) -> None:
        if invocation.cancel_event is not None and invocation.cancel_event.is_set():
            raise SessionCancelledError(f"cancelled {invocation.operation}")
        if time.monotonic() >= deadline:
            cause = subprocess.TimeoutExpired(invocation.arguments, invocation.timeout_seconds)
            raise NativeSessionError(f"timed out {invocation.operation}") from cause

    def _control_count(self, operation: str) -> int:
        return sum(control.operation == operation for control in self._controls.values())

    def _normal_count(self) -> int:
        # Native jobs and cache snapshots/transfers share the daemon's normal request lane.
        return len(self._pending) + sum(self._control_count(name) for name in _SNAPSHOT_OPERATIONS)

    def _request_cancel(self, request_id: str, branch: _Branch) -> None:
        # Clone/close controls cannot consume the space reserved for cancel ACKs.
        if self._control_count("cancel") >= self._max_pending:
            error = SessionProtocolError("native session did not acknowledge cancellation")
            self._fail(error)
            raise error
        control_id = uuid.uuid4().hex
        frame = self._frame(
            {
                "id": control_id,
                "operation": "cancel",
                "sessionId": branch.session_id,
                "targetId": request_id,
            }
        )
        self._controls[control_id] = _Control("cancel", branch)
        try:
            self._enqueue(frame)
        except NativeSessionError:
            self._controls.pop(control_id, None)
            raise

    def _cancel(self, request_id: str, pending: _Pending) -> None:
        with self._condition:
            if request_id not in self._pending or self._closed or self._failure is not None:
                return
            pending.abandoned = True
            self._request_cancel(request_id, pending.branch)
        # A control acknowledgement does not prove that native file reads stopped.
        # Keep the caller's snapshots alive until the original operation drains.
        if not pending.finished.wait(_CLOSE_SECONDS):
            self._fail(NativeSessionError("native cancellation did not drain; stopping session"))
            self.close()

    def _fail(self, error: NativeSessionError) -> None:
        with self._condition:
            if self._failure is None:
                self._failure = error
            for pending in self._pending.values():
                pending.error = self._failure
                pending.ready.set()
            for control in self._controls.values():
                control.error = self._failure
                control.ready.set()
            self._condition.notify_all()

    def _write_loop(self) -> None:
        stream = self._process.stdin
        assert stream is not None
        try:
            while (frame := self._writes.get()) is not None:
                remaining = memoryview(frame)
                while remaining:
                    written = stream.write(remaining)
                    if written is None or written <= 0:
                        raise OSError("native session accepted no request bytes")
                    remaining = remaining[written:]
                stream.flush()
        except (OSError, ValueError) as exc:
            self._fail(NativeSessionError(f"native session write failed: {exc}"))
            self.close()

    def _read_loop(self) -> None:
        stream = self._process.stdout
        assert stream is not None
        try:
            while True:
                frame = stream.readline(MAX_RESPONSE_BYTES + 2)
                if not frame:
                    with self._condition:
                        if self._closed:
                            return
                        diagnostic = self._stderr.decode("utf-8", errors="replace")
                    raise SessionClosedError(f"native session reached EOF: {diagnostic}")
                if len(frame) > MAX_RESPONSE_BYTES + 1 or not frame.endswith(b"\n"):
                    raise SessionProtocolError("native response exceeds limit or is not JSONL")
                response = _Response.model_validate(
                    json.loads(frame.decode("utf-8"), object_pairs_hook=_unique_object)
                )
                self._receive(response)
        except NativeSessionError as exc:
            self._fail(exc)
        except (OSError, ValueError, RecursionError) as exc:
            self._fail(SessionProtocolError(f"invalid native session response: {str(exc)[:4096]}"))
        finally:
            if self._failure is not None:
                self.close()

    def _receive(self, response: _Response) -> None:
        with self._condition:
            if self._closed:
                return
            control = self._controls.pop(response.id, None)
            if control is not None:
                self._receive_control(control, response)
                return
            pending = self._pending.get(response.id)
            if pending is None:
                raise SessionProtocolError("native response has an unknown or stale request id")
            evidence = response.nativeEvidence
            if evidence is None:
                raise SessionProtocolError("native job response omitted evidence")
            branch = pending.branch
            if evidence.session_id != branch.session_id and not (
                branch.session_id == "default" and evidence.session_id is None
            ):
                raise SessionProtocolError("native response has stale or missing session id")
            if (
                evidence.context_id != branch.context_id
                or evidence.generation != pending.generation
            ):
                raise SessionProtocolError("native response has stale context or generation")
            if branch.epoch is None:
                branch.epoch = evidence.session_epoch
            elif evidence.session_epoch != branch.epoch:
                raise SessionProtocolError("native session epoch changed")
            if response.returncode == 0 and (
                not evidence.completed or evidence.outcome != NativeOutcome.COMPLETED
            ):
                raise SessionProtocolError("native success has incomplete evidence")
            for path, digest in evidence.consumed_inputs.items():
                if not Path(path).is_absolute():
                    raise SessionProtocolError("native consumed input path is not absolute")
                expected = pending.snapshot_hashes.get(path)
                if expected is None and pending.snapshot_hashes:
                    expected = pending.snapshot_hashes.get(self._canonical(Path(path)))
                if expected is not None and digest != expected:
                    raise SessionProtocolError("native response consumed a stale source snapshot")
            del self._pending[response.id]
            pending.finished.set()
            if not pending.abandoned:
                pending.response = response
                pending.ready.set()
            self._condition.notify_all()

    def _receive_control(self, control: _Control, response: _Response) -> None:
        try:
            if response.returncode == 7 and "DAFNY_SESSION_UNSUPPORTED:" in response.stderr:
                control.error = SessionUnsupportedError(response.stderr)
            elif response.returncode != 0:
                control.error = NativeSessionError(
                    f"native {control.operation} failed ({response.returncode}): {response.stderr}"
                )
            elif response.nativeEvidence is not None:
                if control.operation in _SNAPSHOT_OPERATIONS:
                    raise SessionUnsupportedError(
                        f"native daemon does not support {control.operation} controls"
                    )
                raise SessionProtocolError("invalid native session control acknowledgement")
            elif control.operation == "clone":
                receipt = CloneReceipt.model_validate(
                    json.loads(response.stdout, object_pairs_hook=_unique_object)
                )
                parent, target = control.branch, control.target
                assert target is not None
                if (
                    receipt.parent_id != parent.session_id
                    or receipt.session_id != target.session_id
                ):
                    raise SessionProtocolError("clone receipt has wrong parent or child session id")
                if parent.epoch is not None and receipt.parent_epoch != parent.epoch:
                    raise SessionProtocolError("clone receipt has stale parent epoch")
                if self._daemon_epoch is not None and receipt.daemon_epoch != self._daemon_epoch:
                    raise SessionProtocolError("clone receipt has changed daemon epoch")
                if receipt.session_epoch == receipt.parent_epoch or any(
                    item is not target and item.epoch == receipt.session_epoch
                    for item in self._branches.values()
                ):
                    raise SessionProtocolError("clone receipt reused a session epoch")
                parent.epoch = receipt.parent_epoch
                target.epoch = receipt.session_epoch
                self._daemon_epoch = receipt.daemon_epoch
                control.receipt = receipt
            elif control.operation == "export-session":
                header = _ExportHeader.model_validate(
                    json.loads(response.stdout, object_pairs_hook=_unique_object)
                )
                source = control.branch
                if header.session_id != source.session_id:
                    raise SessionProtocolError("export document has the wrong session id")
                if source.epoch is not None and header.session_epoch != source.epoch:
                    raise SessionProtocolError("export document has a stale session epoch")
                if self._daemon_epoch is not None and header.daemon_epoch != self._daemon_epoch:
                    raise SessionProtocolError("export document has changed daemon epoch")
                source.epoch = header.session_epoch
                self._daemon_epoch = header.daemon_epoch
                control.exported = response.stdout
            elif control.operation == "import-session":
                imported = ImportReceipt.model_validate(
                    json.loads(response.stdout, object_pairs_hook=_unique_object)
                )
                target_branch = control.branch
                if imported.session_id != target_branch.session_id:
                    raise SessionProtocolError("import receipt has the wrong session id")
                if self._daemon_epoch is not None and imported.daemon_epoch != self._daemon_epoch:
                    raise SessionProtocolError("import receipt has changed daemon epoch")
                if any(
                    item is not target_branch and item.epoch == imported.session_epoch
                    for item in self._branches.values()
                ):
                    raise SessionProtocolError("import receipt reused a session epoch")
                target_branch.epoch = imported.session_epoch
                self._daemon_epoch = imported.daemon_epoch
                control.receipt = imported
            if control.error is not None and control.operation == "cancel":
                raise control.error
            control.response = response
        except (ValueError, RecursionError) as exc:
            error = SessionProtocolError(
                f"invalid native {control.operation} response: {str(exc)[:4096]}"
            )
            control.error = error
            self._fail(error)
            raise error from exc
        except NativeSessionError as exc:
            control.error = exc
            self._fail(exc)
            raise
        finally:
            control.ready.set()
            self._condition.notify_all()

    def _control(
        self,
        operation: str,
        branch: _Branch,
        target: _Branch | None = None,
        payload: str | None = None,
    ) -> tuple[str, _Control]:
        control_id = uuid.uuid4().hex
        control = _Control(operation, branch, target)
        document = {"id": control_id, "operation": operation, "sessionId": branch.session_id}
        if target is not None:
            document["targetId"] = target.session_id
        if payload is not None:
            document["payload"] = payload
        # Build the frame first: an oversized payload must not leave a registered control behind.
        frame = self._frame(document)
        self._controls[control_id] = control
        try:
            self._enqueue(frame)
        except NativeSessionError:
            self._controls.pop(control_id, None)
            raise
        return control_id, control

    def clone(
        self, branch: _Branch, *, timeout_seconds: float, cancel_event: threading.Event | None
    ) -> tuple[_Branch, CloneReceipt]:
        if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be finite and positive")
        invocation = DafnyInvocation(
            arguments=("clone",),
            cwd=self._cwd,
            operation="clone native session",
            timeout_seconds=timeout_seconds,
            cancel_event=cancel_event,
        )
        deadline = time.monotonic() + timeout_seconds
        with self._condition:
            while self._normal_count() >= self._max_pending:
                self._check_open(branch)
                self._check_wait(invocation, deadline)
                self._condition.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic())))
            self._check_open(branch)
            self._check_wait(invocation, deadline)
            target = _Branch(uuid.uuid4().hex, branch.context_id)
            self._branches[target.session_id] = target
            try:
                control_id, control = self._control("clone", branch, target)
            except NativeSessionError:
                self._branches.pop(target.session_id)
                raise
        try:
            while not control.ready.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic()))):
                self._check_wait(invocation, deadline)
            self._check_wait(invocation, deadline)
            if control.error is not None:
                raise control.error
            with self._condition:
                self._check_open(branch)
            if not isinstance(control.receipt, CloneReceipt):
                raise SessionProtocolError("native clone completed without a receipt")
            return target, control.receipt
        except NativeSessionError:
            # Drain the original clone, even when its cancel ACK arrives first.
            if not control.ready.is_set() and self._failure is None:
                try:
                    with self._condition:
                        if not control.ready.is_set():
                            self._request_cancel(control_id, branch)
                except NativeSessionError:
                    # Preserve the original cancellation while physically stopping
                    # a transport whose cancellation lane failed.
                    self.close()
                if not control.ready.wait(_CLOSE_SECONDS):
                    self._fail(NativeSessionError("native clone cancellation did not drain"))
                    self.close()
            if self._failure is not None:
                self.close()
            if control.receipt is not None and self._failure is None:
                self.close_branch(target)
            else:
                with self._condition:
                    target.closed = True
                    target.close_done.set()
                    self._branches.pop(target.session_id, None)
                    last_owner = not self._branches
                if last_owner:
                    self.close()
            raise

    def transfer(
        self,
        operation: str,
        branch: _Branch,
        *,
        payload: str | None,
        timeout_seconds: float,
        cancel_event: threading.Event | None,
    ) -> _Control:
        """Run one export-session or import-session control, admitted and drained like clone."""
        if not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be finite and positive")
        invocation = DafnyInvocation(
            arguments=(operation,),
            cwd=self._cwd,
            operation=f"{operation} native session",
            timeout_seconds=timeout_seconds,
            cancel_event=cancel_event,
        )
        deadline = time.monotonic() + timeout_seconds
        with self._condition:
            while self._normal_count() >= self._max_pending:
                self._check_open(branch)
                self._check_wait(invocation, deadline)
                self._condition.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic())))
            self._check_open(branch)
            self._check_wait(invocation, deadline)
            control_id, control = self._control(operation, branch, payload=payload)
        try:
            while not control.ready.wait(min(_POLL_SECONDS, max(0, deadline - time.monotonic()))):
                self._check_wait(invocation, deadline)
            self._check_wait(invocation, deadline)
            if control.error is not None:
                raise control.error
            with self._condition:
                self._check_open(branch)
            return control
        except NativeSessionError:
            # Drain the original control, even when its cancel ACK arrives first. A transfer
            # that completes late changes only cache contents the native side re-validates.
            if not control.ready.is_set() and self._failure is None:
                try:
                    with self._condition:
                        if not control.ready.is_set():
                            self._request_cancel(control_id, branch)
                except NativeSessionError:
                    self.close()
                if not control.ready.wait(_CLOSE_SECONDS):
                    self._fail(NativeSessionError(f"native {operation} cancellation did not drain"))
                    self.close()
            if self._failure is not None:
                self.close()
            raise

    def export_session(
        self, branch: _Branch, *, timeout_seconds: float, cancel_event: threading.Event | None
    ) -> bytes:
        control = self.transfer(
            "export-session",
            branch,
            payload=None,
            timeout_seconds=timeout_seconds,
            cancel_event=cancel_event,
        )
        if control.exported is None:
            raise SessionProtocolError("native export completed without a document")
        return control.exported.encode("utf-8")

    def import_session(
        self,
        branch: _Branch,
        payload: bytes,
        *,
        timeout_seconds: float,
        cancel_event: threading.Event | None,
    ) -> ImportReceipt:
        try:
            text = payload.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValueError("payload must be the UTF-8 document from export_session") from exc
        control = self.transfer(
            "import-session",
            branch,
            payload=text,
            timeout_seconds=timeout_seconds,
            cancel_event=cancel_event,
        )
        if not isinstance(control.receipt, ImportReceipt):
            raise SessionProtocolError("native import completed without a receipt")
        return control.receipt

    def close_branch(self, branch: _Branch) -> None:
        final_owner = False
        pending: list[_Pending] = []
        with self._condition:
            if branch.closed:
                owns_close = False
            else:
                branch.closed = True
                owns_close = True
                # Reserved clone targets count as owners until cleanup completes.
                final_owner = len(self._branches) == 1
                pending = [item for item in self._pending.values() if item.branch is branch]
                for item in pending:
                    item.error = item.error or SessionClosedError(
                        "native session closed during request"
                    )
                    item.ready.set()
                self._condition.notify_all()
        if not owns_close:
            if not branch.close_done.wait(4 * _CLOSE_SECONDS + 0.5):
                raise NativeSessionError("native branch close did not complete")
            if branch.close_error is not None:
                raise branch.close_error
            return
        try:
            if final_owner or self._failure is not None:
                self.close()
            else:
                deadline = time.monotonic() + _CLOSE_SECONDS
                with self._condition:
                    while self._control_count("close-session") >= MAX_PENDING_REQUESTS:
                        if self._failure is not None:
                            raise self._failure
                        remaining = deadline - time.monotonic()
                        if remaining <= 0:
                            raise NativeSessionError("native branch close admission timed out")
                        self._condition.wait(min(_POLL_SECONDS, remaining))
                    if self._failure is not None:
                        raise self._failure
                    _, control = self._control("close-session", branch)
                if not control.ready.wait(max(0, deadline - time.monotonic())):
                    raise NativeSessionError("native branch close did not drain")
                if control.error is not None:
                    raise control.error
                for item in pending:
                    if not item.finished.wait(max(0, deadline - time.monotonic())):
                        raise NativeSessionError(
                            "native branch close omitted terminal job response"
                        )
        except NativeSessionError as exc:
            branch.close_error = exc
            self._fail(exc)
            self.close()
            raise
        finally:
            with self._condition:
                self._branches.pop(branch.session_id, None)
                # Concurrent closes can both observe another owner before release.
                last_owner = not self._branches
            try:
                if last_owner and not self._closed:
                    self.close()
            finally:
                branch.close_done.set()

    def _stderr_loop(self) -> None:
        stream = self._process.stderr
        assert stream is not None
        try:
            while chunk := stream.read(4096):
                with self._condition:
                    self._stderr = (self._stderr + chunk)[-_STDERR_BYTES:]
        except (OSError, ValueError):
            return

    def close(self) -> None:
        """Drain briefly, then terminate and reap the owned process within bounds."""

        with self._condition:
            if self._closed:
                owns_close = False
            else:
                self._closed = True
                owns_close = True
        if not owns_close:
            if threading.current_thread() in self._threads:
                return
            if not self._close_done.wait(3 * _CLOSE_SECONDS + 0.5):
                raise NativeSessionError("native session shutdown did not complete")
            if self._close_error is not None:
                raise self._close_error
            if not self._stopped.is_set():
                raise NativeSessionError("native worker did not physically stop")
            return
        with self._condition:
            for pending in self._pending.values():
                pending.error = pending.error or SessionClosedError(
                    "native session closed during request"
                )
                pending.ready.set()
            self._condition.notify_all()
            control_id = uuid.uuid4().hex
            self._controls[control_id] = _Control("shutdown", _Branch("", ""))
            try:
                self._writes.put_nowait(self._frame({"id": control_id, "operation": "shutdown"}))
            except queue.Full:
                pass
        try:
            self._stop_worker()
            try:
                self._writes.put_nowait(None)
            except queue.Full:
                pass
            for thread in self._threads:
                if thread is not threading.current_thread():
                    thread.join(timeout=0.1)
            if self._process.stdin is not None:
                try:
                    self._process.stdin.close()
                except BrokenPipeError:
                    # The reaped worker left request bytes unflushed; the stream is closed anyway.
                    pass
            for stream in (self._process.stdout, self._process.stderr):
                if stream is not None:
                    stream.close()
            with self._condition:
                for pending in self._pending.values():
                    pending.finished.set()
                self._pending.clear()
            self._stopped.set()
        except (OSError, subprocess.TimeoutExpired) as exc:
            # Retain the process/stream references when physical teardown failed.
            self._close_error = NativeSessionError("could not stop and reap native worker")
            raise self._close_error from exc
        finally:
            self._close_done.set()

    def _stop_worker(self) -> None:
        try:
            if self._failure is not None:
                self._signal_worker(force=False)
            try:
                self._process.wait(timeout=_CLOSE_SECONDS)
            except subprocess.TimeoutExpired:
                self._signal_worker(force=False)
                try:
                    self._process.wait(timeout=_CLOSE_SECONDS)
                except subprocess.TimeoutExpired:
                    self._signal_worker(force=True)
                    self._process.wait(timeout=_CLOSE_SECONDS)
        finally:
            # The leader can exit while solver descendants still own the group.
            # Kill that owned group even when waiting for the leader succeeded.
            if os.name == "posix":
                self._signal_worker(force=True)

    def _signal_worker(self, *, force: bool) -> None:
        try:
            if os.name == "posix":
                os.killpg(self._process.pid, signal.SIGKILL if force else signal.SIGTERM)
            elif force:
                self._process.kill()
            else:
                self._process.terminate()
        except ProcessLookupError:
            pass


class NativeDafnySession:
    """An independent native branch sharing a bounded, reference-counted daemon.

    ``command`` omits ``analysis-session``. Clones inherit native cache snapshots;
    each handle retains independent generation, cancellation and close ownership.
    A daemon failure explicitly fails every handle sharing that daemon.
    """

    def __init__(
        self,
        command: Sequence[str],
        *,
        cwd: Path,
        env: Mapping[str, str] | None = None,
        context_id: str = "default",
        max_pending: int = 8,
        source_root: Path | None = None,
        logical_root: Path | None = None,
    ) -> None:
        self._branch = _Branch("default", context_id)
        self._transport = _SessionTransport(
            command,
            cwd=cwd,
            env=env,
            max_pending=max_pending,
            source_root=source_root,
            logical_root=logical_root,
            branch=self._branch,
        )
        self.clone_receipt: CloneReceipt | None = None
        self.import_receipt: ImportReceipt | None = None

    def __enter__(self) -> NativeDafnySession:
        return self

    def __exit__(self, *_: object) -> None:
        self.close()

    def __call__(self, invocation: DafnyInvocation) -> NativeSessionCompletedProcess:
        return self.run(invocation)

    def run(
        self,
        invocation: DafnyInvocation,
        *,
        source_snapshots: Mapping[Path, str] | None = None,
        generation: int | None = None,
        source_root: Path | None = None,
        logical_root: Path | None = None,
    ) -> NativeSessionCompletedProcess:
        return self._transport.run(
            self._branch,
            invocation,
            source_snapshots=source_snapshots,
            generation=generation,
            source_root=source_root,
            logical_root=logical_root,
        )

    def clone(
        self, *, timeout_seconds: float, cancel_event: threading.Event | None = None
    ) -> NativeDafnySession:
        branch, receipt = self._transport.clone(
            self._branch, timeout_seconds=timeout_seconds, cancel_event=cancel_event
        )
        child = object.__new__(NativeDafnySession)
        child._branch = branch
        child._transport = self._transport
        child.clone_receipt = receipt
        child.import_receipt = None
        return child

    def export_session(
        self, *, timeout_seconds: float, cancel_event: threading.Event | None = None
    ) -> bytes:
        """Return this branch's reusable caches as one bounded document for ``import_session``.

        The branch is unchanged. The bytes stay in memory with the caller; they are the exact
        UTF-8 document the native process produced; only an identical toolchain accepts it.
        """
        return self._transport.export_session(
            self._branch, timeout_seconds=timeout_seconds, cancel_event=cancel_event
        )

    def import_session(
        self,
        payload: bytes,
        *,
        timeout_seconds: float,
        cancel_event: threading.Event | None = None,
    ) -> ImportReceipt:
        """Install an exported document into this fresh native process before any other request.

        The native side validates toolchain, keys and shapes and imports nothing on failure, which
        raises ``NativeSessionError``. A success leaves results reusable only where native checksum
        lookup still matches.
        """
        receipt = self._transport.import_session(
            self._branch, payload, timeout_seconds=timeout_seconds, cancel_event=cancel_event
        )
        self.import_receipt = receipt
        return receipt

    def close(self) -> None:
        self._transport.close_branch(self._branch)
