"""Bounded native-session contracts through in-memory byte/process boundaries."""

from __future__ import annotations

import hashlib
import json
import os
import queue
import signal
import subprocess
import threading
from collections.abc import Callable, Iterator
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

import pytest

from dafny_analysis import session as session_module
from dafny_analysis.runner import DafnyInvocation
from dafny_analysis.session import (
    NativeDafnySession,
    NativeEvidence,
    NativeSessionError,
    SessionCancelledError,
    SessionClosedError,
    SessionProtocolError,
    SessionUnsupportedError,
)

_HEX = "a" * 64
_CWD = Path("/actual")


class _Pipe:
    def __init__(self) -> None:
        self.chunks: queue.Queue[bytes] = queue.Queue()
        self.remainder = b""

    def readline(self, limit: int) -> bytes:
        chunk = self.remainder or self.chunks.get(timeout=5)
        self.remainder = chunk[limit:]
        return chunk[:limit]

    def read(self, limit: int) -> bytes:
        return self.readline(limit)

    def close(self) -> None:
        self.chunks.put(b"")


class _Input:
    def __init__(self, receive: Callable[[dict[str, Any]], None]) -> None:
        self.receive = receive
        self.buffer = b""

    def write(self, data: bytes) -> int:
        self.buffer += bytes(data)
        while b"\n" in self.buffer:
            frame, self.buffer = self.buffer.split(b"\n", 1)
            self.receive(json.loads(frame))
        return len(data)

    def flush(self) -> None:
        pass

    def close(self) -> None:
        pass


class _Process:
    def __init__(self, respond: Callable[[_Process, dict[str, Any]], None]) -> None:
        self.stdout = _Pipe()
        self.stderr = _Pipe()
        self.stdin = _Input(self.receive)
        self.respond = respond
        self.requests: list[dict[str, Any]] = []
        self.jobs: queue.Queue[dict[str, Any]] = queue.Queue()
        self.exited = threading.Event()
        self.terminated = False
        self.killed = False
        self.ignore_shutdown = False
        self.ignore_terminate = False
        self.pid = 12345
        self.orphaned_solver = False
        self.group_signals: list[int] = []

    def receive(self, request: dict[str, Any]) -> None:
        self.requests.append(request)
        if request.get("operation") == "shutdown":
            if self.ignore_shutdown:
                return
            self.control_response(request)
            self.finish()
        else:
            if "operation" not in request:
                self.jobs.put(request)
            self.respond(self, request)

    def control_response(self, request: dict[str, Any]) -> None:
        self.emit(
            {
                "id": request["id"],
                "returncode": 0,
                "stdout": "",
                "stderr": "",
                "nativeEvidence": None,
            }
        )

    def emit(self, response: dict[str, Any]) -> None:
        self.stdout.chunks.put((json.dumps(response) + "\n").encode())

    def finish(self) -> None:
        self.exited.set()
        self.stdout.close()
        self.stderr.close()

    def wait(self, timeout: float) -> int:
        if not self.exited.wait(timeout):
            raise subprocess.TimeoutExpired("fake-native", timeout)
        return 0

    def terminate(self) -> None:
        self.terminated = True
        if not self.ignore_terminate:
            self.finish()

    def kill(self) -> None:
        self.killed = True
        self.finish()


def _response(request: dict[str, Any], **updates: Any) -> dict[str, Any]:
    evidence = {
        "schemaVersion": 1,
        "sessionEpoch": "e" * 32,
        "generation": request["generation"],
        "sourceIdentity": _HEX,
        "contextId": request["contextId"],
        "optionsIdentity": _HEX,
        "toolchainIdentity": None,
        "consumedInputs": {},
        "completed": True,
        "outcome": "completed",
        "taskCount": 2,
        "cacheHitCount": 1,
        "solverRunCount": 1,
        "analysisModuleHits": 1,
        "analysisModuleMisses": 1,
    }
    if request.get("sessionId", "default") != "default":
        evidence["sessionId"] = request["sessionId"]
        evidence["sessionEpoch"] = request["sessionId"]
    evidence.update(updates)
    return {
        "id": request["id"],
        "returncode": 0,
        "stdout": "native output",
        "stderr": "native diagnostic",
        "nativeEvidence": evidence,
    }


def _invocation(
    *arguments: str, timeout: float = 2, cancel: threading.Event | None = None
) -> DafnyInvocation:
    return DafnyInvocation(
        arguments=tuple(arguments) or ("verify", "/actual/A.dfy"),
        cwd=_CWD,
        operation="test native job",
        timeout_seconds=timeout,
        cancel_event=cancel,
    )


@pytest.fixture
def make_session(
    monkeypatch: pytest.MonkeyPatch,
) -> Iterator[Callable[..., tuple[NativeDafnySession, _Process]]]:
    sessions: list[NativeDafnySession] = []

    def create(
        respond: Callable[[_Process, dict[str, Any]], None] | None = None, **kwargs: Any
    ) -> tuple[NativeDafnySession, _Process]:
        peer = _Process(respond or (lambda process, request: process.emit(_response(request))))

        def popen(command: tuple[str, ...], **options: Any) -> _Process:
            assert command == ("native", "analysis-session")
            assert options["cwd"] == _CWD
            assert options["stdin"] == subprocess.PIPE
            assert options["start_new_session"] == (os.name == "posix")
            return peer

        monkeypatch.setattr(subprocess, "Popen", popen)
        if os.name == "posix":

            def killpg(pid: int, sig: int) -> None:
                assert pid == peer.pid
                peer.group_signals.append(sig)
                if peer.exited.is_set() and not peer.orphaned_solver:
                    raise ProcessLookupError
                if sig == signal.SIGKILL:
                    peer.orphaned_solver = False
                    peer.kill()
                else:
                    peer.terminate()

            monkeypatch.setattr(os, "killpg", killpg)
        native = NativeDafnySession(["native"], cwd=_CWD, **kwargs)
        sessions.append(native)
        return native, peer

    yield create
    for native in sessions:
        native.close()


@pytest.fixture
def source_aliases(monkeypatch: pytest.MonkeyPatch) -> None:
    def resolve(path: Path, strict: bool = False) -> Path:
        for alias in (Path("/alias"), Path("/other-alias")):
            if path.is_relative_to(alias):
                return Path("/real") / path.relative_to(alias)
        return path

    monkeypatch.setattr(Path, "resolve", resolve)


# A native result preserves existing runner output and adds typed provenance.
def test_result_has_typed_evidence_and_preserves_diagnostics(
    make_session: Callable[..., Any],
) -> None:
    native, peer = make_session()
    result = native(_invocation())
    assert result.returncode == 0
    assert result.stdout == "native output"
    assert result.stderr == "native diagnostic"
    assert isinstance(result.native_evidence, NativeEvidence)
    assert result.native_evidence.cache_hit_count == 1
    assert result.native_evidence.model_dump(by_alias=True)["generation"] == 1
    native.close()
    assert peer.requests[-1]["operation"] == "shutdown"


# Retention counters are optional: older executables omit them, newer ones report them.
def test_retention_counters_are_optional_typed_evidence(make_session: Callable[..., Any]) -> None:
    native, _ = make_session()
    assert native(_invocation()).native_evidence.result_cache_clears is None
    native.close()
    counters = {"resultCacheClears": 2, "resultCacheEvictions": 1, "resolverEvictions": 0}
    native, _ = make_session(lambda process, request: process.emit(_response(request, **counters)))
    evidence = native(_invocation()).native_evidence
    assert (evidence.result_cache_clears, evidence.result_cache_evictions) == (2, 1)
    assert evidence.resolver_evictions == 0
    native.close()
    native, peer = make_session(
        lambda process, request: process.emit(_response(request, resultCacheClears=-1))
    )
    with pytest.raises(SessionProtocolError):
        native(_invocation())
    assert peer.exited.is_set()


# Native owns argument mapping; only known analysis path fields change in output.
def test_per_request_mapping_preserves_source_text_and_actual_evidence(
    make_session: Callable[..., Any],
) -> None:
    source = 'method A() { print "/logical/A.dfy"; }'
    digest = hashlib.sha256(source.encode()).hexdigest()

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        response = _response(request, consumedInputs={"/actual/A.dfy": digest})
        response["stdout"] = json.dumps(
            {
                "definitions": [
                    {
                        "sourcePath": "/logical/A.dfy",
                        "includedFiles": ["/logical/Library.dfy"],
                        "body": source,
                    }
                ],
                "sourceFacts": {"includes": [{"targetPath": "/logical/Library.dfy"}]},
            }
        )
        peer.emit(response)

    native, peer = make_session(respond)
    result = native.run(
        _invocation("definition-analysis", "A.dfy", "--filter-symbol", "/logical/A"),
        source_snapshots={Path("A.dfy"): source},
        generation=7,
        source_root=_CWD,
        logical_root=Path("/logical"),
    )
    request = peer.jobs.get(timeout=1)
    assert request["arguments"] == [
        "definition-analysis",
        "A.dfy",
        "--filter-symbol",
        "/logical/A",
    ]
    assert request["cwd"] == "/actual"
    assert request["sourceRoot"] == "/actual"
    assert request["logicalRoot"] == "/logical"
    assert request["sourceSnapshots"] == {"/actual/A.dfy": source}
    document = json.loads(result.stdout)
    assert document["definitions"][0]["sourcePath"] == "/actual/A.dfy"
    assert document["definitions"][0]["body"] == source
    assert document["definitions"][0]["includedFiles"] == ["/actual/Library.dfy"]
    assert document["sourceFacts"]["includes"][0]["targetPath"] == "/actual/Library.dfy"
    assert result.native_evidence.consumed_inputs == {"/actual/A.dfy": digest}


# Constructor mapping remains the default for callers that do not override it.
def test_constructor_mapping_supports_resolve(make_session: Callable[..., Any]) -> None:
    native, peer = make_session(source_root=_CWD, logical_root=Path("/logical"))
    native.run(_invocation("resolve", "project.toml", "A.dfy", "library.doo"))
    request = peer.jobs.get(timeout=1)
    assert request["arguments"] == [
        "resolve",
        "project.toml",
        "A.dfy",
        "library.doo",
    ]
    assert request["sourceRoot"] == "/actual"
    assert request["logicalRoot"] == "/logical"


# Native receives relative roots together with the caller's actual working directory.
def test_relative_source_roots_and_cwd_are_forwarded(make_session: Callable[..., Any]) -> None:
    native, peer = make_session()
    invocation = DafnyInvocation(
        arguments=("resolve", "A.dfy"),
        cwd=Path("/different"),
        operation="resolve relative source",
        timeout_seconds=2,
    )
    native.run(invocation)
    request = peer.jobs.get(timeout=1)
    assert request["arguments"] == ["resolve", "A.dfy"]
    assert request["cwd"] == "/different"


# Supplied aliases and canonical reads both use the caller's exact snapshot text.
@pytest.mark.parametrize("consumed_path", ["/alias/A.dfy", "/real/A.dfy"])
def test_snapshot_alias_and_canonical_bindings_are_preserved(
    make_session: Callable[..., Any], source_aliases: None, consumed_path: str
) -> None:
    supplied = "method A() { assert true; }"
    stale_disk = "method A() { assert false; }"

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        text = request["sourceSnapshots"].get(consumed_path, stale_disk)
        response = _response(
            request, consumedInputs={consumed_path: hashlib.sha256(text.encode()).hexdigest()}
        )
        response["stdout"] = text
        peer.emit(response)

    native, peer = make_session()
    peer.respond = respond
    invocation = DafnyInvocation(
        arguments=("resolve", "A.dfy"),
        cwd=Path("/alias"),
        operation="resolve supplied alias",
        timeout_seconds=2,
    )
    result = native.run(
        invocation,
        source_snapshots={Path("A.dfy"): supplied},
        source_root=Path("/alias"),
        logical_root=Path("/logical"),
    )
    request = peer.jobs.get(timeout=1)
    assert request["cwd"] == "/alias"
    assert request["sourceRoot"] == "/alias"
    assert request["sourceSnapshots"] == {
        "/alias/A.dfy": supplied,
        "/real/A.dfy": supplied,
    }
    assert result.stdout == supplied


# Conflicting aliases cannot silently replace another snapshot for the same file.
def test_conflicting_snapshot_aliases_reject_before_submission(
    make_session: Callable[..., Any], source_aliases: None
) -> None:
    native, peer = make_session()
    with pytest.raises(SessionProtocolError, match="conflicting source snapshots"):
        native.run(
            _invocation(),
            source_snapshots={Path("/alias/A.dfy"): "first", Path("/real/A.dfy"): "second"},
        )
    assert not peer.requests


# A consumed third alias must still match the supplied canonical snapshot digest.
def test_unlisted_consumed_alias_rejects_stale_snapshot(
    make_session: Callable[..., Any], source_aliases: None
) -> None:
    native, peer = make_session(
        lambda process, request: process.emit(
            _response(request, consumedInputs={"/other-alias/A.dfy": _HEX})
        )
    )
    with pytest.raises(SessionProtocolError, match="stale source snapshot"):
        native.run(_invocation(), source_snapshots={Path("/alias/A.dfy"): "supplied"})
    assert peer.exited.is_set()


# Client admission cannot exceed the native protocol's fixed eight-request bound.
@pytest.mark.parametrize("max_pending", [0, 9, True])
def test_pending_limit_rejects_unsupported_capacity(
    make_session: Callable[..., Any], max_pending: int
) -> None:
    with pytest.raises(ValueError, match="between 1 and 8"):
        make_session(max_pending=max_pending)


# Filename-looking nonpath option values are never rewritten by the transport.
@pytest.mark.parametrize(
    "option,value",
    [
        ("--filter-symbol", "Module.dfy"),
        ("--log-format", "trx;LogFileName=foo.dfy"),
        ("--solver-option", "trace_file_name=foo.dfy"),
    ],
)
def test_filename_like_option_values_are_preserved(
    make_session: Callable[..., Any], option: str, value: str
) -> None:
    native, peer = make_session(source_root=_CWD, logical_root=Path("/logical"))
    arguments = ("verify", "A.dfy", option, value)
    native.run(_invocation(*arguments))
    assert peer.jobs.get(timeout=1)["arguments"] == list(arguments)


# Unsupported commands are explicit and never reach the native process.
def test_source_fingerprint_is_explicitly_unsupported(make_session: Callable[..., Any]) -> None:
    native, peer = make_session()
    with pytest.raises(SessionUnsupportedError):
        native.run(_invocation("source-fingerprint"))
    assert not peer.requests


# Native feature rejection remains distinct from operational failures.
def test_native_unsupported_marker_has_typed_exception(make_session: Callable[..., Any]) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        response = _response(request, completed=False, outcome="error")
        response.update(returncode=7, stderr="DAFNY_SESSION_UNSUPPORTED: custom option")
        peer.emit(response)

    native, _ = make_session(respond)
    with pytest.raises(SessionUnsupportedError, match="custom option"):
        native.run(_invocation())


# Nonzero verification exits preserve native stdout and evidence for host policy.
def test_native_verification_failure_is_returned(make_session: Callable[..., Any]) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        response = _response(request)
        response["returncode"] = 4
        peer.emit(response)

    native, _ = make_session(respond)
    assert native.run(_invocation()).returncode == 4


# Invalid provenance cannot become a successful runner result.
@pytest.mark.parametrize(
    "updates",
    [
        {"schemaVersion": 2},
        {"schemaVersion": True},
        {"sessionEpoch": "malformed"},
        {"generation": 999},
        {"contextId": "other"},
        {"completed": False},
        {"outcome": "cancelled"},
        {"cacheHitCount": -1},
        {"consumedInputs": {"relative.dfy": _HEX}},
        {"consumedInputs": {"/actual/A.dfy": _HEX}},
    ],
)
def test_invalid_evidence_fails_closed(
    make_session: Callable[..., Any], updates: dict[str, Any]
) -> None:
    native, peer = make_session(
        lambda process, request: process.emit(_response(request, **updates))
    )
    with pytest.raises(SessionProtocolError):
        native.run(_invocation(), source_snapshots={Path("/actual/A.dfy"): "method A() {}"})
    assert peer.exited.is_set()


# A changed native epoch cannot satisfy a later request in the same session.
def test_epoch_change_is_rejected(make_session: Callable[..., Any]) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        peer.emit(_response(request, sessionEpoch=f"{request['generation']:032x}"))

    native, _ = make_session(respond)
    native.run(_invocation())
    with pytest.raises(SessionProtocolError, match="epoch"):
        native.run(_invocation())


# Unknown IDs, malformed frames and missing evidence wake the waiting caller.
@pytest.mark.parametrize("malformation", ["id", "json", "duplicate", "missing", "truncated"])
def test_bad_response_terminates_transport(
    make_session: Callable[..., Any], malformation: str
) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        response = _response(request)
        if malformation == "id":
            response["id"] = "stale-request"
        elif malformation == "missing":
            response["nativeEvidence"] = None
        elif malformation == "json":
            peer.stdout.chunks.put(b"not json\n")
            return
        elif malformation == "duplicate":
            peer.stdout.chunks.put(b'{"id":"first","id":"second"}\n')
            return
        elif malformation == "truncated":
            peer.stdout.chunks.put(b'{"id":"truncated"}')
            return
        peer.emit(response)

    native, peer = make_session(respond)
    with pytest.raises(SessionProtocolError):
        native.run(_invocation())
    assert peer.exited.is_set()


# Frame limits are checked at byte boundaries without allocating large fixtures.
def test_request_byte_limit_prevents_submission(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    native, peer = make_session()
    monkeypatch.setattr(session_module, "MAX_REQUEST_BYTES", 512)
    with pytest.raises(SessionProtocolError, match="byte limit"):
        native.run(_invocation(), source_snapshots={Path("/actual/A.dfy"): "x" * 512})
    assert not peer.requests


# The native response reader applies a hard per-frame byte bound.
def test_response_byte_limit_fails_closed(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(session_module, "MAX_RESPONSE_BYTES", 128)
    native, _ = make_session()
    with pytest.raises(SessionProtocolError, match="limit"):
        native.run(_invocation())


# Process EOF fails a pending request instead of leaving a waiter blocked.
def test_process_eof_wakes_waiter(make_session: Callable[..., Any]) -> None:
    native, peer = make_session(lambda process, request: process.finish())
    with pytest.raises(SessionClosedError, match="EOF"):
        native.run(_invocation())
    assert peer.exited.is_set()


# Out-of-order replies still satisfy exactly their owning callers.
@pytest.mark.integration
def test_concurrent_requests_correlate_by_id(make_session: Callable[..., Any]) -> None:
    native, peer = make_session(lambda process, request: None)
    with ThreadPoolExecutor(max_workers=2) as pool:
        first = pool.submit(native.run, _invocation("verify", "/actual/First.dfy"))
        first_request = peer.jobs.get(timeout=1)
        second = pool.submit(native.run, _invocation("verify", "/actual/Second.dfy"))
        second_request = peer.jobs.get(timeout=1)
        second_response = _response(second_request)
        second_response["stdout"] = "second"
        peer.emit(second_response)
        first_response = _response(first_request)
        first_response["stdout"] = "first"
        peer.emit(first_response)
        assert first.result(timeout=1).stdout == "first"
        assert second.result(timeout=1).stdout == "second"


# A timed-out job drains its own terminal response and leaves another job intact.
@pytest.mark.integration
def test_timeout_cancels_only_owned_request_and_drains(make_session: Callable[..., Any]) -> None:
    requests: dict[str, dict[str, Any]] = {}

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "cancel":
            peer.control_response(request)
            response = _response(
                requests[request["targetId"]], completed=False, outcome="cancelled"
            )
            response["returncode"] = 7
            peer.emit(response)
        else:
            requests[request["id"]] = request

    native, peer = make_session(respond)
    with ThreadPoolExecutor(max_workers=2) as pool:
        first = pool.submit(native.run, _invocation(timeout=0.1))
        first_request = peer.jobs.get(timeout=1)
        second = pool.submit(native.run, _invocation("resolve", "/actual/Other.dfy"))
        second_request = peer.jobs.get(timeout=1)
        with pytest.raises(NativeSessionError) as caught:
            first.result(timeout=1)
        assert isinstance(caught.value.__cause__, subprocess.TimeoutExpired)
        cancels = [request for request in peer.requests if request.get("operation") == "cancel"]
        assert [request["targetId"] for request in cancels] == [first_request["id"]]
        assert not peer.exited.is_set()
        peer.emit(_response(second_request))
        assert second.result(timeout=1).returncode == 0


# A cancel acknowledgement alone cannot release the source snapshot lifetime.
@pytest.mark.integration
def test_cancel_waits_for_original_terminal_response(make_session: Callable[..., Any]) -> None:
    cancelled: queue.Queue[dict[str, Any]] = queue.Queue()

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "cancel":
            peer.control_response(request)
            cancelled.put(request)

    native, peer = make_session(respond)
    cancel = threading.Event()
    with ThreadPoolExecutor(max_workers=1) as pool:
        result = pool.submit(native.run, _invocation(cancel=cancel))
        request = peer.jobs.get(timeout=1)
        cancel.set()
        cancelled.get(timeout=1)
        assert not result.done()
        response = _response(request, completed=False, outcome="cancelled")
        response["returncode"] = 7
        peer.emit(response)
        with pytest.raises(SessionCancelledError):
            result.result(timeout=1)


# Failure to drain one cancelled job stops the worker and wakes every owner.
@pytest.mark.integration
def test_cancel_drain_failure_stops_worker_and_other_waiter(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(session_module, "_CLOSE_SECONDS", 0.05)

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "cancel":
            peer.control_response(request)

    native, peer = make_session(respond)
    cancel = threading.Event()
    with ThreadPoolExecutor(max_workers=2) as pool:
        first = pool.submit(native.run, _invocation(cancel=cancel))
        peer.jobs.get(timeout=1)
        second = pool.submit(native.run, _invocation())
        peer.jobs.get(timeout=1)
        cancel.set()
        with pytest.raises(SessionCancelledError):
            first.result(timeout=1)
        with pytest.raises(NativeSessionError):
            second.result(timeout=1)
    assert peer.exited.is_set()


# Admission bounds pending work and a waiting caller never cancels admitted work.
@pytest.mark.integration
def test_pending_bound_times_out_before_submission(make_session: Callable[..., Any]) -> None:
    native, peer = make_session(lambda process, request: None, max_pending=1)
    with ThreadPoolExecutor(max_workers=1) as pool:
        first = pool.submit(native.run, _invocation())
        request = peer.jobs.get(timeout=1)
        with pytest.raises(NativeSessionError) as caught:
            native.run(_invocation(timeout=0.05))
        assert isinstance(caught.value.__cause__, subprocess.TimeoutExpired)
        assert len(peer.requests) == 1
        peer.emit(_response(request))
        assert first.result(timeout=1).returncode == 0


# Closing is idempotent and prevents future native requests.
def test_closed_session_rejects_new_work(make_session: Callable[..., Any]) -> None:
    native, _ = make_session()
    native.close()
    native.close()
    with pytest.raises(SessionClosedError):
        native.run(_invocation())


# An unresponsive worker is killed and reaped after both bounded shutdown stages.
@pytest.mark.integration
def test_close_escalates_to_kill_after_bounded_grace(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(session_module, "_CLOSE_SECONDS", 0.02)
    native, peer = make_session()
    peer.ignore_shutdown = True
    peer.ignore_terminate = True
    native.close()
    assert peer.terminated
    assert peer.killed
    assert peer.exited.is_set()


# EOF cleanup kills the owned group even when its native leader already exited.
@pytest.mark.integration
def test_eof_stops_orphaned_solver_group(make_session: Callable[..., Any]) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        peer.orphaned_solver = True
        peer.finish()

    native, peer = make_session(respond)
    with pytest.raises(SessionClosedError):
        native.run(_invocation())
    assert peer.group_signals == [signal.SIGTERM, signal.SIGKILL]
    assert not peer.orphaned_solver


# Poisoning between the ready check and cancellation still waits for worker cleanup.
@pytest.mark.integration
def test_cancel_transport_failure_race_waits_for_physical_stop(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    cancel = threading.Event()
    native, peer = make_session(lambda process, request: cancel.set())
    original_cancel = native._transport._cancel

    def fail_before_cancel(request_id: str, pending: Any) -> None:
        native._transport._fail(SessionProtocolError("simulated reader failure"))
        original_cancel(request_id, pending)

    monkeypatch.setattr(native._transport, "_cancel", fail_before_cancel)
    with pytest.raises(SessionCancelledError):
        native.run(_invocation(cancel=cancel))
    assert peer.exited.is_set()
    assert native._transport._stopped.is_set()


def _clone_receipt(request: dict[str, Any], **updates: Any) -> dict[str, Any]:
    receipt = {
        "schemaVersion": 1,
        "daemonEpoch": "d" * 32,
        "parentId": request["sessionId"],
        "parentEpoch": "e" * 32 if request["sessionId"] == "default" else request["sessionId"],
        "sessionId": request["targetId"],
        "sessionEpoch": request["targetId"],
        "parsedEntries": 3,
        "verificationEntries": 2,
    }
    receipt.update(updates)
    return receipt


def _branch_daemon(peer: _Process, request: dict[str, Any]) -> None:
    operation = request.get("operation")
    if operation == "clone":
        peer.emit(
            {
                "id": request["id"],
                "returncode": 0,
                "stdout": json.dumps(_clone_receipt(request)),
                "stderr": "",
                "nativeEvidence": None,
            }
        )
    elif operation in {"close-session", "cancel"}:
        peer.control_response(request)
    else:
        peer.emit(_response(request))


# Native receipts create two independently routed children without replaying jobs.
def test_two_clones_inherit_receipts_and_keep_parent_usable(
    make_session: Callable[..., Any],
) -> None:
    parent, peer = make_session(_branch_daemon, context_id="verification")
    parent.run(_invocation())
    first = parent.clone(timeout_seconds=1)
    second = parent.clone(timeout_seconds=1)
    try:
        assert len([item for item in peer.requests if "arguments" in item]) == 1
        assert first.clone_receipt is not None and second.clone_receipt is not None
        assert first.clone_receipt.parsed_entries == 3
        assert first.clone_receipt.verification_entries == 2
        assert first.clone_receipt.session_id != second.clone_receipt.session_id
        assert first.run(_invocation()).native_evidence.generation == 1
        assert second.run(_invocation()).native_evidence.generation == 1
        assert parent.run(_invocation()).native_evidence.generation == 2
        assert {item["contextId"] for item in peer.requests if "arguments" in item} == {
            "verification"
        }
    finally:
        first.close()
        second.close()
    assert not peer.exited.is_set()


# Every close order preserves surviving branches and shuts down only the last owner.
@pytest.mark.parametrize("order", [(0, 1, 2), (1, 0, 2), (2, 1, 0)])
def test_cloned_branch_close_order_preserves_other_handles(
    make_session: Callable[..., Any], order: tuple[int, int, int]
) -> None:
    parent, peer = make_session(_branch_daemon)
    handles = [parent, parent.clone(timeout_seconds=1), parent.clone(timeout_seconds=1)]
    for offset, index in enumerate(order):
        handles[index].close()
        handles[index].close()
        with pytest.raises(SessionClosedError):
            handles[index].run(_invocation())
        if offset < 2:
            assert not peer.exited.is_set()
            for survivor in order[offset + 1 :]:
                assert handles[survivor].run(_invocation()).returncode == 0
    assert peer.exited.is_set()
    assert sum(item.get("operation") == "shutdown" for item in peer.requests) == 1
    assert sum(item.get("operation") == "close-session" for item in peer.requests) == 2


# Strict receipts fence wrong branch identities, stale epochs, invalid counts and extra fields.
@pytest.mark.parametrize(
    "updates",
    [
        {"schemaVersion": 2},
        {"parsedEntries": -1},
        {"verificationEntries": True},
        {"daemonEpoch": "bad"},
        {"parentId": "other"},
        {"sessionId": "other"},
        {"parentEpoch": "f" * 32},
        {"sessionEpoch": "e" * 32},
        {"extra": 1},
    ],
)
def test_invalid_clone_receipt_fails_shared_transport(
    make_session: Callable[..., Any], updates: dict[str, Any]
) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "clone":
            peer.emit(
                {
                    "id": request["id"],
                    "returncode": 0,
                    "stdout": json.dumps(_clone_receipt(request, **updates)),
                    "stderr": "",
                    "nativeEvidence": None,
                }
            )
        else:
            _branch_daemon(peer, request)

    parent, peer = make_session(respond)
    parent.run(_invocation())
    with pytest.raises(SessionProtocolError):
        parent.clone(timeout_seconds=1)
    assert peer.exited.is_set()
    with pytest.raises(SessionProtocolError):
        parent.run(_invocation())


# Unsupported clone controls remain explicit and leave a supported parent usable.
def test_missing_clone_support_is_explicit(make_session: Callable[..., Any]) -> None:
    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "clone":
            peer.emit(
                {
                    "id": request["id"],
                    "returncode": 7,
                    "stdout": "",
                    "stderr": "DAFNY_SESSION_UNSUPPORTED: clone",
                    "nativeEvidence": None,
                }
            )
        else:
            _branch_daemon(peer, request)

    parent, peer = make_session(respond)
    with pytest.raises(SessionUnsupportedError):
        parent.clone(timeout_seconds=1)
    assert parent.run(_invocation()).returncode == 0
    assert not peer.exited.is_set()


# Cloned job responses must match their own branch, role, epoch and generation.
@pytest.mark.parametrize(
    "updates",
    [
        {"sessionId": None},
        {"sessionId": "default"},
        {"sessionEpoch": "f" * 32},
        {"contextId": "other"},
        {"generation": 999},
    ],
)
def test_clone_requires_matching_evidence(
    make_session: Callable[..., Any], updates: dict[str, Any]
) -> None:
    parent, peer = make_session(_branch_daemon)
    child = parent.clone(timeout_seconds=1)

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        peer.emit(_response(request, **updates))

    peer.respond = respond
    with pytest.raises(SessionProtocolError):
        child.run(_invocation())
    with pytest.raises(SessionProtocolError):
        parent.run(_invocation())
    child.close()


# A clone that succeeds after timeout is drained and closed before its parent returns.
@pytest.mark.integration
def test_late_cancelled_clone_is_cleaned_without_stopping_parent(
    make_session: Callable[..., Any],
) -> None:
    saved: dict[str, Any] = {}

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "clone":
            saved.update(request)
        elif request.get("operation") == "cancel":
            peer.control_response(request)
            _branch_daemon(peer, saved)
        else:
            _branch_daemon(peer, request)

    parent, peer = make_session(respond)
    with pytest.raises(NativeSessionError) as caught:
        parent.clone(timeout_seconds=0.02)
    assert isinstance(caught.value.__cause__, subprocess.TimeoutExpired)
    closed = [item for item in peer.requests if item.get("operation") == "close-session"]
    assert [item["sessionId"] for item in closed] == [saved["targetId"]]
    assert parent.run(_invocation()).returncode == 0
    assert not peer.exited.is_set()


# A child can clone its own inherited state while all three existing handles remain live.
def test_nested_clone_uses_child_parent_identity(make_session: Callable[..., Any]) -> None:
    parent, _ = make_session(_branch_daemon)
    child = parent.clone(timeout_seconds=1)
    grandchild = child.clone(timeout_seconds=1)
    try:
        assert child.clone_receipt is not None and grandchild.clone_receipt is not None
        assert grandchild.clone_receipt.parent_id == child.clone_receipt.session_id
        assert grandchild.clone_receipt.parent_epoch == child.clone_receipt.session_epoch
        assert parent.run(_invocation()).returncode == 0
        assert child.run(_invocation()).returncode == 0
        assert grandchild.run(_invocation()).returncode == 0
    finally:
        grandchild.close()
        child.close()


# A daemon epoch change cannot be hidden by a valid new child epoch.
def test_second_clone_rejects_changed_daemon_epoch(make_session: Callable[..., Any]) -> None:
    parent, peer = make_session(_branch_daemon)
    child = parent.clone(timeout_seconds=1)

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        peer.emit(
            {
                "id": request["id"],
                "returncode": 0,
                "stderr": "",
                "stdout": json.dumps(_clone_receipt(request, daemonEpoch="f" * 32)),
                "nativeEvidence": None,
            }
        )

    peer.respond = respond
    with pytest.raises(SessionProtocolError, match="daemon epoch"):
        parent.clone(timeout_seconds=1)
    with pytest.raises(SessionProtocolError):
        child.run(_invocation())
    child.close()


# A clone cancel ACK cannot release the parent before the original clone drains.
@pytest.mark.integration
def test_cancelled_clone_waits_for_receipt_and_disposes_child(
    make_session: Callable[..., Any],
) -> None:
    clone_seen: queue.Queue[dict[str, Any]] = queue.Queue()
    cancel_seen = threading.Event()

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "clone":
            clone_seen.put(request)
        elif request.get("operation") == "cancel":
            peer.control_response(request)
            cancel_seen.set()
        else:
            _branch_daemon(peer, request)

    parent, peer = make_session(respond)
    cancel = threading.Event()
    with ThreadPoolExecutor(max_workers=1) as pool:
        future = pool.submit(parent.clone, timeout_seconds=1, cancel_event=cancel)
        request = clone_seen.get(timeout=1)
        cancel.set()
        assert cancel_seen.wait(1)
        assert not future.done()
        _branch_daemon(peer, request)
        with pytest.raises(SessionCancelledError):
            future.result(timeout=1)
    assert any(
        item.get("operation") == "close-session" and item["sessionId"] == request["targetId"]
        for item in peer.requests
    )
    assert parent.run(_invocation()).returncode == 0


# A clone whose cancellation never drains explicitly fails every shared handle.
@pytest.mark.integration
def test_clone_cancel_without_terminal_reply_stops_shared_transport(
    make_session: Callable[..., Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(session_module, "_CLOSE_SECONDS", 0.03)
    parent, peer = make_session(_branch_daemon)
    sibling = parent.clone(timeout_seconds=1)

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "cancel":
            peer.control_response(request)

    peer.respond = respond
    with pytest.raises(NativeSessionError):
        parent.clone(timeout_seconds=0.02)
    assert peer.exited.is_set()
    with pytest.raises(NativeSessionError, match="did not drain"):
        sibling.run(_invocation())
    sibling.close()


# Cancelling one child leaves its parent and sibling requests running independently.
@pytest.mark.integration
def test_child_cancel_preserves_parent_and_sibling_work(make_session: Callable[..., Any]) -> None:
    parent, peer = make_session(_branch_daemon)
    first = parent.clone(timeout_seconds=1)
    second = parent.clone(timeout_seconds=1)
    requests: dict[str, dict[str, Any]] = {}

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "cancel":
            peer.control_response(request)
            response = _response(
                requests[request["targetId"]], completed=False, outcome="cancelled"
            )
            response["returncode"] = 130
            peer.emit(response)
        elif "operation" in request:
            _branch_daemon(peer, request)
        else:
            requests[request["id"]] = request

    peer.respond = respond
    cancel = threading.Event()
    try:
        with ThreadPoolExecutor(max_workers=3) as pool:
            cancelled = pool.submit(first.run, _invocation(cancel=cancel))
            first_request = peer.jobs.get(timeout=1)
            parent_job = pool.submit(parent.run, _invocation())
            parent_request = peer.jobs.get(timeout=1)
            sibling_job = pool.submit(second.run, _invocation())
            sibling_request = peer.jobs.get(timeout=1)
            cancel.set()
            with pytest.raises(SessionCancelledError):
                cancelled.result(timeout=1)
            assert not parent_job.done() and not sibling_job.done()
            peer.emit(_response(parent_request))
            peer.emit(_response(sibling_request))
            assert parent_job.result(timeout=1).returncode == 0
            assert sibling_job.result(timeout=1).returncode == 0
            cancels = [item for item in peer.requests if item.get("operation") == "cancel"]
            assert [(item["sessionId"], item["targetId"]) for item in cancels] == [
                (first_request["sessionId"], first_request["id"])
            ]
    finally:
        first.close()
        second.close()


# Closing a child waits for its original physical response and leaves its sibling usable.
@pytest.mark.integration
def test_close_child_drains_only_its_pending_job(make_session: Callable[..., Any]) -> None:
    parent, peer = make_session(_branch_daemon)
    child = parent.clone(timeout_seconds=1)
    close_seen = threading.Event()

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        if request.get("operation") == "close-session":
            peer.control_response(request)
            close_seen.set()
        elif request.get("sessionId") == "default":
            _branch_daemon(peer, request)

    peer.respond = respond
    with ThreadPoolExecutor(max_workers=2) as pool:
        job = pool.submit(child.run, _invocation())
        request = peer.jobs.get(timeout=1)
        close = pool.submit(child.close)
        assert close_seen.wait(1)
        assert not job.done() and not close.done()
        assert parent.run(_invocation()).returncode == 0
        response = _response(request, completed=False, outcome="cancelled")
        response["returncode"] = 130
        peer.emit(response)
        close.result(timeout=1)
        with pytest.raises(SessionClosedError):
            job.result(timeout=1)
    assert not peer.exited.is_set()


# An unrelated clone and branch-close cannot consume a running job's cancellation lane.
@pytest.mark.integration
def test_cancel_admission_is_independent_of_clone_and_close_controls(
    make_session: Callable[..., Any],
) -> None:
    parent, peer = make_session(_branch_daemon, max_pending=2)
    spare = parent.clone(timeout_seconds=1)
    clone_seen: queue.Queue[dict[str, Any]] = queue.Queue()
    close_seen: queue.Queue[dict[str, Any]] = queue.Queue()
    requests: dict[str, dict[str, Any]] = {}

    def respond(peer: _Process, request: dict[str, Any]) -> None:
        operation = request.get("operation")
        if operation == "clone":
            clone_seen.put(request)
        elif operation == "close-session":
            close_seen.put(request)
        elif operation == "cancel":
            peer.control_response(request)
            response = _response(
                requests[request["targetId"]], completed=False, outcome="cancelled"
            )
            response["returncode"] = 130
            peer.emit(response)
        else:
            requests[request["id"]] = request

    peer.respond = respond
    cancel = threading.Event()
    with ThreadPoolExecutor(max_workers=3) as pool:
        job = pool.submit(parent.run, _invocation(cancel=cancel))
        job_request = peer.jobs.get(timeout=1)
        clone = pool.submit(parent.clone, timeout_seconds=2)
        clone_request = clone_seen.get(timeout=1)
        closing = pool.submit(spare.close)
        close_request = close_seen.get(timeout=1)
        cancel.set()
        with pytest.raises(SessionCancelledError):
            job.result(timeout=1)
        assert not peer.exited.is_set()
        cancels = [item for item in peer.requests if item.get("operation") == "cancel"]
        assert [item["targetId"] for item in cancels] == [job_request["id"]]
        peer.control_response(close_request)
        _branch_daemon(peer, clone_request)
        closing.result(timeout=1)
        child = clone.result(timeout=1)
    peer.respond = _branch_daemon
    try:
        assert parent.run(_invocation()).returncode == 0
        assert child.run(_invocation()).returncode == 0
    finally:
        child.close()


# Jobs and clone snapshots share one normal admission bound in either direction.
@pytest.mark.integration
@pytest.mark.parametrize("first_operation", ["job", "clone"])
def test_jobs_and_clones_share_normal_admission(
    make_session: Callable[..., Any], first_operation: str
) -> None:
    seen: queue.Queue[dict[str, Any]] = queue.Queue()
    parent, peer = make_session(lambda process, request: seen.put(request), max_pending=1)
    with ThreadPoolExecutor(max_workers=1) as pool:
        if first_operation == "job":
            first = pool.submit(parent.run, _invocation())
            request = seen.get(timeout=1)
            with pytest.raises(NativeSessionError) as caught:
                parent.clone(timeout_seconds=0.03)
            assert isinstance(caught.value.__cause__, subprocess.TimeoutExpired)
            assert len(peer.requests) == 1
            peer.emit(_response(request))
            assert first.result(timeout=1).returncode == 0
        else:
            first = pool.submit(parent.clone, timeout_seconds=1)
            request = seen.get(timeout=1)
            with pytest.raises(NativeSessionError) as caught:
                parent.run(_invocation(timeout=0.03))
            assert isinstance(caught.value.__cause__, subprocess.TimeoutExpired)
            assert len(peer.requests) == 1
            _branch_daemon(peer, request)
            child = first.result(timeout=1)
            peer.respond = _branch_daemon
            child.close()
    peer.respond = _branch_daemon
    assert parent.run(_invocation()).returncode == 0


# Cancelling a queued clone leaves the admitted job intact and creates no child branch.
@pytest.mark.integration
def test_cancel_queued_clone_does_not_cancel_admitted_job(make_session: Callable[..., Any]) -> None:
    parent, peer = make_session(lambda process, request: None, max_pending=1)
    cancel = threading.Event()
    with ThreadPoolExecutor(max_workers=2) as pool:
        job = pool.submit(parent.run, _invocation())
        request = peer.jobs.get(timeout=1)
        clone = pool.submit(parent.clone, timeout_seconds=1, cancel_event=cancel)
        cancel.set()
        with pytest.raises(SessionCancelledError):
            clone.result(timeout=1)
        assert len(peer.requests) == 1
        peer.emit(_response(request))
        assert job.result(timeout=1).returncode == 0
