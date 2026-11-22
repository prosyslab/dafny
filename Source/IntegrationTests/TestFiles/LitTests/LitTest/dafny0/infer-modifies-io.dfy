// RUN: %verify --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Streams {
  export reveals Stream, IO, Emit
    provides Stream.bytes, IO.stdinRegion, IO.stdoutRegion, IO.stderrRegion, Prepare, Flush

  class Stream {
    var bytes: seq<int>

    method Append(data: seq<int>)
      modifies this`bytes
      ensures bytes == old(bytes) + data
    {
      bytes := bytes + data;
    }

    method Drain() returns (data: seq<int>)
      modifies this`bytes
      ensures data == old(bytes) && bytes == []
    {
      data := bytes;
      bytes := [];
    }
  }

  class IO {
    const stdinRegion: Stream
    const stdoutRegion: Stream
    const stderrRegion: Stream

    constructor(stdin: Stream, stdout: Stream, stderr: Stream)
      ensures stdinRegion == stdin && stdoutRegion == stdout && stderrRegion == stderr
    {
      stdinRegion, stdoutRegion, stderrRegion := stdin, stdout, stderr;
    }
  }

  twostate predicate Emit(io: IO, out: seq<int>, err: seq<int>)
    reads io.stdoutRegion, io.stderrRegion
  {
    io.stdoutRegion.bytes == old(io.stdoutRegion.bytes) + out &&
    io.stderrRegion.bytes == old(io.stderrRegion.bytes) + err
  }

  method {:inferModifies} Prepare(io: IO) returns (out: seq<int>, err: seq<int>)
    ensures out == old(io.stdinRegion.bytes) && err == [] && io.stdinRegion.bytes == []
  {
    out := io.stdinRegion.Drain();
    err := [];
  }

  method {:inferModifies} Flush(io: IO, out: seq<int>, err: seq<int>)
    requires io.stdoutRegion != io.stderrRegion
    ensures Emit(io, out, err)
  {
    io.stdoutRegion.Append(out);
    io.stderrRegion.Append(err);
  }
}

module Client {
  import S = Streams

  // Verify propagation through exported wrappers and preservation outside Flush's frame.
  method {:inferModifies} RunCore(io: S.IO)
    requires io.stdinRegion != io.stdoutRegion && io.stdinRegion != io.stderrRegion
    requires io.stdoutRegion != io.stderrRegion
    ensures io.stdinRegion.bytes == []
    ensures S.Emit(io, old(io.stdinRegion.bytes), [])
  {
    var out, err := S.Prepare(io);
    S.Flush(io, out, err);
  }
}
