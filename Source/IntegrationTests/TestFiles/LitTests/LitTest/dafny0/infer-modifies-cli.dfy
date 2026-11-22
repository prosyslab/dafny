// RUN: %verify --inferModifies --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %exits-with 4 %verify --cores 1 "%s" > "%t-default"
// RUN: %diff "%s.default.expect" "%t-default"

module IO {
  export reveals Cell, Streams provides Cell.Init, Cell.value, Streams.stdoutRegion, Flush

  class Cell {
    var value: int

    constructor Init() {
      value := 0;
    }
  }

  class Streams {
    const stdoutRegion: Cell

    constructor(c: Cell)
      ensures stdoutRegion == c
    {
      stdoutRegion := c;
    }
  }

  method {:inferModifies} Write(out: Cell)
    ensures out.value == 1
  {
    out.value := 1;
  }

  method Flush(io: Streams)
    ensures io.stdoutRegion.value == 1
  {
    Write(io.stdoutRegion);
  }
}

module CLI {
  import IO

  method Run(io: IO.Streams, other: IO.Cell)
    requires io.stdoutRegion != other
    ensures io.stdoutRegion.value == 1 && other.value == old(other.value)
  {
    var scratch := FreshWrite();
    assert scratch.value == 7;
    IO.Flush(io);
  }

  // Allocation is outside this pass and is still checked by the verifier.
  method FreshWrite() returns (out: IO.Cell)
    ensures fresh(out) && out.value == 7
  {
    out := new IO.Cell.Init();
    out.value := 7;
  }
}
