// RUN: %verify --filter-symbol Rotate --cores 1 "%s"
// RUN: %verify --inferModifies --cores 1 "%s"

class Cell {
  var value: int
  var child: Cell?
}

// A caller outside the cycle uses the recursive helper's inferred empty frame.
method {:inferModifies} Reset(c: Cell)
  ensures c.value == 0
{
  CountDown(3);
  c.value := 0;
}

method CountDown(n: nat)
  decreases n
{
  if n != 0 {
    Step(n - 1);
  }
}

method Step(n: nat)
  decreases n
{
  if n != 0 {
    CountDown(n - 1);
  }
}

// The fixed point must contain the write through both inputs.
method {:inferModifies} Rotate(a: Cell, b: Cell, n: nat)
  decreases n
{
  if n == 0 {
    a.value := 1;
  } else {
    Rotate(b, a, n - 1);
  }
}

module LeftFirst {
  class Cell {
    var value: int
  }

  // Both cycles share Center. The write at Right must reach all three methods.
  method Center(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Left(c, n - 1);
      Right(c, n - 1);
    }
  }

  method Left(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Center(c, n - 1);
    }
  }

  method Right(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Center(c, n - 1);
    }
    c.value := 1;
  }
}

module RightFirst {
  class Cell {
    var value: int
  }

  // The same calls in the opposite order must produce the same frames.
  method Center(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Right(c, n - 1);
      Left(c, n - 1);
    }
  }

  method Left(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Center(c, n - 1);
    }
  }

  method Right(c: Cell, n: nat)
    decreases n
  {
    if n > 0 {
      Center(c, n - 1);
    }
    c.value := 1;
  }
}

class Link {
  const next: Link?
  var value: int
}

// The target changes to anchor.next once. The recursive frame then stabilizes.
method {:inferModifies} StablePath(c: Link, anchor: Link, n: nat)
  requires anchor.next != null
  decreases n
{
  if n == 0 {
    c.value := 1;
  } else {
    StablePath(anchor.next, anchor, n - 1);
  }
}

// The syntactic write grows a frame through next. Verification can prove that
// the write is unreachable, so the original empty frame is sufficient.
method Growing(c: Link, n: nat)
  decreases n
{
  if false {
    c.value := 1;
  }
  if n > 0 && c.next != null {
    Growing(c.next, n - 1);
  }
}

method {:inferModifies} KeepOriginalContract(c: Cell, link: Link)
  ensures link.value == old(link.value)
{
  Growing(link, 1);
  c.value := 0;
}

method WriteExisting(c: Cell)
  modifies c`value
{
  c.value := 1;
}

// A failed implicit substitution must not prevent inference for Recovered.
method Unsupported(c: Cell, n: nat)
  decreases n
{
  if n > 0 && c.child != null && false {
    WriteExisting(c.child);
    Recovered(c, n - 1);
  }
}

method {:inferModifies} Recovered(c: Cell, n: nat)
  decreases n
{
  if n > 0 {
    Unsupported(c, n - 1);
  }
  c.value := 1;
}

// The implicit method falls back before the explicit peer can fail on its frame.
method ImplicitWithAlias(c: Cell, n: nat)
  decreases n
{
  var alias := c;
  if false {
    c.value := 1;
  }
  if n > 0 && false {
    ExplicitWithAlias(alias, n - 1);
  }
}

method {:inferModifies} ExplicitWithAlias(c: Cell, n: nat)
  decreases n
{
  var alias := c;
  if n > 0 {
    ImplicitWithAlias(alias, n - 1);
  }
  c.value := 1;
}
