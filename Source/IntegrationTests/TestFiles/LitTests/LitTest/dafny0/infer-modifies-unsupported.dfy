// RUN: %exits-with 2 %verify --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var value: int
  var next: Cell?
}

method Set(c: Cell)
  modifies c`value
{
  c.value := 1;
}

// Reject rebinding a reference used to locate a later write.
method {:inferModifies} ChangedTarget(c: Cell, d: Cell) {
  c.next := d;
  Set(c.next);
}

class Link {
  const next: Link?
  var value: int
}

// Recursive propagation would keep adding longer paths to the write target.
method {:inferModifies} Recursive(c: Link, n: nat)
  decreases n
{
  c.value := 1;
  if n > 0 && c.next != null {
    Recursive(c.next, n - 1);
  }
}

method {:inferModifies} Mixed(c: Cell)
  modifies c
{
  c.value := 1;
}

method {:inferModifies} Bodyless(c: Cell)

method {:inferModifies} AllocateAndReturn() returns (a: array<int>) {
  return new int[1];
}
