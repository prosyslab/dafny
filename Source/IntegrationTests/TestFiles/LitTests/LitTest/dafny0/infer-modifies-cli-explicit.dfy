// RUN: %exits-with 4 %verify --inferModifies --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var value: int
  var next: Cell?
}

// A handwritten frame still determines which writes are permitted.
method ExplicitEmpty(c: Cell)
  modifies {}
{
  c.value := 1;
}

// An unsupported implicit request is subject to the ordinary frame check.
method Dynamic(c: Cell)
  requires c.next != null
{
  c.next.value := 1;
}
