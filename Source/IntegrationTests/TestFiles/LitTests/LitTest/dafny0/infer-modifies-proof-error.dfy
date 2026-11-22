// RUN: %exits-with 4 %verify --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var value: int
}

method {:inferModifies} Store(c: Cell) {
  c.value := 1;
}

// Verify that inference leaves the usual caller frame check in force.
method NoWritePermission(c: Cell) {
  Store(c);
}
