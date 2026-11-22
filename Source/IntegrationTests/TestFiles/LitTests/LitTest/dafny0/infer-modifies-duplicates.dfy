// RUN: %resolve --inferModifies --rprint:- "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// RUN: %verify --inferModifies --cores 1 "%s"

class Cell {
  var value: int
  var tag: int
}

method SetValue(c: Cell) {
  c.value := 1;
}

method WritePair(c: Cell, d: Cell) {
  SetValue(c);
  SetValue(c);
  SetValue(d);
  c.tag := 2;
}

// Repeated calls preserve one entry per receiver and field.
// CHECK: ^\s*method WriteTwice\(
// CHECK-NEXT: ^\s*modifies c`value, d`value, c`tag\s*$
method WriteTwice(c: Cell, d: Cell) {
  WritePair(c, d);
  WritePair(c, d);
}
