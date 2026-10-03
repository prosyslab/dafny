// Original two-state heap postconditions decided over captured entry and return heaps.
// Bucket = Size() - 2 (ordinals 4b..4b+3); the polarity of each scenario is chosen by its bucket.

// == source Main ==
// Bucket 0 adds 1 (violates), bucket 1 adds 2 (holds), bucket 2 adds 1 through a nonterminating-permission callee,
// bucket 3 calls an invalid callee first. The ghost amount is always 2.
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell, amount: int) reads cell {
    cell.value == old(cell.value) + amount
  }
  method Step(cell: Cell) modifies cell decreases * { cell.value := cell.value + 1; }
  method Bad() returns (x: int) ensures x == 1 { x := 0; }
  method Goal(tag: int, cell: Cell, ghost amount: int) modifies cell
    ensures Changed(cell, amount)
    decreases *
  {
    if tag == 2 {
      Step(cell);
    } else {
      if tag == 3 { var x := Bad(); }
      cell.value := cell.value + (if tag == 1 then 2 else 1);
    }
  }
}
// == generator Main ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell, amount: int) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
  amount := 2;
}

// == source Budget ==
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
  method Goal(cell: Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; }
}
// == generator Budget ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source Observed ==
// Buckets 0 and 1 add 1 and 2 to a refined field; bucket 2 fails the original entry precondition.
module Client {
  type Positive = value: int | value > 0 witness 1
  class Cell { var value: Positive constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell, result: Positive) reads cell {
    result == cell.value && cell.value == old(cell.value) + 2
  }
  method Goal(tag: int, cell: Cell) returns (result: Positive)
    requires tag == 2 ==> cell.value == 99
    modifies cell
    ensures Changed(cell, result)
  {
    cell.value := cell.value + (if tag == 1 then 2 else 1);
    result := cell.value;
  }
}
// == generator Observed ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
}

// == source CertifiedSpecification ==
// A requires-only specification function; bucket 0 adds 1 (violates), bucket 1 adds 2 (holds).
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  function Offset(n: int): int requires n >= 0 { n + 2 }
  twostate predicate Changed(cell: Cell) reads cell {
    cell.value == if old(cell.value) >= 0 then Offset(old(cell.value)) else 0
  }
  method Goal(tag: int, cell: Cell) modifies cell ensures Changed(cell) {
    cell.value := cell.value + (if tag == 1 then 2 else 1);
  }
}
// == generator CertifiedSpecification ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
}
