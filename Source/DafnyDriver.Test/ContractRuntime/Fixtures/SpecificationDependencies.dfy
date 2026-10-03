// Specification dependencies of two-state heap postconditions. Bucket = Size() - 2 (ordinals 4b..4b+3).
// Every scenario owns one guarded postcondition whose predicate reaches its own dependency.

// == source Unvalidated ==
// Each clause reaches an unvalidated contract, so it stays unchecked in every sample.
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate ChangedDirect(cell: Cell) reads cell ensures false { cell.value == old(cell.value) + 2 }
  function BadSelf(): int ensures BadSelf() == 1 { 0 }
  twostate predicate ChangedTransitive(cell: Cell) reads cell { cell.value == old(cell.value) + BadSelf() }
  predicate Good(n: int) ensures false { true }
  type GoodInt = n: int | Good(n) witness 1
  function HiddenTyped(n: GoodInt): int { 0 }
  twostate predicate ChangedTyped(cell: Cell) reads cell { cell.value == old(cell.value) + HiddenTyped(1) }
  function HiddenRecursive(n: int): int ensures HiddenRecursive(n) == 1 { if n <= 0 then 0 else HiddenRecursive(n - 1) }
  twostate predicate ChangedRecursive(cell: Cell) reads cell { cell.value == old(cell.value) + HiddenRecursive(1) }
  function BadValue(): int ensures false { 0 }
  twostate predicate ChangedHigherOrder(cell: Cell) reads cell { cell.value == old(cell.value) + (var f := BadValue; f()) }
  function OffsetFalse(n: int): int ensures false { n }
  twostate predicate ChangedGhost(cell: Cell, amount: int) reads cell { cell.value == old(cell.value) + OffsetFalse(amount) }
  function OffsetMismatch(n: int): (result: int) ensures result == n + 2 { n + 3 } by method { return n + 2; }
  twostate predicate ChangedMismatch(cell: Cell) reads cell { cell.value == OffsetMismatch(old(cell.value)) }
  method Goal(tag: int, cell: Cell, ghost amount: int) modifies cell
    ensures tag == 0 || tag == 1 ==> ChangedDirect(cell)
    ensures tag == 2 ==> ChangedTransitive(cell)
    ensures tag == 3 ==> ChangedTyped(cell)
    ensures tag == 4 ==> ChangedRecursive(cell)
    ensures tag == 5 ==> ChangedHigherOrder(cell)
    ensures tag == 6 ==> ChangedGhost(cell, amount)
    ensures tag == 7 ==> ChangedMismatch(cell)
  {
    cell.value := cell.value + (if tag == 1 || tag == 6 then 2 else 1);
  }
}
// == generator Unvalidated ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell, amount: int) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
  amount := 2;
}

// == source LogicalCertificates ==
// Logical use needs only the original definitions; executed by-method results are still checked.
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  function Hidden(n: int): int { 0 } by method { return 1; }
  twostate predicate ChangedHidden(cell: Cell) reads cell { cell.value == old(cell.value) + Hidden(1) }
  function OffsetGood(n: int): int { n + 2 } by method { return n + (if n == 7 then 2 else 3); }
  twostate predicate ChangedGood(cell: Cell) reads cell { cell.value == OffsetGood(old(cell.value)) }
  function OffsetBad(n: int): int { n + 2 } by method { return n + (if n == 7 then 3 else 3); }
  twostate predicate ChangedBad(cell: Cell) reads cell { cell.value == OffsetBad(old(cell.value)) }
  method Goal(tag: int, cell: Cell) modifies cell
    ensures tag == 0 ==> ChangedHidden(cell)
    ensures tag == 1 ==> ChangedGood(cell)
    ensures tag == 2 ==> ChangedBad(cell)
  {
    if tag == 1 { var actual := OffsetGood(cell.value); }
    if tag == 2 { var actual := OffsetBad(cell.value); }
    cell.value := cell.value + 1;
  }
}
// == generator LogicalCertificates ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
}
