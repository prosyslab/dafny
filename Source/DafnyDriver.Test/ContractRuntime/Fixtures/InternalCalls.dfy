// Callee heap postconditions decided over each internal invocation's own captured entry and return heaps.
// Bucket = Size() - 2 (ordinals 4b..4b+3); each bucket calls only its own callees.

// == source Main ==
module Client {
  class Cell {
    var value: int
    constructor(value: int) { this.value := value; }
    twostate predicate Moved(amount: int) reads this { value == old(value) + amount }
    method StepOne(alias: Cell) returns (result: int)
      requires alias == this
      modifies this
      ensures Moved(1) && result == alias.value
    { value := value + 1; result := value; }
    method TwiceOne(alias: Cell) returns (result: int)
      requires alias == this
      modifies this
      ensures Moved(2) && result == alias.value
    { result := StepOne(alias); result := StepOne(alias); }
    method StepTwo(alias: Cell) returns (result: int)
      requires alias == this
      modifies this
      ensures Moved(1) && result == alias.value
    { value := value + 2; result := value; }
    method TwiceTwo(alias: Cell) returns (result: int)
      requires alias == this
      modifies this
      ensures Moved(2) && result == alias.value
    { result := StepTwo(alias); result := StepTwo(alias); }
  }
  twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
  function Bad(): int ensures false { 2 }
  twostate predicate ChangedBad(cell: Cell) reads cell { cell.value == old(cell.value) + Bad() }
  method StepCross(cell: Cell) modifies cell ensures Changed(cell) {
    cell.value := cell.value + (if cell.value == 7 then 2 else 1);
  }
  method StepLoop(cell: Cell) modifies cell ensures Changed(cell) decreases * { while true decreases * {} }
  method StepNoFrame(cell: Cell) ensures Changed(cell) { cell.value := cell.value + 2; }
  method StepSpec(cell: Cell) modifies cell ensures ChangedBad(cell) { cell.value := cell.value + 2; }
  method Goal(tag: int, cell: Cell) modifies cell ensures false decreases * {
    if tag == 0 { cell.value := cell.value + 10; var result := cell.TwiceOne(cell); }
    if tag == 1 { cell.value := cell.value + 10; var result := cell.TwiceTwo(cell); }
    if tag == 2 { StepCross(cell); StepCross(cell); }
    if tag == 3 { StepLoop(cell); }
    if tag == 4 { StepNoFrame(cell); }
    if tag == 5 { StepSpec(cell); }
  }
}
// == generator Main ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(7);
}
