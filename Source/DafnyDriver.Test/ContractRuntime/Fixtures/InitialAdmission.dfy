// Admission of captured and constructed initial heaps. Sections whose whole-program declarations
// (globals, datatype or class constants, witnesses, omitted fields) decide admission are separate campaigns;
// rows of one program that differ only by generated values are buckets (bucket = Size() - 2).

// == source Store ==
// Buckets: 0 correct ghost-backed draft, 1 wrong draft, 2 even closed callee result, 3 odd closed callee result.
module Store {
  class Cell {
    ghost var value: int
    ghost var unused: int -> int
    constructor Init() requires false {
      ghost var initial: int :| true;
      value := initial;
      ghost var callback: int -> int :| true;
      unused := callback;
    }
    ghost function Read(): int reads this { value }
    method {:extern} {:axiom} ReadValue() returns (result: int) ensures result == Read()
    method {:extern} {:axiom} ReadWrong() returns (result: int) ensures result == Read()
    method {:extern} {:axiom} ReadEven() returns (result: int) ensures exists k: int :: result == 2 * k
    method {:extern} {:axiom} ReadOdd() returns (result: int) ensures exists k: int :: result == 2 * k
  }
}
module Client {
  import Store
  method Goal(tag: int, cell: Store.Cell) returns (result: int)
    ensures tag <= 1 ==> result == cell.Read() + 1
    ensures tag >= 2 ==> false
  {
    if tag == 0 { result := cell.ReadValue(); }
    else if tag == 1 { result := cell.ReadWrong(); }
    else if tag == 2 { result := cell.ReadEven(); }
    else { result := cell.ReadOdd(); }
  }
}
// == generator Store ==
method {:pbt_generator "Client.Goal"}
  {:pbt_heap_constructor "Store.Cell", "Store.Cell.value"}
  Generate(r: PbtRandom.Source) returns (tag: int, cell: Store.Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Store.Cell.ContractDiagnosticCreate(if tag >= 2 then 4 else 7);
}

// == source OmittedByDraft ==
module Store {
  class Cell {
    ghost var value: int
    ghost var unused: int
    constructor Init() requires false {
      ghost var initial: int :| true;
      value := initial;
      ghost var callback: int :| true;
      unused := callback;
    }
    ghost function Read(): int reads this { value }
    method {:extern} {:axiom} ReadValue() returns (result: int)
      ensures result == Read()
  }
}
module Client {
  import Store
  method Goal(cell: Store.Cell) returns (result: int)
    ensures result == cell.Read() + 1
  { result := cell.ReadValue(); }
}
// == generator OmittedByDraft ==
method {:pbt_generator "Client.Goal"}
  {:pbt_heap_constructor "Store.Cell", "Store.Cell.value"}
  Generate(r: PbtRandom.Source) returns (cell: Store.Cell) {
  cell := new Store.Cell.ContractDiagnosticCreate(7);
}

// == source UncallableConstructor ==
// Bucket 0 constructs the ordinary class, bucket 1 the ghost-field class, each through its false-precondition constructor.
module M {
  class Plain { var value: int constructor Init() requires false { value := 7; } }
  class Ghostly { ghost var value: int ghost constructor Init() requires false { value := 7; } }
  method Goal(tag: int, plain: Plain?, ghostly: Ghostly?)
    ensures plain != null ==> plain.value == 8
    ensures ghostly != null ==> ghostly.value == 8
  {}
}
// == generator UncallableConstructor ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, plain: Plain?, ghostly: Ghostly?) {
  var size := r.Size();
  tag := size - 2;
  plain, ghostly := null, null;
  if tag == 0 { plain := new Plain.Init(); } else { ghostly := new Ghostly.Init(); }
}

// == source EmptyGlobal ==
module Client { type Empty = value:int | false witness 0 ghost const unused:Empty
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
  method Goal(cell: Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; }
}
// == generator EmptyGlobal ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source EmptyGlobalInitializer ==
module Client { type Empty = value:int | false witness * ghost const unused:Empty := 0
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
  method Goal(cell: Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; }
}
// == generator EmptyGlobalInitializer ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source DatatypeConstant ==
module Client { type Empty = value:int | false witness * datatype Item = Item { const bad:Empty := 0 }
  method Goal(x:int) returns(result:int) ensures result == x+1 { result:=x; } }
// == generator DatatypeConstant ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(x:int) { x:=1; }

// == source PlainDatatype ==
module Client { type Empty = value:int | false witness * datatype Item = Item
  method Goal(x:int) returns(result:int) ensures result == x+1 { result:=x; } }
// == generator PlainDatatype ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(x:int) { x:=1; }

// == source NegativeConstant ==
module Client { class Cell { var value:int ghost const tag:nat := -1 constructor(value:int) { this.value:=value; } }
  method Goal(cell:Cell) ensures false {} }
// == generator NegativeConstant ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source UndefinedConstant ==
module Client { function Seed():int requires false { 7 }
  class Cell { var value:int ghost const tag:int := Seed() constructor(value:int) { this.value:=value; } }
  method Goal(cell:Cell) ensures false {} }
// == generator UndefinedConstant ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source ValidConstant ==
module Client { class Cell { var value:int ghost const tag:nat := 1 constructor(value:int) { this.value:=value; } }
  method Goal(cell:Cell) ensures false {} }
// == generator ValidConstant ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(7); }

// == source TypedGhostField ==
// Buckets: 0 constructs -1, 1 constructs 2, 2 constructs 0 and then writes -1.
module Client { class Cell { ghost var value: nat constructor() { value := 0; } } method Goal(tag: int, cell: Cell) ensures false {} }
// == generator TypedGhostField ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell", "Client.Cell.value"}
  Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell.ContractDiagnosticCreate(if tag == 0 then -1 else if tag == 1 then 2 else 0);
  if tag == 2 { cell.value := -1; }
}

// == source CyclicTree ==
// Buckets: 0 nests -1, 1 nests 2.
module Client {
  datatype Tree = Node(n: nat, children: seq<Tree>)
  class Cell { var tree: Tree var next: Cell? constructor(tree: Tree) { this.tree := tree; next := null; } }
  method Goal(tag: int, cell: Cell) ensures false {}
}
// == generator CyclicTree ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(Node(0, [Node(if tag == 0 then -1 else 2, [])]));
  cell.next := cell;
}

// == source NegativeResidual ==
module Client { type Positive = n: int | n > 0 witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }
// == generator NegativeResidual ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (cell: Cell) { cell := new Cell(-1); }

// == source RefinedRoot ==
// Buckets: 0 passes argument 2, 1 passes argument -1.
module Client {
  type Positive = n:int | n > 0 witness 1
  class Cell { var value:Positive constructor(value:Positive) { this.value := value; } }
  method Goal(tag: int, cell:Cell, argument:Positive) ensures false {}
}
// == generator RefinedRoot ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, cell: Cell, argument: Positive) {
  var size := r.Size();
  tag := size - 2;
  cell := new Cell(2);
  argument := if tag == 0 then 2 else -1;
}

// == source PlainFunctionWellDefinedness ==
module Client { function Divide(n:int):int { 1 / n }
  type Positive = n:int | Divide(n) > 0 witness *
  class Cell { var value:Positive constructor(value:Positive) { this.value := value; } }
  method Goal(cell:Cell) ensures false {} }
// == generator PlainFunctionWellDefinedness ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(1); }

// == source ConstraintCallee ==
module Client { predicate Good(n: int) ensures false { n > 0 } type Positive = n: int | Good(n) witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }
// == generator ConstraintCallee ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }

// == source HigherOrderConstraintCallee ==
module Client { predicate Good(n: int) ensures false { n > 0 } type Positive = n: int | (var f := Good; f(n)) witness 1 class Cell { var value: Positive constructor(value: Positive) { this.value := value; } } method Goal(cell: Cell) ensures false {} }
// == generator HigherOrderConstraintCallee ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }

// == source EmptyOmittedField ==
module Client { type Hidden = n: int | false witness * class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value: Hidden :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }
// == generator EmptyOmittedField ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source PositiveOmittedField ==
module Client { type Hidden = n: int | n > 0 witness * class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value: Hidden :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }
// == generator PositiveOmittedField ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source OrdinaryArrowOmission ==
module Client { class Cell { ghost var unused: int -> int constructor Init() requires false { ghost var value: int -> int :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }
// == generator OrdinaryArrowOmission ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source RefinedArrowOmission ==
module Client { type Empty = n: int | false witness * class Cell { ghost var unused: int -> seq<Empty> constructor Init() requires false { ghost var value: int -> seq<Empty> :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }
// == generator RefinedArrowOmission ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source ValidWitness ==
module Client { ghost predicate Good(n:int) ensures Good(n) == (n > 0) { n > 0 } type Hidden = n:int | Good(n) witness 1 class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value:Hidden :| true; unused := value; } } method Goal(cell:Cell) ensures false {} }
// == generator ValidWitness ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source InvalidWitness ==
module Client { ghost predicate Good(n:int) ensures Good(n) == (n > 0) { n > 0 } type Hidden = n:int | Good(n) witness 0 class Cell { ghost var unused: Hidden constructor Init() requires false { ghost var value:Hidden :| true; unused := value; } } method Goal(cell:Cell) ensures false {} }
// == generator InvalidWitness ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }

// == source NestedEmptyOmission ==
module Client { type Empty = n: int | false witness * datatype Box<T> = Box(value: T) class Cell { ghost var unused: Box<Empty> constructor Init() requires false { ghost var value: Box<Empty> :| true; unused := value; } } method Goal(cell: Cell) ensures false {} }
// == generator NestedEmptyOmission ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Cell"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell.ContractDiagnosticCreate(); }
