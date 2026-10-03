// Reuse of native heap proofs, membership certificates and closed-query budget across samples and clauses.
// Proof caches and budgets are campaign-wide, so every section is its own campaign with its own sample count.

// == source GlobalReuse ==
module Client { type Positive=n:int | n > 0 witness 1 class Region { ghost var value:Positive ghost var callback:int -> Positive } ghost const {:extern} unused:Region const count:nat:=1 datatype Input=Input(value:int, flag:bool) method Goal(input:Input) returns(result:int, ghost evidence:int) ensures result==input.value+1 { result:=input.value; evidence:=0; } }
// == generator GlobalReuse ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(input:Input) { var n:=r.Int(0,1000000000); input:=Input(n,true); }

// == source DistinctHeaps ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive var unrelated:int constructor(value:Positive, unrelated:int) { this.value := value; this.unrelated := unrelated; } } method Goal(cell:Cell) ensures false {} }
// == generator DistinctHeaps ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { var unrelated := r.Int(1,1000000000); cell := new Cell(2, unrelated); }

// == source ChangedValue ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } method Goal(cell:Cell) ensures false {} }
// == generator ChangedValue ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { var value := r.Int(1,1000000000); cell := new Cell(value); }

// == source UnsuccessfulProof ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive var unrelated:int constructor(value:Positive, unrelated:int) { this.value := value; this.unrelated := unrelated; } } method Goal(cell:Cell) ensures false {} }
// == generator UnsuccessfulProof ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { var unrelated := r.Int(1,1000000000); cell := new Cell(-1, unrelated); }

// == source ObservedReuse ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive var counter:int constructor(value:Positive, counter:int) { this.value := value; this.counter := counter; } } twostate predicate Changed(cell:Cell) reads cell { cell.counter == old(cell.counter) + 2 } method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.counter := cell.counter + 1; } }
// == generator ObservedReuse ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2, 0); }

// == source InvalidLaterState ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value) - 3 } method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.value := -1; } }
// == generator InvalidLaterState ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }

// == source PositiveCell ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } method Goal(cell:Cell) ensures false {} }
// == generator PositiveCell ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }

// == source NativeCertificateReuse ==
module Client { type Positive = n:int | n > 0 witness 1 class Cell { var value:Positive constructor(value:Positive) { this.value := value; } } twostate predicate Changed(cell:Cell) reads cell { cell.value == old(cell.value) + 2 } method Goal(cell:Cell) modifies cell ensures Changed(cell) { cell.value := cell.value + 1; } }
// == generator NativeCertificateReuse ==
method {:pbt_generator "Client.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(2); }

// == source HeapFacts ==
module Client {
  class Cell { var value: int constructor(value: int) { this.value := value; } }
  twostate predicate Changed(cell: Cell) reads cell { cell.value == old(cell.value) + 2 }
  method Goal(cell: Cell) modifies cell ensures Changed(cell) ensures Changed(cell) && cell.value > 0 { cell.value := cell.value + 2; }
}
// == generator HeapFacts ==
method {:pbt_generator "Client.Goal"} Generate(r: PbtRandom.Source) returns(cell: Cell) { cell := new Cell(7); }

// == source RecursiveMembership ==
// Variants (built by the test): a duplicate child id, and `ensures false` on Read.
module M {
  function contractResult():int { 0 }
  datatype Tree = Node(id:int, children:map<int,Tree>)
  function Ids(tree:Tree):set<int> decreases tree {
    {tree.id} + set name:int, id:int | name in tree.children && id in Ids(tree.children[name]) :: id
  }
  function Paths(tree:Tree, id:int):set<seq<int>> decreases tree {
    (if tree.id == id then {[]} else {}) +
    set name:int, suffix:seq<int> | name in tree.children && suffix in Paths(tree.children[name], id) :: [name] + suffix
  }
  predicate Unique(tree:Tree) { forall id :: id in Ids(tree) ==> |Paths(tree,id)| == 1 }
  type UniqueTree = tree:Tree | Unique(tree) witness Node(0,map[])
  class Cell { var value:UniqueTree constructor(value:Tree) { this.value := value; } }
  function Read(cell:Cell):UniqueTree reads cell { cell.value }
  method Goal(cell:Cell) ensures false { var value := Read(cell); }
}
// == generator RecursiveMembership ==
method {:pbt_generator "M.Goal"} Generate(r:PbtRandom.Source) returns(cell:Cell) { cell := new Cell(Node(0,map[1 := Node(1,map[])])); }
