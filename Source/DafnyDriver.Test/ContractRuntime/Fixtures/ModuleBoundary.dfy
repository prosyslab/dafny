// Declarations reached across module, export and import boundaries.
// Main: scenario bucket = Size() - 2 (ordinals 4b..4b+3); each scenario runs only its own code and clause.
// Host: a pure goal next to unrelated native-only host state (a whole-program declaration, so its own campaign).

// == source Main ==
module Numbers { function Width(x: int): nat { if x < 0 then 0 else 1 } }
module Encoding {
  import N = Numbers
  function Encode(x: int): seq<int>
    ensures |Encode(x)| == N.Width(x)
  { if x < 0 then [] else [x] }
}
module Data { datatype Item = Item(value: int) }
module Operations {
  import D = Data
  function Encode(values: seq<int>): seq<D.Item>
    decreases |values|
  { if values == [] then [] else [D.Item(values[0])] + Encode(values[1..]) }
  by method {
    return if values == [] then [] else [D.Item(values[0])] + Encode(values[1..]);
  }
  function EncodeWrong(values: seq<int>): seq<D.Item>
    decreases |values|
  { if values == [] then [] else [D.Item(values[0])] + EncodeWrong(values[1..]) }
  by method {
    return [];
  }
}
module Store {
  export reveals Box provides Read
  class Box { ghost var f: int ghost constructor Init() { f := 1; } }
  ghost function Read(x: Box): int reads x { x.f }
}
module Subsets {
  predicate IsEven(x: int) { x % 2 == 0 }
  type Even = x: int | IsEven(x) witness 0
  function Lo(): int { 3 }
  type Big = x: int | x >= Lo() witness Lo()
}
module Short { export A reveals F export B function F(): int { 1 } }
module Lib {
  class Store {
    ghost var state: int
    constructor() ensures state == 0 { state := 0; }
    method {:extern} {:axiom} ReadState() returns (r: int) ensures r == state
    method {:extern} {:axiom} ReadZero() returns (r: int) ensures r == state
  }
}
module Shapes {
  trait Shape extends object {
    function Area(): int reads this
    method Scale(k: int) returns (a: int) ensures a == k * Area()
  }
  class Square extends Shape {
    var side: int
    constructor(s: int) ensures side == s { side := s; }
    function Area(): int reads this { side * side }
    method Scale(k: int) returns (a: int) ensures a == k * Area() { a := k * side * side; }
  }
}
module M {
  import E = Encoding
  import O = Operations
  import S = Store
  import A = Subsets
  import Short`A
  import Lib
  import Shapes
  method Goal(tag: int, x: int, values: seq<int>, box: S.Box, s: set<int>, n: nat, store: Lib.Store, shape: Shapes.Shape)
    returns (result: int, evens: set<A.Even>)
    requires tag == 5 ==> n > 0
    ensures tag == 0 ==> result == 2
    ensures tag == 1 ==> result == |values| + 1
    ensures tag == 2 ==> result == |values| + 2
    ensures tag == 3 ==> S.Read(box) == 2
    ensures tag == 4 ==> forall e :: e in evens ==> e in s && e % 2 == 0
    ensures tag == 5 ==> result >= 3
    ensures tag == 6 ==> result == Short.F() + 1
    ensures tag == 7 ==> result == store.state + 1
    ensures tag == 8 ==> result == store.state + 2
    ensures tag == 9 ==> result == 3 * shape.Area()
  {
    result, evens := 0, {};
    if tag == 0 { result := |E.Encode(x)|; }
    if tag == 1 { result := |O.Encode(values)|; }
    if tag == 2 { result := |O.EncodeWrong(values)|; }
    if tag == 4 { evens := set e: A.Even | e in s; }
    if tag == 5 { var a := new A.Big[n]; result := a[0]; }
    if tag == 6 { result := Short.F(); }
    if tag == 7 { result := store.ReadState(); }
    if tag == 8 { result := store.ReadZero(); }
    if tag == 9 { result := shape.Scale(3); result := result + 1; }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
  returns (tag: int, x: int, values: seq<int>, box: S.Box, s: set<int>, n: nat, store: Lib.Store, shape: Shapes.Shape) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
  values := [1, 2];
  box := new S.Box.Init();
  s := {1, 2, 4};
  n := 2;
  store := new Lib.Store();
  shape := new Shapes.Square(2);
}

// == source Host ==
module Host {
  class Region {
    ghost var value: int
    ghost constructor Init(initial: int) ensures value == initial { value := initial; }
  }
  class Handle {
    ghost const region: Region
    constructor Init() requires false {
      ghost var initial: int :| true;
      region := new Region.Init(initial);
    }
    method {:extern "NativeHost", "Write"} Write(x: int)
  }
  const {:extern "NativeHost", "Current"} Current: Handle
  function Open(): Handle { Current }
  method {:extern "NativeHost", "Stop"} Stop(code: int)
  method Run() { var handle := Open(); handle.Write(1); Stop(0); }
}
module M {
  import Host
  ghost function Id<T>(x: T): T { x }
  opaque function Double(x: int): int { 2 * x }
  method Goal(x: int) returns (y: int) ensures y == Double(x) + 1 {
    reveal Double();
    assert Id(x) == x;
    y := 2 * x;
  }
}
// == generator Host ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }
