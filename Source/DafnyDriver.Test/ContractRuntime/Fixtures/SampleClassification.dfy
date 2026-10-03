// Sample classification by callee and specification-function contracts.
// Bucket = Size() - 2 (ordinals 4b..4b+3); each scenario runs only its own code and clause.
// Excluded: every bucket is excluded (no valid sample), so its status is "No valid sample completed.".
// Accepted: every bucket is valid and violation-free, so its status is NoViolationFound.
// Entry-state captures are evaluated at entry in every sample, so their guard sits inside old(...).
// Mixed: one callee-invalid bucket and one valid violating bucket share a goal clause and a callee.

// == source Excluded ==
module M {
  class Box { var f: int constructor() { f := 0; } }
  method {:extern} {:axiom} Extern(x: int) returns (y: int) ensures y > x
  method Inner(x: int) returns (y: int) ensures y == x + 1 { y := x; }
  method Outer(x: int) returns (y: int) ensures y == x { y := Inner(x); }
  function InnerDomain(x: int): int requires x < 0 { x }
  function OuterDomain(x: int): int { InnerDomain(x) }
  function Bad(x: int): (b: bool) ensures b { false }
  ghost function GhostBad(x: int): (b: bool) ensures b { false }
  function Mismatch(x: int): int { 0 } by method { return 1; }
  function BadNullary(): (b: bool) ensures b { false }
  method Helper(x: int) returns (y: int) ensures !BadNullary() { y := 1; }
  function BadRead(o: Box): (n: int) reads o ensures n == 0 { o.f + 1 }
  function Pos(o: Box): (b: bool) reads o ensures o.f == 0 && Neg(o) { true }
  function Neg(o: Box): (b: bool) reads o ensures Pos(o) { true } by method { o.f := 1; return true; }
  method Evens(s: set<int>) returns (r: set<int>) ensures forall e :: e in r ==> e in s && e % 2 == 0 { r := s; }
  function Pick<T(==)>(a: T, b: T): (c: T) ensures c == a { b }
  method Natural(x: int) returns (y: nat)
  function InnerPick<U(==)>(a: U, b: U): (c: U) ensures c == a { b }
  function OuterPick<T(==)>(a: seq<T>, b: seq<T>): (c: seq<T>) ensures c == InnerPick(a, b) { a }
  method Goal(tag: int, x: int, o: Box, s: set<int>) returns (y: int, b: bool)
    modifies o
    ensures tag == 0 ==> y > x
    ensures tag == 1 ==> y != x
    ensures tag == 2 ==> y != x
    ensures tag == 3 ==> Bad(x)
    ensures tag == 4 ==> GhostBad(x)
    ensures tag == 5 ==> y == 0
    ensures tag == 6 ==> y == 0
    ensures old(tag == 7 ==> BadRead(o) == 0)
    ensures tag == 8 ==> !Pos(o)
    ensures tag == 9 ==> b
    ensures tag == 10 ==> y == Pick(x, 0)
    ensures tag == 11 ==> y >= 0
    ensures tag == 12 ==> OuterPick([x], [0]) == [x]
  {
    y, b := x, true;
    if tag == 0 { y := Extern(x); }
    if tag == 1 { y := Outer(x); }
    if tag == 2 { y := OuterDomain(x); }
    if tag == 5 { y := Mismatch(x); }
    if tag == 6 { y := Helper(x); }
    if tag == 7 { o.f := 2; }
    if tag == 9 { var r := Evens(s); b := 1 !in r; }
    if tag == 11 { y := Natural(x); }
  }
}
// == generator Excluded ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int, o: Box, s: set<int>) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
  o := new Box();
  s := {1, 2};
}

// == source Accepted ==
module M {
  class Box { var f: int constructor() { f := 0; } }
  function Pos(x: int): (b: bool) ensures b == !Neg(x) { x > 0 }
  function Neg(x: int): (b: bool) ensures b == !Pos(x) { x <= 0 }
  function Recursive(x: int): int { if x <= 0 then 0 else Recursive(x - 1) + 1 }
  by method { var y := 0; if x > 0 { y := Recursive(x - 1) + 1; } return y; }
  function Count(x: int): (n: int) ensures x <= 0 || n == Count(x - 1) + 1 { if x <= 0 then 0 else Count(x - 1) + 1 }
  function Read(o: Box): (n: int) reads o ensures n == o.f { o.f }
  function Outer(o: Box): (n: int) reads o ensures n == Read(o) { Read(o) }
  method Goal(tag: int, x: int, o: Box) returns (y: int, b: bool)
    modifies o
    ensures tag == 0 ==> b == Pos(x) && !Neg(x)
    ensures tag == 1 ==> y == x
    ensures tag == 2 ==> Count(x) == x
    ensures old(tag == 3 ==> Outer(o) == 0)
  {
    y, b := 0, false;
    if tag == 0 { b := Pos(x); }
    if tag == 1 { y := Recursive(x); }
    if tag == 3 { o.f := 2; }
  }
}
// == generator Accepted ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int, o: Box) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
  o := new Box();
}

// == source Mixed ==
module M {
  method Helper(x: int) returns (y: int) ensures y >= 0 { y := if x < 1 then -1 else x; }
  method Goal(tag: int, x: int) returns (r: int) ensures r > 100 { r := Helper(x); }
}
// == generator Mixed ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := tag;
}
