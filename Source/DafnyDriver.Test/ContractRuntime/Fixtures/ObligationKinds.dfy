// Goal obligation kinds decided at runtime. One campaign; scenario bucket = Size() - 2 (ordinals 4b..4b+3).
// Every scenario runs only its own code and clause, guarded by `tag == b`; every sample is valid.

// == source Main ==
module M {
  class Box { var f: int constructor() { f := 1; } }
  method Helper(x: int) requires x > 5 ensures false { while true {} }
  function Negative(x: int): int requires x < 0 { x }
  lemma Same(x: int) ensures x == x {}
  function Head<T>(s: seq<T>): T requires |s| > 0 { s[0] }
  opaque ghost predicate Good(s: seq<int>) { |set e | e in s| == 0 }
  ghost function Sum(s: seq<int>): int { if |s| == 0 then 0 else s[0] + Sum(s[1..]) }
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
  method Goal(tag: int, x: int, random: int, box: Box, s: set<int>, sq: seq<int>, n: nat, shape: Shape, k: int)
    returns (y: int, head: int, r: set<int>, a: array<int>, ghost gy: int, scaled: int)
    requires tag == 12 ==> |sq| > 0
    modifies box
    ensures tag == 0 ==> y == random + 1
    ensures tag == 8 ==> box.f == old(box.f) + 1
    ensures tag == 9 ==> unchanged(box)
    ensures tag == 10 ==> y == x + 1
    ensures tag == 11 ==> forall e :: e in r ==> e in s && e % 2 == 0
    ensures tag == 12 ==> head == sq[0]
    ensures tag == 14 ==> a.Length == n
    ensures tag == 14 ==> forall i :: 0 <= i < n ==> a[i] == 1
    ensures tag == 15 ==> Good([x])
    ensures tag == 16 ==> gy == Sum([x])
    ensures tag == 17 ==> scaled == k * shape.Area()
  {
    y, head, r, scaled := 0, 0, {}, 0;
    ghost var g := x;
    gy := Sum([x]);
    a := new int[n];
    if tag == 0 { y := random; }
    if tag == 1 { var e := x; while e < 3 invariant e == 0 { e := e + 1; } }
    if tag == 2 { var m := 0; while m < 3 invariant m <= 1 { m := m + 1; } }
    if tag == 3 { var b := 0; while b < 3 invariant b <= 1 { b := 9; break; } }
    if tag == 4 { var w := 0; while w < 3 invariant w >= 0 { w := w + 1; } }
    if tag == 5 { for f := 0 to 3 invariant f < 3 {} }
    if tag == 6 { Helper(x); }
    if tag == 7 { y := Negative(x); }
    if tag == 8 { box.f := box.f + 2; }
    if tag == 9 { box.f := 2; }
    if tag == 10 { Same(x); calc { x; == x; } assert x == x; y := x; }
    if tag == 11 { r := s; }
    if tag == 12 { head := Head(sq); }
    if tag == 13 { var alias := box; while false invariant alias.f == old(alias.f) {} }
    if tag == 14 { forall i | 0 <= i < n { a[i] := 2; } }
    if tag == 16 { gy := g + 1; }
    if tag == 17 { scaled := shape.Scale(k); if k > 2 { scaled := scaled + 1; } }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
  returns (tag: int, x: int, random: int, box: Box, s: set<int>, sq: seq<int>, n: nat, shape: Shape, k: int) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
  random := r.Int(1, 100);
  box := new Box();
  s := {1, 2};
  sq := [4, 5];
  n := 3;
  shape := new Square(2);
  k := 3;
}
