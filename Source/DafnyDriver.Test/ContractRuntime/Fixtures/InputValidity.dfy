// Declared input and output type constraints decide sample validity.
// Bucket = Size() - 2 (ordinals 4b..4b+3). Every input and output is valid except the one owned by the bucket;
// bucket 10 is the all-valid control. The marker clause `tag < 0` fails in every valid sample.

// == source Main ==
module M {
  newtype Small = x: int | 0 <= x < 10
  datatype Box = Box(n: nat)
  datatype BoxSeq = BoxSeq(n: seq<nat>)
  class C { constructor() {} }
  datatype Wrapped = Wrapped(c: C)
  datatype List = Nil | Cons(n: nat, tail: List)
  datatype Tree = Node(n: nat, children: map<int, Tree>)
  method Goal(tag: int, n: nat, small: seq<Small>, box: Box, boxSeq: BoxSeq, m: map<int, seq<nat>>,
              deep: seq<seq<seq<seq<seq<nat>>>>>, c: C, wrapped: Wrapped, list: List, tree: Tree)
    returns (outBox: Box, outSeq: seq<Box>, outMap: map<int, seq<Box>>, marker: int)
    ensures tag < 0
  {
    outBox, outSeq, outMap, marker := Box(1), [Box(1)], map[0 := [Box(1)]], 0;
    if tag == 11 { outBox := Box(-1); }
    if tag == 12 { outSeq := [Box(-1)]; }
    if tag == 13 { outMap := map[0 := [Box(-1)]]; }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
  returns (tag: int, n: nat, small: seq<Small>, box: Box, boxSeq: BoxSeq, m: map<int, seq<nat>>,
           deep: seq<seq<seq<seq<seq<nat>>>>>, c: C, wrapped: Wrapped, list: List, tree: Tree) {
  var size := r.Size();
  tag := size - 2;
  var instance := new C();
  n, small, box, boxSeq, m := 1, [3 as Small], Box(1), BoxSeq([1]), map[0 := [1]];
  deep, c, wrapped, list, tree := [[[[[1]]]]], instance, Wrapped(instance), Cons(0, Cons(1, Nil)), Node(0, map[1 := Node(2, map[])]);
  if tag == 0 { n := -1; }
  if tag == 1 { small := [3 as Small, 12 as Small]; }
  if tag == 2 { box := Box(-1); }
  if tag == 3 { boxSeq := BoxSeq([-1]); }
  if tag == 4 { m := map[0 := [-1]]; }
  if tag == 5 { deep := [[[[[-1]]]]]; }
  if tag == 6 { c := null; }
  if tag == 7 { wrapped := Wrapped(null); }
  if tag == 8 { list := Cons(0, Cons(-1, Nil)); }
  if tag == 9 { tree := Node(0, map[1 := Node(-1, map[])]); }
}
