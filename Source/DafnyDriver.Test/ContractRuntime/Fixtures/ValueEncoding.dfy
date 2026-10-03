// Value capture and encoding. One campaign; scenario bucket = Size() - 2, so bucket b owns ordinals 4b..4b+3.
// Every scenario runs only its own code and clause, guarded by `tag == b`.

// == source Main ==
module M {
  datatype Result<T> = Ok(value: T) | Error
  datatype Envelope<T> = Envelope(data: map<int, seq<Result<T>>>)
  class Box {
    var value: int
    var next: Box?
    constructor(value: int) { this.value := value; this.next := null; }
  }
  class Ghosted {
    ghost var f: int
    ghost var unused: int
    constructor() { f := 7; }
  }
  method Read() returns (result: Result<seq<char>>)
    ensures result == Ok(['f'])
  { result := Ok(['f']); }
  function Pick<T(==)>(a: T, b: T): (c: T) ensures c == a { a }
  function Nested<U(==)>(s: seq<U>): seq<U> { Pick(s, s) }
  method Relay<V(==)>(s: seq<V>) returns (t: seq<V>) ensures t == s { t := Nested(s); }
  method Goal(tag: int, left: Envelope<bv7>, right: Envelope<bv8>, box: Box, cyclic: Box, ghosted: Ghosted,
              n: nat, narrow: bv7, wide: bv8)
    returns (result: Result<seq<char>>, a: array<int>, narrowSeq: seq<bv7>, wideSeq: seq<bv8>)
    modifies box
    ensures tag == 0 ==> result == Error
    ensures tag == 1 ==> false
    ensures tag == 2 ==> box.value == old(box.value) + 2
    ensures tag == 3 ==> cyclic.value == 0
    ensures tag == 4 ==> ghosted.f == 8
    ensures tag == 5 ==> forall i :: 0 <= i < n ==> a[i] == 1
    ensures tag != 7
  {
    result := Error;
    narrowSeq, wideSeq := [], [];
    if tag == 0 { result := Read(); }
    if tag == 2 { box.value := box.value + 1; }
    a := new int[n];
    if tag == 5 {
      var j := 0;
      while j < n invariant 0 <= j <= n { a[j] := 2; j := j + 1; }
    }
    if tag == 6 {
      var values := [tag];
      var y := values[1];
    }
    if tag == 7 { narrowSeq := Relay([narrow]); wideSeq := Relay([wide]); }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
  returns (tag: int, left: Envelope<bv7>, right: Envelope<bv8>, box: Box, cyclic: Box, ghosted: Ghosted,
           n: nat, narrow: bv7, wide: bv8) {
  var size := r.Size();
  tag := size - 2;
  left := Envelope(map[1 := [Ok(7 as bv7)]]);
  right := Envelope(map[1 := [Ok(7 as bv8)]]);
  box := new Box(7);
  cyclic := new Box(7);
  cyclic.next := cyclic;
  ghosted := new Ghosted();
  n := 2;
  narrow := 7;
  wide := 7;
}
