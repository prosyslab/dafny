// Target assertion obligations. Scenario bucket = Size() - 2 (ordinals 4b..4b+3).

// == source Main ==
module M {
  ghost method Hidden() returns (y: int) { y := 0; }
  lemma ProofStep() {}
  function Identity<T>(x: T): T requires true { x }
  method Good() { assert true; }
  method Bad() ensures false {}

  method Goal(tag: int, x: int)
    requires tag != 4
    ensures true
  {
    if tag == 0 { Good(); assert Identity<int>(x) == x; }
    if tag == 1 { assert x > 0; }
    if tag == 2 {
      assert true by {
        var i := 0;
        while i < 1 invariant 0 <= i <= 1 { i := i + 1; }
        ProofStep();
        assert Identity<int>(i) == i;
        assert false;
      }
    }
    if tag == 3 { Bad(); assert false; }
    if tag == 4 { assert false; }
    if tag == 5 { assert forall i: int :: false; Bad(); }
    if tag == 6 { ghost var y := Hidden(); assert y == x; }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := 0;
}
