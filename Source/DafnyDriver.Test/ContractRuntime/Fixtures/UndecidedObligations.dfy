// Goal obligations that stay undecided in valid samples (unavailable ghost values, resolver exclusions,
// erased checks and closed clauses without budget). No bucket decides a goal obligation, so the
// campaign status is "No goal obligation was decided in a valid sample.".
// Bucket = Size() - 2 (ordinals 4b..4b+3).

// == source Main ==
module M {
  ghost method Hidden() returns (y: int) { y := 1; }
  ghost method Unknown() returns (v: int) { v :| true; }
  datatype Choice = ghost Secret | Visible
  ghost function Choose(): Choice { Secret }
  datatype D = A | B | ghost C
  method Goal(tag: int, x: int) returns (ghost gy: int, d: D)
    ensures tag == 1 ==> gy == x
    ensures tag == 2 ==> Choose() == Secret
    ensures tag == 3 ==> d != C && d != A
    ensures tag == 4 ==> forall n: int :: n <= x
  {
    if tag == 0 {
      ghost var y := Hidden();
      while false invariant y == x {}
    }
    gy := Unknown();
    d := A;
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
}
