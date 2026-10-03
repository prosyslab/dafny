// Counterexamples from finite observations of nonterminating executions.
// Bucket = Size() - 2 (ordinals 4b..4b+3); every bucket except the rejected one runs until the sample timeout.

// == source Main ==
module M {
  method Help() returns (r: int) ensures r == 0 { r := 1; }
  method HelpUnchecked() ensures forall i: int :: i * i >= 0 {}
  method HelpFalse() ensures false {}
  method Goal(tag: int, x: int)
    requires tag == 0 ==> x > 0
    requires tag == 1 ==> x < 0
  {
    if tag == 0 { var i := 0; while true invariant i == 0 { i := 1; } }
    if tag == 1 { while true invariant tag != 1 {} }
    if tag == 2 { var r := Help(); while true invariant tag != 2 {} }
    if tag == 3 { HelpUnchecked(); while true invariant tag != 3 {} }
    if tag == 4 { while true invariant tag != 4 { HelpFalse(); } }
    if tag == 5 { while true {} }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
}
