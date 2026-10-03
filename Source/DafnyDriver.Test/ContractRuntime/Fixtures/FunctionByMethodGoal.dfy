// Function-by-method goals. Main: bucket = Size() - 2 (ordinals 4b..4b+3).
// Bucket 0 violates the declared postcondition, bucket 1 the defining expression, bucket 2 is a correct recursion.
// Helper: a bodyless method reached only through the by-method body (drafts change the campaign request).

// == source Main ==
module M {
  function Goal(tag: int, n: nat): int
    ensures tag == 0 ==> Goal(tag, n) == n + 1
  { if tag == 1 then n + 1 else if tag == 2 then (if n == 0 then 0 else Goal(tag, n - 1) + 1) else n }
  by method {
    if tag != 2 { return n; }
    var i, c := 0, 0;
    while i < n invariant 0 <= i <= n invariant c == Goal(tag, i) { i, c := i + 1, c + 1; }
    return c;
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, n: nat) {
  var size := r.Size();
  tag := size - 2;
  n := 1;
  if tag == 2 { n := r.Nat(5); }
}

// == source Helper ==
module M {
  method Helper(x: int) returns (y: int) ensures y == x
  function Goal(x: int): int { x } by method { var y := Helper(x); return y; }
}
// == generator Helper ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }
