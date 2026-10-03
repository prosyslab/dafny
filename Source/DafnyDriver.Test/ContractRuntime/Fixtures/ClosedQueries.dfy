// Clauses decided by closed queries over the observed concrete values.
// Budget: bucket = Size() - 2 (ordinals 4b..4b+3); a guarded clause is trivially true outside its bucket.
// ErasedEntry and Initializer change every sample's entry validity, so each is its own campaign.

// == source Budget ==
module M {
  datatype D = A | B | ghost C
  function Sum(k: nat): int { if k == 0 then 0 else k + Sum(k - 1) }
  ghost function Bad(x: int): (b: bool) ensures b { forall k: int :: k != k }
  function HelperFalse(x: int): bool requires forall k: int :: k * k >= 0 && x < 0 { false }
  function HelperTrue(x: int): bool requires forall k: int :: k == k && x > 0 { true }
  method Goal(tag: int, x: int) returns (d: D)
    ensures tag == 0 ==> forall n: int :: n <= x
    ensures tag == 1 ==> d != C && d != A
    ensures tag == 2 ==> forall k: nat :: Sum(k) >= 0
    ensures tag == 3 ==> Bad(x)
    ensures tag == 4 ==> HelperFalse(x)
    ensures tag == 5 ==> HelperTrue(x)
  { d := A; }
}
// == generator Budget ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
}

// == source ErasedEntry ==
module M { datatype D = A | B | ghost C method Goal(d: D) requires d != C && d != A ensures false {} }
// == generator ErasedEntry ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (d: D) { d := A; }

// == source Initializer ==
module M {
  function Seed(): int { 7 }
  class Box { var v: int const tag: int := Seed() constructor(a: int) ensures v == a { v := a; } }
  method Goal(b: Box) returns (r: int) ensures r == b.v + 1 { r := b.v; }
}
// == generator Initializer ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (b: Box) { b := new Box(1); }
