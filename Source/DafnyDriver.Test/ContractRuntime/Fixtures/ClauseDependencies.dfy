// Original logical dependencies certified before scalar closed clause evidence is admitted.
// Main: bucket = Size() - 2 (ordinals 4b..4b+3); each bucket calls only its own helper, whose closed
// postcondition reaches its own Identity definition.
// Budget: the single-dependency program, run with a zero and a one-query budget.
// Bodyless: a bodyless logical dependency is a missing draft, which stops the whole campaign.

// == source Main ==
module M {
  ghost function IdentityValid(x: int): int ensures IdentityValid(x) == x { x }
  ghost function IdentityInvalid(x: int): int ensures IdentityInvalid(x) == x + 1 { x }
  ghost function IdentityTrusted(x: int): int ensures IdentityTrusted(x) == x { assume false; x }
  opaque ghost function IdentityOpaque(x: int): int ensures true { x }
  method HelpValid(x: int) ensures forall n: int :: n * n >= 0 && IdentityValid(x) == x {}
  method HelpInvalid(x: int) ensures forall n: int :: n * n >= 0 && IdentityInvalid(x) == x {}
  method HelpTrusted(x: int) ensures forall n: int :: n * n >= 0 && IdentityTrusted(x) == x {}
  method HelpOpaque(x: int) ensures forall n: int :: n * n >= 0 && IdentityOpaque(x) == x {}
  method Goal(tag: int, x: int) returns (r: int) ensures r == x + 1 {
    if tag == 0 { HelpValid(x); }
    if tag == 1 { HelpInvalid(x); }
    if tag == 2 { HelpTrusted(x); }
    if tag == 3 { HelpOpaque(x); }
    r := x;
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (tag: int, x: int) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
}

// == source Budget ==
module M {
  ghost function Identity(x: int): int ensures Identity(x) == x { x }
  method Help(x: int) ensures forall n: int :: n * n >= 0 && Identity(x) == x {}
  method Goal(x: int) returns (r: int) ensures r == x + 1 { Help(x); r := x; }
}
// == generator Budget ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source Bodyless ==
module M {
  ghost function {:axiom} Identity(x: int): int ensures Identity(x) == x
  method Help(x: int) ensures forall n: int :: n * n >= 0 && Identity(x) == x {}
  method Goal(x: int) returns (r: int) ensures r == x + 1 { Help(x); r := x; }
}
// == generator Bodyless ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }
