// Requests rejected before the runtime diagnostic is compiled. Each section pair is one campaign.

// == source Drafts ==
module M {
  method Helper(x: int) returns (y: int) ensures y == x
  method Scaffold(x: int) returns (y: int) ensures y == x { assert false; }
  method {:extern} {:axiom} NativeMethod(x: int)
  function {:extern} NativeFunction(x: int): int
  method Goal(x: int) returns (y: int) {
    y := Helper(x);
    y := Scaffold(y);
    NativeMethod(y);
    y := NativeFunction(y);
  }
}

// == source NoGenerator ==
module M { method Goal(x: int) {} }

// == source GeneratorDraft ==
module M {
  method MakeInput() returns (x: int) ensures x >= 0
  method Goal(x: int) returns (r: int) ensures r == x { r := x; }
}
// == generator GeneratorDraft ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := MakeInput(); }

// == source GeneratorSyntax ==
module M { method Goal(x: int) {} }
// == generator GeneratorSyntax ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) {
  x := ;
}

// == source OrdinalInput ==
module M { method Goal(ghost x: ORDINAL) {} }
// == generator OrdinalInput ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: ORDINAL) { x := 0; }

// == source HigherOrderShape ==
module M {
  function Id<T>(x: T): T { x }
  method Goal(x: int) ensures false { var f := Id<int>; var y := f(x); }
}
// == generator HigherOrderShape ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source ShapeCollision ==
module M {
  function Id<T>(pbtTypeShape0: T): T { pbtTypeShape0 }
  method Goal(x: int) ensures false { var y := Id(x); }
}
// == generator ShapeCollision ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }
