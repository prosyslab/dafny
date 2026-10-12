// Contract-only lemma goals; each section is an independent immutable source/generator pair.

// == source Main ==
module M {
  lemma MissingProof()
  lemma Goal(x: int)
    requires x >= 0
    ensures x == 0
  {
    MissingProof();
    assert false;
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) {
  var size := r.Size();
  x := 3 - size;
}

// == source Quantified ==
module M {
  datatype Item = Item(value: nat)
  ghost predicate Nonzero(items: seq<Item>) {
    forall i :: 0 <= i < |items| ==> items[i].value > 0
  }
  lemma Goal(items: seq<Item>)
    requires |items| > 0
    ensures Nonzero(items)
}
// == generator Quantified ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (items: seq<Item>) {
  items := [Item(0)];
}

// == source Dependency ==
module M {
  lemma Broken() ensures false {}
  ghost function Identity(x: int): int { Broken(); x }
  lemma Goal(x: int) ensures Identity(x) == 0 {}
}
// == generator Dependency ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source Trusted ==
module M {
  ghost function Identity(x: int): int { assume false; x }
  lemma Goal(x: int) ensures Identity(x) == 0 {}
}
// == generator Trusted ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source PremiseDependency ==
module M {
  ghost predicate Admitted(x: int) { assume false; true }
  lemma Goal(x: int) requires Admitted(x) ensures x == 0 {}
}
// == generator PremiseDependency ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source SelfDependency ==
module M {
  ghost function Identity(x: int): int { Goal(x); x }
  lemma Goal(x: int) ensures Identity(x) == 0 {}
}
// == generator SelfDependency ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source BodylessDependency ==
module M {
  ghost function {:axiom} Identity(x: int): int ensures Identity(x) == x
  lemma Goal(x: int) ensures Identity(x) == 0 {}
}
// == generator BodylessDependency ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source ValidSelfDependency ==
module M {
  lemma Goal(x: nat)
    ensures x == 0 || (Goal(x - 1); true)
    decreases x
  {}
}
// == generator ValidSelfDependency ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: nat) { x := 1; }

// == source BodylessRefinement ==
module M {
  lemma Proof() ensures false
  type Admitted = value: int | (Proof(); value >= 0) witness 0
  lemma Goal(x: Admitted) ensures false {}
}
// == generator BodylessRefinement ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: Admitted) { x := 0; }

// == source TrustedRefinement ==
module M {
  lemma Proof() ensures false { assume false; }
  type Admitted = value: int | (Proof(); value >= 0) witness 0
  lemma Goal(x: Admitted) ensures false {}
}
// == generator TrustedRefinement ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: Admitted) { x := 0; }

// == source SelfRefinement ==
module M {
  lemma Goal() ensures true {}
  type Admitted = value: int | (Goal(); value >= 0) witness 0
  const Initial: Admitted := 0
}
// == generator SelfRefinement ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) {}

// == source VerifiedRefinement ==
module M {
  lemma Proof() ensures true {}
  type Admitted = value: int | (Proof(); value >= 0) witness 0
  lemma Goal(x: Admitted) ensures false {}
}
// == generator VerifiedRefinement ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: Admitted) { x := 0; }

// == source ProofOnlyInput ==
module M {
  lemma GoodProof(x: nat) ensures x >= 0 {}
  lemma Goal(x: nat) ensures (GoodProof(x); false) { assert false; }
}
// == generator ProofOnlyInput ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: nat) { x := 7; }

// == source Hidden ==
module Definition {
  export provides Identity
  opaque ghost function Identity(x: int): int { x }
}
module M {
  import Definition
  lemma Goal(x: int) ensures Definition.Identity(x) == 0 {}
}
// == generator Hidden ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 1; }

// == source Undefined ==
module M {
  lemma Goal(x: int) ensures x / x == 2 {}
}
// == generator Undefined ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }

// == source InvalidType ==
module M {
  type Small = value: int | 0 <= value < 3 witness 0
  datatype Box = Box(value: Small)
  lemma Goal(values: seq<Box>) ensures false {}
}
// == generator InvalidType ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (values: seq<Box>) {
  values := [Box(5)];
}
