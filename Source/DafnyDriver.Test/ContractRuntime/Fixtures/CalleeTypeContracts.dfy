// Contracts of functions evaluated by type constraints, callee outputs and specification formals.
// Bucket = Size() - 2 (ordinals 4b..4b+3). Constrained inputs default to 0, which short-circuits the
// constraint before its function is called; only the owning bucket supplies 3. The marker clause
// `tag < 0` fails in every valid sample.

// == source Main ==
module M {
  function AcceptNeg(n: int): bool requires n < 0 { true }
  type DomainT = n: int | n == 0 || AcceptNeg(n) witness 0
  function AcceptQ(n: int): bool requires forall k: int :: k * k >= 0 && n < 0 { true }
  type UncheckedT = n: int | n == 0 || AcceptQ(n) witness 0
  function AcceptValid(n: int): (v: bool) ensures v { true }
  function AcceptInvalid(n: int): (v: bool) ensures !v { true }
  type SubV = n: int | n == 0 || AcceptValid(n) witness 0
  type SubI = n: int | n == 0 || AcceptInvalid(n) witness 0
  newtype NewV = n: int | n == 0 || AcceptValid(n) witness 0
  newtype NewI = n: int | n == 0 || AcceptInvalid(n) witness 0
  datatype D = D(n: int)
  type DatV = d: D | d.n == 0 || AcceptValid(d.n) witness D(0)
  type DatI = d: D | d.n == 0 || AcceptInvalid(d.n) witness D(0)
  datatype Box = Box(n: nat)
  method HelperBox(bad: bool) returns (b: Box, marker: int) { b := if bad then Box(-1) else Box(1); marker := 0; }
  method HelperSeq(bad: bool) returns (b: seq<Box>, marker: int) { b := if bad then [Box(-1)] else [Box(1)]; marker := 0; }
  class C { constructor() {} }
  function AcceptC(x: C): bool { true }
  method HelperC(x: C?) { var b := AcceptC(x); }
  function HelperQ(x: int): bool requires forall k: int :: k * k >= 0 && x < 0 { false }
  method Goal(tag: int, x: int, domain: DomainT, unchecked: UncheckedT, subV: SubV, subI: SubI,
              nestV: seq<seq<SubV>>, nestI: seq<seq<SubI>>, newV: NewV, newI: NewI,
              newNestV: seq<seq<NewV>>, newNestI: seq<seq<NewI>>, datV: DatV, datI: DatI, cn: C?)
    returns (box: Box, boxes: seq<Box>, marker: int)
    ensures (tag == 16 || tag == 17) ==> !AcceptC(cn)
    ensures tag == 19 ==> HelperQ(x)
    ensures tag < 0
  {
    box, boxes, marker := Box(1), [Box(1)], 0;
    if tag == 12 || tag == 13 { box, marker := HelperBox(tag == 12); }
    if tag == 14 || tag == 15 { boxes, marker := HelperSeq(tag == 14); }
    if tag == 18 { HelperC(cn); }
  }
}
// == generator Main ==
method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
  returns (tag: int, x: int, domain: DomainT, unchecked: UncheckedT, subV: SubV, subI: SubI,
           nestV: seq<seq<SubV>>, nestI: seq<seq<SubI>>, newV: NewV, newI: NewI,
           newNestV: seq<seq<NewV>>, newNestI: seq<seq<NewI>>, datV: DatV, datI: DatI, cn: C?) {
  var size := r.Size();
  tag := size - 2;
  x := 1;
  domain, unchecked, subV, subI, nestV, nestI := 0, 0, 0, 0, [[0]], [[0]];
  newV, newI, newNestV, newNestI, datV, datI := 0 as NewV, 0 as NewI, [[0 as NewV]], [[0 as NewI]], D(0), D(0);
  cn := new C();
  if tag == 0 { domain := 3; }
  if tag == 1 { unchecked := 3; }
  if tag == 2 { subV := 3; }
  if tag == 3 { subI := 3; }
  if tag == 4 { nestV := [[3]]; }
  if tag == 5 { nestI := [[3]]; }
  if tag == 6 { newV := 3 as NewV; }
  if tag == 7 { newI := 3 as NewI; }
  if tag == 8 { newNestV := [[3 as NewV]]; }
  if tag == 9 { newNestI := [[3 as NewI]]; }
  if tag == 10 { datV := D(3); }
  if tag == 11 { datI := D(3); }
  if tag == 17 || tag == 18 { cn := null; }
}
