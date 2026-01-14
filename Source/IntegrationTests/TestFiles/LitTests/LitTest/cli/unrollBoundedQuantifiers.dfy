// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// RUN: %verify --unroll-bounded-quantifiers 1000 "%s"
//
// CHECK: Error: assertion could not be proved

function g(t: int): int { t }

method Main() {
  // Without bounded-quantifier unrolling, the explicit trigger prevents Z3 from finding the counterexample.
  assert !(forall t {:trigger g(t)} :: 1 <= t <= 100 ==> t == 99);
}

