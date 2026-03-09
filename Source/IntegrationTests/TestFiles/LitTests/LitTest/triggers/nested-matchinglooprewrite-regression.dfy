// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate IsAdjacentHeapMove(a: seq<int>, a': seq<int>) {
  |a| == |a'| &&
  exists i :: 0 <= i < |a| - 1 &&
    a'[i] < a[i] &&
    a'[i + 1] < a[i + 1] &&
    forall j :: 0 <= j < |a| && j != i && j != i + 1 ==> a'[j] == a[j]
}

method M(a: seq<int>, a': seq<int>)
  decreases *
{
  assume {:axiom} IsAdjacentHeapMove(a, a');
}
