// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rewritten universal splits retain their distinct generated sequence-index binders.
method CheckAllAdjacent(values: seq<int>, ceiling: int)
  requires forall index: nat :: index + 1 < |values| ==>
                                  values[index] <= values[index + 1] &&
                                  values[index + 1] <= ceiling && values[index + 1] < ceiling
{
}

// Rewritten existential splits retain their distinct generated sequence-index binders.
method CheckSomeAdjacent(values: seq<int>, ceiling: int)
  requires exists index: nat :: index + 1 < |values| &&
                                (values[index] <= values[index + 1] ||
                                 values[index + 1] <= ceiling || values[index + 1] < ceiling)
{
}
