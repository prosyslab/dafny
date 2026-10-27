module Toy {
  function Double(x: int): int { 2 * x }
  method M(x: int) returns (r: int)
    requires x >= 0
    ensures r == Double(x)
  { r := 2 * x; }
}
