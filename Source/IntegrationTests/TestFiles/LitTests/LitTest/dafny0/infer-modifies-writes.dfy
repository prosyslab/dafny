// RUN: %verify --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box {
  var value: int
  var tag: int

  method {:inferModifies} Update(a: array<int>, b: Box, flag: bool)
    requires a.Length > 0
  {
    if flag {
      value := GetValue();
    } else {
      b.value := 2;
    }
    a[0] := 3;
  }
}

method GetValue() returns (v: int)
  modifies {}
  ensures v == 1
{
  v := 1;
}

// Require the generated field-specific contract to fit the handwritten caller frame.
method Caller(a: array<int>, b: Box, c: Box)
  requires a.Length > 0
  modifies a, b`value, c`value
  ensures b.tag == old(b.tag) && c.tag == old(c.tag)
{
  b.Update(a, c, true);
}

method {:inferModifies} WithLoopFrame(b: Box)
  ensures b.value == old(b.value)
{
  for i := 0 to 1
    modifies b`tag
  {
  }
}
