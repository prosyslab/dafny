// RUN: %baredafny complexity --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny complexity --use-basename-for-filename --max-score 6 "%s" > "%t.max-ok"
// RUN: %diff "%s.expect" "%t.max-ok"
// RUN: %exits-with 2 %baredafny complexity --use-basename-for-filename --max-score 5 "%s" > "%t.max-fail"
// RUN: %diff "%s.max-fail.expect" "%t.max-fail"

method Simple() {
  var x := 0;
}

method Nested(n: int) returns (r: int) {
  if n > 0 {
    while r < n {
      if r % 2 == 0 {
        r := r + 1;
      } else {
        r := r + 2;
      }
    }
  }
}

method ProofExcluded(n: int) returns (r: int) {
  assert n == n;
  ghost var g := if n > 0 then 1 else 0;
  r := if n > 0 then 1 else 0;
  assert r >= 0 by {
    if n > 1 {
      assert true;
    }
  }
}

function ByMethod(n: int): int {
  if n <= 0 then 0 else n
} by method {
  if n > 0 {
    return n;
  } else {
    return 0;
  }
}
