// RUN: %verify --show-hints --allow-warnings --suppress-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that the CLI option --suppress-warnings hides all Warning/Info diagnostics,
// even when --show-hints is enabled.

ghost predicate f(x: int)

method M() {
  // Typically produces a trigger warning without any {:nowarn}.
  assert forall n: nat :: (n != 0) == f(n) || true;
}


