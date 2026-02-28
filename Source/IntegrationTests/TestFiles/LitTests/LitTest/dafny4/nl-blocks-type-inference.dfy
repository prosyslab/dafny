// RUN: %exits-with 2 %resolve --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "--natural-language-blocks"} NaturalLanguageTypeInference {
  method InferFromContext() {
    var b: bool := ``decide truth value``;
    var i: int := ``choose integer``;
    var j := if ``decide guard`` then 1 else 2;
    assert b && j >= 0;
  }

  method FailsWithoutTypeContext() {
    assert ``left operand has no type context`` == ``right operand has no type context``;
  }
}
