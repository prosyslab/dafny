// RUN: %resolve --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "--natural-language-blocks"} EnabledNaturalLanguageBlocks {
  method UsesNaturalLanguageBlockAsExpression() {
    assert ``pick a deterministic integer`` == 0;
  }

  method UsesNaturalLanguageBlockAsStatement() {
    ``increment x in a human-readable way``;
  }
}
