// RUN: %resolve --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "--natural-language-blocks"} EnabledNaturalLanguageBlocks {
  method UsesNaturalLanguageBlockAsExpression() {
    print ``pick a deterministic integer``;
  }

  method UsesNaturalLanguageBlockAsStatement() {
    ``increment x in a human-readable way``;
  }
}
