// RUN: ! %baredafny resolve --show-snippets:false --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "--natural-language-blocks"} MalformedWhenEnabled {
  method EmptyNaturalLanguageBlock() {
    var a := ````;
  }

  method ExtraDelimiter() {
    var b := ``alpha````;
  }
}

module FeatureDisabled {
  method NaturalLanguageBlocksNeedOptIn() {
    var c := ``this should parse only when enabled``;
  }
}
