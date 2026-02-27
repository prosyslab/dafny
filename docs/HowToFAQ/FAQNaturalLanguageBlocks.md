---
title: What are natural-language block expressions and statements?
---

## Question

What are natural-language block expressions and statements, and how are they handled right now?

## Answer

Natural-language blocks are an experimental syntax that uses double backticks.

```dafny
module {:options "--natural-language-blocks"} M {
  method Demo() {
    var x := ``pick any int value``;
    ``describe an intent-only step``;
  }
}
```

Current behavior is intentionally placeholder-only:

- Parsing is gated by `--natural-language-blocks`.
- Without that option, parsing reports: `Natural-language blocks are supported only with --natural-language-blocks`.
- Resolver emits a warning: `Natural-language blocks are parsed experimentally, but semantics are not supported yet`.
- Verification and compilation continue with placeholder handling (`NaturalLanguageExpression` is treated as a placeholder value, and `NaturalLanguageStatement` is treated as a no-op).

This feature is experimental and its semantics are expected to change.
