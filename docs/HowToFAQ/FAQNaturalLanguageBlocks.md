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

### Current behavior

- Parsing is gated by `--natural-language-blocks`.
- Without that option, parsing reports: `Natural-language blocks are supported only with --natural-language-blocks`.
- For most source-processing commands, Dafny then runs the experimental natural-language expansion workflow before continuing with the requested command.

### Expansion workflow

When `--natural-language-blocks` is enabled for commands `verify` and `run`:

- Dafny parses the original program and finds each method that still contains natural-language placeholders.
- Dafny sends one request per method to either a configured endpoint (`DAFNY_NL_API_URL`) or the OpenAI Responses API when `OPENAI_API_KEY` is set and `DAFNY_NL_API_URL` is unset.
- The endpoint returns concrete replacements for every placeholder in that method.
- Dafny applies those replacements, re-runs parsing, resolution, and verification, and retries up to 10 times if needed. (For now this number is hard-coded, however, it is going to be customizable later.)
- After the first attempt, Dafny re-requests only the methods that still fail.
- On success, Dafny writes rewritten files with the `.nlgen.dfy` suffix and continues the requested command on those rewritten files.

### Practical notes

- The original source file is not overwritten.
- In NL mode, later commands operate on the rewritten `.nlgen` program rather than on the original placeholders.
- `--natural-language-blocks` does not support stdin input.

### Inspecting intermediate artifacts

If you pass `--natural-language-intermediate-products-directory <dir>`, Dafny writes artifacts such as:

- `*.prompt.<callable>.attempt<N>.txt`: the human-readable prompt with real line breaks.
- `*.task.<callable>.attempt<N>.json`: the exact JSON request body.
- `*.response.<callable>.attempt<N>.json`: the saved API response.
- `*.nlgen.attempt<N>.dfy`: the rewritten source used for that retry attempt.
