# DAFNYREF KNOWLEDGE BASE

Scope: `docs/DafnyRef/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`docs/DafnyRef/` is the reference-manual source and generation pipeline for HTML/PDF outputs.

## STRUCTURE
```text
DafnyRef/
|- DafnyRef.md + section .md files
|- Makefile               # concat/preprocess + pandoc/tectonic pipeline
|- concat                 # markdown assembly helper
|- Options.txt Features.md
|- *.expect               # integration-style expected snippets used in docs checks
`- integration-*/         # target-specific reference examples
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Build pipeline | `Makefile`, `concat` |
| Main content | `DafnyRef.md`, `Types.md`, `Statements.md`, `Expressions.md` |
| Generated options/features | `Options.txt`, `Features.md` |
| Formatting/rendering assets | `head.tex`, `header.tex`, `../KDESyntaxDefinition/` |

## CONVENTIONS
- Keep content compatible with both GitHub markdown rendering and pandoc PDF generation.
- Regenerate option and feature snapshots using Makefile targets instead of manual drift edits.
- Preserve existing section/numbering conventions and include test expectations when examples change.

## ANTI-PATTERNS
- Editing generated option/feature snapshots without running `make options`/`make features`.
- Introducing markdown constructs that render in one pipeline but break the other.
- Leaving `.expect` fixtures stale when reference examples change.

## COMMANDS
```bash
make -C docs/DafnyRef
make -C docs/DafnyRef options
make -C docs/DafnyRef features
make -C docs/DafnyRef clean
```
