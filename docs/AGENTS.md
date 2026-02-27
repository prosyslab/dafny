# DOCS KNOWLEDGE BASE

Scope: `docs/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`docs/` contains website content, tutorials/FAQ, and reference-manual sources with a mixed Jekyll + Makefile pipeline.

## STRUCTURE
```text
docs/
|- DafnyRef/             # reference manual source + PDF generation pipeline
|- OnlineTutorial/       # user tutorial content
|- HowToFAQ/             # troubleshooting and error docs
|- dev/                  # release-note fragment workflow
|- examples/             # docs examples and snippets
`- Jekyll config/assets  # _config.yml, _layouts, _includes, style assets
```

## CHILD GUIDES
- `docs/DafnyRef/AGENTS.md`

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Reference manual content/build | `docs/DafnyRef/` |
| Release note fragment rules | `docs/dev/README.md` |
| End-user docs pages | `docs/OnlineTutorial/`, `docs/HowToFAQ/`, `docs/Compilation/` |
| Site-level behavior | `docs/_config.yml`, `docs/index.html`, `docs/_layouts/` |

## CONVENTIONS
- Keep docs changes aligned with user-visible code changes and release notes.
- Follow fragment naming in `docs/dev/README.md` (`<issue|description>.<kind>`).
- Preserve docs pipeline compatibility (GitHub markdown/Jekyll and reference-manual generation flow).

## ANTI-PATTERNS
- Putting release-note text only in PR descriptions; fragment files belong in `docs/dev/news/`.
- Breaking docs examples without running existing checks.
- Duplicating long content across docs areas when one canonical page can be linked.

## COMMANDS
```bash
make -C docs/DafnyRef
make -C docs/DafnyRef options
make -C docs/DafnyRef features
```
