# STANDARDLIBRARIES KNOWLEDGE BASE

Scope: `Source/DafnyStandardLibraries/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`DafnyStandardLibraries` is the pre-verified stdlib source and packaging pipeline used by `--standard-libraries`.

## STRUCTURE
```text
DafnyStandardLibraries/
|- src/Std/                      # stdlib source modules
|- src/Std/TargetSpecific/       # extern-backed target-specific assets
|- examples/                     # testable examples per target
|- binaries/                     # packaged .doo outputs
|- scripts/check-examples        # markdown example checker
`- Makefile                      # verify/build/test/check/update pipeline
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Packaging behavior | `Makefile`, `binaries/` |
| Core stdlib modules | `src/Std/` |
| Target-specific extern handling | `src/Std/TargetSpecific/` |
| Contribution rules | `CONTRIBUTING.md`, `README.md` |

## CONVENTIONS
- Keep examples/tests backend-aware via `dafny test` target matrix in `Makefile`.
- Update `.doo` artifacts through `update-binary`; do not hand-edit packaged outputs.
- Documentation examples should include check directives compatible with `scripts/check-examples`.

## ANTI-PATTERNS
- Adding docstrings that only restate signatures.
- Modifying `binaries/*.doo` directly instead of rebuilding.
- Introducing target-specific behavior without matching extern and test coverage updates.

## COMMANDS
```bash
make -C Source/DafnyStandardLibraries verify
make -C Source/DafnyStandardLibraries test
make -C Source/DafnyStandardLibraries check-binary
make -C Source/DafnyStandardLibraries update-binary
make -C Source/DafnyStandardLibraries check-format
```
