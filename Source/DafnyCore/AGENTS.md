# DAFNYCORE KNOWLEDGE BASE

Scope: `Source/DafnyCore/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`DafnyCore` is the compiler/verification core: grammar, AST, rewriters, resolver, verifier, and target backends.

## STRUCTURE
```text
Source/DafnyCore/
|- AST/        # syntax tree, types, modules, members
|- Backends/   # target-language translation and compilation adapters
|- Resolver/   # name resolution, type inference, pre-type phases
|- Rewriters/  # phase-based AST transformations
|- Verifier/   # Boogie translation + proof-obligation infrastructure
|- Prelude/    # core Dafny preludes
`- Makefile    # parser generation + generated-from-Dafny sync checks
```

## CHILD GUIDES
- `Source/DafnyCore/Backends/AGENTS.md`
- `Source/DafnyCore/Resolver/AGENTS.md`
- `Source/DafnyCore/Verifier/AGENTS.md`
- `Source/DafnyCore/Rewriters/AGENTS.md`

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Grammar/parsing | `Dafny.atg`, `Parser.cs`, `Scanner.cs`, `Coco/` |
| Pipeline entry | `DafnyMain.cs`, `Pipeline/Compilation.cs` |
| Options and CLI plumbing | `DafnyOptions.cs`, `Options/` |
| AST semantics | `AST/` |
| Rewriter phases | `Rewriters/` |
| Resolution/typechecking | `Resolver/` |
| Verification/Boogie | `Verifier/` |

## CONVENTIONS
- Prefer phase-correct modifications: AST rewrites normally belong in `PreResolve` or `PostResolveIntermediate` rewriter phases.
- Rewriter style is explicit: either in-place mutation for structural updates or cloner-based replacement for localized expression/statement edits.
- Keep deterministic behavior and stable diagnostics; many integration tests lock exact output text.

## ANTI-PATTERNS
- Do not edit `Parser.cs`/`Scanner.cs` directly; regenerate from `Dafny.atg`.
- Do not edit `GeneratedFromDafny/*` manually; regenerate and diff.
- Do not bypass generated sync checks in `Source/DafnyCore/Makefile`.

## COMMANDS
```bash
make -C Source/DafnyCore format
make -C Source/DafnyCore check-format
make -C Source/DafnyCore test
make dfy-to-cs
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ClassName"
```
