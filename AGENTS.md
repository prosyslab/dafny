# DAFNY SUBTREE KNOWLEDGE BASE

**Parent:** `../AGENTS.md`

## OVERVIEW
`dafny/` is an embedded upstream Dafny toolchain and codebase with independent build, test, style, and generated-file rules.

## WHERE TO LOOK
| Task | Location | Notes |
|------|----------|-------|
| Local authority | `dafny/CLAUDE.md` | primary conventions for this subtree |
| Core implementation | `dafny/Source/` | C# compiler, resolver, language server, runtime |
| Build/test scripts | `dafny/Makefile`, `dafny/Scripts/` | local command wrappers and release tooling |
| CI workflows | `dafny/.github/workflows/` | reusable matrix jobs and nightly/release gates |
| Documentation | `dafny/docs/` | language + integration references |

## CONVENTIONS
- Use Dafny-local commands (`dotnet build`, `make test`, `make format`, `make format-dfy`).
- Follow C# formatting/style rules from `dafny/.editorconfig` and `dafny/CLAUDE.md`.
- Preserve existing namespace style and nullable directives in touched C# files.
- Run relevant Dafny tests after changes in this subtree.

## GENERATED FILES (DO NOT HAND-EDIT)
- `dafny/Source/DafnyCore/GeneratedFromDafny/*`
- `dafny/Source/DafnyCore.Test/GeneratedFromDafny/*`
- `dafny/Source/DafnyRuntime/DafnyRuntimeSystemModule.cs`
- `dafny/Source/DafnyCore/Parser.cs`
- `dafny/Source/DafnyCore/Scanner.cs`

## ANTI-PATTERNS
- Applying root Python lint/test workflows as if they governed this subtree.
- Editing generated artifacts directly instead of regenerating through build scripts.
- Skipping Dafny-local formatting and test commands after code changes.

## LOCAL COMMANDS
```bash
dotnet build Source/Dafny.sln
make format
make format-dfy
make test name=comp/Hello.dfy
```
