# SOURCE KNOWLEDGE BASE

Scope: `Source/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins for files under `Source/`.

## OVERVIEW
`Source/` holds all compiler, tooling, runtime, and test implementation projects in `Source/Dafny.sln`.

## STRUCTURE
```text
Source/
|- DafnyCore/               # compiler core (AST, rewriters, resolver, verifier, backends)
|- DafnyDriver/             # CLI command surface
|- DafnyLanguageServer/     # LSP server implementation
|- DafnyRuntime/            # target-language runtimes and generated system modules
|- DafnyStandardLibraries/  # pre-verified stdlib source + packaging
|- IntegrationTests/        # xUnit + LIT harness and corpus
|- XUnitExtensions/         # file-theory and LIT interpreter internals
`- *.Test/                  # project-specific unit/integration test projects
```

## CHILD GUIDES
- `Source/DafnyCore/AGENTS.md`
- `Source/DafnyDriver/AGENTS.md`
- `Source/DafnyLanguageServer/AGENTS.md`
- `Source/DafnyRuntime/AGENTS.md`
- `Source/DafnyStandardLibraries/AGENTS.md`
- `Source/IntegrationTests/AGENTS.md`

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Parse/resolve/verify pipeline | `Source/DafnyCore/` |
| CLI command behavior | `Source/DafnyDriver/` |
| LSP handlers/workspace state | `Source/DafnyLanguageServer/` |
| Runtime target issues | `Source/DafnyRuntime/` |
| Standard library packaging/externs | `Source/DafnyStandardLibraries/` |
| LIT tests and expected outputs | `Source/IntegrationTests/TestFiles/LitTests/LitTest/` |

## CONVENTIONS
- Use `Source/Dafny.sln` as the primary build/test scope for source changes.
- Prefer subsystem Makefiles for regeneration (`DafnyCore`, `DafnyRuntime`, `DafnyStandardLibraries`) over ad-hoc commands.
- Keep LIT tests backend-uniform by default (`%testDafnyForEachCompiler`), and document exceptions with `// NONUNIFORM: <reason>`.

## ANTI-PATTERNS
- Editing generated files directly instead of running local update/check targets.
- Treating `IntegrationTests` as regular unit tests; they are display-name-filtered file-theory tests with `.expect` contracts.
- Skipping module-specific tests after changing CLI, resolver, verifier, runtime, or test harness behavior.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/Dafny.sln
make test name=comp/Hello.dfy
make test name=comp/Hello.dfy update=true
make test-dafny name=comp/Hello.dfy action="verify"
```
