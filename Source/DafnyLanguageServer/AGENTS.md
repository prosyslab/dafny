# DAFNYLANGUAGESERVER KNOWLEDGE BASE

Scope: `Source/DafnyLanguageServer/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`DafnyLanguageServer` implements Dafny's LSP server: request handlers, workspace model, diagnostics, and server lifecycle.

## STRUCTURE
```text
DafnyLanguageServer/
|- LanguageServer.cs            # bootstrap, host, startup/shutdown
|- DafnyLanguageServer.cs       # service wiring and initialization
|- Handlers/                    # LSP request/notification handlers
|- Workspace/                   # document state + verification diagnostics
|- Language/                    # syntax tree, semantic support
`- Caching/ Plugins/ Util/
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Server startup and options | `LanguageServer.cs`, `README.md` |
| Handler registration | `DafnyLanguageServer.cs`, `Handlers/` |
| Workspace and diagnostics | `Workspace/` |
| Syntax/semantic traversal | `Language/` |

## CONVENTIONS
- Keep request-name mappings, handlers, and workspace effects consistent; missing wiring silently drops features.
- Respect documented configuration precedence: CLI options over appsettings values.
- Preserve incremental/interactive behavior assumptions used by IDE tests.

## ANTI-PATTERNS
- Adding handlers without registering or naming them in the existing request wiring.
- Blocking long-running operations directly on request paths without current scheduling patterns.
- Changing diagnostics payload shape without updating language-server tests.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/DafnyLanguageServer.Test
dotnet DafnyLanguageServer.dll --documents:verify=onsave
```
