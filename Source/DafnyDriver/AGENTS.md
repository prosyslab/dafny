# DAFNYDRIVER KNOWLEDGE BASE

Scope: `Source/DafnyDriver/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`DafnyDriver` is the CLI surface: new command model, legacy compatibility bridge, command handlers, logging, and test wiring.

## STRUCTURE
```text
DafnyDriver/
|- DafnyNewCli.cs                 # root command + command registration
|- Legacy/                        # backward-compatible parser/dispatch
|- Commands/                      # command-specific handler wiring
|- CliCompilation.cs              # shared compile/execute flow
`- *VerificationLogger.cs         # CLI result/log output surfaces
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Command registration | `DafnyNewCli.cs` |
| Legacy/new bridge behavior | `Legacy/DafnyBackwardsCompatibleCli.cs` |
| Individual commands | `Commands/*.cs` |
| Shared CLI execution | `CliCompilation.cs`, `Legacy/SynchronousCliCompilation.cs` |

## CONVENTIONS
- Add new commands as dedicated files in `Commands/` and register once in `DafnyNewCli`.
- Preserve legacy/new dispatch semantics; behavior changes can affect scripts relying on old CLI forms.
- Keep command option handling aligned with `DafnyOptions` and existing logger patterns.

## ANTI-PATTERNS
- Embedding command-specific logic directly in `DafnyNewCli` instead of a command handler class.
- Breaking compatibility-path argument handling without tests.
- Diverging output/log formatting from established logger classes.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/DafnyDriver.Test
dotnet run --project Source/Dafny -- --help
dotnet run --project Source/Dafny -- verify Source/IntegrationTests/TestFiles/LitTests/LitTest/comp/Hello.dfy
```
