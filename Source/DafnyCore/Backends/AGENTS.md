# BACKENDS KNOWLEDGE BASE

Scope: `Source/DafnyCore/Backends/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`Backends/` maps resolved Dafny programs to target-language code and target-specific compile/run flows.

## STRUCTURE
```text
Backends/
|- ExecutableBackend.cs        # shared target compile/run contract
|- SinglePassCodeGenerator/    # shared generator base used by many targets
|- CSharp/ Java/ GoLang/ Rust/ Python/ JavaScript/ Cplusplus/
|- Library/                    # library-oriented backend flow
`- Dafny/                      # Dafny-target translation support
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Shared compile/run orchestration | `ExecutableBackend.cs` |
| Shared emission patterns | `SinglePassCodeGenerator/` |
| Target-specific codegen | `<Language>/*CodeGenerator.cs` |
| Target-specific tool invocation | `<Language>/*Backend.cs` |

## CONVENTIONS
- Keep shared behavior in base layers (`ExecutableBackend`, shared code generators) and isolate only true target differences in language folders.
- Respect option-driven behavior (`--include-runtime`, backend flags) uniformly across targets.
- For backend tests, prefer integration LIT patterns that run all compilers by default.

## ANTI-PATTERNS
- Duplicating identical cross-target behavior in each backend instead of shared base helpers.
- Hard-coding target commands or filenames without threading through backend options.
- Introducing backend-only test flows where `%testDafnyForEachCompiler` is sufficient.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
make test name=comp/Hello.dfy
make test-dafny name=comp/Hello.dfy action="build"
dotnet test Source/IntegrationTests --filter "DisplayName~comp/"
```
