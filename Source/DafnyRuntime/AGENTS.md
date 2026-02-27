# DAFNYRUNTIME KNOWLEDGE BASE

Scope: `Source/DafnyRuntime/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`DafnyRuntime` contains runtime support for all targets and generated system-module artifacts used by compiler outputs.

## STRUCTURE
```text
DafnyRuntime/
|- DafnyRuntime.cs                     # C# runtime core
|- Makefile                            # system-module generation/check/update
|- systemModulePopulator.dfy           # generation source
|- DafnyRuntimeSystemModule.cs         # generated C# system module
|- DafnyRuntimeJava/ Go/ Go-gomod/
|- DafnyRuntimeJs/ Python/ Rust/
`- DafnyRuntimeDafny/                  # Dafny-authored runtime source
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| C# runtime behavior | `DafnyRuntime.cs` |
| Generated system-module flow | `Makefile`, `systemModulePopulator.dfy` |
| Go mode differences | `DafnyRuntimeGo/`, `DafnyRuntimeGo-gomod/README.md` |
| Per-language runtime packaging | `DafnyRuntime<Lang>/` |

## CONVENTIONS
- Treat system-module files as generated artifacts; use check/update targets rather than manual edits.
- Keep language runtime trees aligned when changing shared semantics.
- Respect Go split: both GoPath and gomod variants remain supported in-tree.

## ANTI-PATTERNS
- Hand-editing generated runtime outputs (`DafnyRuntimeSystemModule.cs`, `DafnyRuntimeSystemModule.js`, generated Java/Go/Rust modules).
- Updating only one language runtime when behavior should stay cross-target consistent.
- Skipping runtime-specific checks after touching generation or runtime primitives.

## COMMANDS
```bash
make -C Source/DafnyRuntime check-system-module
make -C Source/DafnyRuntime update-system-module
make -C Source/DafnyRuntime/DafnyRuntimeGo check-system-module
make -C Source/DafnyRuntime/DafnyRuntimeRust test
dotnet test Source/DafnyRuntime.Tests
```
