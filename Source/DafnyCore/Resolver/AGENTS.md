# RESOLVER KNOWLEDGE BASE

Scope: `Source/DafnyCore/Resolver/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`Resolver/` is the semantic core for name resolution, type inference, constraint solving, and pre-type processing.

## STRUCTURE
```text
Resolver/
|- ModuleResolver.cs
|- ProgramResolver.cs
|- NameResolutionAndTypeInference/
|- PreType/
|- BoundsDiscovery/
`- resolution visitors/checkers
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Top-level orchestration | `ModuleResolver.cs`, `ProgramResolver.cs` |
| Name/type inference | `NameResolutionAndTypeInference/` |
| Pre-type phases | `PreType/` |
| Bound inference | `BoundsDiscovery/` |
| Resolution diagnostics | `ResolutionErrors.cs` |

## CONVENTIONS
- Preserve phase ordering and invariants between pre-type and full type-resolution passes.
- Keep diagnostics deterministic; integration tests assert exact text and location contracts.
- Prefer targeted visitor/checker changes over broad rewrites when adjusting one rule family.

## ANTI-PATTERNS
- Bypassing resolver context/scope utilities with ad-hoc symbol lookups.
- Mixing pre-type and full-type assumptions in the same rule path.
- Altering error wording/shape without updating affected `.expect` tests.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~Resolver"
make test name=git-issues/
```
