# INTEGRATIONTESTS KNOWLEDGE BASE

Scope: `Source/IntegrationTests/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`IntegrationTests` runs Dafny's LIT-style corpus through an xUnit-based interpreter (`XUnitExtensions`).

## STRUCTURE
```text
IntegrationTests/
|- LitTests.cs                                # test harness + command substitution wiring
|- IntegrationTests.csproj
|- TestFiles/LitTests/LitTest/                # .dfy tests + .expect contracts
`- README.md                                  # harness entry summary
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Harness behavior/macros | `LitTests.cs` |
| Test authoring conventions | `TestFiles/LitTests/LitTest/README.md` |
| Test corpus | `TestFiles/LitTests/LitTest/` |
| LIT interpreter internals | `../XUnitExtensions/Lit/` |

## CONVENTIONS
- Use display-name filtering for targeted runs (`DisplayName~<path-fragment>`).
- Default compile/run tests should use `%testDafnyForEachCompiler`; mark deliberate exceptions with `// NONUNIFORM: <reason>`.
- Keep macro definitions in `lit.site.cfg` and `LitTests.cs` synchronized.

## ANTI-PATTERNS
- Manually duplicating per-backend compile/run boilerplate where uniform macro commands apply.
- Updating expected outputs without controlled update mode.
- Treating LIT tests as plain unit tests; they are file-driven contract tests.

## COMMANDS
```bash
dotnet test --logger "console;verbosity=normal" Source/IntegrationTests
dotnet test --logger "console;verbosity=normal" Source/IntegrationTests --filter DisplayName~comp/Hello.dfy
make test name=comp/Hello.dfy
make test name=comp/Hello.dfy update=true
make test-dafny name=comp/Hello.dfy action="verify"
```

## NOTES
- Expect update env vars: `DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE`, `DAFNY_INTEGRATION_TESTS_MODE`, `DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS`, `DAFNY_INTEGRATION_TESTS_ROOT_DIR`, `DAFNY_INTEGRATION_TESTS_IN_PROCESS`.
