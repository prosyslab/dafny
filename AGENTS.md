# PROJECT KNOWLEDGE BASE

Generated: 2026-02-27T09:04:27Z (UTC)
Commit: d340c85da
Branch: vibe
Mode: update
Precedence: nearest `AGENTS.md` wins on conflicts.

## OVERVIEW
Dafny is a verification-first language and toolchain. This repository contains compiler/verification core, CLI and LSP frontends, multi-language runtimes, packaged standard libraries, and a large xUnit+LIT integration suite.

## STRUCTURE
```text
/workspaces/dafny/
|- Source/    # main implementation and tests (see Source/AGENTS.md)
|- docs/      # website, reference manual, release-note pipeline (see docs/AGENTS.md)
|- Scripts/   # helper scripts used by Makefiles/CI
|- Binaries/  # packaged artifacts and checked-in runtime outputs
`- AGENTS.md  # repo-wide defaults and routing
```

## SUBTREE GUIDES
- `Source/AGENTS.md`
- `Source/DafnyCore/AGENTS.md`
- `Source/DafnyCore/Backends/AGENTS.md`
- `Source/DafnyCore/Resolver/AGENTS.md`
- `Source/DafnyCore/Verifier/AGENTS.md`
- `Source/DafnyCore/Rewriters/AGENTS.md`
- `Source/DafnyDriver/AGENTS.md`
- `Source/DafnyLanguageServer/AGENTS.md`
- `Source/DafnyRuntime/AGENTS.md`
- `Source/DafnyStandardLibraries/AGENTS.md`
- `Source/IntegrationTests/AGENTS.md`
- `docs/AGENTS.md`
- `docs/DafnyRef/AGENTS.md`

## WHERE TO LOOK
| Task | Location | Notes |
|------|----------|-------|
| Parse/resolve/verify internals | `Source/DafnyCore/` | Core AST, resolver, rewriters, verifier, backends |
| CLI dispatch and commands | `Source/DafnyDriver/` | Legacy-to-new CLI bridge and command handlers |
| IDE/LSP behavior | `Source/DafnyLanguageServer/` | Handler wiring, workspace state, diagnostics |
| Runtime per target language | `Source/DafnyRuntime/` | C#, Java, Go, JS, Python, Rust runtime code |
| Standard library packaging | `Source/DafnyStandardLibraries/` | `.doo` generation, target-specific extern bundles |
| Integration tests and expect files | `Source/IntegrationTests/TestFiles/LitTests/LitTest/` | `.dfy` + `.expect`, backend-uniform patterns |
| xUnit LIT interpreter internals | `Source/XUnitExtensions/` | File theory and LIT command executor |
| Reference manual pipeline | `docs/DafnyRef/` | Markdown -> PDF/HTML generation pipeline |

## CODE MAP
LSP codemap requests timed out in this environment. Use the subtree guides above for path-level symbol maps.

## CONVENTIONS
- C#: 2-space indent, LF endings, braces required, preserve namespace style and `#nullable` directives (`.editorconfig`).
- Dafny: 2-space indent, no tabs; use `make format-dfy`.
- Private fields use camelCase; constants/static readonly use PascalCase.
- User-visible changes should update `RELEASE_NOTES.md` and usually `docs/DafnyRef/`.
- PRs should include relevant tests (`Source/IntegrationTests/...` and/or `Source/*.Test/...`).

## ANTI-PATTERNS (THIS PROJECT)
- Do not hand-edit generated parser outputs: `Source/DafnyCore/Parser.cs`, `Source/DafnyCore/Scanner.cs`.
- Do not hand-edit generated Dafny-to-C# outputs: `Source/DafnyCore/GeneratedFromDafny/*`, `Source/DafnyCore.Test/GeneratedFromDafny/*`.
- Do not hand-edit generated syntax deserializer: `Source/DafnyCore/AST/SyntaxDeserializer/Generated.cs`.
- Do not hand-edit generated runtime module outputs:
  - `Source/DafnyRuntime/DafnyRuntimeSystemModule.cs`
  - `Source/DafnyRuntime/DafnyRuntimeJs/DafnyRuntimeSystemModule.js`
  - `Source/DafnyRuntime/DafnyRuntimeJava/src/main/dafny-generated/**`
  - `Source/DafnyRuntime/DafnyRuntimeGo/System_/System_.go`
  - `Source/DafnyRuntime/DafnyRuntimeGo/dafny/dafnyFromDafny.go`
  - `Source/DafnyRuntime/DafnyRuntimeGo-gomod/System_/System_.go`
  - `Source/DafnyRuntime/DafnyRuntimeGo-gomod/dafny/dafnyFromDafny.go`
  - `Source/DafnyRuntime/DafnyRuntimeRust/src/system/mod.rs`
- Do not add standard-library docstrings that only restate signatures (`Source/DafnyStandardLibraries/CONTRIBUTING.md`).
- Do not manually duplicate backend compile/run test boilerplate where `%testDafnyForEachCompiler` is appropriate; use `// NONUNIFORM: <reason>` only when needed.

## UNIQUE STYLES
- Compiler pipeline is phase-oriented: parse -> rewriters -> resolve/typecheck -> Boogie translation -> Z3 -> target compile.
- Integration tests are source-file driven (`.dfy`) and output-contract driven (`.expect`, optional backend-specific `.<id>.expect`/`.<id>.check`).
- Runtime and stdlib assets are intentionally checked in and validated by diff-style regeneration commands.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
make boogie
make format
make format-dfy
make test name=comp/Hello.dfy
make test name=comp/Hello.dfy update=true
make test-dafny name=comp/Hello.dfy action="verify"
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ClassName"
dotnet test Source/IntegrationTests --logger "console;verbosity=normal"
make pr
```

## NOTES
- `make pr` is the canonical pre-PR sync pipeline (build, regenerate, format, runtime updates).
- Integration test expect update knobs: `DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE`, `DAFNY_INTEGRATION_TESTS_MODE`, `DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS`, `DAFNY_INTEGRATION_TESTS_IN_PROCESS`.
- Root `Binaries/` and runtime generated trees are build/release assets; treat edits there as regeneration tasks, not manual source changes.
