# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is this?

Dafny is a verification-ready programming language. It compiles to C#, Go, Python, Java, JavaScript, and Rust. Verification uses the Boogie intermediate language and the Z3 SMT solver.

## Build commands

```bash
dotnet build Source/Dafny.sln        # Build (includes COCO parser generation)
make boogie                           # Build Boogie submodule
make format                           # C# formatting (dotnet format)
make format-dfy                       # Dafny formatting
make pr                               # Full PR-ready pipeline (build, generate, format)
```

## Testing

```bash
# Integration tests (LIT-based, xUnit)
make test name=comp/Hello.dfy                    # Single integration test
make test name=comp/Hello.dfy update=true        # Update .expect file
make test-dafny name=comp/Hello.dfy action="verify"  # Run Dafny directly (no xUnit)

# Unit tests
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ClassName"

# All tests
dotnet test Source/IntegrationTests --logger "console;verbosity=normal"
```

Integration tests live in `Source/IntegrationTests/TestFiles/LitTests/LitTest/`. Each `.dfy` file is a test with an `.expect` file for expected output.

Environment variables: `DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE=true` overwrites `.expect` files. `DAFNY_INTEGRATION_TESTS_IN_PROCESS=true` runs in-process (useful for debugging but can be flaky).

## Code style

- **C#:** 2-space indent, LF endings, braces always required. See `.editorconfig`. Match namespace style of the file being edited (file-scoped vs block). Preserve existing `#nullable` directives.
- **Dafny:** 2-space indent, no tabs. Run `make format-dfy`.
- Private fields: camelCase. Constants and static readonly: PascalCase.

## Architecture

### Verification pipeline
Parse (COCO grammar `DafnyCore/Dafny.atg`) → Rewriters (PreResolve) → Resolve & type check → Rewriters (PostResolve phases) → Translate to Boogie → Z3 verification → Compile to target language.

### Key source layout
- `Source/DafnyCore/` — core library: AST (`AST/`), rewriters (`Rewriters/`), backends (`Backends/`), resolver (`Resolver/`)
- `Source/DafnyDriver/` — CLI driver
- `Source/DafnyLanguageServer/` — LSP server for IDE support
- `Source/DafnyRuntime/` — runtime libraries for each target language
- `Source/DafnyStandardLibraries/` — standard library `.dfy` sources

### Rewriters (IRewriter)
Rewriters hook into 8 resolution phases via `IRewriter`. Two transformation styles:
1. **In-place mutation** — add/modify members, specs, bodies directly. Fast for structural additions.
2. **Cloner-based rewrite** — override `Cloner.CloneExpr`/`CloneStmt` to replace specific nodes. Safer for localized expression/statement rewrites.

Prefer `PreResolve` or `PostResolveIntermediate` for AST changes.

### Generated files (do not hand-edit)
- `Source/DafnyCore/GeneratedFromDafny/*`
- `Source/DafnyCore.Test/GeneratedFromDafny/*`
- `Source/DafnyRuntime/DafnyRuntimeSystemModule.cs`
- `Parser.cs` and `Scanner.cs` (generated from `Dafny.atg` during build)

## Working agreements
- Prefer minimal, targeted changes.
- Run formatting appropriate to touched files (`make format` and/or `make format-dfy`).
- Always run relevant tests after changes.
