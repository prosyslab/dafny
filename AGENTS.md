# AGENTS.md

Repo guidance for agentic coding in this repository.

## Repository layout (high-level)
- `Source/Dafny.sln` — primary .NET solution.
- `Source/Dafny` — Dafny CLI project.
- `Source/DafnyCore`, `Source/DafnyDriver`, `Source/DafnyLanguageServer`, `Source/DafnyRuntime` — main components.
- `Source/*Test*` and `Source/*.Test` — unit/integration test projects.
- `Source/IntegrationTests/TestFiles/LitTests/LitTest/` — integration test corpus.
- `Source/DafnyStandardLibraries/` — Dafny standard library sources.
- `Scripts/` — helper scripts (notably integration test wrappers).

Cursor/Copilot rules: none found (`.cursorrules`, `.cursor/rules/`, `.github/copilot-instructions.md`).

## Build / lint / test commands

### Prereqs / restore
```bash
dotnet restore Source/Dafny.sln
dotnet tool restore
```

### Build
```bash
dotnet build Source/Dafny.sln

# Boogie (local build of the submodule checkout)
make boogie
```

### Format / lint
```bash
# C# whitespace formatting
dotnet format whitespace Source/Dafny.sln \
  --exclude boogie \
  --exclude Source/DafnyCore/GeneratedFromDafny/* \
  --exclude Source/DafnyCore.Test/GeneratedFromDafny/* \
  --exclude Source/DafnyRuntime/DafnyRuntimeSystemModule.cs

# Equivalent wrapper
make format

# Dafny formatting (core + stdlib)
make format-dfy
```

### Tests (unit + integration)
```bash
# Runs test projects referenced by the solution
dotnet test Source/Dafny.sln

# Integration tests (xUnit LIT)
dotnet test Source/IntegrationTests --logger "console;verbosity=normal"
```

### Run a single test

#### Single integration test (preferred for LitTests)
The integration test DisplayName is the test file path relative to the LitTest root.

```bash
dotnet test Source/IntegrationTests --filter "DisplayName~comp/Hello.dfy"

# Wrapper
make test name=comp/Hello.dfy
```

Update expected outputs:
```bash
make test name=comp/Hello.dfy update=true
```

#### Run Dafny on an integration test file directly
Useful for iterating without the xUnit runner.

```bash
# make test-dafny name=<part of path> action="verify ..." [build=false]
make test-dafny name=comp/Hello.dfy action="verify" 

# Example: run a file
make test-dafny name=comp/Hello.dfy action="run" 
```

#### Single xUnit unit test (by method/class)
```bash
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName=Namespace.Class.Method"
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ClassName"
```

Notes:
- `--filter` supports `=`, `!=`, `~`, `!~`, `&`, `|`.
- If you pass just a value (no operator), it defaults to `FullyQualifiedName~<value>`.

## Coding style guidelines

### C# (.cs)
Follow `.editorconfig` (repo root). Highlights:
- 2-space indentation (`indent_size = 2`), LF line endings.
- Prefer braces (`csharp_prefer_braces = true:error`).
- Naming rules (from `.editorconfig`):
  - private fields: camelCase
  - `const` fields: PascalCase
  - `static readonly` fields: PascalCase

Common patterns seen in the codebase:
- Namespace style is mixed:
  - Many files use file-scoped namespaces (`namespace X;`).
  - Some files (notably parts of the language server) use block namespaces (`namespace X { ... }`).
  - Match the style of the file you are editing; don’t churn namespace style in unrelated changes.
- Nullable context is explicit in many files via `#nullable enable/disable`.
  - Preserve existing nullable directives; when `#nullable enable`, use `T?` and avoid null-forgiving unless required.
- Logging:
  - Prefer `Microsoft.Extensions.Logging.ILogger<T>` and structured logging (`logger.LogWarning("... {Value}", value)`), not string concatenation.
- Cancellation:
  - Pass `CancellationToken` through async APIs and use `ThrowIfCancellationRequested()` where appropriate.

### Dafny (.dfy)
Conventions (documented in DafnyRef) and observed in this repo:
- No tabs; 2-space indentation.
- Use `import opened` sparingly (recommended in Dafny docs).
- Use `requires`/`ensures` and lemmas for correctness conditions (standard library and core files follow this heavily).

Formatting:
- Run `make format-dfy` (delegates to core + stdlib Makefiles).

### Test authoring

#### Integration tests
- Location: `Source/IntegrationTests/TestFiles/LitTests/LitTest/`.
- Each `.dfy` is a test; `.expect` files record expected output.
- Prefer the uniform backend macro when applicable (see LitTest README):
  - `// RUN: %testDafnyForEachCompiler "%s"`

#### Unit tests
- Location: `Source/*.Test/` projects.
- Runner: xUnit.

## Environment variables (integration tests)
- `DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE=true` overwrites `.expect` instead of diffing.
- `DAFNY_INTEGRATION_TESTS_IN_PROCESS=true` runs `%dafny` in-process (useful for debugging; can be flaky due to shared static state).

## Generated / derived files (avoid manual edits)
- Generated-from-Dafny C# is excluded from formatting:
  - `Source/DafnyCore/GeneratedFromDafny/*`
  - `Source/DafnyCore.Test/GeneratedFromDafny/*`
- `Source/DafnyRuntime/DafnyRuntimeSystemModule.cs` is excluded from `dotnet format`.
- The `make pr` pipeline performs code generation and reformatting; avoid hand-editing artifacts that are regenerated.

## Docs
```bash
# Build Dafny reference manual
make -C docs/DafnyRef
```

## Working agreements for agents
- Prefer minimal, targeted changes.
- Run formatting appropriate to touched files (`make format` and/or `make format-dfy`).
