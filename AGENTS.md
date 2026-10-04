# DAFNY SUBTREE KNOWLEDGE BASE

**Parent:** `../AGENTS.md`

## OVERVIEW
`dafny/` is an embedded upstream Dafny toolchain and codebase with independent build, test, style, and generated-file rules.

## WHERE TO LOOK
| Task | Location | Notes |
|------|----------|-------|
| Local authority | `dafny/CLAUDE.md` | primary conventions for this subtree |
| Core implementation | `dafny/Source/` | C# compiler, resolver, language server, runtime |
| Build/test scripts | `dafny/Makefile`, `dafny/Scripts/` | local command wrappers and release tooling |
| CI workflows | `dafny/.github/workflows/` | reusable matrix jobs and nightly/release gates |
| Documentation | `dafny/docs/` | language + integration references |

## CONVENTIONS
- Reserve `plan/` and `wiki/`, including nested directories, for Markdown (`.md`) documents only. Do not create or store generated evidence, logs, JSON/JSONL/CSV outputs, images, archives, scripts, source probes, binaries, caches, or artifact symlinks there, even temporarily or when ignored by Git. Renaming an artifact to `.md` does not make it a document.
- Put non-sensitive maintenance scratch and generated artifacts in `/workspace/tmp/<task-slug>/`, and simple experiment artifacts in `/workspace/tmp/experiment/<run-id>/`. Benchmark and private evidence must use the protocol-authorized location and existing isolation rules. Plan/wiki documents summarize commands and results and reference external artifacts with their availability.
- Before finishing, inspect `plan/` and `wiki/` recursively for non-Markdown files. Remove violations created by the current task; preserve pre-existing files unless their cleanup is explicitly authorized.
- Before adding new functionality, search `dafny/Source/` for similar existing implementations first; add new code only when no suitable implementation exists.
- Use Dafny-local commands (`dotnet build`, `make test`, `make format`, `make format-dfy`).
- Follow C# formatting/style rules from `dafny/.editorconfig` and `dafny/CLAUDE.md`.
- Preserve existing namespace style and nullable directives in touched C# files.
- Run relevant Dafny tests after changes in this subtree.

## GENERATED FILES (DO NOT HAND-EDIT)
- `dafny/Source/DafnyCore/GeneratedFromDafny/*`
- `dafny/Source/DafnyCore.Test/GeneratedFromDafny/*`
- `dafny/Source/DafnyRuntime/DafnyRuntimeSystemModule.cs`
- `dafny/Source/DafnyCore/Parser.cs`
- `dafny/Source/DafnyCore/Scanner.cs`

## ANTI-PATTERNS
- Applying root Python lint/test workflows as if they governed this subtree.
- Editing generated artifacts directly instead of regenerating through build scripts.
- Skipping Dafny-local formatting and test commands after code changes.

## LOCAL COMMANDS
```bash
dotnet build Source/Dafny.sln
make format
make format-dfy
make test name=comp/Hello.dfy
```
