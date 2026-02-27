# VERIFIER KNOWLEDGE BASE

Scope: `Source/DafnyCore/Verifier/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`Verifier/` translates resolved Dafny semantics into Boogie and manages proof obligations and verification context.

## STRUCTURE
```text
Verifier/
|- BoogieGenerator*.cs         # split partial class by concern
|- Expressions/ Statements/    # focused translation helpers
|- Datatypes/                  # datatype verification translation
`- ProofDependency*.cs         # dependency/proof metadata
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Entry translation flow | `BoogieGenerator.cs` |
| Expression translation | `BoogieGenerator.ExpressionTranslator.cs`, `Expressions/` |
| Statement translation | `Statements/`, `BoogieGenerator.Methods.cs` |
| Well-formedness checks | `BoogieGenerator.ExpressionWellformed.cs` |
| Obligation descriptions | `ProofObligationDescription.cs` |

## CONVENTIONS
- Keep translation logic partitioned by concern (types, methods, expressions, statements) to preserve the existing partial-file layout.
- Use existing factory helpers (`BoogieFactory` and generator helpers) rather than ad-hoc Boogie node construction.
- Preserve proof-dependency hooks and metadata when adjusting translation paths.

## ANTI-PATTERNS
- Mixing unrelated translation concerns in a single `BoogieGenerator.*` file.
- Introducing boogie-level side effects that bypass current helper/factory paths.
- Updating verifier behavior without refreshing impacted integration `.expect` outputs.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~Verifier"
make test name=proof-obligation-desc/
```
