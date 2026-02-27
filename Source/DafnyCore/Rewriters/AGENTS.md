# REWRITERS KNOWLEDGE BASE

Scope: `Source/DafnyCore/Rewriters/**`
Parent: `../AGENTS.md`
Precedence: nearest `AGENTS.md` wins.

## OVERVIEW
`Rewriters/` contains phase-driven AST transformations used before/after resolution.

## STRUCTURE
```text
Rewriters/
|- IRewriter.cs
|- RewriterCollection.cs
|- PartialEvaluator*.cs
|- QuantifierBounds.cs
|- UnrollBoundedQuantifiersRewriter.cs
`- feature-specific rewriters (induction, linting, contracts, etc.)
```

## WHERE TO LOOK
| Task | Location |
|------|----------|
| Rewriter lifecycle/hooks | `IRewriter.cs`, `RewriterCollection.cs` |
| Partial evaluation | `PartialEvaluator.cs`, `PartialEvaluatorEngine.cs`, `PartialEvaluatorVisitor.cs` |
| Quantifier bounds/unrolling | `QuantifierBounds.cs`, `UnrollBoundedQuantifiersRewriter.cs` |
| In-place expression/stmt rewrites | `ExpressionRewriteUtil.cs` |

## CONVENTIONS
- Match existing style: either in-place mutation rewriters or cloner-style rewrites, chosen intentionally per transformation.
- Place transformations in the correct phase; phase mistakes cascade into resolver/verifier mismatches.
- Keep rewrite helpers deterministic and side-effect scoped; tests lock resulting AST behavior through integration outputs.

## ANTI-PATTERNS
- Running semantic rewrites in the wrong phase (pre-resolve vs post-resolve).
- Re-implementing generic expression/statement traversal instead of using shared rewrite utilities.
- Adding rewrite heuristics without accompanying targeted tests.

## COMMANDS
```bash
dotnet build Source/Dafny.sln
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~PartialEvaluator"
dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~UnrollBoundedQuantifiers"
```
