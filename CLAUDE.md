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

### Partial Evaluator & Bounded Quantifier Unrolling

A custom rewriter subsystem that simplifies resolved AST expressions at compile time. It runs during `PostResolveIntermediate` and mutates the AST in-place. The system has five files:

**`PartialEvaluator.cs`** — The `IRewriter` entry point. Activated by `--partial-eval-entry <name>`. Finds callables matching the entry name in the module and delegates to `PartialEvaluatorEngine.PartialEvalEntry()`.

**`PartialEvaluatorEngine.cs`** — The core engine (a `partial class` split across two files). Contains:
- **Binary simplification** (`SimplifyBinary`): constant-folds `BinaryExpr` nodes for booleans, integers, comparisons, sequences, sets, multisets, and maps. Each resolved opcode dispatches to a type-specific helper (e.g. `SimplifyBooleanBinary`, `SimplifyIntBinary`, `SimplifySetUnion`).
- **Function inlining** (`TryInlineCall`): substitutes a function's body for its call site when the function is static, side-effect-free (no reads, not opaque, revealed), and has at least one literal/lambda argument. Bounded by `inlineDepth`, cycle-guarded via `InlineStack` + `InlineCallStack`, and cached for static calls that fold to a literal (`inlineCallCache`).
- **Quantifier unrolling** (`TryUnrollQuantifier`): delegates to `QuantifierBounds` to expand bounded quantifiers into finite boolean conjunctions/disjunctions.
- **Comprehension materialization** (`TryMaterializeSetComprehension`, `TryMaterializeMapComprehension`): rewrites finite `set`/`map` comprehensions into display literals when all bound variables have concrete domains.
- **Literal helpers**: constructors (`CreateIntLiteral`, `CreateStringLiteral`, etc.), extractors (`TryGetStringLiteral`, `TryGetCharLiteral`, `TryGetSetDisplayLiteral`, etc.), and equality comparisons (`AreLiteralExpressionsEqual`, `SetDisplayLiteralsEqual`, multiset counting via `BuildMultisetCountsDict`). Set/multiset operations use `LiteralExpressionEqualityComparer` (an `IEqualityComparer<Expression>` backed by `AreLiteralExpressionsEqual`) with `HashSet`/`Dictionary` for O(1) element lookup and deduplication via the `LiteralSet` helper struct; set/multiset hashes are order-independent to avoid hash-bucket degeneration.

**`PartialEvaluatorVisitor.cs`** — The second half of the `partial class`. Contains:
- **`PartialEvalState`**: immutable depth counter + mutable inline stack sets, passed through the traversal.
- **`PartialEvaluatorVisitor`**: extends `TopDownVisitor<PartialEvalState>`. The `SimplifyExpression` method is the main recursive entry point — it visits, then retrieves replacements from a `Dictionary<Expression, Expression>` map.
- **Constant propagation**: scoped `constScopes` (a stack of `Dictionary<IVariable, ConstValue>`) tracks variables bound to literal values. `EnterScope`/`ExitScope` manage nesting. Branch isolation (`VisitBranchesWithIsolatedScopes`) clones scopes for if-then-else so constants don't leak across branches; after both branches, any assigned variable is invalidated.
- **Statement visitors**: `VisitOneStmt` dispatches to specialized handlers for `BlockStmt`, `IfStmt`, `WhileStmt`, `AssertStmt`, `SingleAssignStmt`, `CallStmt`, `VarDeclStmt`, `ReturnStmt`, etc. Each simplifies sub-expressions and manages constant invalidation.
- **Expression visitors**: `VisitOneExpr` dispatches to handlers for `UnaryOpExpr` (bool negation, `|seq|`, `|set|`, `|multiset|`), `BinaryExpr`, `ITEExpr` (dead-branch elimination), `FunctionCallExpr` (inlining), `ApplyExpr` (lambda beta-reduction), `MemberSelectExpr` (tuple projection), `QuantifierExpr`, `SetComprehension`, `MapComprehension`, `LetExpr` (constant propagation into body), `SeqSelectExpr` (indexing and slicing), `SeqUpdateExpr`, `StmtExpr`, and collection displays.
- **Exists-sequence solver** (`TrySimplifyExistsSequence`): for `exists s: seq<T> | |s| == N && ...`, enumerates all candidate sequences over a finite element domain and evaluates the residual predicate.
- **Exists-arithmetic solver** (`TrySimplifyExistsArithmetic`): recognizes `exists k: nat | k >= L && k * D == N` divisibility patterns.

**`UnrollBoundedQuantifiersRewriter.cs`** — A separate `IRewriter` activated by `--unroll-bounded-quantifiers <cap>`. Uses in-place AST replacement (via `ExpressionRewriteUtil.RewriteExpressionsInPlace` and `RewriteExpressionsInStmtInPlace`) to traverse the AST and replace `QuantifierExpr` nodes with their unrolled form. Delegates the actual unrolling logic to `QuantifierBounds.TryUnrollQuantifier`. Rewrites all callables in the module (functions, methods, iterators), including pre/post-conditions, invariants, and decreases clauses.

**`ExpressionRewriteUtil.cs`** — Shared utilities for in-place AST rewriting:
- `RewriteExpressionsInPlace(Expression, Func<Expression, Expression>)`: recursively walks an expression tree bottom-up via type-specific field dispatch, applying a rewriter function to each node. Covers all major expression types (binary, unary, comprehension, let, function calls, displays, etc.) with a fallback to `SubExpressions` for unknown types.
- `RewriteExpressionsInStmtInPlace(Statement, Func<Expression, Expression>)`: recursively walks a statement tree, rewriting all expression fields in-place and recursing into sub-statements. Covers block, if, while, assert, call, assignment, forall, calc, and other statement types.
- Also provides list/frame/attributed expression rewriting helpers used by both rewriters.

**`QuantifierBounds.cs`** — Shared infrastructure for both the partial evaluator and the unrolling rewriter:
- **Concrete domain inference**: `TryGetConcreteDomain` handles `IntBoundedPool`, `ExactBoundedPool`, `SetBoundedPool`, `SeqBoundedPool`, `MultiSetBoundedPool`, `MapBoundedPool`, and `SubSetBoundedPool`. For int/nat, resolves literal lower/upper bounds. For sets/multisets/maps, materializes elements and deduplicates. For subsets, enumerates the power set.
- **Multi-variable int domain inference** (`TryGetConcreteIntDomainsFromPools`, `TryGetConcreteIntDomainsFromLogicalBody`): extracts `var + constant` bound constraints from pool bounds or the quantifier's logical body, then iteratively propagates to compute concrete ranges.
- **Char domain inference** (`TryGetConcreteCharDomainsFromLogicalBody`, `TryGetConcreteCharDomainFromRange`): parses char range constraints (disjunctions of conjunctive bounds) into concrete character domains.
- **Quantifier unrolling** (`TryUnrollQuantifier`): the main unrolling algorithm. Computes concrete domains for all bound variables, then enumerates all assignments, substituting into the logical body and simplifying. Supports short-circuiting (false for forall, true for exists). When the domain product exceeds `maxInstances`, partially unrolls up to the cap and conjoins/disjoins the original quantifier (marked with `_partial_unroll` attribute to prevent re-processing).
- **Set/map comprehension materialization**: `TryMaterializeSetComprehension` and `TryMaterializeMapComprehension` enumerate bound variable assignments, evaluate range predicates, and collect term values.
- **Seq domain extraction**: `TryGetSeqLengthConstraint` detects `|s| == N`, `TryGetElementDomainConstraint` detects `forall i :: 0 <= i < N ==> s[i] in {elements}` patterns.
- **Helpers**: `NormalizeForPattern` strips `ConcreteSyntaxExpression`/`ParensExpression`/identity `ConversionExpr`. `CollectConjuncts`/`CollectDisjuncts` flatten boolean trees. `LiteralStructuralEquals` and `DeduplicateLiterals` provide structural comparison and hash-backed deduplication for display expressions to avoid quadratic scans.

#### Key design patterns
- **In-place AST mutation**: both rewriters modify the resolved AST directly (setting `function.Body`, `binary.E0`, etc.) rather than creating new AST nodes. This means the original source tokens are preserved for error reporting.
- **`Substituter` for inlining**: function inlining and quantifier instantiation use Dafny's `Substituter` class to replace bound variables with concrete values in expression trees.
- **Depth-bounded recursion**: inlining depth is controlled by `PartialEvalState.Depth`, decremented on each inline. Cycle detection uses both a `HashSet<Function>` (function identity) and a `HashSet<string>` (call-site identity including argument values); receiver identity hashing avoids expensive AST stringification.
- **Two-pass simplification after inlining**: after substitution and simplification at `depth - 1`, a second pass at `depth = 0` catches further simplifications without allowing new inlines.

### Generated files (do not hand-edit)
- `Source/DafnyCore/GeneratedFromDafny/*`
- `Source/DafnyCore.Test/GeneratedFromDafny/*`
- `Source/DafnyRuntime/DafnyRuntimeSystemModule.cs`
- `Parser.cs` and `Scanner.cs` (generated from `Dafny.atg` during build)

## Working agreements
- Prefer minimal, targeted changes.
- Run formatting appropriate to touched files (`make format` and/or `make format-dfy`).
- Always run relevant tests after changes.
