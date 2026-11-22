# Infer modifies for fixed IO regions

Status: done

The user approved planning and implementation on 2026-11-22. Native Dafny owns the change. The baseline is `a9dd0480d` on `expecto`, with a clean native worktree at inspection.

## Goal and acceptance

An ordinary method can opt in with `{:inferModifies}` and omit its handwritten `modifies` clause. Dafny calculates a conservative frame for the supported writes and verifies the method and all callers through its existing frame checks. A `Prepare`, `Flush`, and `RunCore` example must verify, including stdout and stderr relational postconditions and a caller's proof that stdin is preserved by `Flush`.

Keep the ordinary omitted frame empty, preserve handwritten frames, and diagnose unsupported inference at the source. No change to Boogie, benchmark definitions, benchmark admission or scoring, the compiler pin, or installed executables. Allocation dataflow, mutable reference paths, recursion among inferred methods, refinement, and inference for ghost, overriding, trait, constructor, or bodyless declarations are outside the first version. An explicit callee frame remains the contract for native or bodyless calls. The feature describes the Dafny heap model.

## Existing code and changes

`LiteralModuleDecl.Resolve` resolves modules in import order and checks export views. `Substituter.SubstFrameExpr` preserves field-level frame selectors. `BoogieGenerator.TrCall` checks that callee frames fit the caller, and `BoogieGenerator.Methods` turns method frames into the proof assumptions and obligations used at calls and in bodies. `AutoContractsRewriter` provides a precedent for inserting a frame in the resolved AST.

| Files and symbols | Change | Reason and verification |
| --- | --- | --- |
| `Source/DafnyCore/AST/Modules/LiteralModuleDecl.cs`, module resolution | Run inference on the resolved declarations before the generated frame is consumed by export checks or verification. | An exported contract must only refer to visible names. Test explicit export and intermodule use. |
| `Source/DafnyCore/Resolver/InferModifiesClause.cs`, new pass | Compute opted-in method frames in callee-first order, substitute receiver and input arguments, collect stable direct writes, resolved call output assignments, return updates, and declared loop or opaque-block frames. Report unsupported effects or a handwritten and inferred frame on the same method. Store normal frame expressions with source-shaped syntax for re-resolution. | A stable frame can be interpreted at method entry. Keep usual verification obligations and reject unsupported inferred cycles, dynamic paths, and sources the pass cannot represent. |
| `Source/DafnyCore/AST/Grammar/Printer/Printer.cs`, serialization of resolved methods | Serialize a materialized frame as an ordinary contract and omit the attribute that requested it. | C# embeds resolved Dafny source that can be parsed again. `.doo` libraries store the parse snapshot and re-infer on import. Verify both representations locally. |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny0/infer-modifies*.dfy` and `.expect` files | Cover the IO example and transitive calls, stable assignments, return and loop effects, export visibility, and a failing proof outside the generated frame. Check unsupported inference and the historical empty frame. | Catch behavior differences at both resolution and proof time. |
| `docs/DafnyRef/Attributes.md` | Document the attribute, the supported expressions, and manual frame fallback. | The usage example should agree with the tests. |
| `wiki/inferred-modifies.md` and `wiki/INDEX.md` | Record reusable implementation and verification findings. | Link back to this plan and distinguish verified cases from scope limits. |

The first version uses inputs and `this` followed by constant fields, and may union finite displays of supported objects. Field-level permissions use the existing selector and array stores use the array object. Existing explicit frames on other declarations are input summaries. An inferred contract may be wider than its actual writes, so caller preservation remains an important regression check.

## Local verification

Run serially from `/workspace/dafny` with the installed .NET SDK and Z3. No paid run or container build is needed.

- `dotnet build Source/Dafny/Dafny.csproj --no-restore -m:1` should build the native checkout executable at `Binaries/Dafny`.
- `dotnet test Source/IntegrationTests --no-restore -m:1 --filter 'DisplayName~infer-modifies'` should pass the feature Lit cases. If the local test harness lacks a prerequisite, run the same source cases with `Binaries/Dafny` and compare their expected outcomes. Record any harness limitation.
- If VSTest cannot open its local testhost socket, invoke the built `IntegrationTests.LitTests.LitTest` method directly with the small runner in `/workspace/tmp/infer-modifies/lit-runner/`. This uses the repository's Lit expectations in a serial loop without VSTest transport.
- `cp Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny0/infer-modifies-io.dfy /workspace/tmp/infer-modifies/io.dfy`, then `Binaries/Dafny build --target lib --cores 1 /workspace/tmp/infer-modifies/io.dfy` should produce a `.doo` library. `Binaries/Dafny verify --stdin --cores 1 --library /workspace/tmp/infer-modifies/io.doo` should re-resolve its contracts and verify a caller of `Client.RunCore` with a standing explicit frame.
- `Binaries/Dafny translate cs --cores 1 --output /workspace/tmp/infer-modifies/io.cs /workspace/tmp/infer-modifies/io.dfy` should embed the materialized contracts. Verify the extracted Dafny source with `Binaries/Dafny verify --stdin --cores 1`.
- `Binaries/Dafny verify --cores 1 --verification-time-limit 15 /workspace/tmp/infer-modifies/bench-io.dfy` should prove the standalone wrappers over the actual BenchIO module. The source probe is temporary and lives outside the benchmark checkout.
- `git diff --check` should report no whitespace errors. Check the affected C# and Dafny formatting using the checkout's tools.
- A new independent reviewer will inspect the current worktree and rerun targeted source cases from the requirements.

## Implementation and verification record

The module resolver calls the pass before export checking. Its generated frames are regular inputs to the existing verifier, and its source-shaped expressions let export views re-resolve the contracts. Resolution rejects an unsupported target at its assignment or call site. A mixed recursion with an explicit-frame boundary can use that contract without requiring a recursive inference dependency.

- Native baseline `a9dd0480d4d7ace80945d1c819b23070c193e663`. Native worktree was clean at start and contains the uncommitted changes in this plan. The actual IO probe imported Dafnyutils `4e6061f`. Its existing `coreutils` submodule status was left alone.
- .NET SDK `8.0.133`, Z3 `4.16.0`, and rebuilt native Dafny `4.11.1+a9dd0480d4d7ace80945d1c819b23070c193e663`. `dotnet build Source/Dafny/Dafny.csproj --no-restore -m:1 -v:q` succeeded on the final source. Earlier dependency builds printed a read-only Gradle lock error while processing the existing Java runtime. Java code generation and a fresh Java runtime build were outside the proof checks.
- `Binaries/Dafny verify --cores 1 --verification-time-limit 15 /workspace/tmp/infer-modifies/bench-io.dfy` returned 7 verified and zero errors. The proof uses real BenchIO operations and proves preservation of stdin across `Flush`. The [source probe](../../tmp/infer-modifies/bench-io.dfy) is temporary.
- `dotnet test Source/IntegrationTests --no-restore -m:1 --filter 'DisplayName~infer-modifies'` built the assembly. VSTest then aborted because the sandbox disallowed its local socket. From `/workspace/dafny/Source/IntegrationTests/bin/Debug/net8.0`, `dotnet /workspace/tmp/infer-modifies/lit-runner/bin/Debug/net8.0/LitRunner.dll TestFiles/LitTests/LitTest/dafny0/infer-modifies-*.dfy` ran the same Lit cases directly. All five passed, including their exit-code and output comparisons.
- The same runner also passed `dafny0/AutoContracts.dfy`, `dafny0/ModuleExport.dfy`, `dafny0/ForallStmtResolveErrors.dfy`, and `proof-obligation-desc/modify-frame-subset.dfy` from the integration output tree.
- The `.doo` build and consumer re-verification passed with 12 and 2 verified respectively. C# translation and re-verification of its embedded source each passed with 12 verified. Both used the temporary artifacts in `/workspace/tmp/infer-modifies/`.
- The independent reviewer used serial CLI probes for stable paths, generic and set substitution, arrays, loops, opaque blocks, external contracts, caller permissions, dynamic paths, and serialization. It identified an unsupported return-call syntax in a test fixture. The final fixture checks rejection of allocation in a return, and the direct Lit run passed it.
- `dotnet format whitespace Source/DafnyCore/DafnyCore.csproj --no-restore --verify-no-changes --include Source/DafnyCore/Resolver/InferModifiesClause.cs Source/DafnyCore/AST/Modules/LiteralModuleDecl.cs Source/DafnyCore/AST/Grammar/Printer/Printer.cs` passed with a workspace-loading warning. `Binaries/Dafny format --check` passed for the five new Dafny fixtures.
- `git diff --check` passed. The final native diff and new files match the change table. [Wiki notes](../wiki/inferred-modifies.md) capture the export and serialization details. The native build is available at `Binaries/Dafny`. The repository pin and installed benchmark tooling were outside this task.
