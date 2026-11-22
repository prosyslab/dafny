# Enable modifies inference from the CLI

Status: done

The user approved keeping both controls. Native Dafny owns the change. The baseline is `a9dd0480d` plus the existing uncommitted [method-level implementation](2026-11-22-infer-modifies.md).

## Goal and acceptance

`dafny verify --inferModifies file.dfy` infers supported frames on ordinary source methods that omit `modifies`, including transitive calls. The declaration attribute `{:inferModifies}` retains its current behavior with or without the flag. Without either control, an omitted frame retains its existing meaning. The flag respects handwritten frames and leaves unsupported methods to their usual verification checks. Unsupported explicit attribute requests retain their diagnostics. Saved library contracts must preserve established frames when consumed without the flag, and already-verified imports retain their contracts when the flag is enabled.

This change leaves the supported effect vocabulary, Boogie, benchmark definitions, and installed tools at their current scope. No paid work, deployment, or commit is required.

## Existing code and changes

`InferModifiesClause` traverses resolved methods and produces standard frames with source syntax for export checking. `DafnyCommands.ResolverOptions` is used by verification, resolution, and build. `LibraryBackend` serializes the parse snapshot to preserve parsed module structure. `CachingResolver` reuses resolved declarations, so its key must distinguish the inference context.

| Files and symbols | Change | Verification |
| --- | --- | --- |
| `Source/DafnyCore/Options/CommonOptionBag.cs`, `Source/DafnyCore/Options/DafnyCommands.cs` | Register `--inferModifies` on the normal resolver commands. | Check help, resolve, verify, and library build. |
| `Source/DafnyCore/Resolver/InferModifiesClause.cs`, `Source/DafnyCore/AST/Modules/LiteralModuleDecl.cs` | Share existing traversal between explicit attribute requests and eligible CLI-enabled source methods. Skip already-verified imports for CLI inference. An unsupported implicit callee keeps its original contract, which callers can still use. Cycles and strict failures propagate through the inference traversal. | Verify positive/minimal caller and IO cases in both modes, and verify original failures without the flag or with a narrow explicit frame. Include a caller of a valid fresh-only callee. |
| `Source/DafnyCore/AST/Members/MethodOrConstructor.cs`, `Source/DafnyCore/Backends/Library/LibraryBackend.cs` | Track which resolved methods actually got a nonempty generated clause. Serialize a copy of the parse snapshot with the source-shaped frame on the originating declaration. | Verify a `.doo` made with the flag can be imported without it. Verify that an enabled consumer can also use an archive built without it and preserve that archive's contract. |
| `Source/DafnyLanguageServer/Language/CachingResolver.cs` | Include the CLI mode and the source URI set eligible for inference in the resolved-module cache identity. Existing proof-option identity picks up registered resolver options. | Inspect cache separation and check fresh resolution with both modes. |
| `Source/IntegrationTests/TestFiles/LitTests/LitTest/dafny0/infer-modifies-cli*.dfy` and `.expect` | Add real CLI proof and no-flag/explicit-frame checks. Re-run existing attribute regressions. | Catch command wiring and accidental permission widening. |
| `docs/DafnyRef/Attributes.md`, `wiki/inferred-modifies.md`, `wiki/INDEX.md` | Describe both opt-in paths, fallback, and archived contracts. | Match wording to observed CLI and proof results. |

## Local verification

Commands run serially from `/workspace/dafny` unless otherwise stated.

- `dotnet build Source/Dafny/Dafny.csproj --no-restore -m:1` should produce a working native CLI. `Binaries/Dafny verify --help` and `Binaries/Dafny resolve --help` should list `--inferModifies`.
- `dotnet build Source/IntegrationTests --no-restore -m:1` should stage the affected Lit fixtures. Run the existing socket-free Lit runner from `/workspace/dafny/Source/IntegrationTests/bin/Debug/net8.0` with `dotnet /workspace/tmp/infer-modifies/lit-runner/bin/Debug/net8.0/LitRunner.dll TestFiles/LitTests/LitTest/dafny0/infer-modifies-*.dfy`. The prior plan records the sandbox restriction on VSTest's local testhost socket.
- Create a source copy of the actual BenchIO example from `/workspace/tmp/infer-modifies/bench-io.dfy` without attributes under `/workspace/tmp/infer-modifies-cli/`. `Binaries/Dafny verify --inferModifies --cores 1 --verification-time-limit 15 /workspace/tmp/infer-modifies-cli/bench-io.dfy` should prove the wrappers and stdin preservation.
- `Binaries/Dafny build --target lib --inferModifies --cores 1 /workspace/tmp/infer-modifies-cli/io.dfy` should create an archive. `Binaries/Dafny verify --stdin --cores 1 --library /workspace/tmp/infer-modifies-cli/io.doo` should verify an explicit-framed client without enabling inference. Also verify an import of a library built with default options under `--inferModifies` and check that the bundled standard library loads.
- Build `/workspace/tmp/infer-modifies-cli/prefix.dfy` with `Binaries/Dafny build --target lib --inferModifies --cores 1`, then verify its `prefix-client.dfy` with `--library /workspace/tmp/infer-modifies-cli/prefix.doo` and inference off. The library uses a prefix-named module and an abstract import. Build `old-library.dfy` without the flag and verify `old-library-client.dfy` with the flag and an explicit empty frame. The scratch files live together under `/workspace/tmp/infer-modifies-cli/`.
- `Binaries/Dafny translate cs --inferModifies --cores 1 --output /workspace/tmp/infer-modifies-cli/io.cs /workspace/tmp/infer-modifies-cli/io.dfy` should emit concrete clauses in embedded source. Extract and reverify that source without the CLI option.
- Run `git diff --check`, C# whitespace verification for the touched files, and `Binaries/Dafny format --check` for new Dafny fixtures. Request a fresh independent review of the implementation and evidence.

## Implementation and verification record

- The final `dotnet build Source/IntegrationTests --no-restore -m:1 -v:q` returned zero errors and built the CLI. SDK `8.0.133`, Z3 `4.16.0`, native commit `a9dd0480d` plus the uncommitted method-level and CLI changes. The [temporary build log](../../tmp/infer-modifies-cli/build-final.log) records nine warnings outside the changed code. Both verify and resolve help list the new switch, and `resolve --inferModifies` accepted the feature fixture.
- The socket-free Lit run passed all seven `infer-modifies-*.dfy` cases, including five original method-level cases. The new positive case returned 9 verified with the flag and the expected missing-frame failure without it. The new negative case returned the ordinary proof failures for a handwritten empty frame and an unsupported automatic path. The standalone [BenchIO probe](../../tmp/infer-modifies-cli/bench-io.dfy) returned 7 verified, 0 errors using only the CLI switch.
- The archived IO and prefix-named module fixtures built with the flag and verified consumers without it. The prefix fixture also used an abstract import. The consumer of `old-library.doo`, built without the flag, verified under the flag and retained its explicit empty frame. The bundled standard library loaded and the `Std.Collections.Seq.ToSet` proof passed under the flag.
- C# source translation completed with 9 verified. Extracted Dafny source from the C# output contained concrete clauses and re-verified without the flag with 9 verified. The archive and translation artifacts in `/workspace/tmp/infer-modifies-cli/` are temporary.
- Independent source review found a duplicate library frame mapping caused by abstract clones. The final binary passed that probe after the marker was limited to resolved-field clones. Independent tests also confirmed original-frame fallback, strict attribute diagnostics, and proof assertion checks. The [final independent record](../../tmp/infer-modifies-cli/independent-review/final-results.json) is temporary. Resolution cache key separation was checked in source. A warm language-server session was outside the runtime probes.
- C# whitespace verification for the touched files passed with a workspace-loading warning. `Binaries/Dafny format --check` passed for both new fixtures, and `git diff --check` passed. [Wiki notes](../wiki/inferred-modifies.md) record the two controls and how libraries retain their frames. The native build is available at `Binaries/Dafny`.
