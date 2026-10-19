# Unify the two native Dafny revisions

Status: done
Date: 2026-10-19
Classification: repository maintenance; no evaluated run or paid provider access.

## Objective and acceptance

Use one native Git commit for `cosyn/dafny` and `dafnyutils/dafny`, preserving Cosyn body-visibility/trusted-source functionality and Dafnyutils verification-target discovery. Both parent gitlinks and the integration gitlinks must record the result. Strict consumer parsing must accept the combined producer. Preserve existing dirty documents, scratch, benchmark specifications, proof obligations, scoring, and isolation.

## Evidence and approach

Inspected native source, CLI flags, wire models, safe tests, Makefiles and applicable AGENTS/CLAUDE instructions. Cosyn starts at `4cd8162e968d8660ee50257671b697b7a4e64c89`; Dafnyutils starts at `4fb94fc9fecc8209e289148c6347a2c313606e6b`; common base is `bc427b21461f258fd8de34232e01bb6be03cee39`. The read-only synthetic merge reported 18 conflicts (3 product, 6 tests, 9 documents). Integrate linearly on the Cosyn native revision, porting the missing verification-target functionality and meaningful logger assertions. Preserve canonical logger API, resource-reporting cleanup and fixture positions. Retain both original native histories through existing refs; historical counterpart documents remain available at the original benchmark commit rather than overwriting canonical records. No merge commit or forced branch rewrite is needed; the benchmark checkout may detach at the common commit.

## Change table

| Owner / exact paths | Change and reason / unmet without it | Validation |
| --- | --- | --- |
| Native `Source/DafnyCore/DefinitionAnalysis.cs`, new `DefinitionAnalysis.VerificationFacts.cs` | Add optional verification target inventory while retaining body visibility and proof inputs; otherwise benchmark flag has no native producer | Fresh build, focused in-memory Core tests, combined CLI JSON |
| Native `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` | Preserve `--include-verification-facts` and compose with existing flags | Fresh Driver build and public synthetic CLI checks |
| Native `Source/DafnyCore.Test/DefinitionVerificationFactsTest.cs`, `Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs` | Preserve benchmark cases against canonical APIs and exercise combined metadata without disk fixtures | Serial filtered native tests; trace setup/teardown first |
| Dafnyutils `src/analysis/models.py`, `tests/core/test_verification_limits.py` | Add local strict optional `bodyVisibility` schema and in-memory compatibility/error cases; otherwise producer JSON is rejected | Affected unit tests, Ruff, canonical Pyright |
| Native `wiki/unified-dafny-runtime.md`, `wiki/INDEX.md`; all owners `plan/2026-10-19-unify-dafny.md`, `plan/INDEX.md` | Record source ownership, integration decisions, actual evidence and preserved history | Diff/link review; Markdown-only trees |
| Cosyn `dafny`, Dafnyutils `dafny`, root `cosyn` and `dafnyutils` gitlinks | Pin the same committed toolchain and updated consumers | Exact native HEAD/gitlink equality; independent final review |
| Root `wiki/architecture/dafny-toolchain-ownership.md`, `wiki/INDEX.md` | Update current same-revision source policy while retaining separate command/isolation ownership and historical image receipts | Current source/pin inspection |

## Layers, risks and non-goals

Only native analysis metadata, associated tests, Python external JSON schema, documentation and Git pins change. No benchmark dataset, Dafny task source, proof specification, oracle, evaluator, scoring, provider policy or container boundary changes. Default trust remains absent; no verification bypass is added. Existing images are not relabeled or silently rebuilt. Fresh local binary/source checks are distinct from image admission and benchmark proof success. No dependency additions, push, paid experiment or full benchmark run is authorized/needed. Earlier local commit authorization applies. Git metadata mutations may require managed execution approval; request only through execution tooling. Existing incomplete plans and their index deltas stay unstaged.

## Validation

Prerequisites: .NET SDK 8.0.131 and existing offline project assets; Python 3.12 with existing dependencies. Logs/artifacts go to `/workspace/tmp/unify-dafny-20261019/`, never plan/wiki. In canonical native cwd, build Core.Test, Driver.Test, TestGeneration.Test sequentially with `dotnet build <project> --no-restore -m:1 -nr:false -p:UseSharedCompilation=false -v:minimal`; build actual CLI project if not referenced. Inspect/run supported `make format`, constrain any follow-up formatting to planned C# paths. Run relevant in-memory Core/Driver/TrustedSources tests with `dotnet test --no-build --no-restore --filter ...` serially and IPC approval if needed. After synchronizing the second checkout, build its `Source/Dafny/Dafny.csproj` with the same offline serial flags so both development command routes use new source. Use both fresh owner CLIs on a tiny public synthetic source for combined metadata and both independent Python parsers; no hidden tasks.

In Dafnyutils run `python3 -m pytest -c pytest-dev.ini -q tests/core/test_verification_limits.py`, then supported `make test-unit` after disk-boundary review. Run Ruff and canonical-source Pyright for affected Python. In root/Cosyn use supported `make lint`, canonical-source typecheck and affected fake units; integration only at final review if affected and safe. A fresh independent agent reviews current source from requirements and runs its own focused checks. Record exact commands, outcomes, scope/skips and current revisions here. Check staged diffs and both native SHA equality before local commits. Recursively inspect every root/submodule plan/wiki for non-Markdown files; preserve pre-existing violations.

## Progress and knowledge

Native source implementation and required local checks are complete; see Native owner closure below for actual outcomes and limits. Durable findings are recorded in the native runtime topic and root toolchain ownership topic. Parent plans track common-pin delivery and final command metadata; no image, benchmark proof or provider experiment success is claimed.

Related plans: [integration](/workspace/plan/2026-10-19-unify-dafny.md), [Cosyn](/workspace/cosyn/plan/2026-10-19-unify-dafny.md), [Dafnyutils](/workspace/dafnyutils/plan/2026-10-19-unify-dafny.md), [native](/workspace/cosyn/dafny/plan/2026-10-19-unify-dafny.md).

### Checkpoints

- Canonical Core.Test and Driver.Test fresh offline serial builds passed, zero warnings/errors (.NET SDK 8.0.131). Initial VSTest launch aborted before tests because local IPC was denied; managed execution retry is used, without bypassing test scope.
- First verification-facts run passed the seven original cases; the new combined metadata case failed because its in-memory parser has no `SourceFiles` for the additional semantic fingerprint request. Remove that unrelated opt-in/assertion while retaining the planned visibility-plus-target-inventory assertion; no production behavior changes.
- Dafnyutils supported `make test-unit` with current source path and bytecode disabled passed 106 tests, 15 integration cases deselected. Root and Cosyn supported `make lint` passed (70 and 199 files). Canonical-source typechecks and remaining native gates are running.

- Root/Cosyn canonical-source Pyright passed with zero errors/warnings (existing source alias/configs from prior commit maintenance); stock editable import discovery is not treated as passing. The schema agent's scoped stock Pyright failed installed-package resolution; canonical mapped check follows. Its focused memory-only model module passed17 tests and Ruff.
- Second combined native test checkpoint exposed existing conservative visibility behavior: modern `@TimeLimit` syntax makes `revealsAllFunctions` conservative, so its precise-closure assertion was invalid. Use the existing legacy timeout syntax in the combined closure case; original modern-attribute inventory cases remain. No native product visibility change.

## Native owner closure

Native acceptance is the combined source and its fresh build/test/format gate. Parent gitlink delivery, post-commit revision metadata rebuilds and two-owner command-route checks are owned by the linked parent/integration plans; they do not change native source. Original benchmark `expecto` remains reachable at `4fb94fc9fecc8209e289148c6347a2c313606e6b`; its same-path historical development records remain in that history.

Fresh sequential builds from `/workspace/cosyn/dafny`: Core.Test19.04s/0warnings, Driver.Test20.73s/0warnings, TestGeneration.Test10.58s/4warnings, actual `Source/Dafny/Dafny.csproj` CLI6.57s/0warnings, final Core.Test rebuild7.49s/0warnings. Commands used `dotnet build <project> --no-restore -m:1 -nr:false -p:UseSharedCompilation=false -v:minimal`; actual CLI also used `-p:PathMap=/workspace/cosyn/dafny=/src/dafny -p:ContinuousIntegrationBuild=true -p:Deterministic=true`. SDK8.0.131, runtime8.0.31, MSBuild17.8.49. TestGeneration warnings are pre-existing CS0162 in ContractRuntimeProfileTests44/55, CS0618 in PbtObservationTests287, and VSTHRD103 in ContractPhaseTimingTests211.

Implementation checks passed Core30 (22visibility+8inventory), Driver9 (6logger+3internal error), TrustedSources15; zero skips. Fresh independent serial class-by-class native runs passed90: VerificationFacts8, BodyVisibility22, ProofInputs21, TriggerBoundVariableScope3, MatchTriggerVariableScope12, JsonVerificationLogger6, InternalErrorExit3, ContractTrustedSources15. Commands were `dotnet test <project> --no-build --no-restore --filter FullyQualifiedName~<class> -v:minimal`, with local IPC approved after an initial sandbox socket denial. DLL/source timestamps confirmed fresh; no native compilation occurs inside tests.

Supported `make format` and `dotnet format whitespace Source/Dafny.sln --no-restore --include <five changed C# paths> --verify-no-changes` passed, with the general workspace-loading warning retained. No unrelated tracked formatting edits occurred. `git diff --check` and recursive Markdown-only audits passed. Independent source review found no lost benchmark-only product capability; unchanged bodyVisibility/proofInputs/trust implementations remain byte-identical to their appropriate initial revisions. Native source acceptance is complete.

The canonical CLI was consumed successfully by both independent Python clients on one tiny public synthetic source: four definitions, four native target identities (including datatype constructor), two proof-input entries, semantic facts and body visibility. An earlier smoke attempted the not-yet-updated default benchmark executable and failed its new-visibility assertion; the explicit canonical route passed. Final default-route rebuild/smoke is recorded by parents. Dafnyutils focused units17/fullunits106 pass; source model canonical Pyright passes. Including the existing test module in Pyright reproduces19 pre-existing snake-case/Pydantic-alias diagnostics on both HEAD baseline and current file; no unrelated helper/type changes made. Root/Cosyn lint and canonical-source Pyright pass.

Durable findings: [unified runtime](../wiki/unified-dafny-runtime.md). Logs and synthetic JSON under `/workspace/tmp/unify-dafny-20261019/`, local maintenance evidence only. Four build warnings, formatter workspace warning and the two failed fixture checkpoints above are retained. Full native suites, benchmark proofs, image builds and paid experiments were not run; affected in-memory scope passed without skips. No remaining native-source blocker; next parent action is commit import/pin equality and source-revision rebuild.

- Additional operational all-native-flags check passed raw JSON coexistence of semantic facts, proof inputs, target inventory and body visibility. Parsing that all-opt-in document with the benchmark's strict model rejected `sourceFacts.proofInputs`, which its client never requests; this is outside its supported request contract. Keep each consumer's optional request schema: benchmark target-inventory document and Cosyn proof-input document both parse successfully using the same canonical CLI. No `extra` relaxation or unrelated schema expansion.
