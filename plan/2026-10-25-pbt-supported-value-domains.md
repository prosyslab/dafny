# Extend generator proof value domains

Status: done
Date: 2026-10-25

## Objective and acceptance

Support ordinary generator proofs for static concrete targets with no explicit
`requires`, recursively finite set/multiset/map values, and immutable datatype/tuple
and finite-map projections. Preserve all source/identity/trust/dependency/coverage
requirements and runtime fallback. This is development maintenance, not evaluation.
The complete evidence, risks, validation commands and cross-owner scope are in the
[Cosyn plan](../../plan/2026-10-25-pbt-supported-value-domains.md).

## Inspection and design

Read native `AGENTS.md`, `CLAUDE.md`, `Makefile`, indexes and current proof/runtime
owners. No local plan/wiki instruction or template files exist. Native base is
`a88ff6bc3af1b490b032cc70b9632cd363dd64f0`, initially clean. Existing
`ContractGeneratorProofTests` supplies bounded dictionary-backed parse/resolve and
proof-source fixtures without a solver or filesystem writes.

The five observed empty-premise proof rejections are recorded by the bounded
2026-10-24 csplit response projection linked in the parent plan. Current source
independently exposes collection omissions and immutable-field misclassification.
`ContractHarnessBuilder`, membership instrumentation and codecs already support
finite collections; native `DatatypeDestructor`/`DatatypeDiscriminator` distinguish
immutable value selectors from class fields. Use resolved identities, no heuristic.

## Change table

| File/symbol | Change and need | Validation |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs`: `SupportedSelectedGoal`, `SupportedValueType`, `TargetRequiresAreValueOnly` | Remove the nonempty-premise admission restriction, add recursive finite collection types, recognize precise immutable projections in both direct/transitive scans. | Focused memory regression tests, unchanged binding/coverage controls |
| `Source/DafnyTestGeneration.Test/ContractGeneratorValueDomainTests.cs` | Add real parser/resolver and ordinary proof-source positive/negative controls. | No test directories, sync, sample compilation, provider or live solver |
| This plan and `plan/INDEX.md` | Track native ownership and actual checks. | Diff/index review |
| `wiki/pbt-generator-value-domain.md`, `wiki/INDEX.md` | Record domain and proof-boundary invariants with originating plan. | Source/test evidence and independent review |

## Compatibility, risks and exclusions

No external JSON/schema/CLI, core verifier, benchmark/evaluator, dependency or runtime
campaign policy changes. Reject mutable class/array/receiver state, nested references,
infinite collections, unsupported scalar/function types, generic selected goals and
trust-affecting attributes as before. Empty target premises still require generator
body/type/own-contract and helper proofs. No package/paid-run/commit approval needed.
The main soundness risk is a broad field exception: limit it to native immutable
value projection nodes and test direct and transitive real heap reads.

## Validation and progress

Use the exact serial separate assembly build, audited `--no-build --no-restore`
memory test filter and targeted whitespace/diff commands from the parent plan.
Installed .NET SDK is 8.0.131. Do not run full Driver campaign tests or build from a
test fixture. Keep real solver, generated runtime sample, image and benchmark claims
separate. A fresh independent verifier must run from requirements/current source.
Implementation started. Record executed commands/outcomes and final limits here.

The first focused native run passed 122 and failed two new negative fixtures on
invalid bodyless non-null constants. Nullable constants preserve the intended heap
reads and fix only the fixtures. A separate assembly rebuild passed. The initial
independent 9/9 result is not final matching-source evidence because a later
diagnostic/formatting edit was newer than the assembly. A refined-input obligation
control for empty premises is being added before the final build; independent final
tests remain pending. See the parent plan for full host results and evidence census.

Later independent matching-source review passed 67 bounded memory tests. Root's
final domain review identified an additional supported-subset-map projection gap:
the receiver shape check must use existing `AsMapType` normalization while keeping
the full original value-domain check. Add a same-owner regression, rebuild once
source is stable and independently rerun affected checks. This is within the existing
finite-map/subset compatibility requirement; no scope or proof relaxation is added.

## Final outcome

All planned source work and bounded verification are complete. The final producer
hash is `f48c9c95626d22718f2dfebd8c5e3267673705dc90f9bd6dda33954bf0afce6e`;
test owner hash is `840747d96aec891de29c5c8cb724f53bee5655c57ebf3dd4f9923af68f1215cd`.
The final matching assemblies postdate both source files, and the independent
verifier rechecked the pins before and after its run. No later C# edit occurred.

From native root with .NET SDK 8.0.131, the exact separate serial `dotnet msbuild`
command in the parent plan passed. Existing unrelated nullable, unreachable-code,
obsolete-library and synchronous-cancellation warnings remain. The planned seven-owner
`dotnet test ... --no-build --no-restore -m:1 -nodeReuse:false` filter passed 127/127
with zero skips. Independent new-domain/proof/verification selection passed 69/69
with zero skips; these are overlapping populations. Vstest's local control socket
required approved execution outside the sandbox, with no solver/provider/test build.

Targeted native whitespace verification and `git diff --check` passed. Earlier build
CS0104 in the new test, two whitespace findings, two invalid non-null constant
fixtures and source/assembly timing checkpoints are retained in the parent record;
all were corrected before final validation. No production error was masked.

Empty premises retain authored ensures, subset/newtype well-formedness and positive
generator correctness checks. Finite nested values, direct/transitive immutable
projections and refined finite maps enter ordinary proof-source preparation. Infinite
collections, nested/hidden references, real heap access and incomplete correctness
coverage remain unsupported. Final independent review found no blocker.

Durable knowledge is in [Generator proof value domain](../wiki/pbt-generator-value-domain.md)
and indexed. Recursive plan/wiki audit contains no non-Markdown files. Full Driver/
campaign suites, actual solver/sample verification, installed-image delivery and paid
experiments were not run; their temporary-directory/compilation paths and downstream
claims are outside these memory checks. No commit or dependency change was made.

## Authorized commit handoff

The later user request authorizes a focused commit of this implementation, test,
plan and wiki record. Cosyn will then create its own single commit recording this
native Git submodule revision and related guide/development records. The native
payload excludes concurrent `ContractRuntimeSourceAuthoring.cs` and
`ContractRuntimeSourceAuthoringTests.cs` repairs. Production/test source hashes still
match the verified values above; this handoff changes only documentation and Git
records, so no source tests are repeated. Check staged files/content independently,
run normal hooks and confirm unrelated work remains after committing. The commit's
own identity is available from Git history; no hash is fabricated in advance.
