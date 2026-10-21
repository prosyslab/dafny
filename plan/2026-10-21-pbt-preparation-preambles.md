# Preserve include preambles during PBT source preparation

Status: done
Date: 2026-10-21

## Objective and acceptance

During the explicitly requested repaired csplit rerun, actual public registered
MCP controls found a remaining diagnostic parser failure before generator proof.
Fix source preparation so imports, generator declarations and draft helpers in
Dafny's default module never precede include directives. Preserve original
contracts, proof/fingerprint authority, source maps, collision rejection and
named-module placement. The parent experiment plan is
[/workspace/plan/2026-10-21-csplit-pbt-repaired-experiment.md](/workspace/plan/2026-10-21-csplit-pbt-repaired-experiment.md).

Acceptance: realistic string-backed include-first/default-module/cross-file and
Unicode/trailing-comment regressions parse and resolve with the prepared generator
and helpers; existing named-module/body-replacement/source-map tests still pass.
A fresh independent verifier inspects the patch and runs its own relevant pure
memory checks. No private receipt, benchmark task, solver campaign, compilation,
temporary directory, fsync or generated disk tree is used by development tests.
Actual operational build/MCP/image checks remain parent-owned and separately
recorded. No new native/Cosyn/root commit or push is authorized by this plan.

## Evidence, design and boundaries

Native HEAD b4f683fd85c9764c032346e0367df325f73dd4be is clean before this work.
The root, Cosyn and native AGENTS.md plus native CLAUDE.md apply; no narrower
source/plan/wiki instructions were found. SourcePreparation.PrepareAsync inserts
the default-module PbtRandom import at byte zero; AddHelper repeats byte-zero
placement for generators and helpers. The parser accepts includes only before
top-level declarations. The later obligation transformer repair does not cover
this earlier preparation phase. Actual synthetic controls reached the unsupported
zero-sample parsing failure even with fresh b4 binaries.

Reuse existing edit application and immutable ContractSource UTF-8 byte positions.
For a default-module target, append declarations at the end of that exact target
source snapshot with existing newline delimiters; forward declaration resolution
preserves scope. Do not add the named-module `import PbtRandom` there: the top-level
runtime module is already directly visible, and an import with that same name
conflicts during resolution. Named modules retain their import and parser-owned
BodyStartTok placement. At an equal source offset, apply every original callable
body insertion before any appended helper or generator declaration. This ordering
must be global across drafts because an earlier draft can queue an EOF helper
before a later draft queues its bodyless target's EOF body. Prefer a shared small
position helper if it prevents the two declaration paths diverging. Do not scan
braces or guess include lines, redirect declarations into other user files, alter
native obligations, change API contracts, or weaken qualified-symbol selection.

## Changes and ownership

| Exact native owner file | Necessary change and otherwise unmet behavior | Validation |
| --- | --- | --- |
| This plan; plan/INDEX.md | Record independently observed preparation-phase defect | Links/status/Markdown-only audit |
| Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs | Preserve include-first default-module preambles for both imports and added generator/draft helper declarations | In-memory prepare, parse/resolve, exact original source maps and named-module regression |
| Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs | Add bounded realistic regressions using existing in-memory parser/resolver helper only | Trace complete helper path before edits; no native process, solver, runtime compile or disk boundary |
| Existing relevant native wiki page and wiki/INDEX.md, exact path added before edits if useful | Record verified reusable insertion rule and limits | Source/evidence-backed fresh review and reciprocal links |

## Validation and handoff

Working directory /workspace/cosyn/dafny. Supported operational solution build:
dotnet build Source/Dafny.sln --no-restore -m:1 /nr:false, existing cached assets,
no package installs. Run relevant native unit checks with --no-build --no-restore
and a filter restricted to ContractRuntimeSourcePreparationTests plus directly
affected preparation/signature/parser tests after tracing their I/O. Use supported
formatting with exact touched-file scope and record command/exit. New real
campaigns, image overlay, source patch fingerprinting and final paid dispatch are
separate parent operational steps and require an amended parent plan before use.

Implementation begins only after root announces this ready plan. Preserve
unrelated work. Record exact files/hashes, commands/outcomes and skipped checks;
do not equate unit or build success with actual generator/PBT/evaluator success.
Keep source patch reviewable and uncommitted, then hand back to the parent for
explicitly attested patched-native experiment provenance.

## Implementation and validation record

Implementation on clean native base `b4f683fd85c9764c032346e0367df325f73dd4be`
routes both generator and draft-helper declaration placement through one helper.
It returns the exact owning snapshot's UTF-8 byte length for the default module
and retains `BodyStartTok.pos + 1` for a named module. Named modules still receive
their `PbtRandom` import there. The default module receives no redundant import,
because the supplied top-level runtime module is directly visible in that scope.

The first focused run established this last rule rather than being treated as a
pass: 20 of 22 cases passed, the new cross-file fixture had a static-signature
mismatch, and the other new case parsed but resolution rejected `import
PbtRandom` as the same name as the runtime module in the default scope. The
fixture now uses a module-level draft target with its actual signature, and the
product omits only that conflicting default-scope import. No contract, source-map,
collision, proof, fingerprint, named-module or qualified selection rule changed.

Fresh independent review then withheld acceptance because stable start-position
ordering still placed an earlier draft's appended EOF helper before a later
bodyless callable's zero-length EOF body insertion. The superseded product diff
SHA-256 `b12e5416a8364da193c1fabf47eb4cd23996a2281d5614b051c07433feda96f5`
must not be used. The bounded repair adds an explicit edit tie priority for all
helper/generator declarations, leaving body replacements and existing edits ahead
at equal positions. New method and function regressions use multiple drafts so
reordering operations inside only one draft cannot satisfy them.

Validation used .NET SDK `8.0.131` in `/workspace/cosyn/dafny`:

- `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs` exited 0 after each settled source edit; workspace loading reported its existing nonspecific warning.
- Tmux session `pbt-prep-build3-20261021` ran `dotnet build Source/Dafny.sln --no-restore -m:1 /nr:false`; it exited 0 in 26.24 seconds with four existing warnings and no errors. Log and exit record are `/workspace/tmp/pbt-preparation-preamble-20261021/build3.log` and `build3.exit`. Earlier superseded builds remain separately recorded as `build.log`/`build.exit` and `build2.log`/`build2.exit`.
- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeSourcePreparationTests --logger 'console;verbosity=normal'` passed 24 of 24 in-memory cases, including the two-draft method and function EOF tie cases. The first sandboxed attempt before the final repair could not open VSTest's loopback socket; approved local-socket retries produced the stated results.
- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --filter FullyQualifiedName~ContractRuntimeGeneratorSignatureTests --logger 'console;verbosity=minimal'` passed 33 of 33 in-memory cases through the same approved local test-runner socket.
- `git diff --check` exited 0. No Docker, solver, runtime compilation, provider, paid, private-data or experiment command ran.

The current uncommitted product source SHA-256 is
`39db263d394a81480feb993195387d3ccbd6c4aa224e1ce53abe020457ba17a7`; the
test source SHA-256 is
`4ae370c1f5d53a43e0fa90d405e71e05867c4e798414ddef21c22f0e7820d5eb`.
The accepted exact product-only diff is
`/workspace/tmp/pbt-preparation-preamble-20261021/product-accepted.patch`,
SHA-256 `f09b18486d7b79e42e080cf1eb5cb399ffecdb0b9033883641dd8e34a9abbd78`;
it was byte-compared with the single product-file `git diff`. The existing
`product.patch` artifact carries the explicitly invalidated intermediate
`b12e...` diff and is not current evidence. Test and plan changes are intentionally
excluded from the operational product identity.

Fresh independent verification inspected the settled source and tests and passed
57 of 57 independently selected checks. Its frozen acceptance record is
`/workspace/tmp/pbt-preparation-preamble-20261021/verification/acceptance.json`,
SHA-256 `ad70c49b3659bde09434c44089d26a0535adcd0cf5b5c176554bdd3e34a23c05`.
Any later product or test edit invalidates that acceptance and requires review.

No durable wiki page was added: this narrow source-placement invariant and its
default-scope import limit are recorded directly in the owning regression tests
and this plan. Parent-owned patched-image controls remain separate; none of the
local or independent checks establishes an actual generator, PBT, proof,
evaluator or paid-run outcome.
