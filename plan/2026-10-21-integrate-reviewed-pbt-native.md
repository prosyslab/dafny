# Integrate the reviewed PBT native source into live main

Status: done (exact live transfer and independent source/local verification)
Date: 2026-10-21

## Objective and observable acceptance

Transfer the independently reviewed 28-path native PBT inventory from
`/workspace/tmp/pbt-worker-failure-20261021/native` into the live Dafny checkout
at `/workspace/cosyn/dafny`. Both trees have base revision
`b4f683fd85c9764c032346e0367df325f73dd4be`. This is repository maintenance,
not an evaluated experiment. The parent integration record is
[/workspace/plan/2026-10-21-pbt-stabilization-loop.md](/workspace/plan/2026-10-21-pbt-stabilization-loop.md).

Acceptance requires all of the following:

- Preserve the live checkout's existing, independently accepted preparation
  changes and `plan/2026-10-21-pbt-preparation-preambles.md`. The two reviewed
  preparation source/test files already match the isolated bytes and are not
  overwritten.
- Copy the other 25 reviewed paths byte for byte. The 13 reviewed product files
  must match their manifest hashes, including the already-identical preparation
  source. Fourteen original non-product paths must also match exactly, including
  the already-identical preparation test. The only original reviewed path that
  is intentionally not byte-identical is `plan/INDEX.md`.
- Merge `plan/INDEX.md` manually so it retains the existing preparation-plan
  entry, adds the three isolated historical entries without changing their text,
  and adds this integration plan's entry. Do not replace the live index with the
  isolated index.
- Preserve the three imported plans, two imported wiki topics, and imported
  `wiki/INDEX.md` byte for byte. They are immutable historical records: do not
  rewrite their status, acceptance, causation, evidence, or limitations.
- Preserve raw CRLF bytes in `Source/DafnyCore.Test/DafnyCore.Test.csproj`, whose
  required SHA-256 is
  `c5df8e8dcd0c379963925f9f669294ae0fb22da422e0d1d56de7d4a973f0ce7d`.
- Produce a new live inventory after transfer. Keep it distinct from the
  immutable historical complete-reviewed identity
  `c82d710c1aa9db6b84275e7f7d2ac2c28a4fccba5baaf7172e48b36e30db02cd`
  and historical 13-product map identity
  `40b9b23ff62f16eb97b6e2afa6867b0537cc0e5123fe9f2aaa27868b7c51f323`.
  The live inventory must explicitly identify the merged-index exception and
  the additional integration plan instead of relabelling the historical hashes.
- Pass the sequential cached project builds, four exact memory-test selections,
  20-file scoped whitespace verification, diff/Markdown checks, and the separate
  canonical launcher build below. A fresh independent review of the resulting
  live checkout must inspect the implementation and run its own checks.

No benchmark specification, task, dataset, evaluator, oracle, scoring, report,
frozen experiment input, prebuilt binary copy, image, provider configuration, or
root/Cosyn source change is part of this transfer. The explicitly listed live
builds may update their normal local build outputs; those outputs are validation
artifacts and are not transferred source or image inputs. No dependency change,
package install, Docker operation, tmux session, native campaign, provider call,
commit, or paid run is authorized. Do not read private provider, candidate,
evaluator, reference, solution, or old-trace material.

## Inspected evidence and ownership

The root, Cosyn, and live Dafny `AGENTS.md` files and live `CLAUDE.md` apply. The
live native `plan/` and `wiki/` trees have no narrower instructions or templates.
The live tree was inspected at the required base with these pre-existing changes:

- `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs`
  has SHA-256 `39db263d394a81480feb993195387d3ccbd6c4aa224e1ce53abe020457ba17a7`.
- `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs`
  has SHA-256 `4ae370c1f5d53a43e0fa90d405e71e05867c4e798414ddef21c22f0e7820d5eb`.
- `plan/2026-10-21-pbt-preparation-preambles.md` and its live index entry belong
  to that completed work and must remain intact.

The exact original reports are read-only provenance and remain untouched:

- `/workspace/tmp/pbt-repeatable-proof-inputs-20261021/source-review.json`,
  SHA-256 `e88ebf21a2bebadec02db751ac0734d065a97be33e47e8e0e930004aad827f15`.
  It records 28 reviewed paths, 13 products, 15 non-products, stable historical
  identity `c82d...`, product map `40b9...`, source acceptance, eight cached
  builds, and 139 selected memory checks. It explicitly does not provide
  packaging, operational, stabilization, image, provider, or benchmark acceptance.
- `/workspace/tmp/pbt-repeatable-proof-inputs-20261021/launcher-build.json`,
  SHA-256 `a44a7fa32c9cab35c48876733b79c9a5d952f3ffaf6715954965f784692ebf48`,
  and `launcher-build.log`, SHA-256
  `64830b3a1746a282799ae32461c515d45ef96f2fd81c6beb342549a1eed27761`.
  These separately record the isolated canonical launcher build; they are not
  evidence for the new live tree.
- `/workspace/tmp/experiment/pbt-authored-generator-20261021-r03/verification/execution-review.json`,
  SHA-256 `5a14e16a5fbfc87d0b48b65a59201413d5170acc07bb9c85630f7fd45fdef933`,
  and `manifest.json`, SHA-256
  `c0c25236eb66f8084ac1cbc70b6feb0caae206118f6b7a44a9e51c69c50bef63`.
  They are public historical operational provenance only. Their accepted
  synthetic run does not establish repeated stability, benchmark efficacy,
  sole historical causation, paid-run authority, or acceptance of this live
  transfer.

The Dafny repository owns every transferred implementation, proof boundary,
test, and native knowledge record. No root composition or Cosyn harness contract
changes. Specification, dataset, isolation, evaluator, oracle, scoring, and
reporting layers are unchanged. The transfer preserves reviewed behavior rather
than redesigning or weakening proof, trust, scope, fingerprint, or fallback
rules.

## Exact 28-path transfer table

The source of every row is the same relative path below
`/workspace/tmp/pbt-worker-failure-20261021/native`; the destination is the same
relative path below `/workspace/cosyn/dafny`. `Copy` means exact byte copy,
`skip-identical` means verify current live bytes and leave them untouched, and
`manual merge` is the single stated hash exception.

| Path | Class/action | Required isolated SHA-256 | Why and validation |
| --- | --- | --- | --- |
| `Source/DafnyCore.Test/DafnyCore.Test.csproj` | non-product test project; Copy | `c5df8e8dcd0c379963925f9f669294ae0fb22da422e0d1d56de7d4a973f0ce7d` | Embed the bounded prelude fixture; raw byte/hash check preserves CRLF. |
| `Source/DafnyCore.Test/DefinitionProofInputsTests.cs` | non-product test; Copy | `3004dbd2d78c6c3d81c185033852c5985aec557b5714b9fa42cb08a9af6d5476` | Adapt analyzer controls to the injected memory boundary; Core selection. |
| `Source/DafnyCore/AST/Expressions/Variables/NonglobalVariable.cs` | product; Copy | `5cd70506bbb29e0ad6fb3042032c51f98e9dd59c49acf80bb2cc386f60911cba` | Scoped verification names; build plus repeatability checks. |
| `Source/DafnyCore/AST/Statements/Assignment/LocalVariable.cs` | product; Copy | `5ddff47c0e4dde57c06170ecb03cfd7a8b67aff9cc2cdfa9cebb0bcf42232157` | Scoped local verification names; build plus repeatability checks. |
| `Source/DafnyCore/AST/TypeDeclarations/Declaration.cs` | product; Copy | `7952dc3dcd12115721df16ffc4f3825ac9031f8a7d5cd225ee299cbe3c273ba7` | Route declaration verification IDs through the scope; build and tests. |
| `Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs` | product; Copy | `a1e415e69d23c0b7b923f8fe989b68c27ca5414f46bac104d2a6ba42baaefad6` | Retain production analyzer and internal memory-test seam; Core selections. |
| `Source/DafnyCore/Verifier/BoogieGenerator.cs` | product; Copy | `5149f84bbfbfa213f5dd7f52b69521b762f53484abb61e1670768cf2812b8602` | Own each synchronous translation naming scope and prelude seam; build/tests. |
| `Source/DafnyCore/Verifier/FreshIdGenerator.cs` | product; Copy | `162457247474beb363667b6d8d36b7a9041578428a529ed3b517f56a2fc634f3` | Implement nested/restored verification naming scope; build/tests. |
| `Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs` | non-product test; Copy | `d9777eb8d464cb7fba6c444ab02e21e5f7a8ad750660a0a307668e4fa92e4e9a` | Pure result/budget and pre-artifact request cases; Driver selection. |
| `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs` | product; Copy | `2d701825efc09c625b331da63836e075450727b1a7baaea0028d1c989783c145` | Preserve proof reporting/budget and early null-draft validation; build/tests. |
| `Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs` | non-product test; Copy | `6e06413b3b4329012af661d9af9c35d980216bb48151e9a5840ea8dcbd9826db` | Bounded helper/audit/visibility/fallback checks; TestGeneration selection. |
| `Source/DafnyTestGeneration.Test/ContractGeneratorProofTests.cs` | non-product test; Copy | `3d5cbaed546905d67b7858435a2d2b8629f5d56bf7dd796c4fcefaa5bba76f74` | Authored proof, binding, audit, and policy checks; TestGeneration selection. |
| `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs` | non-product test; skip-identical | `4ae370c1f5d53a43e0fa90d405e71e05867c4e798414ddef21c22f0e7820d5eb` | Preserve accepted live preparation work; compare bytes and run included selection. |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs` | product; Copy | `c89723ae57375485c946bcdef11961b7fff7f153eeebc5585d1bc21890c5537a` | Preserve authored source, analyzer bindings, certificate and fallback gates. |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProofAudit.cs` | product; Copy | `e6edeb40f9e2d494ce83d92e81655417a9ec6722353c66275dcf4a1957961a46` | Preserve raw/resolved trust audit; selected memory tests. |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs` | product; Copy | `77d2eb68f4c153664bdfafaaa86d55d91b5129395a0792199d934e9eff581547` | Preserve certificate-controlled entry omission and ordinary runtime checks. |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs` | product; skip-identical | `39db263d394a81480feb993195387d3ccbd6c4aa224e1ce53abe020457ba17a7` | Preserve accepted live include/default-module preparation; compare bytes. |
| `Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs` | product; Copy | `2f9af24975c88afec0623372a85461bfbda8cc928f4e3f3a7ac8d1d70381113e` | Preserve audited execution/logical helper scope; selected memory tests. |
| `plan/INDEX.md` | non-product memory; manual merge | historical `fc6286ba3520da3e7eb320f19ab26b5480011bc060a34c01e27371c9e829be1d` is not a live target | Retain preparation entry, add three historical entries unchanged, add this ready plan; inspect diff. |
| `wiki/INDEX.md` | non-product memory; Copy | `2b16cfa76dd5fb961f6039da6ce7fba20c1968f37718561fd8b61b58db227158` | Import reviewed knowledge index byte for byte; hash/Markdown audit. |
| `wiki/pbt-generator-proof-helpers.md` | non-product memory; Copy | `d204fb63da9d820277c0f2c9ac8df9a5b8e1fc573f86f1c4664feada8cdcd5cb` | Import reviewed helper boundary/history unchanged; hash check. |
| `wiki/pbt-generator-proof-integrity.md` | non-product memory; Copy | `b778c839ae6f6b2f53dcb12f46f6ea7650ffea2677a7cb0f532c12ee4015fd6d` | Import reviewed proof-integrity boundary/history unchanged; hash check. |
| `Source/DafnyCore.Test/ProofInputRepeatabilityTests.cs` | non-product test; Copy | `eb1fc4daaa8a6368fe07ecc7ca288d36d9916ad40eedc2ccf4c80bb1121df99c` | Add actual in-memory repeat-translation regression; Core selection. |
| `Source/DafnyTestGeneration.Test/ContractGeneratorVerificationTests.cs` | non-product test; Copy | `6c796b38ad24d973f82fc155bf92a6e7f23142a678d8a608902da9ddf06e195e` | Add pure complete-part accounting and origin controls; TestGeneration selection. |
| `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorVerification.cs` | product; Copy | `2fd4aacde6e6fe63b54705d6c604a7037c2ab4823f18045a9662d8db0e54bb66` | Use host ordinary task enumeration and complete result accounting. |
| `plan/2026-10-21-pbt-authored-generator-proofs.md` | non-product historical plan; Copy | `dae570286b2d4f3bac4552aec1935a5fb92175180451406a799cfb2952388636` | Preserve original status, acceptance, causation, commands, and limits. |
| `plan/2026-10-21-pbt-worker-failure.md` | non-product historical plan; Copy | `5c2b14daabedd4ce8690a5d4613fc674cad997c3a5b02e97048209a1c82a21d8` | Preserve original status, acceptance, causation, commands, and limits. |
| `plan/2026-10-21-repeatable-proof-inputs.md` | non-product historical plan; Copy | `2fb951e61e3b745e97dfcaecc2318fd3f220efc56700cc968d6dc9a6fa43317f` | Preserve original status, acceptance, causation, commands, and limits. |

Without these exact transfers, live main lacks the reviewed naming repair,
authored generator proof boundary, verifier accounting, worker validation,
regressions, and their historical development record. Reimplementing, formatting,
or selectively editing the isolated sources would discard the reviewed identity
and is outside this plan.

## Test-helper and external-boundary trace

The four proposed selections were traced through their fixtures, production
entry points, setup, execution, and managed teardown before inclusion:

- `ProofInputRepeatabilityTests` parses bounded strings with a strict dictionary
  `IFileSystem` that throws on unknown file or directory access. It resolves in
  memory, parses the unchanged embedded `DafnyPrelude.bpl` resource in memory,
  performs ordinary Boogie translation without an execution engine, and injects
  a synthetic toolchain digest into the real projection/serialization/lexer/hash
  path. `DefinitionProofInputsTests` reuses that helper. Neither selection calls
  the production six-assembly `ProofToolchainHash`, reads a source program from
  disk, creates a directory, starts a solver/verifier task, spawns a process, or
  reaches a durable-write/synchronization boundary.
- `ContractGeneratorProofTests`, `ContractGeneratorProofHelperTests`, and
  `ContractRuntimeSourcePreparationTests` use bounded strings,
  `ContractSourceSnapshot`'s dictionary-backed filesystem, in-memory parser and
  resolver objects, and embedded runtime text. Analyzer bindings are supplied by
  whole fake providers. Helper proof cases inspect scopes and fake coverage. The
  `UnusedVerifier` throws if native task enumeration is reached; cancellation and
  invalid-authored-source cases stop before that boundary. They do not invoke a
  solver, compiler, native process, campaign staging, installed-toolchain hash,
  temporary directory, or synchronization operation.
- `ContractGeneratorVerificationTests` exercises pure task-part accounting and
  bounded parsed origin selection. It does not construct an execution engine or
  call `GetVerificationTasksAsync`.
- `GeneratorProofResultTests` uses JSON values and pure result/budget helpers.
  Its apparent `RunAsync` call carries a null draft: `Validate(request)` rejects
  it before `ContractPhaseRecorder`, path construction, directory creation,
  source parsing, compilation, campaign process, or artifact writes.

The `dotnet test` host itself uses a local VSTest TCP socket and is a separately
visible runner prerequisite. `--no-build --no-restore` keeps the four selections
from compiling or restoring. No selected body has a fixture/autouse fixture,
deferred cleanup, temporary-directory helper, real filesystem fallback, real
toolchain identity, verifier/solver execution, process launch, `fsync`,
`fdatasync`, or equivalent durable sync. Build output from the explicitly listed
build commands is validation output, not a hidden test side effect.

## Implementation sequence and artifacts

Implementation starts only after the root announces this ready plan. First set
the status to `in-progress` and capture the live base, status, existing changed
paths, and current hashes. Then perform the 25 exact copies, verify the two
skip-identical files, and manually merge the plan index. Do not overwrite,
delete, reset, or reformat unrelated live work. Stop and amend this plan before
any path, source, action, or validation scope changes.

If generated records are needed, reserve only this bounded owner directory:
`/workspace/tmp/pbt-native-live-integration-20261021/`. Proposed files are
`before-state.json`, `after-state.json`, `transfer.json`, `build.log`,
`checks.log`, `verification.json`, and `verification.md`. None exists or is
created during planning. Each log is bounded to 8 MiB. `transfer.json` must list
the 28 reviewed paths, action, expected and actual byte count/hash, the manual
index exception, and the additional integration plan. `after-state.json` must
record a newly computed live identity under a new field name; it must not assign
`c82d...` to the merged live inventory. Do not write generated evidence under
`plan/` or `wiki/`.

## Validation commands, prerequisites, and expected results

All commands run sequentially from `/workspace/cosyn/dafny`. Prerequisites are
the installed SDK selected by `global.json` (`8.0.111` with latest-feature
roll-forward), already restored project assets and existing generated parser
sources. Do not restore, download, invoke Gradle, generate parsers, install a
package, or run the full solution. If cached assets are missing, record the
blocker rather than broadening the command.

Run these eight exact affected-project builds in order; each must exit zero with
no errors, while warnings are recorded rather than hidden:

```text
dotnet build Source/DafnyCore --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyPipeline --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyLanguageServer --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyTestGeneration --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyDriver --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyCore.Test --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyTestGeneration.Test --no-restore --no-dependencies -m:1 /nr:false
dotnet build Source/DafnyDriver.Test --no-restore --no-dependencies -m:1 /nr:false
```

Then run these exact four memory selections. Expected results are all selected
cases passing with zero failures and zero skips; record actual counts. A sandbox
denial of the VSTest loopback socket is a runner failure, not a test failure or
pass, and requires the approved local socket execution path.

```text
dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~ProofInputRepeatabilityTests
dotnet test Source/DafnyCore.Test --no-build --no-restore --filter FullyQualifiedName~DefinitionProofInputsTests
dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore --filter 'FullyQualifiedName~ContractGeneratorProofTests|FullyQualifiedName~ContractGeneratorVerificationTests|FullyQualifiedName~ContractGeneratorProofHelperTests|FullyQualifiedName~ContractRuntimeSourcePreparationTests'
dotnet test Source/DafnyDriver.Test --no-build --no-restore --filter FullyQualifiedName~GeneratorProofResultTests
```

Verify the exact 20 touched C# files without allowing formatter writes:

```text
dotnet format whitespace . --folder --include Source/DafnyCore.Test/DefinitionProofInputsTests.cs Source/DafnyCore/AST/Expressions/Variables/NonglobalVariable.cs Source/DafnyCore/AST/Statements/Assignment/LocalVariable.cs Source/DafnyCore/AST/TypeDeclarations/Declaration.cs Source/DafnyCore/DefinitionAnalysis.ProofInputs.cs Source/DafnyCore/Verifier/BoogieGenerator.cs Source/DafnyCore/Verifier/FreshIdGenerator.cs Source/DafnyDriver.Test/ContractRuntime/GeneratorProofResultTests.cs Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs Source/DafnyTestGeneration.Test/ContractGeneratorProofHelperTests.cs Source/DafnyTestGeneration.Test/ContractGeneratorProofTests.cs Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProofAudit.cs Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs Source/DafnyTestGeneration/ContractTesting/ContractSpecificationChecker.cs Source/DafnyCore.Test/ProofInputRepeatabilityTests.cs Source/DafnyTestGeneration.Test/ContractGeneratorVerificationTests.cs Source/DafnyTestGeneration/ContractTesting/ContractGeneratorVerification.cs --verify-no-changes
```

Run `git diff --check`; inspect `git status --short`, the complete live diff, and
the manual `plan/INDEX.md` diff against this table; compare the 25 copied files
and two skipped files byte for byte with the isolated tree; verify every stated
byte count/hash and the CRLF project bytes; and confirm no source, binary, image,
frozen-experiment, or record changes outside this plan. Recursively run
`find plan wiki -type f ! -name '*.md' -print` and
`find plan wiki -type l -print`; both must be empty. Confirm every imported
historical plan/wiki hash remains exact and that reciprocal plan/wiki links and
both indexes are consistent.

After those checks, separately run the supported canonical main launcher build:

```text
dotnet build Source/Dafny --no-restore --no-dependencies -m:1 /nr:false
```

It must exit zero and records launcher packaging only. It does not establish a
Dafny proof, generator proof, runtime campaign, experiment, image, provider, or
benchmark result. No full-solution build is planned.

A fresh independent live review must start from these requirements and the
current repository state, independently inspect all 13 products and affected
tests, verify the exact transfer/inventory/index exception, and run its own
appropriate checks. It must not treat the historical reports or imported plans
as authority for the new live tree. Record its bounded results in the reserved
verification JSON/Markdown paths only after implementation.

## Risks, compatibility, approvals, and closeout

The primary risks are overwriting the two accepted preparation changes, replacing
the live plan index and losing its preparation entry, normalizing the CRLF
project, editing immutable historical records, or claiming the historical
`c82d...` identity for a different live set. Exact copy/hash checks, the single
manual merge, and separate live inventory address those risks. Existing public
interfaces and behavior are those already represented by the reviewed sources;
this plan authorizes no compatibility redesign or fallback heuristic.

The root plan already authorizes the bounded live transfer and local validation
after it announces this plan ready. No additional package, live-provider, Docker,
campaign, commit, or benchmark authority exists. Any such need requires a plan
update and explicit approval before action.

Mark this plan `done` only after exact transfer acceptance, all required local
checks, separate canonical launcher build, and fresh independent live acceptance.
If a prerequisite or check fails, preserve the evidence, mark the concrete
blocker and next action, and do not relabel an unrun or failed check as passing.
Update the existing imported wiki topics only if this integration yields a new
durable technical finding; otherwise record `No durable findings` here because
the transfer itself adds no knowledge beyond the exact historical records.

## Planning record

The live/isolated bases, current live changes, original report hashes, 28-path
manifest, transfer split, historical identities, CRLF project bytes, supported
commands, Makefile/global SDK context, selected test bodies, fixtures, parser
filesystem seams, embedded resources, analyzer/toolchain seams, verifier/task
seams, campaign early validation, process paths, and synchronization boundaries
were inspected. The two skip-identical files were byte-compared successfully.
Root reviewed and announced the ready plan, authorizing phase 2 within this
exact transfer and validation scope; status is now `in-progress`.
No implementation transfer, artifact creation, build, test, format, campaign,
provider call, package action, commit, or independent verification ran in this
planning phase. The next action is the exact transfer.

## Settled implementation handoff

After the root announcement, the live tree received the exact planned transfer:
25 paths were copied byte for byte from the isolated source, both preparation
files were confirmed byte-identical and left untouched, and `plan/INDEX.md` was
merged manually. The live index retains the preparation entry, includes the
three isolated historical entries verbatim, and identifies this plan as
`in-progress`. All three imported plans, both imported wiki topics, and the
imported wiki index retain their manifest bytes and historical wording.

All 27 original reviewed paths other than the manual index exception match the
isolated bytes, sizes, and SHA-256 values. The CRLF project remains
`c5df8e8dcd0c379963925f9f669294ae0fb22da422e0d1d56de7d4a973f0ce7d`.
The original isolated reports retain their pinned hashes. The new live inventory
records the original 28-path set with `plan/INDEX.md` as its sole merge exception,
and records this mutable owner integration plan separately. Historical identities
`c82d...` and `40b9...` remain labels for the isolated reviewed set/product map;
they are not relabelled as a hash of the merged live documentation set. This
owner plan can receive later independent-review status/progress notes, so its
current hash must not be used to claim that the entire live inventory remains
unchanged after documentation closeout.

The eight sequential affected-project builds ran exactly as listed. DafnyCore,
DafnyPipeline, DafnyLanguageServer, DafnyTestGeneration, DafnyDriver,
DafnyCore.Test, and DafnyDriver.Test each passed with zero warnings and errors.
DafnyTestGeneration.Test passed with four known warnings and zero errors: two
unreachable-code warnings in `ContractRuntimeProfile.cs`, one obsolete
`ISequence.Elements` warning in `PbtObservation.cs`, and one synchronous-cancel
analyzer warning in the unchanged `ContractPhaseTimingTests.cs`.

The first `ProofInputRepeatabilityTests` invocation was aborted before executing
a test because the sandbox denied VSTest's loopback socket. The exact same
audited command then ran through the approved local socket path and passed 12/12.
The other traced selections used that same narrow runner path and passed 21/21
DefinitionProofInputs, 97/97 combined TestGeneration proof/verification/helper/
preparation cases, and 9/9 Driver result cases. Total: 139 passed, zero failed,
zero skipped. No test body reached real source-program filesystem, installed
toolchain hashing, verifier/solver execution, native compilation, campaign
process, temporary-directory/staging, or synchronization boundaries.

The exact 20-file folder whitespace command with `--verify-no-changes` exited
zero. `git diff --check` and recursive plan/wiki non-Markdown and symlink audits
passed. A preliminary manifest-inspection shell loop failed without checking
files because its local variable was named zsh's reserved `path`, which emptied
the command search path inside the loop. The corrected read-only loop used
`reviewed_file`, found no mismatch, and made no repository change.

The separately planned canonical
`dotnet build Source/Dafny --no-restore --no-dependencies -m:1 /nr:false`
passed with zero warnings and errors. No restore, download, Gradle, full-solution
build, Docker, tmux, native campaign, experiment-input edit, provider/private
access, package change, commit, or prebuilt binary/image copy occurred.

Bounded records live only under
`/workspace/tmp/pbt-native-live-integration-20261021/`. Fresh independent live
acceptance remains pending; therefore this plan remains `in-progress` and must
not be marked done by the implementation owner. No durable findings: this was an
exact reviewed-source integration, and the immutable imported wiki records
already contain the reusable technical findings. The next action is root rehash
of the settled input identities followed by fresh independent review from a new
context.

## Independent live acceptance

A fresh verification context independently inspected the13production paths,
all20changed C# files and the project file, byte-compared the27non-index original
paths with the isolated sources, and checked the reviewed28-path identity
7b9ecfb883a4bb39b7306aedf7c244f208fb716f5de53a13f248ab30929bd62f.
It independently ran the eight sequential affected builds and separate canonical
launcher build, all with zero warnings/errors. Its four exact memory selections
passed12+21+97+9=139, zero failed/skipped. The first sandboxed VSTest launch was
aborted by loopback denial before tests; the exact approved local-socket rerun
passed and the aborted attempt was not counted. Scoped20-file whitespace, diff,
index-preservation and recursive Markdown/symlink checks passed.

The independent original records are
/workspace/tmp/pbt-native-live-integration-20261021/verification.json,
SHA256bf30ff940509ff07d2f697fe25571496d45ea450a3a25cb04c62b5d71a5a36e9,
and verification.md,
SHA256f805f7ede1fbbd361af2e4e6adb0dc6b7ffb768c98d545af9a3792bbd0939135.
Root rehashed both originals and sealed them0444. Acceptance is source/local
only; the verifier ran no solver-backed generator control, Docker, campaign,
provider, private input, benchmark or paid experiment. Previously accepted r03
public operational controls remain separate evidence, not a result of this
live source review.

Closeout updates only this additional owner plan and its merged-index entry to
done. The accepted27original non-index files, CRLF project bytes, preparation
plan, isolated historical records, frozen inputs and image remain unchanged.
The reviewed28-path identity above describes the review-time state; the index
status edit is a disclosed post-review documentation change and must carry a
distinct current live identity. No durable findings beyond the exact historical
wiki records: this bounded work only integrates and verifies those sources.
The parent stabilization/cohort work remains active; no commit was made.

After that documentation closeout, the current original28-path live identity is
a31093366f001abf136b2e9b21f596b92db1b04991f999ce504230fc9d173f55,
using the same sorted path/TAB/size/TAB/SHA256/LF scheme. Its6167-byte merged
plan index is c36d0d7b47b0733ad72515350e5f0bd30429f687667bd77a6db0f00c5d73cf71.
Root rechecked all27non-index original paths still match isolated bytes.
This additional integration plan remains outside that28-path identity.
