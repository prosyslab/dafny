# PBT trusted source snapshots

Status: independently accepted on the combined integration base, 2026-10-19.
The owning plan is
[2026-10-19-pbt-trusted-sources](../plan/2026-10-19-pbt-trusted-sources.md).

## Contract

Schema-v2 runtime campaign requests can carry an optional `TrustedSources` list
of `ContractDependency` identities (`Path`, `Sha256`). The default is null and
retains strict checking. Validation requires each identity to match one unique
source snapshot exactly; source content hashes and canonical path uniqueness use
the existing `ContractSourceSnapshot.Validate` checks.

The specification checker binds the list to canonical source origin URIs only
after validating path and digest membership. A trusted source's original
declarations remain in dependency closure and scope symbols, but their own
declaration trust audits and native declaration proof obligations are omitted.
The checker still verifies ownership against the original resolved program, and
declarations reached transitively from a trusted declaration remain checked
unless their own source identity is explicitly trusted. Scope/cache identity
contains both source-set and trust-set hashes. Trust is source-granular and is an
explicit host assumption.

Runtime value admission remains separate. Campaign input validation, concrete
predicate reduction, runtime type evidence, heap field membership, frame checks,
and candidate/helper obligations retain their existing code paths. Internal
initial and observed heap checks carry a defensive trust-set copy; initial
preparation attestation hashes that copy with its request, and checker binding
checks it before carrier or observed construction work. The legacy
`ContractTestRequest` has no trust field.

## Verification and limits

The focused test class uses the in-memory `ContractSourceSnapshot.ParseAsync`
path and a pure expression reducer. It covers exact path/digest membership,
same-path foreign AST ownership, default/untrusted `assume` and `extern` rejection,
trusted axiom audit omission, retained candidate and transitive helper checks,
module-name lookalikes, trust-separated scope identity, concrete false predicate
reduction, and initial/observed checker-context mismatch.

On the original native tree at `bef89d2244ddd9a3bc898ad97252d82049ff5cdd`,
`.NET SDK 8.0.131` test-project and driver builds passed. The first
test restore attempt stopped during MSBuild's restore-project-reference walk
without an emitted error diagnostic; a serial scratch-isolated restore then
passed. The initial Java runtime build could not use the incomplete default
Gradle wrapper cache in the read-only home directory; preparing the official
Gradle 8.14 distribution under task scratch resolved that prerequisite without
repository changes. The test-project build had zero errors and four existing
warnings outside the changed code; the driver build had zero warnings/errors.
The focused filter `FullyQualifiedName~ContractTrustedSourcesTests` passed 15/15
with no skips. VSTest's ordinary sandbox attempt failed before executing tests
with `SocketException (13): Permission denied`; the authorized local-socket run
first found an incorrect expected label (`Function` instead of Dafny's
`Predicate`), which was corrected before the passing rerun. A fresh independent
review accepted that native source and independently passed the 15 focused tests.
No solver was invoked by the focused tests. Final logs and the test assembly are
under `/workspace/tmp/pbt-trusted-core-20261019/`. These results make no Dafny
proof, benchmark or performance claim.

Integration follow-up: the native patch is now at
`0e5338b75e4094be20e005d79abcc750cf69a44e` on base
`29da48b6c47e9c8484c8a2818e2be2032ad14206`, which adds separate
DefinitionAnalysis visibility changes. On 2026-10-19, the serial test-project and
Driver builds were rerun against this HEAD using the prepared Gradle cache and
scratch output paths; the focused in-memory filter passed 15/15 with no skips.
The test-project build had four unrelated existing warnings and no errors; the
Driver build had zero warnings/errors. VSTest used the approved local-socket path.
Logs are under `/workspace/tmp/pbt-trusted-core-20261019/` as
`build-test-integration.log`, `build-driver-integration.log`, and
`test-focused-integration.log`. The plan/wiki diff passes `git diff --check`, and
the plan/wiki trees contain Markdown files only. Fresh independent review accepted the
combined source and independently passed all 15 focused tests (zero failures/skips).

Source of record: native Dafny changes in `Source/DafnyTestGeneration` and
`Source/DafnyDriver`; implementation plan above. Independent verification
accepted both the original and combined native source, and independently passed
all 15 focused tests on the combined assembly.
