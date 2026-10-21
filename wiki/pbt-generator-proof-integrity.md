# Exact generator admission proof boundary

Status: authored-contract proof gates preserved; repeatable translation naming locally validated, with fresh repair review and new operational controls pending.

Current source state: 2026-10-21, isolated native base `b4f683fd85c9764c032346e0367df325f73dd4be` plus preserved worker repair and authored-contract changes. Originating [current plan](../plan/2026-10-21-pbt-authored-generator-proofs.md). Earlier acceptance below applies to the superseded mechanism only.

The optional ordinary runtime request uses schema 4 with `proveGeneratorPreconditions: true`, and returns schema 3 with bounded `generatorProof` observations. Ordinary requests retain schema 2 and result schema 1. Public JSON metadata never authorizes omission: only the private in-process certificate from `ContractGeneratorProof.TryProveAsync` can do so.

The generator keeps its authored body and every authored ensures clause. The source builder adds one ordinary lemma over the generator outputs: its requires are the generator ensures, and its ensures are every original target requires in original order. It uses resolved capture-free substitution. The empty lemma body asks ordinary Dafny verification to establish that implication; it never calls the executable generator. Independently, the generator body must establish its own authored contract.

Proof receives source-preparation snapshots before `MakeGeneratorVisible` erases
ghost method bodies. Reapplying that exact visibility operation and appending
the exact runtime resource must reproduce the runtime snapshots. Both contexts
are normally parsed before analyzer translation. A successful certificate owns
the normal runtime resolve used by subsequent transformation; the diagnostic
resolver's partially resolved AST never reaches this analyzer path. Invalid
authored ghost code makes proof unsupported while leaving runtime fallback intact.

`ContractGeneratorInputBinding` reuses `DefinitionAnalysis.AnalyzeDocument` with proof inputs enabled and semantic facts disabled, together with `SourceFingerprint.Compute` over immutable source snapshots. It requires schema 1, complete SHA256 digests, unique in-snapshot identities and an exact row for every audited callable, including generator, bridge and helpers. Each row retains ambient non-callable translation; ordinary helper implementations need their own rows because the analyzer excludes other modular method bodies. Runtime and private proof programs are rechecked before certificate issuance and omission. No separate resolved-AST reflection fingerprint remains. Production analyzer capture reads compiler assemblies for its existing toolchain identity; PBT boundary memory tests fake the entire analyzer provider. The Core repeatability tests described below exercise actual translation and fingerprinting with an internal environment seam.

`ContractGeneratorProofAudit` policy v3 pins the exact embedded `PbtRandom` digest `f565ca5d86962c87a6b64f860fb7ba8450dbe5573f6980eb6b5751f577df8f72`. Its raw traversal uses `PreResolveChildren`, including concrete-syntax call arguments. Existing audited execution/logical scope discovery retains reachable helper bodies and all ambient logical functions, constants and constrained types. The target ordinary body stays outside the proof prerequisite; a dependency back to it rejects the optimization.

`ContractGeneratorVerification` uses the host-owned ordinary `IProgramVerifier` task lifecycle, exact native role names and module/origin ownership. Every enumerated required part must complete successfully. Complete trusted enumeration can establish an assertion-free role, but generator and bridge each require positive correctness tasks. Missing or unbound parts never become assertion-free; zero-task roots conservatively retain runtime checks. The internal host entry and private certificate remain unavailable to request JSON. Existing option/trust policy is reapplied, and the certificate privately retains the full required-check set to reject coverage narrowing. The specialized specification-checker verification path and its generator-specific pinned-solver machinery are no longer used for generator proofs.

Only selected-entry explicit requires checks may be omitted. Declared input type constraints, heap admission and recursive/callee requirements remain runtime obligations. Unsupported, failed, timed-out, cancelled, incomplete or forged proof observations retain ordinary runtime checking. The retained value-only proof capability does not cover arbitrary heap-dependent requirements or change target implementation proof obligations.

Current local evidence: 78 selected TestGeneration source/audit/identity/part-accounting/preparation cases and nine Driver result/budget cases passed, zero skips. Affected TestGeneration, Driver and Driver.Test builds passed with zero warnings/errors; TestGeneration.Test passed with four pre-existing warnings. The full solution attempt was interrupted after the unchanged Java target failed to create a Gradle cache lock; this is an environment failure, not a passing solution build. The exact commands and test I/O trace are in the current plan. No actual proof or runtime control was run for this refactor.

## Public binding rejection and diagnostic follow-up, 2026-10-21

The subsequent parent-owned public r02 control used the quantified generic
generator and reported three generated/executed/valid samples, zero runtime
errors, and retained entry requirements. Its generator proof was unsupported
with the compound final source/options/scope-change diagnostic. That message
does not identify which comparison failed, and the public report supplies no
individual proof-stage evidence. Repeated translation's mutable identifier
state is a source-backed hypothesis, not an established cause.

The current diagnostic-only follow-up preserves exact source and serialized
analyzer equality, every required-definition check, and certificate authority.
Its ordered final gate reports proof-binding, runtime-binding or caller-policy
rejection. Binding diagnostics distinguish unavailable/incomplete inputs,
source fingerprint, toolchain/options identities, and changed/missing/added
definition identities. Definition display is bounded and control characters
are replaced; equality and completeness are checked over the full inputs.
Reordered analyzer rows still reject even when their individual digests match.
Each comparison captures once, in the original short-circuit order.

Local diagnostic validation passed 73 selected proof/helper/verification memory
cases and nine Driver cases, zero skips; source-preparation tests are outside
this unchanged-source follow-up selection. Four affected project builds passed,
with only the four existing TestGeneration.Test warnings. All analyzer/toolchain
boundaries in these development tests are faked. Independent current-source
review and a separately planned public diagnostic campaign remain pending.
Source and validation records are in the [owner plan](../plan/2026-10-21-pbt-authored-generator-proofs.md)
and [root diagnostic plan](/workspace/plan/2026-10-21-pbt-verifier-binding-diagnostics.md).

Local unit/build results establish the implementation's inspected trust and transformation controls. They do not establish solver proof success, compiled runtime omission, benchmark correctness, statistical outcomes or independent acceptance. Parent-owned final `tmux` proof probes and review must provide those separate results.

## Repeatable translation naming, 2026-10-21

The later accepted parent-owned public diagnostic identified a proof-binding
definition-input change for `QuantifiedControl.GeneratorRange`. It executed one
valid sample and retained runtime checks. Its report does not expose individual
proof stages or the changing Boogie tokens. See the [root repair plan](/workspace/plan/2026-10-21-pbt-repeatable-proof-inputs.md)
and [native repair plan](../plan/2026-10-21-repeatable-proof-inputs.md).

The Core memory regression reproduced fingerprint drift for the once-resolved
public quantified helper both between consecutive analyses and across an
intervening ordinary translation. Both tests failed before naming changes;
the exact pre-fix patch, source hashes and original failures are preserved in
`/workspace/tmp/pbt-repeatable-proof-inputs-20261021/`. This establishes a local
repeat-translation defect, not that it was the only input changing in the public
operation.

`BoogieGenerator.DoTranslation` now owns a small synchronous thread-local naming
scope. `Declaration.IdGenerator` and both variable implementations' verification
name accessors use that scope's dictionaries. Generated wellformedness locals,
original binder names and forall child scopes therefore share one allocation
history within a translation without inheriting the previous translation's
history. Disposal restores an enclosing scope even on exceptions. Plugin
PreVerify callbacks retain their prior outside-scope view; compilation names
and generators remain unchanged.

Legacy caches and generators remain separate and coherent. A first scoped
assignment also initializes an absent legacy name through its legacy generator.
Outside `HasBeenAssignedUniqueName` still observes assignment, existing outside
names remain stable, and later outside allocations remain unique. A newly
initialized outside name need not equal the scoped emitted identifier. Current
source has no consumer requiring that equality; trigger comparison sees the
active scope's names. This synchronous scope is not a general promise of safe
concurrent mutation of the same resolved AST.

The analyzer's projection, lexer, digest schema, modular exclusions and exact
equality gates are unchanged. Core tests call the actual analyzer through an
internal translation/toolchain environment seam, use a strict dictionary
filesystem and the unchanged 67,083-byte embedded prelude, and never run a
solver, external compiler, process, disk staging or installed-assembly hashing.
Resolved-body/postcondition, effective-option and synthetic toolchain changes
still alter the appropriate fingerprints. Detailed local commands and final
results belong to the native repair plan. Final local checks passed 12 repeatability,
21 analyzer, 97 PBT proof/preparation and nine Driver memory cases, zero skips;
all eight affected project builds passed with four pre-existing TestGeneration.Test
warnings. Fresh independent repair acceptance and canonical packaging/public
controls remain separate requirements.

## Historical acceptance of the superseded mechanism, 2026-10-20

Fresh independent verification passed 127 TestGeneration, five shared analyzer fingerprint and eight Driver metadata cases with zero skips. All 14 promoted C# files match the frozen source manifest. Six public native r02 controls passed: Size/Char proof 6/6, sibling helpers 10/10, false helper and bad generator/false requirement fail without omission, legacy wire unchanged. Bad generator and false requirement are rejected before execution. Independent quantified-predicate/lemma controls additionally preserve target assertion, loop-invariant, type and postcondition checks while certifying 9/9 generator obligations. The verifier retained an initially overstrict script expectation as an expectation failure; no product change was needed.

Canonical Core/Pipeline/TestGeneration/Driver/launcher cached builds passed. A real canonical Cosyn API + default `dafny` transport control certifies sibling helpers 10/10 and still reports the deliberately false target postcondition. Artifacts: `/workspace/tmp/experiment/pbt-main-hardening-20261020/r02/`, its `independent/` subdirectory, and `canonical-smoke/`; independent report `/workspace/tmp/pbt-main-hardening-20261020/verify-proof-main.md`. An initial six-case controller used invalid absolute request paths; those pre-proof errors remain in the parent experiment directory and are not passing evidence. The root owns requested commits/main pins. No paid provider, image, benchmark or efficacy claim.

## Historical unresolved-reference repair, 2026-10-21

Before the authored-contract refactor, TryResolvedProgramFingerprint
was changed to reject a reference whose Referred target is null through its existing
bounded unsupported-result contract. It does not omit the reference, invent an
identity or accept a partial fingerprint. A tiny legal unused qualified alias
still resolves with complete targets and a full fingerprint. Only a separately
tampered AST with cleared resolution reproduced the pre-fix null reference;
this does not establish an ordinary-source defect or the actual live worker
failure's cause. Request validation also rejects null draft entries before
projection or creation of campaign artifacts.

Source: ContractGeneratorProof.cs::TryResolvedProgramFingerprint and
ContractRuntimeCampaignRunner.cs::Validate. Originating
[repair plan](../plan/2026-10-21-pbt-worker-failure.md). Fresh independent
verification accepted124 proof,9 Driver and24 preparation memory cases, zero
failed/skipped, plus supported full-build evidence and scoped format/diff checks.
Evidence remains local at
/workspace/tmp/pbt-worker-failure-20261021/verification-goal-001.md and its JSON
companion. This is local boundary evidence only; no new proof/runtime/live
stability claim and no deployment to the frozen experiment image.

That custom fingerprint mechanism and its implementation-specific tests have
since been replaced. The exact inherited repair is preserved in the frozen
patch recorded by the current plan; the null-draft request validation remains.
