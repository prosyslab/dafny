# Unified native Dafny runtime

Status: native source independently verified; parent plans own pin delivery and post-commit runtime metadata
Date: 2026-10-19
Origin: [unification plan](../plan/2026-10-19-unify-dafny.md)
Integration: [toolchain ownership](/workspace/wiki/architecture/dafny-toolchain-ownership.md)

## Composition and compatibility

The common native tree starts from Cosyn `4cd8162e968d8660ee50257671b697b7a4e64c89` and adds the verification-target projection from Dafnyutils `4fb94fc9fecc8209e289148c6347a2c313606e6b`. Existing refs preserve the original histories; the benchmark native checkout can detach at the common commit without rewriting its `expecto` branch. Same-path historical plans/wiki are retained at those commits; they are historical evidence, not current parity receipts.

`Source/DafnyCore/DefinitionAnalysis.cs` composes optional `DefinitionSourceFacts.VerificationTargets` with resolved `DefinitionInfo.BodyVisibility`. The separate partial implementations in `DefinitionAnalysis.VerificationFacts.cs`, `DefinitionAnalysis.BodyVisibility.cs`, and `DefinitionAnalysis.ProofInputs.cs` retain their owners' behavior. `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` exposes `--include-verification-facts` alongside `--include-proof-inputs`. Verification-target inventory is emitted only when requested. Body visibility accompanies resolved definitions; the benchmark's strict independent JSON model must explicitly represent that optional object. Neither Python package imports the other.

Cosyn's trusted-source handling remains in `Source/DafnyTestGeneration/ContractTesting/`; this integration does not change its default or enable trust for benchmark verification. The canonical JSON logger conversion bridge is retained and benchmark normal/empty/mixed-result assertions are added against that API. CommonOptionBag help and five LIT fixture conflict choices retain the canonical resource-statistics cleanup and correct source positions; benchmark differences there are stale comments/padding or wording, not distinct evaluator behavior.

## Evidence and limits

Fresh Core/Driver/TestGeneration/CLI builds and formatting passed. Independent serial class checks passed90 native cases with no skips, including both metadata projections, proof inputs, trigger scopes, logger outcomes, internal exits and trusted sources. Both Python clients accepted the fresh canonical producer on a public synthetic source; the post-commit default-route rebuild/smoke is recorded in parent plans. SDK8.0.131; four known TestGeneration warnings and the general formatter workspace warning remain. Full commands, initial IPC denial, fixture corrections and logs are in the linked plan. Local source parity does not establish existing image parity, benchmark proof success, evaluator score, or provider performance. Docker images must be built through the owners before a new evaluated run; historical/frozen images are unchanged. Maintenance artifacts are under `/workspace/tmp/unify-dafny-20261019/` and are not benchmark inputs.

Existing body visibility conservatively reports `revealsAllFunctions` when retained modern attribute syntax is unresolved in its dependency closure; unification preserves that behavior. The combined precise-closure regression uses existing legacy timeout syntax, and original modern-attribute inventory cases remain covered.

Native optional flags compose in one raw JSON document. The strict consumers request different subsets: Cosyn accepts proof-input metadata and never requests target inventory; Dafnyutils accepts target inventory and never requests proof inputs. Source unification does not make either Python schema a parser for the other caller's unrequested optional fields. The always-emitted body-visibility object is explicitly accepted by both.
