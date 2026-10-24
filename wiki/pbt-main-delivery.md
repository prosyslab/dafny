# Native PBT delivery and validation boundaries

Status: reviewed source delivery
Verified: 2026-10-25
Origin: [delivery plan](../plan/2026-10-25-pbt-reviewed-main-delivery.md)

The native tool supports checking a selected helper without requiring bodies
for unrelated executable declarations. Runtime preparation follows the selected
execution/proof dependencies, preserves iterator isolation and original contracts,
and retains meaningful missing-draft or unsupported results. Output captures use
snapshots that generated C# can safely reference.

`test-contracts --screen-contract` inspects or screens an explicit typed input
against a body-independent helper contract. Requests and results bind source,
declaration, contract, preparation, native producer and verifier options.
The screen preparation rejects trust-affecting verifier options before parsing.
Checked bounded existential witnesses support realizability queries; a timeout
or undecided query remains undecided. Screening does not prove an implementation
correct or authorize changing the original target specification.

Generator admission retains both obligations: prove the executable generator
and its helper closure establish every authored postcondition, then separately
prove those postconditions imply every original target precondition. Existing
analyzer fingerprints and exact proof inputs guard the scope. Unsupported,
failed or incomplete proof cannot omit runtime entry checks. This delivery does
not synthesize a generator from arbitrary preconditions or provide a complete
frontend dispatcher; the unused preparation DTO foundation remains uncommitted.

The supervised runtime worker receives the configured `--verification-seed`.
Sampling seed and verification seed are different controls. The native CLI
default remains zero; the controlled image check separately used verifier seed
42 and observed the actual worker argument and ordinary proof completion.
That observation does not directly attest an SMT solver's effective option.

Current delivered sources match the detached, compiled validation checkout for
all affected leaves except the default-on Driver.Test asset-copy guard. Existing
matching-source evidence includes selected-draft 26/26, related runtime 27/27,
Core witness 209/209 and screen-service 36/36 checks. The finite image control
also reports eleven registered callbacks, generator proof completion, candidate
access isolation and cleanup. Source parity and those controlled results are
distinct from running a build in this canonical checkout.

Canonical build preparation stopped before any build because an existing
Boogie dependency has two hard links. No canonical binary was overwritten and
no canonical build/test pass is claimed. Future canonical builds must resolve
the owned output boundary first. The source commits remain on `expecto` and are
ready for pinning by Cosyn/integration main. No paid experiment or csplit improvement is
established by this delivery.

Relevant sources: `ContractRuntimeSelectedDraftPreparation`,
`ContractRuntimeCampaignRunner`, `ContractRuntimeObligationTransformer`,
`ContractScreenSourcePreparation`, `ContractScreenService`, `ContractSolver`,
`ContractGeneratorProof` and `TestContractsCommand`.
