# Installed draft provenance in runtime campaigns

Status: independently verified, 2026-10-20.
Source: `8e5652221199a2ac4414d225266ef92d62965fd5` plus the three-file owner change.
Originating [plan](../plan/2026-10-20-pbt-installed-draft-evidence.md).

Diagnostic drafts supply unfinished helper bodies. An existing concrete source body takes precedence: `ContractRuntimeSourcePreparation.PrepareAsync` validates every supplied draft's target, syntax, matching marker and signature, then installs a draft only when `NeedsDraft` requires a body. An unused invalid draft remains an error. Source-body implementation requires the host's independent exact-symbol edit authorization; a missing-draft response grants no rights.

`ContractRuntimePreparedSources.InstalledDraftSymbols` now records canonical `FullDafnyName` identities only after actual replacement edits have been queued. The additive init property preserves the record's positional constructor/deconstruction. The campaign runner uses this collection for runtime type-evidence dependencies and callee-violation `Draft` flags. Merely supplying an unused matching draft no longer suppresses evidence or attributes execution to that draft. All other request-draft uses remain unchanged, including request/source hashes and native proof bindings.

Source paths: `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeSourcePreparation.cs`, `Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs`, `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeTypeEvidence.cs`; regression controls in `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs`.

Independent verification reviewed canonical naming through obligation emission and type dependencies, preserved source maps/constructor shape and unchanged fingerprint/trust/certificate/selection paths. Its `make exe` passed with zero warnings/errors, selected memory-only source-preparation tests passed 20/20 without skips, and whitespace/diff checks passed. Owner build additionally reported four warnings in untouched files; sandbox build/test failures and approved successful reruns are retained in the plan. Audit: `/workspace/tmp/pbt-installed-draft-evidence-20261020/verify.md` (local scratch).

This evidence covers preparation and provenance, not a generated native campaign, generator proof or benchmark outcome. No expensive generated-campaign fixture was added or run. The active evaluated experiment retains its immutable pre-change image and frozen package; these development findings are not candidate input.
