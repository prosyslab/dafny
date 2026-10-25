# Generator proof value domain

Status: independently accepted local source and bounded memory validation
Verified date/revision: 2026-10-25 on native
`a88ff6bc3af1b490b032cc70b9632cd363dd64f0` plus this task's changes, retained by
the focused native commit authorized in the originating plan.
Originating [native plan](../plan/2026-10-25-pbt-supported-value-domains.md) and
[Cosyn plan](../../plan/2026-10-25-pbt-supported-value-domains.md).

## Applicability and invariant

`ContractGeneratorProof.SupportsRequiredPostconditions` governs automatic generator
postconditions and ordinary direct generator proof. It is separate from runtime
generation and the body-independent child contract screen. The proof target must
remain concrete, nongeneric, static and value-only.

Supported values recursively include int/bool/char/bitvectors, sequences, finite
sets, multisets, finite maps, inductive datatypes and supported subset/newtype
wrappers. Map keys and values both need supported types. Arrays/references hidden
inside a collection or datatype are outside this capability, as are infinite
collections, real/ordinal/function values and codatatypes. A supported type is only
admission to the ordinary proof, not evidence that a generated value is valid.

An empty original `requires` list contributes no additional generator
postconditions. It still requires ordinary generator correctness, declared-type
validity, authored ensures, checked helpers and complete native check coverage.
No vacuous premise may mint a certificate from zero checks. The existing public
`entryRequiresOmitted` flag is certificate-driven, including the vacuous empty-list
case; it confers no implementation verification and does not remove type checks.

`DatatypeDestructor` and `DatatypeDiscriminator` derive from `Field`, but access
immutable values rather than heap cells. Finite-map `Keys`/`Values`/`Items` are also
immutable projections. Classify these precise resolved AST operations consistently
in direct requirements and reachable pure-function bodies. Do not treat every
read-only class field or every `SpecialField` as a value operation: arrays and
receiver state retain their separate restrictions.

Map shape recognition uses native `Type.AsMapType`, which expands a subset wrapper;
the separate `SupportedValueType` guard checks the original constrained type. A
subset-of-map therefore retains its refinement well-formedness and native generator
type obligations while allowing its immutable map projections. Shape normalization
alone never admits reference-valued keys/ranges or infinite maps.

All original contract clauses, exact generator/module/source identities, source
hashes, analyzer bindings, dependency/trust audits and native correctness coverage
remain required. Failed/unsupported/incomplete/timed-out proofs retain runtime entry
checks. Public proof metadata cannot supply the internal certificate.

## Sources and evidence

- `Source/DafnyTestGeneration/ContractTesting/ContractGeneratorProof.cs`:
  `SupportedSelectedGoal`, `SupportedValueType`, `TargetRequiresAreValueOnly`,
  `RequiredPostconditions`, `ProofScopes`, `ContractGeneratorProofCoverage`.
- Existing runtime support: `ContractHarnessBuilder.SupportedType`,
  `ContractRuntimeObligationTransformer.CompilableType`/membership checks,
  `ContractRuntimeInstrumentation`, `ContractModelCodec` and library observations.
- Native AST definitions: `Source/DafnyCore/AST/Members/SpecialField.cs` and
  `Source/DafnyCore/AST/SystemModuleManager.cs`.
- `Source/DafnyTestGeneration.Test/ContractGeneratorValueDomainTests.cs` and the
  existing proof/authoring owners: bounded in-memory source/AST/fake-proof checks.

The recent bounded csplit projection recorded five no-`requires` generator proof
rejections. Its seven runtime `unsupported` results instead concern already repaired
output capture and invalid authored generator expressions; they are not seven
instances of this type-domain fix. Collection and selector restrictions were found
by comparing current code paths, without claiming their experimental prevalence.
Retained heap/instance and trust-attribute rejections remain intentional boundaries.

Final source hashes are production
`f48c9c95626d22718f2dfebd8c5e3267673705dc90f9bd6dda33954bf0afce6e` and test
`840747d96aec891de29c5c8cb724f53bee5655c57ebf3dd4f9923af68f1215cd`.
The separate serial assembly build and targeted native whitespace checks passed.
Matching-source owner selection passed 127 memory cases; fresh independent selection
passed 69 overlapping cases, both with zero failures/skips. Source/assembly timing,
pins, exact commands and earlier failed attempts are recorded in the linked plans.
Python gates passed 1156 units/126 integrations, lint and configured full-source
typing; default typing discovery remains failed.

Memory checks do not establish real solver success, generated sample behavior,
installed-image delivery, model adoption or benchmark improvement. Full Driver/
campaign fixtures with temporary-directory and generated-compilation workloads were
excluded. There were no provider calls, package changes or image changes.
