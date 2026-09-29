# Historical inconclusive runtime and query optimization

Status: done (bounded implementation and validation; broader coverage limits remain)

Root authorization and acceptance: [six-case optimization](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).
This is local engine maintenance using public retained requests. Read source and
native evidence before extending scope; keep original contracts, values, limits,
WD and checked equivalence intact. Preserve all pre-existing dirty changes.

## Exact initial changes

| Files/symbols | Change and necessity | Validation |
| --- | --- | --- |
| Source/DafnyTestGeneration/ContractTesting/ContractModelCodec.cs, EscapeCharacter | Replace Unicode-incompatible legacy control escape with mode-independent scalar expression where needed; reuse existing renderer | Native equality and negation retain original values across default/Unicode modes |
| Source/DafnyTestGeneration.Test/ContractCharacterEncodingTests.cs | Dedicated native value-encoding regression controls | NUL/control, escaping, non-BMP, nested containers and WD controls |
| This plan, plan/INDEX.md, wiki/contract-testing.md and wiki/INDEX.md | Record exact engine deltas, validation and boundaries | Root report links, diff check |

Runtime and quantified investigations are read-only until this table names their
exact symbols and validation. No tests/builds concurrent with another native
lane. Root owns codec changes; delegated investigations own no source yet.

## Validation

Cwd `/workspace/cosyn/dafny`, TMPDIR `/workspace/tmp`:
`dotnet build Source/Dafny.sln --no-restore -m:1`;
`dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter
'FullyQualifiedName~ContractCharacterEncodingTests|FullyQualifiedName~ContractClosedClauseTypeTests|FullyQualifiedName~ContractPatternTests|FullyQualifiedName~ContractQueryTests'`.
Run the new focused controls before the fix to reproduce the failure and after
the fix to verify semantics. Root coordinates final makeformat, supported
packaging/transport, fresh independent review, freeze and unchanged reruns.

## Evidence and risks

ContractModelCodec.EscapeCharacter emits `\\uXXXX` for control chars. Runtime
campaigns set UnicodeCharacters=true; retained h13/v2 closed queries7 and9 reject
that syntax. Render exact scalar values without a mode-specific fallback or
altering request content. Rune decoding already rejects malformed surrogate
input. Native tests must cover default legacy options too.

## Progress

Ready initial scope. Source diagnosis of runtime and residual quantifiers runs
alongside root implementation; findings will amend this record before edits.

### Authorized parallel implementation slices

| Exact files/symbols | Owner and proposed change | Validation |
| --- | --- | --- |
| ContractCallableSelector.DescribeFunction/FunctionResultName; ContractRuntimeObligationTransformer descriptor creation; dedicated native tests | Runtime owner: reuse collision-safe result family within one immutable transformation; remove evidenced repeated structural preparation/serialization work only with exact identities | Identical generated source and observations; name collisions; runtime recording flush/cancellation controls |
| ContractSolver.ReduceConcreteAssertion/IsConcreteValue; PartialEvaluatorEngine concrete-value helper; related Core/query tests | Quantifier owner: admit already-supported resolved map/set/multiset/bitvector concrete values consistently | Native WD/positive/negative structured bindings and retained h13 query |
| PartialEvaluatorVisitor existential handlers, QuantifierBounds helpers where necessary; dedicated reducer/native query tests | Quantifier owner: bounded exact witness decomposition/substitution, only after minimal experiment; preserve residuals and checked gates | Dependent sequence/product-datatype true/false/unsupported cases under shared limits |
| ContractStubRuntime encoding helpers and recording tests if profiling establishes exact repeated work | Runtime owner: request-scoped structural caches/reuse without dropping records, flushes or dependency checks | Exact complete trace equality, separate inputs/state invalidation and native Driver controls |

Each delegated owner must write a dedicated child plan before its edits and send
the path to root for index registration. Root alone updates shared indexes/wiki.
No concurrent native builds/tests. No hardcoded historical witness, guessed-domain
negative verdict or contract-verification skip is authorized.

Implementation child plans: [runtime structural reuse](2026-09-29-runtime-structural-reuse.md)
and [checked witness reduction](2026-09-29-checked-witness-reduction.md).
Codec red tests run in tmux `pbt-inconclusive-codec-red-20260929`; the sandbox
blocks the local tmux socket, so the approved local execution path is used.
Logs/exits: `/workspace/tmp/experiment/pbt-inconclusive-20260929/codec-before.*`.

The first native encoding run fails13/17: seven Unicode parse failures and six
incorrect constant reductions. Source diagnosis shows the PE conversion path
passes escaped CharLiteralExpr text to ConstantFolder, which treats its first
UTF-16 code unit as the character. Extend root's codec slice to
`PartialEvaluatorEngine.TryEvaluateContractConcreteConversion`: use the existing
decoded BMP character helper for char-to-int/bitvector, retain supplementary
conversions as residual, and recognize exact non-surrogate BMP int-to-char
conversions for mode-independent control literals. Original WD and assertions
remain mandatory. Existing native codec tests reproduce both problems; keep the
failed log. Quantifier owner does not edit this method.

Codec green native suite passes137/137 in36.927s, including17 dedicated encoding
controls,12 captured-type controls and existing query/pattern cases. Exit0, log
`codec-after.log`; no original values/contracts/options changed. The int-to-char
normalization admits only universally valid non-surrogate BMP scalars; larger
conversions remain residual. Quantifier implementation now holds the native lane.

Root adds [finite-prefix counterexamples](2026-09-29-runtime-prefix-counterexamples.md)
after observing original false loop invariants discarded solely because the
subsequent process times out. The child plan preserves all prior validation gates,
raw traces, and distinguishes prefix validity from normal completion.

Second pass: [scalar clause dependencies](2026-09-29-scalar-clause-dependencies.md) certifies exact original dependency closures; checked-witness plan adds constructor injectivity. Frozenv3 six-case results remain intact and v4 gets separate validation/freeze/reruns under the root plan.

## Integrated closure, 2026-09-29

Root completed the combined workflow on recorded source hashes at engine
HEAD060d5ad532f67d5367450689225274fb0a0243e7 plus preserved dirty changes.
V3 independent Driver32/Core62/Query83 controls and final v4 independent
Core33/Query21/Driver14 controls passed in fresh contexts. These overlap; they
are not an additive unique-test count. Final makeformat changed no source bytes;
supported `make build-dafny` passed0warnings/0errors and transport4/4 passed.
Frozen v4 manifest1628files SHA256
f7f02a2e14e08e45fb5696da3ad6fbf0d6e1f58ef815a65d6a807db9c34bd402.

All six unchanged historical campaigns finished, preserving original requests,
seeds and budgets. h13 reports two validated finite-prefix violating samples;
representative ordinal1 replays with exact violation equality, exit0 in60.352s.
The other cases retain documented proof/runtime/coverage limits; this bounded
implementation plan does not claim all historical cases or broader M1/M2 solved.
Root orchestration plan tracks next work. Failed attempts, first reviewer quota
interruption, independent replacement review, source patches and native baseline
comparison remain explicit in the [report](../../../pbt-draft-exp/inconclusive-followup.md)
and [root plan](../../../plan/2026-09-29-pbt-inconclusive-optimization.md).
Reusable findings: [contract-testing knowledge](../wiki/contract-testing.md#exact-reduction-and-finite-prefix-counterexamples-2026-09-29).
No package additions, paid runs, original specification edits or commits.
