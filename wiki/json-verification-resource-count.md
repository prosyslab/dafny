# JSON verification resource-count aggregation

Status: superseded for active modern reports on 2026-10-15; historical evidence retained.
Verified: 2026-10-15, dirty native tree based on
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a`.
Originating plan: [preserve large JSON verification resource totals](../plan/2026-10-15-json-verification-resource-overflow.md).

## Supersession

The active modern JSON verification logger no longer emits scope or per-VC
resource counts under the authorized reporting-removal plan. Its current schema
retains scope/VC outcomes, duration strings, random seeds, assertions and proof
dependencies. The overflow repair and all receipts below remain accurate for the
earlier schema and are preserved as historical maintenance evidence; they no
longer impose an active aggregation requirement. The legacy backwards-compatible
JSON/XML path and internal solver resource counters are outside that removal.

Current plan: [remove verification resource statistics](../plan/2026-10-15-remove-verification-resource-statistics.md).

## Invariant

`VerificationRunResult.ResourceCount` is an `int`, but a verification scope can
contain several individually valid counts whose mathematical total exceeds
`Int32.MaxValue`. `JsonVerificationLogger.SerializeVerificationResult` must widen
each count before LINQ chooses its `Sum` overload. The scope total is therefore a
`long` JSON number; each `vcResults[].resourceCount` stays its original `int`
number. Outcome merging and every other JSON field are unchanged.

The relevant expression is:

```csharp
results.Sum(r => (long)r.Result.ResourceCount)
```

Casting the completed sum would be too late because
`Enumerable.Sum(IEnumerable<int>)` performs checked 32-bit addition. Catching,
saturating, wrapping or stringifying the value would lose the exact reporting
contract.

## Evidence

`Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs` constructs public
synthetic verification results and observes `LogScopeResults` plus `Flush`. With
the old selector, counts `Int32.MaxValue` and `1` reproduced
`System.OverflowException` from `Enumerable.Sum`; the normal mixed-outcome control
passed. With the widened selector, both cases pass, the scope value is the numeric
`2147483648`, the two per-VC counts remain `2147483647` and `1`, and the normal
scope retains `Errors`, `Valid`/`Invalid`, and the existing field sets.

The focused 2-test run and native solution build pass, with zero build warnings
or errors. Scoped whitespace verification passes. The full 296-test driver run
includes both new tests as passes but has three persistent failures in two
pre-existing contract-runtime campaigns. One isolated rerun per failing method
reproduced those classifications. The campaign harness calls
`ContractRuntimeCampaignRunner.RunAsync` directly with default `DafnyOptions`;
that runner does not construct `VerificationResultLogger` or
`JsonVerificationLogger`. JSON logger construction occurs in
`VerifyCommand.LogVerificationResults`, which these campaign tests do not call.
This source evidence supports treating the failures as outside the changed logger
path, but fresh independent review owns the acceptance judgment.

## Applicability and limits

This invariant applies only to the new CLI JSON verification scope total in
`Source/DafnyDriver/JsonVerificationLogger.cs`. It does not widen the per-VC type,
change resource accounting or alter verification. Other existing integer totals,
including text logging and summary statistics, were not part of this repair and
have not been claimed safe for the same aggregate range. Local tests do not prove
a Dafny program, benchmark result, image admission or resumed experiment success.

## Clean independent targeted acceptance — 2026-10-15

A fresh source-only verifier accepts the targeted change after2real logger tests,
portable-PDB source binding, and direct-csc public API probes producing exact
numeric totals4294967296and6442450941with original per-VC/outcome/runtime/schema
data. It independently traces ContractRuntime campaign compile/proof paths and
finds they bypass this aggregation. No restore/network/provider call or native
file edit occurred. Evidence:
`/workspace/tmp/native-json-overflow-harness-clean-independent/report.md`.

The wider full Driver criterion remains unmet(implementation reports293/296with
3reproduced campaign failures); the linked plan remains in-progress. The first
verifier's report is qualified by plan over-reading and unintended NuGet audit
traffic and is not the clean acceptance gate. Image/proof/benchmark results stay
separate from this targeted serializer contract.
