# Validate finite-prefix invariant counterexamples

Status: done (bounded implementation and validation; broader coverage limits remain)

Parent: [inconclusive optimization](2026-09-29-inconclusive-runtime-optimization.md).
User authorizes continued optimization toward deciding existing inconclusive
cases. This is engine development against public retained inputs. No request,
specification, benchmark scoring, timeout or sample policy change.

## Evidence and acceptance

Retained h13/v2 sample1 records original loop invariant false at iteration1 and
then times out after further iterations. The current runner collects the failure
but discards it because `complete` is absent. A finite trace through a violated
loop invariant is enough if original entry validity and every prior called
contract are validated. Requiring subsequent termination hides a real violation.

Only select a prefix ending at a recognized compiled `check` with `passed=false`
for `LoopInvariantEntry` or `LoopInvariantMaintenance`. Keep every earlier record;
ignore later evidence for validation. Native/compiled validation of that prefix
must pass all existing type, premise, entry and callee gates. Do not accept an
unreturned target postcondition, unchecked closed clause, failed callee or invalid
entry. Preserve whole original raw traces and original process/timeout provenance.
Classify a validated finite-prefix goal violation as a valid violating sample,
without claiming normal target completion. Emit a separate prefix certificate
with endpoint identity, record count and original completion/timeout flags.

## Changes and validation

| File/symbol | Change / why | Validation |
| --- | --- | --- |
| Source/DafnyDriver/ContractTesting/ContractRuntimeCampaignRunner.cs | Select an exact prefix before evidence collection; retain original termination metadata; allow proven prefix classification and write explicit receipt | Native loop failure then nontermination; invalid entry, bad/unchecked callee remain excluded |
| Source/DafnyDriver.Test/ContractRuntimePrefixTests.cs | Behavioral native controls of incomplete execution and dependency gates | Focused Driver filter, no assertion-mirroring tests |
| This plan, parent engine plan/index, contract-testing wiki/index | Record semantic boundary and evidence | Independent review, root report |

Cwd `/workspace/cosyn/dafny`, workspace TMPDIR. Root coordinates serial lane:
`dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter
'FullyQualifiedName~ContractRuntimePrefixTests|FullyQualifiedName~ContractRuntimeCheckTests'`.
First run dedicated controls against existing runner to establish failure; then
rerun after correction through fresh independent verification. Its Driver scope
includes prefix + recording and existing invariant entry/maintenance, break, weak
invariant, call/entry precondition, draft/callee, timeout and population controls;
Core reducer/witness and TestGeneration query/witness/character checks run serially
in the same independent lane. Avoid a redundant root green run. Final supported build/transport and six exact requests
are coordinated by root. No paid provider, packages, commits or trace rewriting.

## Risks

Suffix observations must not supply type/dependency evidence to a prefix. Record
the first malformed record position: only a complete prefix ending before it is
eligible. Missing prefix inputs and captures remain rejected. Only known
compiled goal loop checks qualify; runtime helper failure is a callee result.
Statistics must explicitly identify prefix completion, not report a normal
terminating execution. Source hashes and the original raw record count are retained.

## Progress

Ready scope; root owns this slice and does not change runtime instrumentation or
the quantifier owner's files. New native checks wait for the serial lane.

Root red: `prefix-before.sh` in tmux `pbt-prefix-before-20260929`, exit1,
4/6 passed and the two expected missing-prefix cases failed. Complete raw log
retained under the parent experiment directory. Selection now records first
malformed record position, builds prefix-only input/evidence/captures, requires
known compiled original invariant and all input names, no prior runtime error,
one initial capture and all original entry/callee gates. Certificate preserves
original raw trace hash/count/termination flags. No normal completion is inserted.

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
