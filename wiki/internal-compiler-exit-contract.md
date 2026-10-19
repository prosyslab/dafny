# Native internal compiler exit contract

Status: accepted; local native build and fresh independent producer checks passed.
Verified: 2026-10-14, dirty native tree based on
`dce5a96612b6516c5b180bb215d6eb3e3b430d5a`.
Originating plan: [internal compiler exit contract](../plan/2026-10-14-internal-compiler-exit-contract.md).

## Contract

The new CLI returns `ExitValue.INTERNAL_ERROR` (6) for an unexpected exception
that reaches its existing System.CommandLine exception middleware. It retains
the native exception diagnostic. `CliCompilation` also preserves the existing
typed `InternalCompilationException` event and prioritizes that state over
ordinary diagnostics when reporting an exit value. Existing exit values 0–5
retain their definitions. No diagnostic message wording is used for classification.

A failed measurement mutation sends terminal `OnError` and immediately stops.
It does not start another seed or emit `OnCompleted` afterward, even when the
observer accepts the error without throwing. This fixes the scheduling contract
independently of how observers report errors.

## Evidence and sources

- `Source/DafnyDriver/Legacy/DafnyBackwardsCompatibleCli.cs`: numeric enum contract.
- `Source/DafnyDriver/DafnyNewCli.cs`: production parser middleware and internal
  parser factory used by injected-error tests.
- `Source/DafnyDriver/CliCompilation.cs`: typed event and exit priority.
- `Source/DafnyDriver/Commands/MeasureComplexityCommand.cs`: terminal mutation path.
- `Source/DafnyDriver.Test/InternalErrorExitTests.cs`: 11 native cases, including
  an injected verifier failure and actual generic candidate controls in both
  command modes.

From the native root, `dotnet test Source/DafnyDriver.Test --no-restore --filter
FullyQualifiedName~InternalErrorExitTests` runs the focused checks. Local solution
build, scoped formatting and the three trigger-scope regressions also passed.
Logs and generic CLI source/output records are available in this workspace at
`/workspace/tmp/dafny-internal-exit-contract/`; they are not repository artifacts.

## Compatibility and limits

Old binaries can still return 1 for an internal exception; historical receipts
remain ambiguous and must not be relabeled using this new contract. Consumers
need the rebuilt native binary and an explicit code-6 infrastructure mapping.
The old verification JSON schema reports solver obligations, not this compiler
exception category; adding text matching would not repair its type information.

Process-level aborts can still have signal-derived exit statuses; this change
does not intercept every background/runtime crash. Such exits remain operational
failures for consumers. Local checks are not benchmark results or evidence of a
successful resumed experiment. Image admission, downstream propagation and fresh
independent acceptance are tracked by the parent plan.

Fresh independent review confirmed production middleware/typed-event/mutation
behavior, driver11/11 and trigger3/3, all existing exit0–5controls, current built
driver identity and clean formatting/hygiene. Benchmark-native propagation and
Cosyn consumer/image acceptance are separate; old-image receipts stay immutable.

2026-10-19 maintenance correction: the eight `CandidateOutcomesKeepTheirExitCodes` native CLI theory cases were removed because they created GUID scratch directories and wrote source/log files. Their earlier receipts are historical; current retained development controls use in-memory boundaries. See the [commit maintenance plan](../plan/2026-10-19-commit-native-working-trees.md).
