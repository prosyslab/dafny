# C# sequence construction and output-parameter capture

Status: generation3 independently accepted 2026-10-12; source fix and local compiler available
Date: 2026-10-12
Compiler revision: c6e96a59f679bb71e565a27ec1bf93ac68f0803d plus preserved unrelated local changes
Originating plan: [C# output capture](../plan/2026-10-12-csharp-out-capture.md)

## Confirmed baseline mechanism

The C# backend's EmitSeqConstructionExpr optimizes seq(N, lambda) into an array
loop inside an immediately invoked System.Func. Unlike ordinary lambda emission,
this path omits free-variable capture. A Dafny method with multiple non-ghost
outputs becomes a C# method with out parameters, which cannot be referenced from
that generated lambda. The failure can occur in both N and the initializer body.

The small source below isolates the public weekly paste-r01 ObserveInputs shape.
It passed native verification (2 verified/0 errors) but its generated C# failed
with two CS1628 diagnostics, one at each observations reference.

```dafny
method Project() returns (observations: seq<int>, entries: seq<int>)
  ensures observations == [4, 7]
  ensures entries == [5, 8]
{
  observations := [4, 7];
  entries := seq(|observations|,
    j requires 0 <= j < |observations| => observations[j] + 1);
}
```

The relevant generated code is structurally:

```csharp
entries = ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
  BigInteger dim = new BigInteger(observations.Count); // CS1628
  // ... allocation and index loop ...
  arr[(int)j] = observations.Select(j) + BigInteger.One; // CS1628
  return Dafny.Sequence<BigInteger>.FromArray(arr);
}))();
```

## Reproduction and evidence

Artifacts are local under /workspace/tmp/dafny-csharp-out-capture/; no original
benchmark proof or evaluator was executed. Commands from that directory:

```sh
/workspace/dafnyutils/dafny/Binaries/Dafny verify sequence-out.dfy --standard-libraries:false --verification-time-limit:10
/workspace/dafnyutils/dafny/Binaries/Dafny build sequence-out.dfy --target:cs --standard-libraries:false --no-verify --spill-translation --output:before/sequence-out
dotnet build before/sequence-out.csproj --configfile NuGet.Config -p:NuGetAudit=false
```

The middle command emits the C# but its initial automatic restore was blocked
by network permission; that failed attempt is preserved separately. The final
command restores only already-cached dependencies using a task-local config
with package sources cleared, then reaches and confirms CS1628. The no-verify
flag is solely a backend isolation control; the separate first command verifies
the source. No dependency additions or machine-wide configuration changes.

Source and generated files: sequence-out.dfy and before/sequence-out.cs.
Logs: before-verify.log, before-build.log and before-offline-build.log.
Baseline and preservation identities: baseline.json. Original public final
diagnostic and source snapshot remain in the authorized weekly trial artifacts;
the reusable reproduction above contains no benchmark task contracts or answers.

## Correction and limits

The accepted C#-only correction captures free variables at each original
expression evaluation point. One variable uses an existing unary wrapper; two
or more use one native C# tuple argument and fresh deconstructed BoundVars,
avoiding a System.Func arity limit. Enclosing LetExpr/MatchExpr/NestedMatchExpr
with optimized sequence descendants are captured before shared lowering creates
lambdas. This prevents statement-prelude hoisting under repeated loop guards.
The original optimized array construction helper is unchanged.

Implementation is in CsharpCodeGenerator.cs: EmitExpr,
CaptureSequenceConstructionVariables and EmitSeqConstructionExpr. Persistent
regression is comp/csharpOutCapture.dfy with its .dfy.expect companion. The
native regression verifies27obligations/0errors; its generated assembly exits0
and matches25expected lines. Independent acceptance covers nine proof/compile/
runtime programs and four official multi-backend-runner fixtures selected for
C#: the new regression, Calls, 6_Calls-VariableCapture and Comprehensions. Each
official fixture exercises legacy/refresh resolution and runtime source/DLL
inclusion. A deliberately wrong copied expectation fails in both runtime modes,
confirming actual execution/comparison. Independent receipt:
`/workspace/tmp/dafny-csharp-out-capture/verification/verification-result.json`,
SHA-25628ac0fcaf07525476effefd20ed7cdac3843542258ee1adfb1b07953a8a33917.

The solution build succeeds with0errors and3warnings in unchanged test-generation
files. Source SHA-256f8094051b7694ec455954feb91d196610472d75f7d819f1fa5b1a62739625e01;
core SHA-256dd85c62ac0ecc0067144586abd8d2a2d35d28147f5c95f7f5dd26191e60cc9e4.
Run the accepted local compiler at
`/workspace/dafnyutils/dafny/Binaries/Dafny`; `/usr/bin/dafny` still resolves to
the separate Cosyn tree. No tool-link, running evaluation or deployment changed.
The reviewable code/test patch is `/workspace/tmp/dafny-csharp-out-capture/fix.patch`.

### Rejected approaches preserved as evidence

An initial whole-expression CaptureFreeVariables correction compiled the original
reproduction, but independent testing rejected it: a previously valid17-input
sequence body generated a System.Func with18generic type arguments and failed
CS0305. Preserve this rejected generation; do not apply this approach unqualified.

The rejected second generation reused existing identifier-to-local copy emission
in the C# optimized helper. Both length and body were emitted with inLetExprBody=true;
body emission uses the typed EmitArrayUpdate writer overload followed by
EmitExpr because its convenience Expression overload hardcodesfalse. This keeps
the zero-argument optimized lambda and avoids adding a function-arity limit.
Independent verification then rejected this replacement too: copyInstrWriters
places temporaries before a while statement, so a sequence in its guard sees
stale values on later evaluations. A baseline-valid ordinary-local loop verified
and built under both versions but changed from2iterations to3and an expectation
failure. Thus statement-level copying is not sufficient for reevaluated expressions.

The accepted third generation above replaces both rejected approaches. Tests
cover length/body evaluation, reassignment, nested scopes,17ordinary inputs,
more-than16outputs, direct/let/match output/local guards, short-circuiting,
zero-length initialization, generics, functions/constants and delayed lambdas.

This finding establishes a specific C# sequence-constructor bug. It does not
explain every INF marker, Boogie trigger failure or workflow asymmetry. Original
full-candidate proof/runtime behavior and deployment of a replacement toolchain
remain outside this fix's acceptance scope.

## Commit packaging revalidation (2026-10-13)
The user authorized committing the unchanged accepted generation3 backend fix and regression. Current source/fixture/expect identities match the existing acceptance bindings. Fresh checks pass27native proof obligations, scoped C#/Dafny formatting and substantive official C# runner verification/compile/runtime/expected-output comparisons in isolated scratch. The checked runtime uses core SHA-256`dd85c62ac0ecc0067144586abd8d2a2d35d28147f5c95f7f5dd26191e60cc9e4`. The owning root Binaries/DafnyCore.dll currently differs, so it must not be assumed to contain this fix. No compiler was globally deployed. Evidence: /workspace/tmp/commit-codegenerator/verify-direct-runner.log; applicability and broader scope limits above remain unchanged. See the originating plan for commit packaging scope and command details.
