# Fix C# capture of method output parameters

Status: done (2026-10-13 authorized commit packaging verified)
Date: 2026-10-12
Owner: Dafny compiler C# backend
Parent plan: [Integration coordination](../../../plan/2026-10-12-dafny-csharp-out-capture.md)
Knowledge: [C# sequence construction output capture](../wiki/csharp-out-capture.md)

## Objective and observable acceptance

Investigate CS1628 in weekly Topdown paste-r01's generated C# observations
references. Recover the relevant public source shape, demonstrate a minimal
valid Dafny source whose baseline C# compilation fails, identify the responsible
compiler emitter and implement a minimal semantic-preserving correction.
Regression must compile and execute expected results, and pass native proof when
applicable. A fresh independent verifier checks the implementation and meaningful
regressions from current requirements/source, without implementation conclusions.

## Non-goals and evidence

No benchmark/candidate/specification/evaluator/scoring/harness/other backend
changes unless source investigation requires a shared emitter correction and
the plan is amended first. No installs, paid calls, commits, binary deployment,
tool-link changes or Site publishing. Existing generated files cannot be edited.
HEAD c6e96a59f679bb71e565a27ec1bf93ac68f0803d, preexisting DefinitionAnalysis files
and declaration regression dirty; preserve them. Existing free-variable capture
helpers in SinglePassCodeGenerator and CsharpCodeGenerator are the first reuse
targets. Read local AGENTS.md, CLAUDE.md, Makefile and .editorconfig before edits.
Public historical evidence is only the exact paste-r01 agent_artifacts source,
progress and final public logs. Toy inputs live under /workspace/tmp; do not run
the original benchmark or inspect private evaluator/runner/reference material.

## Planned changes

| Exact files/symbols | Change/how/why | Unmet without it | Validation |
| --- | --- | --- | --- |
| plan/2026-10-12-csharp-out-capture.md and plan/INDEX.md | Evidence/progress/results | Unreviewable scope | Links/status |
| Source/DafnyCore/Backends/CSharp/CsharpCodeGenerator.cs EmitExpr, EmitSeqConstructionExpr and private expression-local capture helper | Reuse free-variable substitution plus arity-safe value capture at the original evaluation point; intercept enclosing let/match lowering | CS1628, arity or repeated-evaluation failures persist | Generated C#, native verify, compile/runtime and baseline compatibility controls |
| Source/IntegrationTests/TestFiles/LitTests/LitTest/comp/csharpOutCapture.dfy and .expect | Minimal confirmed construct plus reassignment/aliasing/control scenarios, following existing Lit conventions | Future regression undetected | make test name=comp/csharpOutCapture.dfy |
| wiki/csharp-out-capture.md and wiki/INDEX.md | Verified mechanism, scope and reproduction | Durable mechanism lost | Source/log-backed fresh review |
| /workspace/tmp/dafny-csharp-out-capture/ | Reproducer, logs, before/after identities/audits | No traceability | Fingerprints, independent reproduction |

## Validation commands and scope

From this repo root, existing SDK8.0.131 (global.json8.0.111 latestFeature):
dotnet build Source/Dafny.sln --no-restore; targeted make test name=comp/csharpOutCapture.dfy
and actual neighboring capture regressions selected after inspection. Existing
dependencies only, report missing prerequisites. Run native verify on the small
valid source with bounded solver time, then C# build/run; backend-only --no-verify
controls do not replace proof evidence. Use owning Binaries/Dafny explicitly,
not /usr/bin/dafny which points at the other tree. Run C# whitespace formatting
for touched files using local make format command with include narrowing if
supported; format new Dafny file using local formatter. Do not bulk rewrite dirty
unrelated code or generated files. Record actual commands/revisions/outcomes and
proof/compile/runtime scope independently. Root Python suites are inapplicable.

## Risks and required approvals

Copying parameters must preserve expression evaluation, snapshot timing, datatype
and collection semantics. Regression needs output reassignment and nested source
forms when relevant, not merely text matching. Dependencies/tool installs or
different backend scope require approval/amendment before action. User already
authorized this debugging/fix; local reversible work needs no further approval.

## Results and closure

The first source-derived toy passes native proof (2 verified/0 errors). Dafny
build emitted its C# but the generated project's restore contacted NuGet and was
denied before compilation. Use task-local NuGet.Config with package sources
cleared and NuGet audit disabled, relying only on existing cached dependencies;
this adds no packages and changes no compiler/benchmark behavior. Retain that
failed attempt separately, then build the same generated project offline to
confirm compiler diagnostics. Apply the same config to focused tests as needed.
Baseline offline build now fails with precisely two CS1628 diagnostics for
observations, in sequence length and initializer body. The original public
ObserveInputs helper has two non-ghost outputs and uses seq(|observations|,
j => observations[j].entry), so the small input preserves the responsible shape.
The C# optimized sequence construction emits an immediately invoked lambda and
bypasses ordinary free-variable capture. Implement only EmitSeqConstructionExpr's
LambdaExpr branch: use existing CaptureFreeVariables on the full sequence
expression, substitute it and retain the current optimized loop. Merely changing
inLetExprBody is insufficient because EmitArrayUpdate resets it for the body.
No shared-emitter or adjacent nested-match changes are planned.

Implementation agent owns only the C# file and comp/csharpOutCapture.dfy plus
its actual Lit expectation companion comp/csharpOutCapture.dfy.expect (the
earlier .expect shorthand denotes this filename). Regression cases separately
exercise length/body/both, snapshot timing and justified nested/control forms.
Focused C# tests use DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS=cs; neighbor coverage
is comp/Calls.dfy, comp/firstSteps/6_Calls-VariableCapture.dfy and comp/Comprehensions.dfy
as justified after focused regression. Whole candidate/full benchmark remains
excluded. No packages are added; existing cached dependency restoration is only
for these standalone generated projects.
Keep artifacts outside plan/wiki; audit recursively
before close. No full original candidate proof or experiment-success claim.

### Implementation progress

The lambda-only sequence branch now captures/substitutes the full expression
before invoking the unchanged optimized emitter. Added eight realistic scenarios:
length-only, body-only, datatype projection, self-reassignment, nested index
scope, let-expression body, index shadowing and nonliteral function initializer.
The expanded test's first native proof failed only on a nested finite sequence
equality; two explicit row assertions supplied intermediate facts without
changing its contract. Native verification then passed9verified/0errors with a
20-second limit. Keep both attempts in implementation/verify-baseline.log and
verify-regression.log. New Dafny formatting completed; scoped C# formatting,
solution build and native C# Lit execution/independent acceptance remain pending.

### Compatibility acceptance addition

Fresh independent verification supplied a valid17-input sequence-constructor
control: native2verified/0errors and baseline C# compile/run [153]. The initial
whole-expression beta-redex capture can introduce a System.Func arity limit where
the previous zero-argument optimized lambda had none. Include this baseline
success as mandatory before/after acceptance. Also inspect evaluation-order,
generic/delayed-lambda and zero-length controls from independent source tests.
If patched failure reproduces, amend this plan with a narrow arity-safe C# value
capture mechanism before changing the implementation approach; do not drop the
control or alter general compilation behavior/specifications to obtain a pass.

### Local build environment

The initial solution --no-restore build failed without diagnostics. A serial,
build-server-disabled diagnostic retry identified the Java runtime Gradle wrapper
trying to create its lock under the existing /home/vscode/.gradle cache, which is
read-only in the sandbox. Resolve through an approved local-build escalation for
existing runtime/cache access, or task-local reuse of existing cached artifacts;
no new dependencies/downloads and no benchmark or compiler check bypasses.
Record the rejected/failed attempts and actual successful build command distinctly.

### Required arity-safe approach correction

Authorized serial solution build succeeded (17.41s,0warnings/0errors). Fresh
verification confirmed first-generation original-case compilation/runtime success,
but the mandatory17-input control failed with CS0305: whole-expression capture
created a System.Func with18type arguments. Baseline identical source verifies
2/0, compiles and prints[153]. Preserve generation1 as rejected evidence.

Replace only the task's initial LambdaExpr branch edits with a C#-private helper
correction in EmitSeqConstructionExprFromLambda. Reuse the existing identifier
value-copy mechanism by emitting both sequence length and initializer body with
inLetExprBody=true. Body emission must use the existing typed EmitArrayUpdate
overload returning the array and rhs writers, then EmitExpr(body,true,...), since
the Expression overload hardcodesfalse. This keeps the zero-argument loop lambda,
introduces ordinary local temporaries rather than an unbounded System.Func, and
requires no shared backend/capture-helper changes. Check copyInstrWriters scope,
nested/let behavior and evaluation order independently; add17ordinary-input and
more-than16output compatibility controls. No root/candidate/tool-policy changes.

Fresh verification must bind generation2 binary/source hashes and repeat failed
compatibility plus original/evaluation controls. Prior generation1 success alone
cannot close this plan. VSTest socket permission denied before any Lit test ran;
use approved local execution for the existing targeted test runner, not a bypass.

### Generation2 implementation validation (later rejected)

Generation2 is the C#-only temporary-copy correction. Removed the now-unused
private-helper context argument, emitted length withtrue, and emitted initializer
via typed array-update writers plus EmitExpr(body,true,...). Shared backend code
and optimized allocation/loop/return remain unchanged. Final source SHA-256:
38a561cf0677eed01703c3f7cab6607c0c40ba17c68ca97b211d45dd21667fe7.
Binaries/DafnyCore.dll and integration-test copy both have SHA-256
c836d1d08f344fe58e432d649fd6ab9bec67a62bb874a5bcca96c1c0ade70f31.
Bindings are in implementation/gen2-bindings.sha256; generation1 identities and
failed compatibility controls remain separately preserved.

From the owning repo root, authorized local
`dotnet build Source/Dafny.sln --no-restore --disable-build-servers -m:1`
passed in32.79s with0warnings/0errors (implementation/build-gen2.log). Existing
Gradle distribution/dependency caches were inspected before escalation; no
packages/dependencies were added. Scoped C# formatter
`dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyCore/Backends/CSharp/CsharpCodeGenerator.cs`
completed0; workspace-load warnings are recorded. The redundant narrowed
formatter attempt was canceled130, not falsely counted as passed. New Dafny
source was formatted with the owning Binaries/Dafny formatter.

Expanded regression covers10scenarios, including17inputs/17scalar outputs,
and native verification passed11verified/0errors with20s limit. The original
source-derived sequence-out and independent17-input toy each pass full native
verify2/0 and compile/run output[5,8] and[153], respectively. This is small-source
proof/compilation/runtime evidence, not original benchmark verification.

Existing targeted make runner invoked for comp/csharpOutCapture.dfy,
comp/Calls.dfy and comp/firstSteps/6_Calls-VariableCapture.dfy with build=false;
each passed1test/fail0/skip0. Environment selected C# and supported in-process
mode so task-local RestoreConfigFile/NuGetAudit=false reach compiler subprocesses:
DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS=cs,
DAFNY_INTEGRATION_TESTS_IN_PROCESS=true,
RestoreConfigFile=/workspace/tmp/dafny-csharp-out-capture/NuGet.Config,
NuGetAudit=false. VSTest's sandbox socket denial was resolved through authorized
local execution. Tests verify source, compile/run C# with runtime inclusion
enabled/disabled and compare expected output; final independent check will audit
actual execution rather than rely solely on pass-count/exit status. The C# fix
needs no other-backend or root Python suite; no full benchmark suite ran.

`git diff --check` passes. Final independent generation2 acceptance and global
preservation/Markdown closure remain pending before statusdone.

### Generation2 independent rejection: loop guard timing

Independent source-derived loop-scope.dfy verifies2/0 and compiles undergen2,
but runtime prints loop:3:3 then expectation failure instead of expected2:2.
The ordinary-local control loop-ordinary-scope.dfy is a direct semantic regression:
baseline andgen2 both verify2/0 and compile, baseline printsordinary-loop:2 and
exits0, gen2 printsordinary-loop:3 and exits1. Copy instructions were emitted
in the surrounding while-statement prelude and never refreshed per guard
evaluation. Rejectgen2 despite all earlier focused test/build passes; preserve
its source/binary/log identities. A statement-level copy is not sufficient for
expressions reevaluated by a loop.

New mandatory acceptance: capture at the original expression evaluation point on
every invocation, with no Func arity limit, preserving nested/let/constant/function
contexts and delayed-lambda snapshots. Add both output/local loop guards to the
persistent compiler regression; independent audit also checks test execution
instead of relying on VSTest elapsed/pass summaries alone. No code changes until
the next exact design amendment. Read-only Astra/high review and existing Sol
implementation agent independently assess a C# local function with value
parameters declared in the statement writer and called at the expression point,
or arity-safe tuple capture; final verifier remains separately independent.

### Generation3 exact approved design

Read-only source assessments agree on an expression-local, arity-safe tuple
wrapper rather than statement writer/local-function declaration. A local-function
declaration risks insertion mid-assignment when existing array-update emission
passes its current writer as wStmts; avoid expanding writer behavior.

Within CsharpCodeGenerator.cs only, restore the generation2 optimized helper to
baseline, add a private capture helper reusing CreateFreeVarSubstitution and
Substituter, and call it in the optimized literal-lambda sequence branch. Zero
free variables retain the baseline IIFE; one uses unary EmitBetaRedex; two or
more pass one native C# tuple to Func<(T1,...,TN),Result>, deconstruct fresh
BoundVar locals, and return the unchanged optimized sequence IIFE. Native tuple
syntax lowers arbitrary arity under existing net8.0 target; no new dependency.
Arguments stay at the original expression's evaluation point.

Also add a C# EmitExpr override for LetExpr, MatchExpr and NestedMatchExpr whose
expression subtree contains the literal-lambda SeqConstructionExpr optimization.
Capture/substitute the WHOLE enclosing context with the same helper before
calling base.EmitExpr directly. This is a structural emitter boundary, not a
behavioral diagnosis heuristic: those lowerings create enclosing lambdas/true
flags that otherwise hoist captures. The outer context's substitution makes all
descendant references fresh BoundVars, which shared identifier lowering exempts
from copyInstrWriters. Keep incoming flags for already-substituted descendants;
do not force true or change shared emitters. Review normalization/descendant
traversal and avoid recursive recapture of the same context.

Extend persistent regression and independent acceptance with direct and let/match
wrapped output/local while guards, nested/shadowed contexts, more-than16freevars
in enclosing contexts, conditional/short-circuit evaluation, plus all previous
generic/delayed-lambda/zero-length/evaluation-order controls. Baseline independent
ordinary let/match loops verify2/0, compile and print2; output let loop verifies
2/0 and baseline failsCS1628. Generation3 must preserve baseline successes and
correct affected output cases. Capture at the original evaluation point is a
required observable behavior, not optional optimization. All earlier failed
generations remain explicitly rejected. Fresh verification binds final hashes.

### Generation3 implementation results

Final C# source diff41insertions/1deletion is confined to EmitExpr,
CaptureSequenceConstructionVariables and EmitSeqConstructionExpr; baseline
optimized helper is restored. Source SHA-256
f8094051b7694ec455954feb91d196610472d75f7d819f1fa5b1a62739625e01;
both active/integration DafnyCore.dll SHA-256
dd85c62ac0ecc0067144586abd8d2a2d35d28147f5c95f7f5dd26191e60cc9e4.
Bindings are in implementation/gen3-bindings.sha256 and
gen3-runtime-bindings.sha256. The implementation agent made no documentation
or other source edits.

Final authorized serial solution build passed in88.41s with0errors and3warnings
in unchanged ContractRuntimeProfile.cs/PbtObservation.cs test-generation files;
record actual warnings rather than carry forwardgen2's0. Scoped C#/Dafny
formatters passed. Persistent expanded regression verifies27obligations/0errors,
compiles and runs; standalone generated assembly output matches all25expected
lines byte-for-byte with diffexit0. Six direct/let/match output/local loops each
produce2, variable-rich contexts produce153, and conditional/short-circuit,
zero-length, delayed-lambda, generic/function/constant and simultaneous-assignment
observations pass. The same three focused C# Lit regressions each pass1/0/0.

Independent gen3 nine-program proof/compile/runtime suite has passed all native
proofs and exact expected transcripts, including prior negative generations'
compatibility controls. Final actual-runner and preservation acceptance completed
as recorded below.

## Final independent acceptance and closure

Fresh verifier accepted generation3 in verification/verification-result.json,
SHA-25628ac0fcaf07525476effefd20ed7cdac3843542258ee1adfb1b07953a8a33917.
Nine valid programs each pass native proof with0errors, C# compilation with0exit,
runtime with0exit and exact full transcripts. Four official runner suites (new
fixture plus Calls,6_Calls-VariableCapture,Comprehensions) each perform legacy/
refresh native verification and runtime-source/runtime-DLL execution with actual
expected-output comparison. Deliberately wrong copied .expect fails both modes,
exit255. Source/fixture/.expect/core identities match accepted generation3;
all initial DefinitionAnalysis/declaration hashes remain unchanged. The verifier
did not rely on implementation conclusions, run the full solution itself, or
read benchmark/private evaluator/other-run material; its own generated C# builds
and runtime checks validate the exact accepted compiler.

Root closure-audit.json confirms4immutable baseline files preserved, only the
planned C# baseline changed, and stable root/compiler HEADs. Recursive metadata
inspection across plan/wiki found252directories/4,657files,98preexisting non-md
paths and zero task-created violations; preserve all preexisting paths. Scoped
diff/links and git diff--check pass. A three-file code/test fix.patch was produced
without index mutation/commit; reverse-check against current source passes.
Patch SHA-256c2c46451f11eff9ad0176c6e532533d911449f29a4be2cbae596c80b63e53d55.

Durable mechanism, rejected approaches, reproduction, acceptance and limits are
in the linked compiler wiki/index. All required acceptance is met; no pending
work or blocker for this local backend fix. Original full-candidate proof,
benchmark/provider/evaluator runs, other-backend matrix and runtime deployment
were not part of this scope. No package additions, commits or global tool-link
changes occurred. The accepted local compiler is Binaries/Dafny in this owning
tree; the default /usr/bin/dafny remains the separate Cosyn tree. Preserved
rejected generations1/2 remain available as regression provenance.

## 2026-10-13 commit packaging plan
The user now explicitly authorizes committing this backend fix with the exact title `[CodeGenerator] fix CS1628 error in valid dafny code compliation`. This supersedes the original no-commit non-goal for packaging only. The code remains unchanged.

Ready scope: CsharpCodeGenerator.cs, comp/csharpOutCapture.dfy and its .dfy.expect, this owner plan/index and the existing csharp-out-capture wiki/index. The parent Dafnyutils gitlink will be updated in a separate focused commit; root integration edits remain uncommitted. Acceptance: independent focused native verification, C# compile/runtime regression and formatting checks pass, staged diff matches the approved fix and records, both native and parent commits exist. No new dependencies, benchmark or scoring changes, provider runs or compiler deployment.

Validation from this owner root: supported `DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS=cs make test name=comp/csharpOutCapture.dfy build=false`; native `Binaries/Dafny verify --verification-time-limit:20` on that fixture; scoped C# whitespace and Dafny format checks. Inspect binary/source binding; preserve any environment failures separately and report exact evidence limits. Prior independently accepted nine-program/four-suite results remain historical evidence, not a claim of rerunning them today. Recursive root/owner plan/wiki non-Markdown audit and final status review are required. Scratch: /workspace/tmp/commit-codegenerator/. No additional user approval is required.

Change table addition: parent `/workspace/dafnyutils/dafny` gitlink must track the new backend commit or parent checkouts omit the fix; validate with `git ls-files -s dafny` and native HEAD.

### 2026-10-13 precommit results
Fresh independent review found no actionable defects. On precommit native HEAD`cebdacfb8`, backend/fixture/expect SHA-256 values match the accepted generation3 bindings. `dotnet Binaries/net8.0/DafnyDriver.dll verify Source/IntegrationTests/TestFiles/LitTests/LitTest/comp/csharpOutCapture.dfy --verification-time-limit:20`:27verified/0errors. Scoped Dafny format --check passes. `timeout 45s dotnet format whitespace --folder --verify-no-changes --include Source/DafnyCore/Backends/CSharp/CsharpCodeGenerator.cs`:passes; the broader project-based formatter attempt was canceled after a bounded wait.

Supported C# `make test name=comp/csharpOutCapture.dfy build=false` exited successfully, but its sub-millisecond duration was insufficient execution evidence. A direct official TestDafny runner in isolated scratch with explicit empty mode, in-process=true, compilers=cs and expectation updates disabled substantively passed legacy and refresh verification, C# source-runtime and `--include-runtime:false` execution and full expected-output comparison. Log: `/workspace/tmp/commit-codegenerator/verify-direct-runner.log`. Runner core SHA-256`dd85c62ac0ecc0067144586abd8d2a2d35d28147f5c95f7f5dd26191e60cc9e4` matches accepted generation3. Existing root Binaries/DafnyCore.dll has a different hash and is not used as fix acceptance evidence. No global binary deployment occurred.

Final whitespace/diff review and recursive root/owner plan/wiki artifact audit pass with zero non-Markdown files. The approved commit packages code, two fixture files, this plan/index and existing wiki/index. Parent gitlink follows in its own focused commit. There are no remaining fix/validation blockers. No broader backend matrix, paid benchmark or provider experiment was run.
