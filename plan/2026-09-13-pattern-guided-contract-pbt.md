# 범용 Dafny 입력 패턴 샘플러와 원본 전제조건 판정

- 상태: done
- 작성일/갱신일: 2026-09-14
- 소유 저장소: Dafny (`/workspace/cosyn/dafny`).
- 기준 커밋: `1eb9fc5fa2661483de151ff85b21eed0b695878a`의 기존 dirty 작업 트리.
- 상위 계획: [CoSyn 계획](../../plan/2026-09-13-pattern-guided-contract-pbt.md)

## 목표와 비목표

해결된 일반 Dafny 타입에 대해 타입 검사된 pattern AST를 유한 generator로 컴파일하고,
재현 가능한 random 후보를 원본 entry P로 필터링한다. 희소 P에서는 지정 leaf만 P-only SMT로
보정한다. 2026-09-14 사용자 범위 조정에 따른 이번 완료 경계는 구체 후보의 타입·정제 조건과
원본 P 판정까지다. 구현 실행, bodyless/extern 계약 전이, Q 판정과 replay 관련 변경은 이번
커밋에서 제외하고 후속 범위로 남긴다.

DSL과 엔진에 `mv`, coreutils, path, filesystem, inode 또는 `BenchIO` 전용 구문·분기·값을
추가하지 않는다. 실제 mv는 이 API의 소비자 수용 시험일 뿐이다. 무한 값 전체 탐색,
co-datatype/function value, 경로 완전성 및 전역 증명은 비목표다. 미지원 영역은 구조화된
frontier로 남긴다.

## 초기 장기 수용 기준

아래 기준은 최초 전체 설계를 기록한다. 이번 P-only 완료 범위에는 후보 생성, 타입·힙 구조
검사, 정제 조건, 원본 P 판정과 그에 필요한 부분 평가·residual SMT까지만 포함한다.

- strict JSON AST가 int/bool/char/string/bv, finite seq/set/multiset/map, datatype,
  subset/newtype, array/class/reference/null, binding/reuse/alias와 solver hole을 지원한다.
- 조건 AST는 해결된 입력·초기 힙 projection과 내장 순수 연산/해결된 pure call만 허용하며
  raw Dafny source, output, final heap, Q, statement와 `assume`를 표현하지 못한다.
- sampler는 SHA-256 counter stream의 seed와 ordinal로 결정적이고 lazy하며 pattern별
  공정성, budget과 중복 제거를 지킨다.
- 후보는 complete concrete/logical value가 된 뒤 original P와 타입·할당·alias invariant를
  다시 통과해야 실행된다. false/unknown/timeout은 각각 계수된다.
- repair는 non-repair leaf를 고정하고 original P만 푼다. 재검사 없는 model은 내보내지 않는다.
- runtime-visible heap과 logical-only ghost/const heap은 동일 object ID로 연결되고 entry/call
  `old`, frame, alias가 외부 호출 연속 전이에 보존된다.
- concrete heap object는 모든 runtime field를 계속 요구하되, 선택 entry에서 resolved call
  graph로 도달 가능한 contract/body가 참조하지 않는 ghost field만 생략할 수 있다. 같은 class의
  object는 동일 supplied field set을 사용하고 unknown/non-ghost/reachable ghost 생략은 failure-closed다.
- reachable internal body가 tracked logical heap을 ghost-only statement로 변경하면 실행 전
  효과 분석이 `unsupported`로 거부한다. ghost local과 heap을 바꾸지 않는 proof call만
  dependency 근거와 함께 소거한다.
- bodyless/extern 구현은 실행되지 않으며 final Q는 entry H0, actual outputs, final Hn에 대해
  별도 검사한다. 애매한 logical completion은 `inconclusive`다.
- original pattern/seed/sample을 먼저 재현하고, 구조 축소 뒤에는 별도 reduced concrete
  request와 call choices가 같은 P, path, Q violation을 재현한다.
- 모든 단위·통합 fixture는 benchmark-independent 이름과 상태로 작성한다.

## 변경표

| 단계 | 파일·심볼 | 변경 방법 | 없으면 남는 문제 | 검증 |
| --- | --- | --- | --- | --- |
| 1 | `Source/DafnyTestGeneration/ContractTesting/ContractPatternModels.cs`(신규), `ContractInputModels.cs`, `ContractTestModels.cs` | generator/expression discriminated records, pattern origin/epoch/provenance, strategy, `ContractCampaignFeedback`, sample/repair/coverage와 original/reduced replay outcome, map/set/multiset/bv value variants를 추가한다. | wire에서 일반 패턴, 반복 라운드와 결과를 무손실·엄격하게 표현할 수 없음 | serialization/invalid variant tests |
| 2 | `ContractPatternCompiler.cs`(신규) | entry의 resolved formals/receiver/heap field 타입에 AST를 대조하고 type substitution, constructor/field, pure-call, binding scope와 금지 참조를 검사한다. | 잘못된 LLM 패턴이 source generation 시점까지 미뤄지거나 코드를 삽입할 수 있음 | primitive/collection/generic/datatype/ref/type-error tests |
| 3 | `ContractPatternSampler.cs`(신규), `ContractTypeShapeGenerator.cs`, `ContractModelCodec.cs` | lazy seeded sampler, boundary/random 분포, finite collection, datatype depth, object layout와 alias materialization을 구현한다. 기존 shape/value codec을 공통 primitive로 추출한다. | Cartesian prefix 고갈과 제한된 value kinds 때문에 복합 일반 입력을 만들 수 없음 | determinism/fairness/bounds/dedupe/materialization tests |
| 4 | `ContractLogicalHeap.cs`(신규), `ContractLogicalEffectAnalyzer.cs`(신규), `ContractHeapFactory.cs`, `ContractQueryBuilder.cs`, `ContractStateObserver.cs` | runtime cell과 logical-only ghost/const cell, identity map, entry/call snapshots와 frame 계획을 분리한다. diagnostic source copy에 source-located snapshot constructor를 삽입한다. trait parent와 compatible dynamic reference를 지원한다. tracked ghost heap write는 unsupported, proof-local ghost만 소거한다. | ghost 제거 후 P/Q 상태가 실행 trace와 분리되며 내부 ghost update를 무시하면 거짓 판정이 생김 | ghost const/alias/parent/dynamic type/old/frame, ghost-effect rejection tests |
| 5 | `ContractPatternCampaign.cs`(신규), `ContractInputGenerator.cs`, `ContractScenarioExtractor.cs`, `ContractSolver.cs` | 공통 `RecheckCandidateAsync`로 sample→P query→optional minimal repair→complete P recheck를 구현한다. concrete input의 spec-case를 분류하고 prior covered branches/cases, seen hashes, round와 remaining budget을 다음 batch에 반영한다. solver-only generation은 별도 strategy로 유지한다. | rejection starvation과 쉬운 경로 반복을 구별·복구할 수 없고 새 전략이 기존 생성과 뒤섞임 | selective-P, repair Q-isolation, case classification, round feedback, unknown/timeout/checkpoint tests |
| 6 | `ContractHarnessBuilder.cs`, `ContractStubRuntime.cs`, `ContractHeapModelRealizer.cs`, `ContractModelRealizer.cs`, `ContractTestRunner.cs` | runtime event마다 logical state session을 조회·전이시키고 외부 계약의 call-entry old/frame을 적용한다. entry Q는 전이가 끝난 뒤만 평가하고 replay 시 모든 state/choice hash를 검사한다. | 여러 abstract call과 ghost state가 있는 실행을 Hoare triple로 판정할 수 없음 | multi-call state continuity, correlated output/postheap, poison extern, ambiguous completion tests |
| 7 | `Source/DafnyDriver/Commands/TestContractsCommand.cs` | existing `--generate`에 pattern strategy, probe-only request와 checkpoint를 추가하되 fixed/check/symbolic 명령과 상호 배타성을 보존한다. | 소유 CLI에서 제출 직후 semantic probe와 시간 제한·취소·부분 결과를 안전하게 운반할 수 없음 | supervisor, probe와 CLI integration tests |
| 8 | `Source/DafnyTestGeneration.Test/ContractPatternTests.cs`(신규), 기존 Contract tests | 하나의 test가 하나의 정상/오류 의미를 검사하도록 일반 fixtures를 추가하고 기존 generation/check/replay를 회귀한다. | benchmark 없이 DSL의 범용성과 사운드니스 퇴행을 입증할 수 없음 | focused 및 Contract 전체 xUnit |
| 9 | `ContractHeapFactory.cs`, `ContractHarnessBuilder.cs`, `ContractStubRuntime.cs`, `ContractHeapTests.cs`, `ContractExternExecutionTests.cs`, `wiki/contract-testing.md`, `wiki/INDEX.md` | heap field subset을 declared field에 대조하고 non-ghost/unknown/inconsistent class subset을 거부한다. entry에서 resolved intra/inter-module call graph를 transitive하게 따라 internal full AST와 extern/bodyless contract/frame AST의 `MemberSelectExpr.Member` field를 수집해 omitted ghost 참조를 거부한다. diagnostic constructor는 supplied field만 인자로 받고 omitted ghost는 declaring class 내부 fresh ghost witness로 초기화하며 runtime metadata/sidecar/query/observation/frame/post assignment는 supplied logical cell만 추적하고 경계를 지식 문서와 index에 기록한다. | function-valued 등 concrete codec이 지원하지 않는 irrelevant ghost field 하나 때문에 일반 program 전체 heap을 만들 수 없고, 단순 생략은 P/Q/body/extern contract 의존성을 잃거나 runtime sidecar field 수를 불일치시킴 | `ContractHeapTests`의 partial/exact/error/source parse-resolve tests와 `DafnyDriver.Test`의 compile-execute test |
| 10 | `Source/DafnyTestGeneration/ContractTesting/ContractTypeShapeGenerator.cs`의 `RefinementObligationsAsync`/carrier 추출, `ContractInputGenerator.cs`의 no-requires pattern 판정, `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs`의 datatype literal/equality, `PartialEvaluatorVisitor.cs`의 datatype member/map selection, `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs`, `ContractReductionResult.cs`, `Source/DafnyTestGeneration.Test/ContractPatternTests.cs`, `Source/DafnyCore.Test/ContractExpressionReducerTests.cs` | nullable 실패를 success/unavailable/failure 구조화 결과와 단계별 진단으로 바꾸고, synthetic non-null class type은 기존 heap structural validation에 맡긴다. resolved constraint-erased concrete carrier에서 recursive datatype·finite map·nested subset/newtype constraint를 각각 치환한 뒤 기존 partial evaluator와 bounded quantifier unrolling로 줄인다. concrete datatype의 constructor identity를 보존한 destructor/discriminator 및 finite-map lookup 평가와 bounded membership 전용 inline depth를 사용한다. reducer 결과에 원본을 바꾸지 않은 concrete-substituted membership을 보존해 `True`만 직접 승인하고 `False`는 거부하며 `Residual`/budget exhaustion은 해당 원 membership SMT fallback으로 보낸다. | carrier source/resolve/AST 추출 실패가 일반 P recheck `unknown`으로 뭉개져 원인을 알 수 없고, synthetic non-null reference가 direct 경로를 불필요하게 중단하며, 구조적으로 유효한 recursive datatype·map refinement 후보가 no-requires fast path를 통과하지 못하거나 inner refinement를 놓침 | nullable 각 실패 경로 진단, non-null/custom reference 구분, recursive datatype + finite map + nested refinement valid/invalid/exhaustion/cache tests, focused/full Contract xUnit, 직렬 solution build, touched-file format/diff |

## 사운드니스와 호환성

1. pattern constraint와 repair query는 entry P를 강화하는 탐색 힌트다. 생성 완료 후 그
   가정을 제거한 원본 P 질의로 전체 값·힙을 다시 검사한다.
2. 외부 계약 실현은 enclosing Q를 받지 않는다. 모델 선택 뒤 해당 call P/Q/frame을 원식으로
   재검사하고 entry final Q는 실행 종료 후 독립 질의로만 판정한다.
3. ghost/const를 위해 바꾸는 것은 hash-bound diagnostic source copy뿐이다. production source,
   constructor, 외부 binding과 proof obligation은 수정하지 않는다.
4. 기존 schema-1 fixed requests와 solver generation의 기본 동작을 보존한다. 새 필드는 optional,
   pattern AST 자체는 독립 version을 가진다.
5. 부분/무한 모델, cyclic heap 또는 지원하지 않는 frame을 임의 기본값으로 채우지 않는다.
   실현 여부가 Q 값에 영향을 줄 수 있으면 `inconclusive`다.
6. partial logical heap은 생략 field에 임의 concrete `ContractValue`를 만들지 않는다. 생략 가능한
   field는 ghost이고 reachable relevant AST에서 참조되지 않을 때뿐이며, diagnostic copy의 declaring
   class constructor가 `ghost var witness: T :| true;`로 Dafny logical heap만 완전하게 만든다.

## 검증 계획과 인계

- `/workspace/cosyn/dafny`: `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractPattern|FullyQualifiedName~ContractHeap|FullyQualifiedName~ContractInput|FullyQualifiedName~ContractExecution'`
- `/workspace/cosyn/dafny`: `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~Contract'`
- `/workspace/cosyn/dafny`: `dotnet test Source/DafnyDriver.Test --no-restore --filter 'FullyQualifiedName~ContractPattern'`
- `/workspace/cosyn/dafny`: `make test name=cli/contractGeneration build=false`
- `/workspace/cosyn/dafny`: `dotnet build Source/Dafny.sln --no-restore`
- `/workspace/cosyn/dafny`: `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes`
- `/workspace/cosyn/dafny`: `git diff --check`

새 dependency, network, native/host side effect와 유료 provider는 필요하지 않다. 구현과 분리된
검증 에이전트가 현재 요구사항과 작업 트리만 보고 P/Q 비순환성, ghost identity, extern
미호출과 replay를 독립 검증한다. 2026-09-13 사용자 시작 지시에 따라 구현을 시작했으며
pattern DTO/compiler의 실패 회귀부터 추가했다.

2026-09-13 현재 schema-1 pattern wire, resolved-type compiler, SHA-256 counter sampler,
complete-pattern initial fairness, 원본 P 재검사, provenance와 global ordinal을 구현했다. 내부
구현은 실제로 실행되고 bodyless/extern은 native fallback 없이 계약으로 실현된다. 도달 가능한
내부 ghost heap write는 실행 전 `unsupported`로 막고, heap을 바꾸지 않는 proof-local ghost만
소거한다. worker는 Unicode를 포함한 실제 wire 직렬화에서 계산한 input/heap digest를 반환한다.
현재 지원 타입으로 모든 static formal을 만들 수 있으면 실행기 소유 소경계 baseline을
ordinal 0에 합성한다. 모델 패턴은 같은 총 예산의 다음 ordinal부터 초기 공정 순서를
사용한다.

visible instance ghost 필드는 diagnostic runtime의 object-ID sidecar에 보존한다. 최초 snapshot,
외부 계약이 선택한 postHeap, frame write와 최종 snapshot이 같은 논리 상태를 공유하며, 두 번
연속 외부 호출하는 일반 fixture에서 `1 -> 2 -> 3` 전이를 확인했다. 외부 poison body는 실행되지
않았고 내부 구현의 ghost heap write는 계속 실행 전에 거부한다.

구현 파일 매핑은 계획 당시 제안과 달라졌다. 별도 `ContractLogicalHeap.cs`는 만들지 않고
논리 sidecar와 snapshot 책임을 기존 `ContractHeapFactory`, `ContractStateObserver`,
`ContractStubRuntime`, `ContractTestRunner`에 배치했다. 별도 `ContractPatternCampaign.cs`도
만들지 않고 sample/P 재검사와 batch 결과는 `ContractInputGenerator`가 담당하며, 다중 round
feedback 정책은 호출자인 CoSyn이 소유한다. 변경표의 두 파일명은 논리 책임을 가리키는 초기
제안이며 현재 소스에 파일이 존재한다는 뜻이 아니다.

`dotnet test Source/DafnyTestGeneration.Test --no-restore --filter
FullyQualifiedName~Contract -m:1`은 커밋 전 현재 트리에서 `218/218`, DafnyDriver의
`ContractExternExecutionTests`는 `1/1`, CoSyn actual-pattern 네 사례는 `4/4` 통과했다. 구현되지
않은 collection/bitvector/subset/newtype/condition/solver-hole, instance/reachable pattern entry와
접근 불가 logical state 때문에 M3와 actual `mv` M4는 남아 있다. 실제 `mv` probe는 과거
`BenchIO.IO.fsRegion` field 거부를 넘어 현재 `map<InodeId, InodeRecord>` shape에서 중단된다.

2026-09-14 후속 slice는 다른 module/source에 선언되어 현재 entry scope에서 숨겨진
runtime/ghost field를 원본 source가 아니라 hash-bound diagnostic copy에서만 초기화하고
질의하도록 확장한다. `ContractSourceSnapshot.ApplyEdits`가 immutable source bundle 안의
위치만 허용하고 모든 수정 사본의 hash를 다시 계산한다. heap constructor와 필요한 field
member는 선언 module의 명시적 default export에만 추가하며, default view가 없거나 예약된
diagnostic constructor가 충돌하면 임의 export alias나 사용자 본문 실행으로 우회하지 않고
failure-closed로 거부한다. 관련 변경은 `ContractHeapFactory`, `ContractHarnessBuilder`,
`ContractSourceSnapshot`, solver call sites와 `ContractHeapTests`에 한정한다. 숨김 필드의
premise 일관성 및 모순, 잘못된 Q, ghost/non-ghost, 원본 snapshot 불변, wildcard/default 및
named-only export와 constructor 충돌을 집중 검사하고 전체 contract filter와 solution build를 재실행한다. 이 slice만으로
collection shape나 actual `mv` M4가 완료됐다고 주장하지 않으며 actual `mv`는 다시 실행하지
않는다.

2026-09-14 추가 soundness slice는 arbitrary Dafny heap object가 irrelevant unsupported ghost
field를 생략하도록 허용한다. `ContractHeapFactory`가 supplied subset, full declared fields와 omitted
ghost fields를 구분하고 unknown field, omitted runtime field, 같은 class의 서로 다른 subset을 먼저
거부한다. 그 뒤 선택 entry의 original callable에서 resolved module/inter-module call graph를
transitive하게 따라가며 internal callable의 contract/body 전체와 extern/bodyless callable의
requires/ensures/reads/modifies/decreases를 보수적으로 검사한다. omitted field의 resolved
`MemberSelectExpr.Member`가 하나라도 발견되면 callable과 source 위치를 포함해 거부한다.
Diagnostic constructor는 supplied field만 parameter로 받고 omitted ghost field는 fresh ghost
assign-such-that witness로 초기화한다. `ContractStubRuntime`의 class metadata도 prepared plan의
supplied ghost field만 logical sidecar에 등록하여 snapshot/apply/query/observation/frame/post-state가
같은 tracked subset을 유지한다. 기존 exact heap은 같은 constructor/value/cell 경로를 유지한다.
변경은 `ContractHeapFactory.cs`, `ContractHarnessBuilder.cs`, `ContractStubRuntime.cs`,
`ContractHeapTests.cs`, `ContractExternExecutionTests.cs`, `wiki/contract-testing.md`, `wiki/INDEX.md`에 한정하며 source parse/resolve와 실제
diagnostic C# compile/execute를 포함한 focused tests, 전체 Contract filter, solution build,
format/diff 검사를 수행한다. actual `mv`, benchmark data, evaluator와 `/workspace/dafnyutils`는 범위
밖이며 실행하거나 수정하지 않는다.

2026-09-14 partial logical heap 구현과 local 검증을 완료했다. 검증 기준은 Dafny HEAD
`336ae4ce66176cf8360d107894d5a4ad5a7a3a2d`, .NET SDK `8.0.131`과 위에 열거한 기존 dirty
작업 트리다. `/workspace/cosyn/dafny`에서 다음을 실행했다.

- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --filter 'FullyQualifiedName~ContractHeapTests' -m:1`: 32/32 통과.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~Contract' -m:1`: 246/246 통과.
- `dotnet test Source/DafnyDriver.Test --no-restore --filter 'FullyQualifiedName~Contract' -m:1`: 4/4 통과. 새 function-valued omitted ghost field의 diagnostic compile/execute와 기존 native extern 미호출을 포함한다.
- `dotnet build Source/Dafny.sln --no-restore -m:1`: 성공, warning/error 0.
- `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include Source/DafnyTestGeneration/ContractTesting/ContractHeapFactory.cs Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs Source/DafnyTestGeneration/ContractTesting/ContractStubRuntime.cs Source/DafnyTestGeneration.Test/ContractHeapTests.cs Source/DafnyDriver.Test/ContractExternExecutionTests.cs`: 성공.
- `git diff --check`: 성공.
- 전체 solution `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes`는 변경하지
  않은 generated C#의 기존 whitespace 위반을 대량 보고하여 exit 2였다. generated file은 수정하지
  않았고 위의 changed-file scoped 검사로 현재 slice를 확인했다.

재사용 가능한 partial logical heap 경계, 검증 근거와 제한은
[`wiki/contract-testing.md`](../wiki/contract-testing.md)에 갱신했다. 계획 전체에는 아직 collection
shape, condition/solver-hole과 상위 acceptance 작업이 남아 있으므로 상태는 `in-progress`로 유지한다.

2026-09-14 독립 검증에서 partial heap slice의 두 correction이 필요함을 확인했다. 첫째, omission
audit가 runtime instrumentation용 resolved call graph successor를 그대로 따라 extern source body
안에서만 호출한 helper까지 reachable로 보았다. omission audit는 별도 traversal로 바꾸고 각
callable의 outgoing call을 동일 `RelevantNodes`에서만 추출한다. internal executable callable은 full
AST, extern/bodyless callable은 requires/ensures/reads/modifies/decreases roots만 사용하며 resolved
function/method calls과 override implementation을 transitive하게 보수적으로 추가한다. instrumentation
reachability는 extern body를 실행하지 않는 기존 rewrite 경계를 보존하기 위해 이번 correction에서
변경하지 않는다. extern body에서만 callback을 읽는 helper는 omission을 허용하고, extern contract가
같은 helper를 호출하면 계속 거부하는 회귀를 `ContractHeapTests.cs`에 추가한다.

둘째, diagnostic constructor/export edit가 default export만 수정해 caller가 named view로 import한
경우 allocation source에서 constructor를 볼 수 없었다. `ContractHeapFactory.cs`가 declaring module의
각 existing export view 중 heap class를 실제로 reveal/expose하는 view를 식별해 그 view에 constructor와
필요한 supplied hidden field를 hash-bound diagnostic edit로 추가한다. class를 노출하지 않는 view는
수정하지 않고, 외부 allocation scope에 class는 보이지만 안전하게 수정할 export view를 찾지 못하면
정확한 진단으로 조기 거부한다. no-export, wildcard, same-module과 default import를 보존하고 named import
runtime-source parse 및 compile/execute 회귀를 `ContractHeapTests.cs`와
`ContractExternExecutionTests.cs`에 추가한다. 변경 파일은 기존 slice의
`ContractHeapFactory.cs`, 두 test file, active plan/wiki 기록에 한정하고 focused/full Contract tests,
solution build, changed-file whitespace와 diff 검사를 재실행한다. actual `mv`와 `/workspace/dafnyutils`는
계속 실행하거나 수정하지 않는다.

두 correction 구현 후 `/workspace/cosyn/dafny`에서 focused `ContractHeapTests` 35/35와 전체
DafnyTestGeneration `Contract` filter 249/249가 통과했다. extern body에서만 pure helper를 부르는
경우 omission이 허용되고, extern requires가 같은 helper를 부르면 해당 helper의 field reference로
거부되는 두 회귀가 포함된다. named-only revealing export와 default+named export에서 named import를
선택한 runtime source가 parse/resolve되는 회귀도 포함된다. DafnyDriver `Contract` filter는 4/4가
통과하여 mixed supplied/omitted ghost sidecar compile/execute와 native extern 미호출을 재확인했다.
최종 `dotnet build Source/Dafny.sln --no-restore -m:1`은 warning/error 0으로 성공했고, touched C#
five-file scoped `dotnet format whitespace ... --verify-no-changes`와 `git diff --check`도 통과했다.
전체 solution whitespace 검사의 기존 generated-file limitation은 위 기록과 같으며 generated file을
수정하지 않았다. correction 과정에서도 actual `mv`와 `/workspace/dafnyutils`는 실행하거나 수정하지
않았고 commit을 만들지 않았다.

2026-09-14 독립 재검증에서 omission 전용 traversal이 직접 `FunctionCallExpr`와 `CallStmt`만
수집하여 first-class function reference를 빠뜨리는 soundness gap을 확인했다. Dafny
`CallGraphBuilder.VisitOneExpression`은 호출 구문뿐 아니라 resolved `MemberSelectExpr.Member`가
`Function`인 경우에도 call-graph edge를 만든다. 예를 들어 entry contract가 `Select()(box)`를
호출하고 `Select`가 function value `Read`를 반환하며 `Read`가 omitted ghost field를 읽으면 현재
audit는 `Read`에 도달하지 못한다. omission traversal의 outgoing dependency 추출을 resolved
call-graph builder의 callable-reference expression/statement cases와 맞추되, extern/bodyless에서는
계속 contract/frame/decreases roots만 검사하여 extern source body를 다시 포함하지 않는다.
`ContractHeapTests.cs`에 이 first-class dependency가 omitted field를 정확히 거부하는 일반 회귀를
추가하고 focused/full Contract tests, solution build, touched-file whitespace 및 diff 검사를 다시
실행한다. durable reachability 설명과 실제 결과는 `wiki/contract-testing.md`에 갱신한다. actual
`mv`, `/workspace/dafnyutils`, generated files와 commit은 계속 범위 밖이다.

first-class correction 구현 후 omission traversal은 relevant nodes에서 `FunctionCallExpr`,
`MemberSelectExpr.Member Function`, `MemberSelectExpr.Member ConstantField`, `CallStmt`와
`DatatypeValue`의 resolved callable target을 추출한다. constant initializer와 redirecting-type
constraint/witness, datatype default formal expression도 해당 callable vertex가 도달하면 검사하며,
prefix predicate/lemma와 dynamic override edge를 보수적으로 추가한다. extern/bodyless callable은
여전히 contract/frame/decreases roots만 제공한다. 요구된 `Select -> Read -> box.callback` 회귀는
omission을 `PartialHeap.Read`에서 거부하고, 같은 first-class `Read` reference가 reachable extern의
source body에만 있는 보완 회귀는 omission을 허용한다.

최종 `/workspace/cosyn/dafny` 검증은 focused `ContractHeapTests` 37/37, 전체
DafnyTestGeneration `Contract` filter 251/251, DafnyDriver `Contract` filter 4/4가 통과했다.
`dotnet build Source/Dafny.sln --no-restore -m:1`은 warning/error 0으로 성공했다. 기존 partial heap
slice의 touched C# five-file scoped `dotnet format whitespace ... --verify-no-changes`는 workspace-load
warning만 출력하고 exit 0이었으며 `git diff --check`도 통과했다. 기준은 Dafny HEAD
`336ae4ce66176cf8360d107894d5a4ad5a7a3a2d`, .NET SDK `8.0.131`이다. 전체 solution whitespace는
앞서 기록한 generated-file 기존 위반 때문에 재시도하지 않았다. actual `mv`와
`/workspace/dafnyutils`는 실행하거나 수정하지 않았고 commit도 만들지 않았다. 상위 plan의
미완료 acceptance가 남아 있으므로 상태는 계속 `in-progress`다.

2026-09-14 추가 독립 재검증에서 omission traversal이 resolved expression/statement callable
reference는 따라가지만 `CallGraphBuilder.AddTypeDependencyEdges`가 만드는 user-provided type
declaration edge를 재구성하지 않아 redirecting type constraint가 unreachable인 soundness gap을
확인했다. `type GoodBox = box: Box | box != null && box.callback(0) == 0 witness *`를 entry formal로
사용하면 omitted `Box.callback`을 현재 잘못 허용한다. `RelevantNodes`의 extern/body exclusion은
유지하면서 callable signature와 각 relevant contract/body node에서 AST visitor가 방문하는 type을
수집하고, 각 type component의 `UserDefinedType.ResolvedClass is ICallable` target을 transitive하게
enqueue한다. entry subset constraint 및 reachable internal/extern signature의 type dependency 회귀를
`ContractHeapTests.cs`에 추가하고 focused/full Contract tests, solution build, touched-file whitespace와
`git diff --check`를 재실행한다. 실제 결과와 bounded coverage는 active plan 및
`wiki/contract-testing.md`에 기록한다. actual `mv`, `/workspace/dafnyutils`, generated files와 commit은
계속 범위 밖이다.

type-dependency correction은 hybrid traversal로 구현했다. executable internal callable과
constant/redirecting-type/datatype vertex처럼 전체 declaration AST가 relevant한 경우 resolved
module/inter-module call-graph successor를 직접 사용하여 `CallGraphBuilder`가 이미 계산한 call,
type, default-value dependency를 보존한다. extern/bodyless callable만 relevant contract/default
expression에서 call target을 재수집하고, input/output signature type 및 relevant node의 명시적
`Type` 각각에 `ForeachTypeComponent`를 적용해 `UserDefinedType.ResolvedClass is ICallable` target을
추가한다. 따라서 extern source body의 call/local-type edge는 계속 제외된다.

일반 fixture에서 entry formal, reachable internal formal, reachable bodyless extern formal의
`GoodBox` subset constraint가 omitted `Box.callback`을 모두 `PartialHeap.GoodBox`에서 조기 거부하고,
동일 subset type이 extern source body local에만 나타나면 omission을 허용하는 네 회귀를 추가했다.
최종 `/workspace/cosyn/dafny` 검증은 focused `ContractHeapTests` 41/41, 전체
DafnyTestGeneration `Contract` filter 255/255, DafnyDriver `Contract` filter 4/4가 통과했다.
`dotnet build Source/Dafny.sln --no-restore -m:1`은 warning/error 0으로 성공했고, touched C#
five-file scoped whitespace 검사는 workspace-load warning만 출력하고 exit 0이었으며 `git diff --check`도
통과했다. actual `mv`, `/workspace/dafnyutils`, generated files와 commit은
계속 건드리지 않았으며 상위 plan 상태는 `in-progress`다.

2026-09-14 최종 독립 재검증에서 Dafny `CallGraphBuilder.AddTypeDependencyEdges`가 same-module
type target만 graph에 추가하므로, internal callable이 cross-module imported subset type을 signature에
사용할 때 hybrid traversal의 resolved successor만으로는 constraint가 reachable하지 않는 soundness
gap을 확인했다. 모든 callable에서 resolved/manual call successor와 별개로 declaration signature 및
각 callable의 `RelevantNodes`에 포함된 user-provided type component를 직접 union한다. extern/bodyless의
`RelevantNodes`는 계속 contract/frame/decreases/default에 한정하여 extern body local type은 제외한다.
두 module fixture에서 `Client.Entry`가 exported `Store.GoodBox` formal을 사용할 때 omitted
`Store.Box.callback`을 거부하고, 동일 type이 선언만 되고 entry에서 사용되지 않으면 전역 scan 없이
omission을 허용하는 회귀를 추가한다. focused/full Contract tests, solution build, scoped whitespace와
diff를 재실행하고 plan/wiki evidence를 갱신한다. actual `mv`, `/workspace/dafnyutils`, generated files와
commit은 범위 밖이며 plan 상태는 `in-progress`로 유지한다.

2026-09-14 actual r10 결과에서 partial-heap availability를 통과한 submitted sample 23개가 모두
`Datatype constructor and fields do not match expected heap value type.` 진단으로 중단되었으나,
`ContractHeapFactory.ValidateFieldValues`에서 `ValueExpression`으로 내려갈 때 heap object/cell 경로가
소실되어 일반 DSL feedback이 원인 값을 식별하지 못했다. benchmark 이름이나 shape special case 없이
heap field 검증의 root `objectId.field` context를 전달하고 datatype/map nested component를 재귀할 때
가능한 세부 path를 누적해 기존 type-mismatch 원인을 함께 보고한다. nested datatype mismatch가
cell/path를 포함하는 focused `ContractHeapTests` 회귀를 추가하고 focused Contract tests, solution
build, touched-file whitespace와 `git diff --check`를 실행한다. actual `mv`와 `/workspace/dafnyutils`는
실행하거나 수정하지 않고 plan 상태는 `in-progress`로 유지한다.

heap value diagnostic correction은 `ValueExpressionAt`에 optional path를 두고
`ValidateFieldValues`가 class cell에는 `objectId.field`, array cell에는 `objectId[index]` root를
전달하도록 구현했다. sequence/set/multiset은 `[index]`, map은 `[index].key`/`.value`, datatype은
`.formalName`을 누적한다. coarse recursive `ValueMatchesType` precheck를 제거하고 동일 typed renderer가
nested mismatch를 발견하게 하여 기존 원인 문구를 보존했으며 codec identifier 오류도 같은 root/path로
감싼다. 일반 map-nested datatype fixture의 정확한 진단은
`Heap value at 'box.payload[0].value.inner': Datatype constructor and fields do not match the expected heap value type.`다.

검증은 해당 단일 회귀 1/1, focused `ContractHeapTests` 44/44, 전체 DafnyTestGeneration `Contract`
filter 258/258가 통과했고 `dotnet build Source/Dafny.sln --no-restore -m:1`은 warning/error 0으로
성공했다. 두 touched C# file scoped whitespace 검사는 workspace-load warning만 출력하고 exit 0이었으며
최종 `git diff --check`도 통과했다. actual
`mv`와 `/workspace/dafnyutils`는 실행하거나 수정하지 않았고 commit도 만들지 않았다. plan은 전체
미완료 acceptance 때문에 `in-progress`로 유지한다.

cross-module correction은 모든 reachable callable에서 resolved/manual call target에 더해
`DeclaredTypes(callable)`과 `RelevantNodes(callable).OfType<Type>()`의 component dependency를 union하도록
구현했다. declaration type 수집은 function input/result, method input/output, constant field, newtype/type
synonym base, datatype constructor formal, iterator input/output을 포함한다. 두 module 회귀에서
`Client.Entry(box: Store.GoodBox)`는 omitted `Store.Box.callback`을 `Store.GoodBox` constraint 위치에서
거부했고, `Client.Entry(box: Store.Box)`가 `GoodBox`를 사용하지 않으면 동일 omission을 허용해 global
scan이 아님을 확인했다.

최종 검증은 focused `ContractHeapTests` 43/43, 전체 DafnyTestGeneration `Contract` filter 257/257,
DafnyDriver `Contract` filter 4/4가 통과했다. `dotnet build Source/Dafny.sln --no-restore -m:1`은
warning/error 0으로 성공했고, touched C# five-file scoped whitespace 검사는 workspace-load warning만
출력하고 exit 0이었다. 최종 `git diff --check`도 통과했다. actual `mv`,
`/workspace/dafnyutils`, generated files와 commit은 건드리지 않았다. plan 상태는 `in-progress`다.

2026-09-14 actual r11의 fixed/mutant generation artifact에서는 executor baseline을 제외한 구조 유효
sample 23개가 모두 구체 원인을 잃은 `Original entry precondition recheck was unknown`으로 분류됐다.
명시적 P가 없는 entry에서 `ContractInputShape.RefinementObligationsAsync`가 nullable `null`로 실패하면
호출부가 direct membership 경로를 포기하고 전체 heap P recheck로 내려가는 것이 관찰된 직접 원인이다.
이번 slice는 benchmark 이름·값 분기 없이 candidate 수집, cache collision, carrier source resolve,
resolved carrier AST 추출 및 reducer 단계의 실패를 구조화해 정확히 보고하고, 일반 recursive datatype과
finite map 안의 subset/newtype concrete membership이 기존 PE + bounded quantifier unrolling 경로에서
결정되게 한다. 변경은 위 10단계 파일에 한정하고 actual `mv` 및 `/workspace/dafnyutils`는 실행하거나
수정하지 않으며 plan 상태는 `in-progress`로 유지한다.

## 2026-09-14 구현 중단과 세부 재계획

사용자 요청에 따라 진행 중인 step 10 구현과 actual `mv` r12 준비를 중단했다. 중단 시점의
`ContractExpressionReducerTests`는 10개 중 7개가 통과했고, 새 recursive datatype + finite map
세 사례가 모두 boolean literal 대신 `Residual`로 남았다. production build는 성공했지만 이
결과만으로 전역 PE 의미 변경이나 pattern P 통합을 승인하지 않는다.

### A. 현재 hunk 분류와 진단 안정화

재개할 때 먼저 다음 미완성 파일의 diff와 실패 결과를 로컬 checkpoint로 기록했다. 이 raw
checkpoint는 사용자 요청에 따라 이후 삭제했고 Git에는 보존하지 않는다.

- `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs`
- `Source/DafnyCore/ContractTesting/ContractReductionResult.cs`
- `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs`
- `Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs`
- `Source/DafnyCore.Test/ContractExpressionReducerTests.cs`
- `Source/DafnyTestGeneration/ContractTesting/ContractTypeShapeGenerator.cs`
- `Source/DafnyTestGeneration/ContractTesting/ContractInputGenerator.cs`
- `Source/DafnyTestGeneration.Test/ContractPatternTests.cs`

그 뒤 hunk를 `A 유지`, `B로 이동`, `폐기`로 분류한다. `Complete`/`Unavailable`/`Failure`, nested
value path, carrier parse/resolve/extraction/reduction 진단은 A에 둔다. datatype/map/recursive
inline, `NonNullTypeDecl` 제외, nested refinement 수집과 membership 승인 정책은 A에서 제거하고
B/C에서 다시 검토한다. 다른 작업의 변경이 같은 파일에 있으므로 `git reset`, `git checkout`,
`git restore`로 파일 전체를 되돌리지 않는다.

A의 의미는 진단만 바꾸는 것이다. 직접 평가가 적용되지 않으면 기존 whole-P SMT fallback을
계속 실행하면서 실패 단계와 fallback 결과를 함께 남긴다. 기존 fixed/solver/symbolic 전략과
no-refinement fast path의 승인·거부 집합은 바꾸지 않는다. carrier와 cache의 내부 오류를
성공으로 계수하지 않는다. focused 진단, 전체 Contract, 직렬 build가 통과해야 B로 이동한다.

### B. 계약 전용 닫힌 구체식 평가 프로필

`ContractExpressionReducer`를 facade로 유지하고, 내부 PE engine에 기본값이 꺼진 명시적 평가
정책을 전달한다. 기본 partial-eval rewriter는 기존 정책을 사용한다. 계약 전용
`ContractConcrete` 정책은 다음 조건을 모두 만족할 때만 새 fold를 활성화한다.

1. datatype 값의 모든 인자가 닫힌 concrete value이고 resolved constructor identity가 같다.
2. destructor는 현재 constructor에 속할 때만 projection하고, discriminator는 query-field
   identity로 계산한다. 잘못된 destructor는 residual이다.
3. map lookup과 `Keys`는 완전히 concrete finite map/key일 때만 계산한다. 없는 key, 함수값,
   symbolic key는 residual이다. duplicate key의 Dafny overwrite 의미를 보존한다.
4. recursive function은 모든 실제 인자가 닫혀 있고 call-key cycle 및 inline depth 제한을
   통과할 때만 펼친다. recursive term을 가진 quantifier도 domain이 concrete finite이고 누적
   quantifier instance limit 안일 때만 펼친다.
5. node, quantifier, depth 한도 중 하나라도 소진되면 승인하지 않고 residual과 정확 이유를
   반환한다. opaque/reveal 경계를 평가 편의를 위해 넓히지 않는다.

`ContractReductionResult`는 원본 resolved 식, concrete substitution만 적용한 보존 식, reduced
식을 구분한다. `True`/`False`만 지역 판정으로 사용하고 residual SMT에는 reduced 식이 아니라
보존한 concrete-substituted 원 membership을 보낸다. 예산은 호출자가
`ContractReductionBudget`으로 명시하며 별도 magic depth 상수를 두지 않는다.

B gate의 필수 일반 테스트는 valid/invalid/nested recursive datatype+finite map, 다른 constructor
사이 equality, shared destructor의 올바른 formal index, wrong-constructor destructor, map absent
key와 duplicate key, finite/over-budget quantifier, direct/self recursion cycle, opaque/reads/bodyless
residual, 기본 PE profile 무변경과 reducer/SMT 독립 대조다. 중단 시점의 세 실패가 기대값을
만족하고 전체 DafnyCore reducer 회귀가 통과하기 전 C로 진행하지 않는다.

### C. pattern P 필터

`ContractTypeShapeGenerator`가 입력/힙 value path와 redirecting type 각 계층에서 독립 membership
의무를 수집한다. `NonNullTypeDecl`은 null, dangling reference, dynamic type과 allocation 검사를
기존 구조 단계가 막는 일반 회귀가 통과한 뒤 사용자 subset과 구분해 제외한다. no-requires
후보는 각 의무를 B로 평가하여 True cache, False reject, Residual 원 membership SMT, Failure
error로 분류한다. explicit `requires`와 참조를 포함한 custom subset은 기존 exact-heap whole-P
SMT를 유지한다. 어느 경로도 Q, 구현 출력이나 알려진 반례 조건을 P 판정에 사용하지 않는다.

C gate는 no-refinement zero-query, nested subset/newtype chain, non-null class allocation, custom
reference subset fallback, false membership, residual SMT, unknown/timeout, same-batch cache와 hash
collision을 각각 독립 fixture로 검사한다. 승인되지 않은 표본은 `inputsGenerated`에 들어가지
않고 유효 입력 0개는 `inconclusive`다.

### D. 실행/Q와 E. actual 수용 시험

D에서는 이미 구현된 internal execution, extern/bodyless contract transition, logical heap H0/Hn,
observed Q와 replay를 benchmark-independent fixed/mutant fixture로 다시 검증한다. poison extern
body marker 0, 동일 입력의 fixed pass/mutant counterexample, abstract-choice replay가 모두
통과해야 한다. P, execution, Q 중 애매한 단계는 별도 `inconclusive`로 남긴다.

E는 새 binary hash를 기록한 뒤 세 번으로 나눈다. E1 fixed-only 소표본으로 P latency와 유효
입력 생성을 확인한다. E2에서만 동일 seed·24표본 fixed/mutant population을 생성한다. E3는 생성된
population을 실행해 Q와 replay를 확인한다. E1 실패 시 E2/E3를 실행하지 않는다. fixed 반례는
harness 오류, mutant 무반례는 coverage 부족으로 분류하며 둘 다 성공으로 보고하지 않는다.
모든 실제 실행은 새 tmux session과 새 artifact directory를 사용하고 `/workspace/dafnyutils`는
계속 read-only다. benchmark 전용 PE 연산·값·패턴 조건·예산 특례는 추가하지 않는다.

2026-09-14 사용자 재개 요청을 받아 계획을 `in-progress`로 전환했다. 구현 전 read-only
instrumentation으로 다음을 확인했다.

1. `ValidForest`는 body 존재, non-opaque, revealed, reads 0, non-recursive다. 첫 residual은
   opacity가 아니라 map value의 `ApplySuffix.Resolved == DatatypeValue` 포장을 `IsLiteralLike`와
   map traversal이 재귀 정규화하지 않아 concrete map을 비구체 인자로 오판한 결과다.
2. 내부 resolved 포장을 재귀 정규화하면 reducer는 `forall key | key in {1} :: ValidTree(...)`까지
   진행한다. 이 quantifier에 기존 `TryUnrollQuantifier`를 직접 적용하면 `Leaf(7)`은 true,
   `Leaf(12)`는 false가 된다. 따라서 concrete finite domain이 이미 확인된 정확 전개 경로에서는
   recursive logical body의 blanket guard를 제거한다. lower-bound peel과 finite-support heuristic의
   재귀 guard는 유지한다.
3. `Branch([Leaf(7)])`은 바깥 전개 뒤 `forall i | 0 <= i < 1 :: ValidTree([Leaf(7)][i])`가 남고,
   동일한 직접 유한 전개로 true가 된다. 단일 traversal에서는 현재 `BuildInlineCallCycleKey`가
   모든 datatype을 `x`로 표현해 `Branch(...)`와 `Leaf(...)`를 같은 재귀 호출로 오인할 수 있으므로
   constructor declaration identity와 재귀 concrete arguments를 포함한 구조적 call key가 필요하다.

Gate B의 정확 변경은 `PartialEvaluatorVisitor`의 map display child traversal 및 concrete syntax
정규화, `PartialEvaluatorEngine`의 wrapper-insensitive literal equality/hash/inlineability와 구조적
cycle key, concrete finite quantifier 전개 정책, 그리고 `ContractExpressionReducerTests`의 독립
회귀다. 기본 PE profile에는 새 전개 정책을 켜지 않으며 budget exhaustion, absent map key,
wrong-constructor destructor, opaque/reads/bodyless 호출은 residual로 유지한다. 구현과 독립된 검증
컨텍스트가 Gate B를 확인한 뒤에만 Gate C로 진행한다.

2026-09-14 Gate B 구현과 독립 검증을 완료했다. `ContractExpressionReducer`만 opt-in
`ContractConcrete` profile을 선택하고 기본 partial evaluator는 기존 `Default` profile을 유지한다.
구체 데이터타입, 중첩 sequence/set/multiset/map, finite-map overwrite/lookup/`Keys`, 올바른
discriminator/destructor, 구체 유한 quantifier와 재귀 호출을 계산한다. 함수와 quantifier 치환은
식 생성 전에 보수적인 node budget을 예약하며 한도 초과 시 concrete-substituted membership의
독립 clone을 residual로 되돌린다. bodyless, opaque, unrevealed, reads-dependent, 잘못된 constructor의
destructor와 absent map key는 계속 residual이다. 독립 검증은 reducer 22/22, 기본 PE와 quantifier
회귀 97/97, 전체 solution build warning/error 0, 관련 파일 whitespace와 `git diff --check` 통과를
확인했다. 전체 Dafny suite와 기존 PE의 모든 특수 materialization 경로에 대한 낮은 node-cap 조합은
실행하지 않았다.

Gate C의 재귀 refinement 통합도 일반 fixture로 고정했다. input pattern이 만든
`map[1 := Branch([Leaf(7)])]`은 `ValidForest` membership을 `True`로 줄여 SMT 질의 없이 승인되고,
`map[1 := Leaf(12)]`는 `False`로 줄여 SMT 질의 없이 거부된다. carrier reducer는
`RedirectingTypeDecl.Module`과 그 visibility scope를 사용하므로 원 선언 모듈 경계를 약화하지 않는다.
전체 DafnyTestGeneration `Contract` filter 260/260과 DafnyDriver extern execution 4/4가 통과했으며,
후자는 native extern body가 호출되지 않고 계약 전이와 최종 Q 관찰만 사용함을 포함한다. actual
`mv` 수용 시험은 이번 검증에서 실행하지 않았고 Gate E의 단계별 artifact 절차를 유지한다.

### Gate C 추가 범위 명세 — r13 cross-module refinement carrier

r13의 `Refinement CarrierResolve`는 P 판정 전 단계에서 imported datatype의 source-level
constructor 이름을 찾지 못했다. 기존 step 10의 carrier 작업을 아래 두 구현/테스트 파일로
구체화한다. `CollectRefinementLayers`가 resolved expected type으로 이미 검사한 shape를 버리고
원본 JSON value의 local constructor spelling을 `ContractModelCodec.ToDafny`에 그대로 보내는
것이 원인이다. non-open import가 있는 진입점에서는 이 spelling이 lexical scope에 없다.

| 파일·심볼 | 변경과 필요성 | 보존 범위·검증 |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractTypeShapeGenerator.cs`: `ContractShapeValue`, `ConcreteValue`, `Shapes`, `CollectRefinementLayers` | shape에 선택된 `DatatypeCtor` identity를 보존한다. carrier 생성 직전에 shape의 datatype fields, sequence/set/multiset elements, map key/value를 재귀 순회하여 새 value의 constructor만 declaring datatype의 module-qualified 이름으로 정규화한 뒤 기존 codec을 재사용한다. 이 변경이 없으면 구조적으로 올바른 local pattern constructor도 cross-module carrier resolve에서 거부된다. | 원본 pattern/value/source snapshot, 일반 `Expression`/`Materialize`, fixed/solver heap renderer는 변경하지 않는다. 이름을 JSON spelling으로 재추측하거나 benchmark 이름으로 분기하지 않는다. |
| `Source/DafnyTestGeneration.Test/ContractPatternTests.cs`: imported refinement helper 및 두 독립 `Fact` | 두 source의 `Store`/`Client`, non-open import, `FileSystem` subset과 `Parcel` 안의 map/recursive `Tree`를 사용한다. local `Parcel.Pack`, `Tree.Branch`, `Tree.Leaf` 패턴으로 유효 값의 direct True/SMT 0회와 무효 값의 direct False/SMT 0회를 각각 고정한다. | 같은 모듈 회귀와 전체 Contract filter, 직렬 solution build, 두 파일 scoped whitespace 및 diff 검사를 실행한다. 원본 snapshot과 pattern constructor spelling 보존도 확인한다. |

소유 저장소는 Dafny이며 변경 층은 diagnostic carrier 구현과 일반 회귀 테스트다. benchmark
명세·구현·proof/evaluator/scoring·provider에는 변경이 없다. 실제 `mv`, `/workspace/dafnyutils`
수정, actual opt-in 실행과 `spec_check`는 이번 검증에서 제외한다. 새로운 dependency나 유료
provider 실행은 필요하지 않다. 계획 상태는 상위 acceptance가 남아 있어 `in-progress`를 유지한다.

검증 명령의 작업 디렉터리는 `/workspace/cosyn/dafny`다.

- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --filter 'FullyQualifiedName~ContractPatternTests' --logger 'console;verbosity=minimal' -m:1`
- `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-restore --filter FullyQualifiedName~Contract --logger "console;verbosity=minimal" -m:1`
- `dotnet build Source/Dafny.sln --no-restore -m:1`
- `dotnet format whitespace Source/Dafny.sln --no-restore --include Source/DafnyTestGeneration/ContractTesting/ContractTypeShapeGenerator.cs Source/DafnyTestGeneration.Test/ContractPatternTests.cs --verify-no-changes`
- `git diff --check`

첫 cross-module fixture의 sample budget 2는 direct 판정 뒤 duplicate-sample goal을 추가해
`Assert.Single`을 실패시켰다. 각 독립 scenario를 1표본으로 제한했다. 첫 전체 Contract 명령은
sandbox의 test-runner socket 생성 거부로 실행되지 않았고, 승인된 같은 `dotnet test` 명령으로
재실행한다. 코드 실행과 독립된 검증 전에는 이번 발견을 wiki에 반영하지 않는다.

#### r13 carrier 구현과 로컬 검증 결과

`ContractShapeValue.ResolvedConstructor`는 `ConcreteValue`와 `Shapes`가 선택한 resolved
`DatatypeCtor`를 보존한다. `QualifyConstructors`는 해당 identity의
`EnclosingDatatype.FullDafnyName`과 constructor `Name`을 조합하고 nested value를 새 record로
정규화한다. `CollectRefinementLayers`는 그 새 value만 기존 codec에 넘긴다. 원본 JSON의 local
이름, source snapshot, symbolic shape 식과 materialization 결과는 그대로다.

`ImportedRefinementCarrierAcceptsResolvedNestedConstructors`와
`ImportedRefinementCarrierRejectsResolvedNestedConstructors`는 서로 독립된 두 `Fact`이며,
공통 fixture helper를 사용한다. non-open import 진입점에서 local pattern constructor만 지정한
중첩 `Parcel -> map -> Branch -> seq -> Leaf`의 7은 direct True로 승인되어 queries 0개이고,
12는 direct False로 거부되어 SMT 0회다.

검증한 기준은 Dafny HEAD `336ae4ce66176cf8360d107894d5a4ad5a7a3a2d` 위의 기존 dirty tree와
이번 두 C# 파일 및 계획 기록 변경이다. .NET SDK는 `8.0.131`이다. 위 명령 중
`ContractPatternTests` filter는 53/53 통과했고, 두 `Fact`로 분리한 최종 tree의 전체 `Contract`
filter는 262/262 통과했다(1분 24초). `dotnet build Source/Dafny.sln --no-restore -m:1`은 29초에
warning/error 0으로 성공했다. 두 C# 파일 scoped whitespace 검사는 workspace-load warning만
출력하고 exit 0이었으며 최종 `git diff --check`도 통과했다.

전체 Dafny suite, actual `mv` opt-in, provider 실행, `spec_check`는 실행하지 않았다.
`/workspace/dafnyutils`와 benchmark source는 변경하지 않았다. 독립 검증은 상위 작업자가
별도 context로 수행할 다음 단계이며, 그 전에는 wiki를 갱신하지 않는다. 현재 이 slice의
구현/요청된 로컬 검증은 완료했지만 상위 Gate E acceptance는 남아 있으므로 계획은
`in-progress`를 유지한다.

#### r13 carrier 독립 검증과 배포 바이너리

구현 대화와 분리된 검증 context가 production diff와 요구사항을 다시 검사했다. cross-module
valid/invalid 및 같은 recursive-forest focused 회귀 4/4, 관련 reducer 6/6,
`ContractPatternTests` 53/53, `ContractExpressionReducerTests` 22/22, 전체 DafnyTestGeneration
`Contract` 262/262, 기본 partial evaluator와 bounded-quantifier 97/97, DafnyDriver `Contract`
4/4가 통과했다. solution build는 warning/error 0이었고 changed-file whitespace와
`git diff --check`도 통과했다. raw request/source/pattern 불변, 모든 collection/datatype 층의
재귀 constructor qualification, `ContractConcrete` profile 격리와 benchmark-specific 분기 부재를
코드에서 별도로 확인했다. blocking/non-blocking 결함은 발견하지 못했다.

그 뒤 `/workspace/cosyn`에서 `make build-dafny`를 실행해 31.40초에 warning/error 0으로
`Binaries`를 갱신했다. 버전은
`4.11.1+336ae4ce66176cf8360d107894d5a4ad5a7a3a2d`이며 SHA-256은 `Dafny`
`5898a1abe985fb83f138614c5c51dda1d6e03662d49d6f96f3ca7ac852440a3a`, `Dafny.dll`
`997f9023f7e01640fa653ff1da024c8067e74e9c9169f4b1e1d49d459c0525cb`, `DafnyCore.dll`
`d8a663de0bf23d03c046df384c6e4021385a00f9b5a713b44c9ef60e11cad802`,
`DafnyTestGeneration.dll`
`3e345fb9078d440ff7ed46589ebac5256acc35b3b4d71993908c433d09c8a8dd`다. 이 단계에서도
actual `mv`, provider와 `spec_check`는 실행하지 않았다.

### Gate C 추가 범위 명세 — r14 cross-module residual SMT query site

상위 E1 r14에서 constructor-qualified carrier는 정상 해석됐지만, 실제
`BenchWorld.FileSystem` constraint는 계약 전용 reducer의 bounded 단면을 넘어 residual로 남았다.
현재 `ContractInputGenerator`는 이 resolved residual을 항상 entry source의
`MvCore.RunCore` 앞에 삽입한다. `Printer.ExprToString`이 원 선언 모듈에서는 유효한 지역 이름
`ValidInodeFileSystemData`, `InodeFileSystemData`, `InodeTree` 등을 보존하므로, fallback query가
entry 모듈에서 resolve error가 되어 P를 `unknown`으로 만든다. 이는 reducer 실패나 constructor
carrier 실패와 구별되는 residual-query lexical-context 결함이다.

| 파일·심볼 | 변경과 필요성 | 보존 범위·검증 |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractTypeShapeGenerator.cs`: `ContractRefinementCandidate`, `ContractRefinementObligation`, `TryCarrierTypes` | 각 user refinement layer에서 resolved `RedirectingTypeDecl.Origin.Uri`가 가리키는 supplied source와 원 선언 시작 위치를 query site로 보존한다. cache canonical은 기존 type/value/constraint hash를 유지한다. | system/미공급 source는 성공으로 추정하지 않고 fail closed한다. direct True/False와 constructor normalization은 변경하지 않는다. |
| `Source/DafnyTestGeneration/ContractTesting/ContractInputGenerator.cs`: residual branch, `RefinementQuerySource` | residual membership method를 entry source가 아니라 obligation의 원 선언 source에서 선언 시작 위치에 삽입하고, `ContractSolver`에 동일 원본 snapshot 집합과 정확 source path를 넘긴다. reference-free closed membership이므로 heap diagnostic edit에 의존하지 않는다. | reducer가 `Residual`인 경우만 변경한다. explicit entry `requires`, whole-heap fallback, implementation/Q/replay 및 solver 판정은 변경하지 않는다. |
| `Source/DafnyTestGeneration.Test/ContractPatternTests.cs`: imported residual refinement 회귀 | non-open `Store`/`Client` fixture에서 선언 모듈 지역 predicate와 datatype을 쓰고, unbounded quantifier로 direct reducer가 residual을 유지하게 한 뒤 SMT 1회가 유효 표본을 승인하는 한 정상 시나리오를 검사한다. | 기존 imported direct True/False 두 Fact, same-module residual, raw source/pattern 불변과 전체 회귀를 함께 검사한다. benchmark 이름은 사용하지 않는다. |

구현 전 위험은 source position과 snapshot identity다. query site는 heap source-edit가 적용되기 전
original `SourceSnapshots`의 declaration token 위치와 짝지어 사용한다. closed reference-free
membership에는 diagnostic heap constructor/visibility edit가 필요하지 않으며, query source와
snapshot path를 섞지 않는다. type declaration이 supplied immutable snapshot에서 정확히 하나
확인되지 않으면 `Failure`로 보고한다.

검증 작업 디렉터리는 `/workspace/cosyn/dafny`다. focused imported residual test와 기존 imported
direct 2개, 전체 `ContractPatternTests`, 전체 DafnyTestGeneration `Contract`, 관련 reducer/default
PE 회귀, DafnyDriver `Contract`, solution build, changed-file whitespace와 `git diff --check`를
실행한다. 독립 검증 전 wiki를 갱신하지 않는다. actual `mv`, provider, `/workspace/dafnyutils`
수정과 `spec_check`는 이 구현 검증에서 제외한다. plan은 `in-progress`다.

2026-09-14 사용자 범위 조정에 따라 이 계획의 현재 완료 경계는 pattern candidate의 resolved
구조/타입 검사와 direct reduction/residual SMT를 통한 원 precondition 자동 판정까지다. 실제
implementation, Q/postcondition, replay와 상위 Gate E2/E3는 후속 범위로 남기고 실행하지 않는다.
`spec_check`도 제외한다. 일반 회귀와 fixed-only actual E1에서 P를 만족한 입력이 하나 이상
보존되는 것을 이번 작업의 최종 acceptance로 사용한다.

첫 구현의 imported residual 집중 회귀는 1/1 통과했지만 `ContractPatternTests` 전체는 53/54로
실패했다. `NoRequiresComplexRefinementUsesDirectMembershipQueries`의 중첩 `nat`는 system 선언이라
supplied source query site가 없는데, candidate 수집 시점에 site를 필수화하여 SMT가 필요 없는
direct True 판정까지 `CandidateCollection` failure로 바꾼 것이 원인이다. query site는 obligation의
선택 필드로 유지하고 direct True/False에는 요구하지 않는다. 오직 reduction decision이
`Residual`일 때 exact supplied site가 없으면 Error로 fail closed하도록 범위를 바로잡은 뒤 focused와
전체 회귀를 재실행한다. 이 보정도 residual fallback 이외의 승인 의미를 바꾸지 않는다.

선택 query-site 보정 후 새 imported residual 회귀 1/1과 기존 nested `nat` direct 회귀 1/1이
각각 통과했다. `ContractPatternTests` 전체도 최종 54/54로 통과했다. 새 회귀는 Store-local
predicate/datatype과 non-open Client import를 사용하며 reduction decision `Residual`, 정확히 한
SMT query의 `Unsat`, 승인된 입력 하나와 raw source/pattern 불변을 확인한다. 다음 단계는 구현
대화와 분리된 전체 독립 검증이며 그 전에는 wiki와 배포 바이너리를 갱신하지 않는다.

독립 검증은 기능 회귀를 모두 통과한 뒤 source-position 감사에서 차단 결함을 발견했다.
`Token.pos`는 scanner의 UTF-8 byte offset인데 query site가 이를 `string.Insert`의 UTF-16 character
index로 직접 사용한다. ASCII-only 새 회귀는 이를 드러내지 못하며 선언 앞에 비ASCII 문자가 있으면
삽입 위치가 어긋나거나 범위 밖으로 거부된다. query site 필드를 byte position으로 명시하고,
path+SHA가 일치하는 source content의 UTF-8 prefix를 이용해 정확한 character index로 변환한 뒤에만
삽입한다. byte offset이 전체 UTF-8 길이를 넘거나 character boundary와 일치하지 않으면 residual을
Error로 fail closed한다. `DefinitionAnalysis.CharacterIndexForByteOffset`은 동일 변환을 하지만
private라 직접 재사용할 수 없으므로 계약 경계에 좁은 변환 helper와 근거 주석을 둔다. 기존 imported
residual fixture의 refinement 선언 앞에 한글 주석을 추가해 이 경계를 재현한다. 이 변경은
`ContractInputGenerator.cs`와 해당 테스트에 한정하며 다시 독립 검증한다.

비ASCII 집중 회귀와 nested `nat` direct 회귀는 통과했지만 첫 전체 Pattern 재검증은 52/54였다.
기존 same-file default-module residual 두 사례의 subset declaration byte position이 0인데, 새 변환
helper가 nonempty source의 offset 0을 첫 문자와 비교한 뒤 boundary가 아니라고 거부했다.
`bytePosition == 0`을 character index 0으로 먼저 승인하고 기존 out-of-range/mid-scalar 거부를
유지한다. `ResidualRefinementMembershipFallsBackToSolver`와
`ExhaustedRefinementReductionFallsBackToSolver`를 UTF-8 집중 회귀와 함께 재실행한 뒤 전체 Pattern을
다시 확인한다.

offset 0을 character index 0으로 처리한 최종 helper에서 imported 비ASCII residual 1/1, nested
`nat` direct 1/1, same-module residual 1/1, budget-exhausted residual 1/1과
`ContractPatternTests` 전체 54/54가 통과했다. 첫 same-module 집중 실행 한 번은 test runner의
local socket이 sandbox에서 거부되어 테스트가 시작되지 않았고, 승인된 동일 명령으로 재실행해
통과했다. 다음 단계는 이전 차단 결함을 보고한 독립 검증 context가 UTF-8 boundary와 현재 사용자
범위인 P 판정 회귀를 다시 확인하는 것이다.

최종 독립 재검증에서 결함은 발견되지 않았다. reflection boundary probe는 offset 0, 한글과
astral scalar의 정확한 UTF-8 경계를 올바른 UTF-16 index로 바꾸고 negative/out-of-range,
mid-scalar, invalid high/low surrogate, null/wrong path/SHA/duplicate source를 모두 거부함을 확인했다.
P focused 6/6, `ContractPatternTests` 54/54, reducer 22/22, 기본 PE+unroll 97/97, solution build
warning/error 0, 세 관련 파일 whitespace와 `git diff --check`가 통과했다. production diff에
benchmark 이름/분기는 없었다. 사용자 범위에 따라 implementation/Q/replay, Driver 실행 회귀,
actual `mv`, `spec_check`와 provider는 이 독립 검증에서 실행하지 않았다. 다음 단계는 배포
바이너리를 갱신하고 fixed-only actual E1에서 자동 P 승인을 확인하는 것이다.

CoSyn root의 `make build-dafny`로 배포 바이너리를 갱신했으며 solution build는 warning/error
0으로 통과했다. 패키지 버전은 `4.11.1+336ae4ce66176cf8360d107894d5a4ad5a7a3a2d`,
`DafnyTestGeneration.dll` SHA-256은
`7b0f68346bc5437348baa0d98e21844f3fc1285fb29747f26f2fd494c8436b4c`다.

fixed `MvCore.RunCore` P-only E1 r17은 18-source snapshot, seed `332160582228`, 3표본,
60초 제한에서 34.80초에 status `passed`, 유효 입력 2개, `unknown=0`, `unsupported=0`,
`patternPreconditionFalse=0`으로 끝났다. 첫 입력의 cross-module `BenchWorld.FileSystem`
membership은 원 선언 query site에서 SMT 1회 `Unsat`로 승인됐고, 두 번째 입력은 동일한 5개
obligation cache를 재사용해 SMT 0회로 승인됐다. pytest는 `1 passed, 9 deselected`, 종료 코드
0이었다. raw artifact는 검증 당시 로컬로 생성했지만 사용자 요청에 따라 삭제했고 Git에는
보존하지 않는다.
사용자 범위에 따라 implementation/Q/replay, E2/E3, `spec_check`와 provider는 실행하지 않았다.
원본 P 자동 판정 수용 기준이 충족되어 계획을 `done`으로 닫는다.
