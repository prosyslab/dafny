# 범용 Dafny 입력 패턴 샘플러와 논리 힙 계약 실행

- 상태: in-progress
- 작성일/갱신일: 2026-09-13
- 소유 저장소: Dafny (`/workspace/cosyn/dafny`).
- 기준 커밋: `1eb9fc5fa2661483de151ff85b21eed0b695878a`의 기존 dirty 작업 트리.
- 상위 계획: [CoSyn 계획](../../plan/2026-09-13-pattern-guided-contract-pbt.md)

## 목표와 비목표

해결된 일반 Dafny 타입에 대해 타입 검사된 pattern AST를 유한 generator로 컴파일하고,
재현 가능한 random 후보를 원본 entry P로 필터링한다. 희소 P에서는 지정 leaf만 P-only SMT로
보정한다. 유효 후보의 내부 구현을 실행하면서 bodyless/extern 계약 전이를 논리 힙에
누적하고 원본 entry Q를 최종 판정한다.

DSL과 엔진에 `mv`, coreutils, path, filesystem, inode 또는 `BenchIO` 전용 구문·분기·값을
추가하지 않는다. 실제 mv는 이 API의 소비자 수용 시험일 뿐이다. 무한 값 전체 탐색,
co-datatype/function value, 경로 완전성 및 전역 증명은 비목표다. 미지원 영역은 구조화된
frontier로 남긴다.

## 수용 기준

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
