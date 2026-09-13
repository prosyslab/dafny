# Expecto 부분 평가 강화와 잔여 계약 제약 풀이

- 상태: done
- 작성일/갱신일: 2026-09-12
- 소유 저장소: Dafny (`cosyn/dafny` 체크아웃).
- 기준 커밋: `1eb9fc5fa2661483de151ff85b21eed0b695878a`, 로컬 `origin/expecto`와 동일한 detached HEAD.
- 범위: 한국어 계획 작성 후 2026-09-12 사용자의 `구현 진행`으로 구현·로컬 검증 승인. 아래 과거 미실행 기록과 새 실행 기록을 구별한다.
- 구현 기록: [통합 구현 기록](../../../plan/2026-09-12-hybrid-contract-testing-implementation.md). G0부터 실제 실행·원식 판정을 연결한다.
- 상위 요구·수용 기준: [CoSyn 주 계획](../../plan/2026-09-12-topdown-hybrid-contract-testing.md).
- 통합·작업 기록: [통합 계획](../../../plan/2026-09-12-topdown-hybrid-testing-design.md).
- 입력 생성 후속 보완: [후속 기록](../../../plan/2026-09-12-contract-input-generation-design.md). 임의 Dafny 선언의 타입/힙 생성·구현 경로 탐색을 기본 경로로 재정리하고 독립 재검토를 마쳤다.

## 1. 목표와 비목표

구체 입력으로 계약식을 단순화하고, 남은 제약을 기존 Dafny→Boogie→Z3 경로로 풀어
부분 프로그램의 테스트에 사용할 출력·상태·반례를 만든다.
실행 가능한 본문은 C# 대상 코드로 실제 실행하며, 본문 없는 선언만 계약 모델로 연결한다.
반례의 유효성은 원래 계약과 구체 실행을 이용해 다시 확인한다.

일반적인 Dafny 명세를 모두 결정하는 솔버, 별도 언어 해석기, Python SMT 인코더,
무제한 한정자 전개, 검증 정책 변경, 벤치마크 전용 오류 규칙은 비목표다.
기본 적용 대상은 임의의 함수/메서드 선언과 호출 그래프다. 타입 인자·인자·수신 객체·
유한 힙을 Dafny 구조에서 생성하며 별도 `ValidInput` 명세나 프로그램별 생성기를 요구하지 않는다.
유틸리티/CLI/외부 파일시스템은 선택적 응용이다. 일반 객체·별칭·프레임까지 범용 회귀로 검사한다.
사용자의 두 사례는 응용 회귀로 보존하며, 모든 구문·무한 상태 공간의 자동 결정은 보장하지 않는다.

## 2. 조사 근거와 기존 구현

`AGENTS.md`, `CLAUDE.md`, 부모 `cosyn/AGENTS.md`와 통합 지침을 읽었다.
기존 `plan/`·`wiki/`는 없었다. 새 코드보다 기존 전처리·번역·모델 복원을 우선 조사했다.

| 소스·심볼 | 현재 관찰 |
| --- | --- |
| `Source/DafnyCore/Rewriters/PartialEvaluator.cs::PostResolveIntermediate` | `--partial-eval-entry`가 지정한 선언을 찾고 엔진 호출 |
| `PartialEvaluatorEngine.cs::PartialEvalEntry` | 본문이 있는 함수·메서드의 본문을 제자리에서 수정. 본문 없는 선언의 계약을 이 진입점에서 평가하지 않음 |
| 같은 파일의 `DefaultPartialEvalUnrollCap`, `TryInlineCall` | 기본 전개 한도 100. 본문/깊이, 가시성, opaque, `reads` 등 인라이닝 조건이 있음 |
| `PartialEvaluatorVisitor.cs::SimplifyQuantifierExpr` 및 존재·유한 지지집합 처리 | 일부 산술·점 대입·유한 시퀀스/문자열·유한 지지집합의 한정식을 이미 처리 |
| `QuantifierBounds.cs::TryUnrollQuantifier` | 유한 도메인 및 단순 정수 범위 전파. 전개 상한 초과 시 호출 모드에 따라 잔여 한정자 보존 또는 미변환 |
| `UnrollBoundedQuantifiersRewriter.cs::UnrollEngine.Rewrite` | 함수·메서드 분기에는 `Body: not null` 조건이 있음. 그 안에서는 계약·프레임도 처리. 별도 iterator 경로가 있음 |
| `ExpressionRewriteUtil.cs`, `Substituter` | 해결된 AST의 재작성·변수 치환을 재사용할 수 있음. 원본을 직접 바꾸는 현재 도구를 새 진단 경로에 그대로 적용하지 않도록 주의 |
| `Source/DafnyCore/Options/CommonOptionBag.cs` | `--partial-eval-entry`, `--partial-eval-inline-depth`, `--unroll-bounded-quantifiers` 옵션 |
| `Source/Scripts/RewriterAstPrinter.cs` | `print-after-partial-eval-and-unroll`로 변환 결과 조사 가능 |
| `Source/DafnyTestGeneration/ProgramModifier.cs::RemoveChecks` | 모든 Boogie 단언을 가정으로, 사후조건을 `free ensures`로 변환. 계약 위반 질의에는 그대로 사용 불가 |
| `Source/DafnyTestGeneration/{TestGenerator,ProgramModification,TestMethod}.cs` | 구현 CFG의 경로/블록 입력 생성·솔버 실행·값 복원 기반. 사후조건 경우를 입력으로 투영하는 생성기는 아님. 용도별 변환을 분리해 재사용 |
| `TestMethod.cs::{ExtractVariable,ExtractInputs}`와 `DafnyModel.AssignConcretePrimitiveValues` | 첫 모델/상태·보충값을 이용하고 배열 입력은 미지원. 일부 생성 `expect`가 있어도 전체 모델·프레임 재검사를 대체하지 않음 |
| `ProgramModifier.cs::AddAxioms`와 `GenerateTestsCommand.SequenceLengthLimit` | 모든 시퀀스에 대한 전역 길이 공리를 넣음. 신규 생성 범위는 특정 입력의 지역 제약으로 별도 구성 |
| `Source/DafnyCore/Rewriters/ExpectContracts.cs::{CreateContractExpectStatement,MakeContractCheckingBody,PostVerification}` | extern 대상에 전제/본문/사후 `expect` 래퍼를 만들고 호출을 재지정한다. `ExpressionTester.UsesSpecFeatures`인 조항은 경고 후 `expect true`로 대체하므로 ghost 명세 판정기로 사용할 수 없음 |
| `Source/DafnyCore/Rewriters/RewriterCollection.cs`, `DafnyOptions.cs::TestContracts`, `Options/CommonOptionBag.cs::{TestAssumptions,TestAssumptionsMode}` | 기존 `--test-assumptions`와 legacy 계약 테스트 모드의 등록·전달 경계. 새 `test-contracts` 명령과 이름/옵션 혼동 및 중복 래핑을 방지해야 함 |
| `Source/DafnyCore/CounterExampleGeneration/DafnyModel.cs` | 모델의 부분값을 복원·보충. 보충값은 제약 재검사를 거쳐야 함 |
| `Source/DafnyDriver/Commands/GenerateTestsCommand.cs`, `Source/DafnyCore/Verifier/BoogieGenerator.cs` | CLI 연결과 기존 번역 경계. 신규 전용 명령은 이 구성에 맞춰 추가 |
| `Source/DafnyTestGeneration/TestGenerator.cs::AddVerificationGoalsToEntryPoints`, `FirstPass.cs`, `DafnyInfo.cs` | 기존 `testEntry`·접근성·receiver·타입 지원 제약이 있음. 새 명령은 임의 심볼/타입 인스턴스의 진단용 진입점을 만들고 미지원을 보고해야 함 |
| `Source/DafnyTestGeneration/Inlining/InliningTranslator.cs::{ShouldProcessForInlining,TranslateForFutureInlining}` | `testEntry`/`testInline` 대상 중심이며 opaque 처리도 포함. 본문 방출/인라이닝 기법은 조사하되 가시성 변경까지 일괄 재사용하지 않음 |
| `Source/DafnyCore/Verifier/BoogieGenerator.cs::EmitImplementation`, `Statements/BoogieGenerator.TrLoop.cs::TrLoop` | 구현 방출 조건·검증용 루프/불변식 번역 경계. 계약 없는 실제 보조 본문과 반복 접두 경로가 질의에 남는지 별도 확보해야 함 |
| `Source/DafnyTestGeneration/{BlockBasedModifier,PathBasedModifier,ProgramModification}.cs` | 기존 Boogie 프로그램에 블록/경로 목표를 붙여 모델을 얻는다. 보존된 프로그램의 대입/가드 제약은 재사용 가능하나 호출 요약/불변식·havoc 추상화 뒤 모델이 실제 실행을 재현한다는 보장은 없음 |

현재 기능이 사용자 사례를 자동 탐지한다는 테스트 결과는 없다.
상태를 가진 IO 관찰과 명세만 있는 호출의 다음 상태는 단순 함수 인라이닝으로 해결되지 않는다.

## 3. 전체 처리 구조

```text
계약 검사 요청(소스·선언 심볼·구체 타입 인자·단위/진입점 모드·예산)
  → 해석된 원본 프로그램 고정
  → 진단 진입점 생성 + 타입/유한 힙 기본 입력 + 구현 경로/명세 경우 목표
  → 필요한 실제 본문/반복 접두 경로의 제한적 확장 + 미정 값의 잔여 SMT 풀이
  → 구체화·상태 실현·실제 초기 관찰의 적합성/경우 재검사
  → 진단용 실행 사본 / 독립 원본 계약식 보존
  → 실제 C# 본문 실행 ↔ 미구현 호출용 계약 런타임 ↔ 잔여 SMT 세션
  → 관찰 결과를 원본 사후조건·프레임과 대조
  → 모델·경로·반례 재검사
  → 구조화 결과와 재실행 산출물
```

신규 명령 이름은 `dafny test-contracts`를 제안한다. 아직 존재하는 명령이 아니다.
외부 요청·응답은 버전 있는 JSON이며 CoSyn 모델과 C# 직렬화 모델의 계약 테스트를 둔다.
기존 `generate-tests` 모드의 기본 의미는 변경하지 않는다.
새 명령은 원 소스에 `{:testEntry}`/`{:testInline}`를 추가하도록 요구하지 않는다.
진단 사본의 래퍼·원래 선언/Boogie 구현 대응·타입 인스턴스를 엔진이 관리한다.
독립 명령은 CoSyn이나 벤치마크 없이 일반 Dafny 소스와 지원되는 형식 인자만으로 사용할 수 있어야 한다.

### 기존 계약 래퍼와의 공존

`ExpectContracts`의 호출 위치 보존·래퍼 구성·`CallRedirector` 사용 방식은 기존 부품으로
재사용할 수 있는 부분을 먼저 확인한다. 그러나 `CreateContractExpectStatement`의 ghost→
`expect true` 경로는 새 판정기에 재사용하지 않는다. 새 `ContractHarnessBuilder`는 원본
계약 목록을 별도 보존하고 실행 가능한 조항과 ghost/잔여 조항 모두에 판정 결과를 연결한다.
컴파일할 수 없는 조항은 reducer/SMT와 실제 관찰 상태로 검사하거나 명시적 미확정으로 남긴다.

기존 `--test-assumptions`/legacy 모드와 `ExpectContracts`의 기존 의미는 유지한다.
새 `test-contracts`는 `DafnyOptions.TestContracts=None`인 독립 계측 경로를 사용하며,
동시에 기존 계약 래퍼 모드를 요청하면 설정 오류로 거절한다. 사용자 옵션을 조용히 무시하지 않는다.
원식 조항이 생략된 실행 성공은 계약 검사 성공이 아니다. 기존 extern 래퍼 회귀와 새 명령의
ghost 조항 실패/미확정·중복 옵션 거절을 모두 검사한다.

검사 실행 호스트는 기존 `DafnyTestGeneration` 프로젝트의 부품을 사용한다.
새 테스트용 C# 브리지는 계측된 메서드 호출에서 값·힙을 전달하고, 검사 호스트는
시험 단위의 SMT 세션에서 일관된 출력·다음 상태를 돌려준다.
프로세스 간 메시지는 결과용 채널과 후보의 stdout/stderr를 분리한다.
취소·시간 제한은 호스트와 실행 자식 프로세스 트리에 함께 적용한다.
별도 외부 서비스나 유료 제공자는 필요하지 않다.

### 어셈블리와 컴파일·실행 연결

`PartialEvaluatorEngine`과 `QuantifierBounds`는 Core 내부 타입이므로 다른 어셈블리에서
직접 호출하는 설계를 사용하지 않는다. Core에 공개된 작은
`ContractExpressionReducer` 파사드와 결과 타입을 두고 내부 엔진을 감싼다.
전체 내부 API를 공개하거나 새 friend assembly로 접근 제한을 우회하지 않는다.

`DafnyDriver`가 이미 `DafnyTestGeneration`을 참조하므로 역방향 참조를 만들지 않는다.
테스트 생성 프로젝트에는 `IContractProgramCompiler` 인터페이스만 두고, 새 Driver 명령이
Driver 소유 구현을 주입한다. **프로세스 경계에는 AST 객체를 전달하지 않는다.**
`ContractTestModels.cs`의 버전 있는 컴파일 요청은 불변 소스 스냅샷과 파일별 해시,
include 파일 목록, 선언의 정규 심볼·위치, 구체 타입 인자, 진단 계측 요청과 컴파일 옵션,
허용된 외부 의존 파일의 경로/해시 목록, 출력 디렉토리와 기한을 담는다.
작업자는 스냅샷 해시를 확인하고 자신이 파싱/이름·타입 해석을 수행한 뒤,
`ContractCallableSelector`/`ContractHarnessBuilder`로 진단용 AST 사본·스텁·진입점을 만든다.
호스트의 해결된 AST를 직렬화할 공개 API가 있다고 가정하지 않는다. 호스트와 작업자는
동일 소스/옵션/컴파일러 버전에 결합된 선언 ID와 원래 토큰 위치로 대조한다. 결과에는
실행 산출물 해시와 생성 선언/계측 지점→원래 선언/위치 대응표를 반환하며 불일치를 거절한다.

작업자는 충돌하지 않는 정적 진단 메서드를 생성하고 `DafnyOptions.MainMethod`를 그
정규 이름으로 지정한다. 원래 `Main` 유무와 무관하게 선택한 함수/메서드를 호출하며,
원래 진입점을 실수로 실행하지 않도록 `SinglePassCodeGenerator.HasMain`이 선택한
심볼을 검사한다. 그 뒤 같은 작업자 안에서
`SynchronousCliCompilation.CompileDafnyProgram(program, outputPath, otherFileNames, true)`를
호출한다. `hasMain`→`callToMain` 생성→C# `OutputType=Exe`를 확인하며 라이브러리만
생성된 경우를 실행 준비 완료로 표시하지 않는다. 기존 C# 백엔드의 `CompileTargetProgram`이
사용하는 `otherFileNames`에
생성된 브리지 `.cs`와 허용된 외부 `.cs`/`.dll`을 전달한다.
브리지는 값 직렬화·로컬 메시지 교환만 수행하며 컴파일러/솔버 어셈블리에 의존하지 않는다.

`RunAfterCompile=false`로 빌드와 실행을 분리하고 명시적 임시 출력 경로의 DLL과 필요한
런타임 산출물을 확인한다. 기존 `CsharpBackend.RunTargetProgram`은 외부 `.dll`을 실행
디렉토리로 복사하므로 이를 우회하는 새 실행 경로에도 의존성 준비 단계가 필요하다.
작업자가 요청에 명시된 의존 DLL과 필요한 전이 의존 파일을 시험 전용 디렉토리에 준비하고
파일 해시/이름 충돌·누락을 검사한다. 임의 디렉토리를 검색하거나 패키지를 설치하지 않는다.
의존성을 해석할 수 없으면 구조화된 컴파일/실행 준비 오류를 반환한다.
검사 호스트가 `dotnet <시험 DLL>`을 별도 실행해 stdout/stderr와 프로토콜 채널을 수집한다.
컴파일 작업자와 시험 프로세스에 동일한 기한을 적용하고 취소 시 전체 자식 트리를 종료·회수한다.
현재 `ExecutableBackend.WaitForExit`는 무제한 대기이므로 그 함수를 취소 가능하다고 가정하지 않는다.
별도 작업자 프로세스의 수명 관리는 신규 `ContractExecutionProcess`가 담당한다.

## 4. 단계별 변경표

재개 후 일반성 보완은 기존 파일에서 처리한다. `ContractBodyExpansionResult.cs`에 해결된
사용자 선언과 충돌하지 않는 공통 이름 계열을 두고 body expander/type shape/capture/query
생성이 이를 공유한다. 임의 사용자 식별자 때문에 진단 질의가 실패하는 회귀를 추가한다.
`ContractTypeShapeGenerator`의 객체 타입 수집은 데이터타입 생성자 필드까지 원래 타입
치환·방문 집합으로 순회하여 데이터타입 안의 유한 객체도 기존 힙 생성에 포함한다.
같은 범위의 `ContractHeapFactory.ValueExpression`/참조 순회는 시퀀스·데이터타입의 중첩
참조를 원래 생성자 필드 타입에 따라 재귀적으로 검사·표현하며 누락 객체/잘못된 필드도
거절한다. 스칼라 codec에 객체 ID를 넘겨 기본값으로 채우지 않는다.
`ContractCallableSelector`/prepared descriptor/호출·선택 DTO/`ContractModelRealizer`는 명시한
진입 타입과 해결된 호출 그래프에서 얻은 구체 타입 인자를 사용한다. 같은 진입점의 본문 없는
제네릭과 한 심볼에 단일 인스턴스가 전파되는 일반 보조 호출을 처리하며 CLR 값에서 타입을
추측하지 않는다. 다형 재귀/복수 인스턴스와 보이지 않는 타입은 명시적 미지원으로 남긴다.
이에 필요한 Python `ContractCallObservation`/`ContractAbstractChoice`의 `type_arguments`와
전송·재현 테스트는 CoSyn 소유 계획에 함께 기록한다. 다중 파일 스냅샷/include는 기존 C1의
불변 소스·파일별 해시 계약대로 파싱/컴파일/위치 대응을 유지하는지 점검하고 단일 파일로
묵시적으로 축소하지 않는다. 내부 신규 객체 할당의 일반 지원은 이 변경에서 추가하지 않는다.
다중 소스 구현은 신규 `ContractSourceSnapshot.cs`의 닫힌 `IFileSystem`과 기존 native
`ProgramParser.ParseFiles`를 사용한다. 공급한 정규 파일 URI만 읽고 디스크 fallback은
허용하지 않는다. compiler worker/harness는 파일별 삽입과 원본 위치·해시를 유지하고,
heap factory/query builder/generator/solver는 변경한 질의 파일과 나머지 불변 스냅샷을
함께 전달한다. 기존 단일 문자열 질의 API는 회귀 호환을 유지한다. 여러 암시적 root,
정상 상대 include, 누락/탈출 include, 파일별 해시 불일치와 교차 파일 실제 호출을 검사한다.

생성 기한은 감독 프로세스가 작업자 시작 비용까지 포함한다. 작업자의 상대 기한만으로는
감독자가 먼저 종료하여 이미 완성한 입력을 잃을 수 있으므로, 기존 `ContractInputGenerator`
에 선택적 진행 콜백을 두고 `TestContractsCommand`가 일관된 부분 결과를 시험별 디렉토리에
원자적으로 저장한다. 시간 초과/취소 시 저장된 입력·단계별 분모를 해당 상태와 함께 돌려주고
유효한 체크포인트가 없으면 기존 빈 결과를 유지한다. 검증된 입력을 추가할 때만 저장하며
실행 예산을 연장하지 않는다. 기존 생성/CLI 테스트에서 부분 결과 보존을 확인한다.
상위 Python 감독자가 먼저 종료하는 경로는 `TestContractsCommand`의 선택적
`--generation-checkpoint` 파일 인자로 연결한다. 명시한 실행자 임시 파일을 작업자에도
전달하여 매 검증된 입력에서 원자적으로 저장한다. 인자 없는 기존 CLI는 현재 내부
체크포인트만 사용한다. 표준 출력은 여전히 최종 JSON 한 줄이며 요청 파일 옆에 임의로
산출물을 만들거나 두 감독자의 기한을 연장하지 않는다.

### A14 실행 도달/추상 선택 프로토콜 구체화 (2026-09-12)

기존 C1/C3/C4의 selector, harness, runtime, runner, 모델 DTO와 입력/경로 생성 파일에서
`entry_reachable`을 실제 상위 접두 실행으로 구현한다. `entry.reachableFrom`은 상위 선언,
`reachableReceiver`는 그 수신 객체, `reachableInvocation`(기본 0)은 선택한 실제 호출 회차다.
이 모드의 `request.inputs`는 상위 인자이며 `entry.receiver`는 허용하지 않는다. 대상 선언의
인자·수신 객체·호출 직전 힙은 실행에서 포착하고 결과의 `reachability`로 별도 보존한다.
대상 진입에서 원래 P를 검사하고 해당 호출의 반환에서 원래 Q/프레임을 검사한다.
재귀 호출은 호출 식별자로 구별하며 대상에 도달하지 못한 실행은 성공으로 보고하지 않는다.
분기가 없는 대상도 생성하도록 Core의 실제 진입 목표에 호출 회차를 부여한다. 기존
`ContractPathCandidate`에 선택적 `expectedEntry {symbol, invocation, sha256}`를 두고
실행 결과의 선택 선언·원본 해시·실제 도달 회차와 대조한다. 분기 접두도 있으면 둘 다
일치해야 한다. 외부 진입점에서 선택 대상 명세 경우를 투영하지 못하면 명시적 미지원으로
남기며, 외부 사후조건을 대상 사후조건인 것처럼 대체하지 않는다.

입력 생성이 선택한 분기 이전의 미구현 호출 모델은 `replayChoices`와 선택적인
`replayPrefix`(기본 false)로 전달한다. true일 때도 지정된 모든 접두 선택은 순서/인자/상태가
정확히 일치해야 하고, 소비한 뒤에만 새로운 후속 선택을 허용한다. 최종 반례 재실행에는
실제 전체 선택과 false를 사용한다. 기존 정확 재실행 의미는 유지한다.
중복 제거는 입력/초기 힙만 다른 미사용 존재 증인을 구별하지 않는다. 반면 실제 실행에
전달해 소비하는 하위 선택 접두가 다르면 서로 다른 실행 시험이므로 해당 선택도 키에
포함한다. 입력 개수와 실행 제안/선택 변형 수를 혼동하지 않게 산출물에 구체 요청을 보존한다.
검증은 기존 `ContractEntryTests`, `ContractExecutionTests`, `ContractInputGenerationTests`,
`ContractModelRealizerTests` 및 Python 경로/생성 회귀에 추가한다. 데이터타입 모델 복원도
기존 model codec에서 실제 SMT 생성자/필드를 읽고 전체 원래 관계를 재검사한다.
공개 비교 실패에 대한 일반 수정은 기존 `ContractScenarioExtractor`/`ContractInputGenerator`
범위에서 수행한다. 합성 가드의 부정 한 덩어리만 풀어 같은 논리합 증인에 머무르지 않도록
`&&`/`||`/함의를 원래 단락 평가 순서의 서로 배타적인 경우로 분해한다. 앞선 가드·정의 가능성은
보존한다. 목표 공급원은 기본 P를 먼저 시도한 뒤 명세/본문을 교대로 진행해 본문 목표 수가
명세 목표를 밀어내지 않게 한다. 새 프로그램별 상수·규칙·범위 변경은 없다. 다른 이름/상수를
사용하는 작은 예산 회귀로 확인하고 동일한 8개 선언·3방식·60초 예산 비교를 다시 수행한다.
같은 `ContractHeapModelRealizer`에서 힙을 읽는 본문 없는 함수도 selector의 함수 계약
descriptor를 사용한다. 함수의 결과 참조를 출력 변수로 바꾸고 실제 호출 힙에서 P/Q를
검사하며 post-heap은 입력 힙과 동일해야 한다. 현재 힙을 무시한 순수 스칼라 모델로
대체하지 않는다. 함수 reads·수신 객체·변경된 호출 힙·잘못된 상태 재실행을 모델 회귀에 추가한다.

모든 경로는 이 Dafny 저장소 기준이다. `ContractTesting/` 아래 파일과 신규 테스트는 제안이다.
기존 프로젝트를 확장하며 별도 패키지나 라이브러리를 추가하지 않는다.
**C0 → G0 → C1–C5의 기능 확대** 순서로 구현한다. G0는 아래 파일의 최소 기능을 먼저
연결하며, 단계 번호가 일반 생성기를 실제 실행/힙 관찰보다 먼저 만들라는 의미는 아니다.
일반 `ContractScenarioExtractor`/`ContractInputGenerator`는 G0 통과 전 구현하지 않는다.
G0는 일반 정수/시퀀스/데이터타입, 무계약 보조 본문, 미구현 계약 호출, 작은 객체/별칭/프레임의
수동 입력 회귀다. CLI·유틸리티 모델·외부 상태 어댑터를 사용하지 않는다.
G0의 사전 고정 입력/조합과 진행 조건은 상위 계획 8절을 따른다. 전제 일관성 `SAT`,
정상 종료 그룹 `N_Q/N_Q`의 전체 원식 참/거짓 판정, 조기 중단 그룹 `N_P/N_P`의 호출 전제
위반 판정·재현, 선언한 범용 오류본 검출·수정본 수용이 충족되어야 확대한다.
필수 조합의 미지원/미확정/생략은 0이어야 하며, 조기 중단 결과를 사후조건 검사로 세지 않는다.
실제 BenchIO/MvSpec 반복은 소유자의 공개 구성·관찰 어댑터를 갖춘 뒤의 별도 도입 조건이다.

| 단계 / 정확한 파일·심볼 | 무엇·어떻게 | 필요성 / 없으면 남는 문제 | 검증 |
| --- | --- | --- | --- |
| C1 `Source/DafnyCore/Resolver/TypeCharacteristicChecker.cs::CheckInstantiation`, `CheckTypeCharacteristicsVisitor.cs::CheckTypeInstantiation` | 기존 타입 특성/경계 검사를 작은 공개 전달 함수로 재사용하여 명시적 제네릭 인스턴스를 진단 질의 전에 검사 | 런타임 컴파일 전 잘못된 타입 인스턴스로 모델을 생성하거나 특성 규칙을 중복 구현 | 타입 특성 위반 거절·허용된 구체 제네릭 생성/실행 회귀 |
| C1 `Source/DafnyCore/AST/Grammar/{ParserNonGeneratedPart,ProgramParser}.cs::ParseType`, 기존 `ContractCallableSelector`/harness/query/type shape 파일 | 기존 파서/타입 해석으로 명시적 타입 인자를 해석하고 형식 인자/계약 사본에 치환하되 실행은 원래 제네릭 본문을 명시적 타입 인자로 호출 | 모든 제네릭 선언을 미지원으로 남기면 구체 제네릭 선택 수용 기준 미충족 | 일반 함수/메서드의 명시적 타입 인자·잘못된 타입·원본 보존·실제 실행/원식 판정 |
| C0 이 문서·`plan/INDEX.md` | 조사·소유권·실행하지 않은 검증 기록 | 구현과 계획의 상태 혼동 | 링크·인덱스·독립 검토 |
| G0 신규 `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs`; 신규 `Source/DafnyTestGeneration/ContractTesting/{ContractCallableSelector,ContractQueryBuilder,ContractSolver,ContractModelCodec,ContractHarnessBuilder,ContractHeapFactory,ContractStubRuntime,ContractTestRunner,ContractStateObserver,IContractProgramCompiler,ContractExecutionProcess}.cs`; 신규 `Source/DafnyDriver/ContractTesting/{DriverContractProgramCompiler,ContractCompilerWorker}.cs`와 `Commands/TestContractsCommand.cs` | C1–C5 최소 부분부터 연결: 일반 값/메모리 객체의 수동 입력·무계약 본문 포함 실제 실행·명세만 있는 자식·전체 `Q`. 자동 경우/경로/입력 탐색은 이후 | 도메인 어댑터가 필요한 예제만 실행하고 범용 엔진이라고 주장하게 됨 | 신규 `Source/DafnyTestGeneration.Test/ContractExecutionTests.cs`, `ContractHeapTests.cs` 및 CLI/상위 범용 사례에서 G0 진행 조건 검사 |
| C1 신규 `Source/DafnyTestGeneration/ContractTesting/ContractCallableSelector.cs`; 기존 `DafnyInfo.cs`, `FirstPass.cs`, `TestGenerator.cs::AddVerificationGoalsToEntryPoints` 재사용 경계 | 명시적 선언 심볼·구체 타입·receiver/단위/진입점 모드로 래퍼 생성. 소스에 사용자 시험 속성을 요구하지 않고 원래 선언 ID 보존 | 기존 `testEntry`·타입/접근성 필터 때문에 임의 선언 선택이 불가능 | 신규 `ContractEntryTests.cs`: 함수/메서드/수신 객체·구체 제네릭·접근 불가/미지원·원본 불변성 |
| C1 `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs::PartialEvalEntry`, `PartialEvaluatorVisitor.cs`, `UnrollBoundedQuantifiersRewriter.cs::UnrollEngine.Rewrite` | 원본을 보존하는 계약식 입력 API; 계약 방문을 본문 유무와 분리; 결과에 잔여식/소진 이유 제공 | 명세만 있는 선언과 미확정 식을 검사할 수 없음 | `PartialEvaluatorTest.cs`, `UnrollBoundedQuantifiersTest.cs`의 본문 없는 계약·원본 보존 사례 |
| C1 `Source/DafnyCore/Rewriters/QuantifierBounds.cs`, `ExpressionRewriteUtil.cs` | 명시적 치환 환경·누적 예산·의미 보존 잔여식. 기존 유한 도메인 분석 재사용 | 불완전 전개를 완전 판정으로 착각하거나 폭증 | 빈 범위·중첩/의존 경계·예산 경계·원본식 대조 |
| C1 `Source/DafnyCore/ContractTesting/ContractExpressionReducer.cs` 및 `ContractReductionResult.cs` 신규 | Core 공개 파사드·결과 타입으로 내부 전처리기를 감싸고 사본·예산·잔여식 전달 | `DafnyTestGeneration`에서 internal 엔진을 직접 호출할 수 없음 | 별도 테스트 생성 어셈블리에서의 호출·원본 AST 불변성 테스트 |
| C1/G0 `Source/DafnyCore.Test/ContractExpressionReducerTests.cs` 신규 | 공개 reducer의 원본 보존·치환·예산/잔여식·본문 없는 계약을 독립 회귀로 검사 | 내부 전처리 테스트만으로 공개 호출 경계의 의미를 보장하지 못함 | `dotnet test Source/DafnyCore.Test --filter FullyQualifiedName~ContractExpressionReducerTests` |
| C2 `Source/DafnyTestGeneration/ContractTesting/ContractTestModels.cs`, `ContractQueryBuilder.cs`, `ContractSolver.cs` 신규 | 요청/결과 DTO와 소스/계측 컴파일 요청; 전제·모델 실현·위반 질의 분리; 기존 Boogie 번역/ExecutionEngine 이용 | 실현 가능성과 적합성을 혼동하고 가정으로 오류를 가림 | `Source/DafnyTestGeneration.Test/ContractQueryTests.cs` 신규; 의도적 실패/모순/비유일 모델·빈 기능 계약의 타입/프레임 모델 분류 |
| G0/C2 `Source/DafnyTestGeneration/ContractTesting/ContractModelRealizer.cs`, `Source/DafnyTestGeneration.Test/ContractModelRealizerTests.cs` 신규; `ContractSolver.cs` | 본문 없는 호출의 원래 관계를 고정 입력에서 풀고 Boogie/DafnyModel 포착 상태의 출력값을 복원·원식 재검사 | 타입 기본값이나 임의 출력이 SMT 실현 모델로 오인될 수 있음 | 결정적/비유일/모순 관계·모델 누락·실제 관계 재검사, 기존 SMT 엔진 사용 |
| G0/C2 같은 모델 실현 파일의 부분 모델 완성 | SMT 모델이 생략한 기본 타입 값에는 타입 증인 후보를 보충하되 별도로 표시하고 전체 원래 타입/전제/사후조건을 고정 후보로 다시 검사한다. 재검사 실패는 미확정이며 출력으로 반환하지 않는다 | 기능 계약 없는 출력이 solver에서 제거되어 타입/프레임 모델조차 실현할 수 없음 | 무제약 정수 출력의 성공과 잘못된 보충값의 원식 재검사 거부. 보충을 solver의 원래 관찰값이라고 표시하지 않음 |
| C3/C4 `Source/DafnyTestGeneration/ContractTesting/ContractHeapModelRealizer.cs` 신규와 `ContractModelRealizer.cs` | 실제 호출 직전의 객체 식별자/필드 상태에서 원래 P와 modifies를 사용해 출력+호출 이후 상태를 한 모델로 선택하고 원래 Q/프레임을 재검사. partial 클래스로 기존 모델 복원 부품을 공유 | 초기 요청 힙을 호출별 old로 오인하거나 독립 출력/힙 모델을 혼합하고, 상태를 바꾸는 미구현 메서드를 실행할 수 없음 | `ContractModelRealizerTests`의 old 상태·별칭·프레임·상관관계·정확 상태 재실행; 공개 두 유한 IO 사례 실제 실행 |
| C2 `Source/DafnyTestGeneration/ContractTesting/ContractScenarioExtractor.cs`, `ContractInputModels.cs` 신규 | 해결된 AST에서 입력 의존성·정의 가능성·분기 부정·바인더/힙 시점·투영 정확도를 보존한 경우 추출; 미처리 조각도 기록 | 루트 `requires`만 보고 중첩된 오류/정상 경우를 놓침 | `Source/DafnyTestGeneration.Test/ContractScenarioTests.cs` 신규; `requires` 없음·중첩/비배타 논리합·출력 의존 가드·한정자 교차·`old` |
| C2 `Source/DafnyTestGeneration/ContractTesting/ContractInputGenerator.cs`, `ContractQueryBuilder.cs` 신규 | 사전조건 기본 입력/경우별 지역 입력 제약/선택적 전체 관계 생성 질의 분리; 공정한 목표 순회·입력별 범위·실제 입력 중복 차단 | 쉬운 SAT/가상 증인만 반복하고 모순 계약 입력을 제거함 | `Source/DafnyTestGeneration.Test/ContractInputTests.cs` 신규; 동일 입력/다른 증인·지역 상한·기한·전개 잔여식·모순 입력 유지 |
| C2 신규 `Source/DafnyCore/ContractTesting/{ContractBodyExpander,ContractBodyExpansionResult}.cs`; 기존 `Substituter`, AST 복제/재작성·`BoogieGenerator` 번역 경계 재사용 | 지원되는 실제 호출/루프/재귀를 진단 사본에서 한정 확장. 원래 대입/가드/힙 의미·정의 가능성과 frontier를 보존하고 검증용 불변식 요약으로 대체 금지 | 무계약 보조 본문의 중간값이 임의 값으로 바뀌거나 cap 밖을 실제 종료로 취급 | 신규 `ContractBodyExpansionTests.cs`: 보조 본문·루프 0/1/k회·반환/break·상한·미지원·원본 보존 |
| C2 신규 `Source/DafnyTestGeneration/ContractTesting/{ContractPathExplorer,ContractTraceModels,ContractTraceValidator}.cs`; `ContractQueryBuilder.cs`, 기존 `ProgramModification.cs`/`Utils.Translate`/Boogie CFG 재사용 | 단위/진입점 접두 경로와 목표 가드·명세 경우를 제약으로 연결; 구현/계약 모델 구분·실행 추적 매핑·후보 재실행 대조 | CFG trap의 SAT를 실제 실행 경로로 오인하며 계산된 guard의 입력을 못 찾음 | 신규 `ContractPathTests.cs`: 무계약 helper에서 `x=8` 자동 탐색·누락 분기·불변식/요약 오염·재실행 불일치·frontier |
| C2 `Source/DafnyTestGeneration/ProgramModifier.cs`, `ProgramModification.cs`, `TestGenerator.cs` | 기존 경로의 공통 실행 부품만 추출하거나 모드 분리. 검사 모드에는 `RemoveChecks` 적용 금지 | 기존 생성기를 그대로 사용하면 반례 경로 소실 | 기존 전체 테스트 + 단언/사후조건을 가정하지 않는 반례 테스트 |
| C3 `Source/DafnyTestGeneration/ContractTesting/ContractModelCodec.cs` 신규; `TestMethod.cs`, `DafnyModel.cs` 재사용 | 자료형별 모델 복원, 객체 식별자·별칭·상태 직렬화, 복원 결과의 원래 제약 재검사 | 부정확한 모델이 거짓 반례/거짓 통과가 됨 | `ContractModelTests.cs` 신규; 부분 모델·배열·별칭·불일치 재검사 |
| C3 신규 `Source/DafnyTestGeneration/ContractTesting/{ContractTypeShapeGenerator,ContractHeapFactory}.cs`; `ContractInputGenerator.cs`, `ContractModelCodec.cs`, `ContractHarnessBuilder.cs` | 타입에서 작은 컬렉션/데이터타입/객체 슬롯·배열·별칭 생성, 진단 팩토리로 일반 힙 실현/관찰. 외부 서비스 없이 `W/P` 재검사 | 모든 프로그램에 수동 타입/상태 생성기를 요구해 범용성이 사라짐 | 신규 `ContractHeapTests.cs`/`ContractInputTests.cs`: 기본값 보충 재검사·부분형·빈/비빈 컬렉션·객체 두 개/별칭·배열·지원 불가 초기화 |
| C3 `Source/DafnyTestGeneration/ContractTesting/IContractInputConstructor.cs`, `ContractInputGenerator.cs`, `ContractModelCodec.cs` 신규 | 기본 타입/힙 생성기에 덧붙이는 선택적 외부 자원/특수 런타임 구성 경계; 실현 산출물·재관찰·`W/P/G_i` 확인 | 외부 상태 지원을 기본 메모리 객체 지원과 혼동 | `ContractInputTests.cs`, `ContractExecutionTests.cs`: 기본 서비스 없이 일반 값/힙 생성, 확장 지원 부족·실현 불일치·생성 증인 분리 |
| C3 `Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs`, `ContractStubRuntime.cs`, `ContractTestRunner.cs` 신규 | 해결된 AST 사본에 본문 없는 호출용 스텁만 삽입; 실제 본문 C# 실행과 RPC/상태 경계 관리 | 입력 생성만 되고 부분 프로그램의 실제 실행이 없음 | `ContractExecutionTests.cs` 신규; 호출 추적·실제 출력 고정·취소·재실행 |
| C3 같은 `ContractHarnessBuilder.cs`; 기존 `Source/DafnyCore/Rewriters/ExpectContracts.cs::{ExpectContracts,CallRedirector}`와 `RewriterCollection.cs`를 재사용 경계로 조사; C5 `TestContractsCommand.cs` | 기존 래퍼의 AST/호출 재지정 부품 재사용 가능성을 확인하되 ghost 조항 생략 금지; 새 명령과 기존 모드의 중복 요청 거절 | `expect true`로 생략된 ghost 명세가 검사 통과로 표시됨 | 기존 `contract-wrappers/AllExterns.dfy` 회귀, 신규 `ContractExecutionTests.cs`/`cli/contractTesting.dfy`의 ghost 거짓 조항·미확정·중복 옵션 거절 |
| C3 `Source/DafnyTestGeneration/ContractTesting/IContractProgramCompiler.cs`, `ContractTestModels.cs`, `ContractExecutionProcess.cs`, `ContractCallableSelector.cs`, `ContractHarnessBuilder.cs`; `Source/DafnyDriver/ContractTesting/DriverContractProgramCompiler.cs`, `ContractCompilerWorker.cs` 신규 | 소스/요청 DTO를 받는 Driver 작업자가 해석·진단 AST/entry 생성·기존 `CompileDafnyProgram`/`CompileTargetProgram` 호출까지 소유. Main/Exe 확인·허용 `.cs`/`.dll` 의존성 준비·원본 매핑·프로세스 기한/회수 | AST를 프로세스 간 전달할 계약이 없으며 라이브러리/누락 DLL을 실행 가능 산출물로 오인할 수 있음 | `ContractEntryTests.cs`, `ContractExecutionTests.cs`와 CLI 통합 사례: Main 없음/있음·원본 해시/위치 보존·실제 DLL 호출·누락/충돌 의존성·스텁 RPC·실행/빌드 취소·의존성 방향 |
| C4 같은 파일들과 `ContractQueryBuilder.cs`, `Source/DafnyTestGeneration/ContractTesting/ContractStateObserver.cs` 신규 | 유한 힙·입출력·동적 프레임·관찰 어댑터 인터페이스 및 단계별 제약 환경 | 대상 디렉토리 유효성 사례를 순수 모델로만 모사하거나 erased ghost 상태를 실제 관찰로 오인 | 실제 상위 본문 + 클래스 IO + 미구현 하위 호출 + 수정본 대조 |
| C4 `Source/DafnyCore/Verifier/BoogieGenerator.cs`와 기존 힙/함수 번역 부품 | 필요할 때만 기존 의미의 계약 질의 인터페이스를 노출. 새 의미 인코딩이나 일반 검증 옵션 변경 금지 | 타입·힙 의미를 별도 구현해 불일치할 위험 | 기존 번역/증명 회귀와 격리된 검사 질의 비교 |
| C5 `Source/DafnyDriver/Commands/TestContractsCommand.cs` 신규, `Source/DafnyDriver/DafnyNewCli.cs`의 명령 등록부 | 전용 JSON 계약 검사 명령 연결, 표준 출력과 프로그램 로그 분리 | Python 하네스가 안정된 계약으로 호출할 수 없음 | `Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/contractTesting.dfy` 및 결과 사례 신규 |
| C5 `Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/Inputs/contractTesting.{frameRestore,classAssertion,functionPrecondition}.request.json` 신규와 `cli/contractTesting.dfy` | 독립 검토에서 확인한 실제 함수의 호출 전제·다른 클래스의 단언·프레임 밖 쓰기 후 복구를 고정 CLI 회귀로 보존 | 고정 G0 밖의 누락 검사가 재발해 잘못된 통과가 될 수 있음 | 각 질의를 일반 Dafny 검증과 실제 계약 검사로 대조; 기존 20개 manifest는 변경하지 않음 |
| C5 `Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/contractGeneration.dfy` 및 `cli/Inputs/contractGeneration.request.json` 신규 | `test-contracts --generate`의 독립 작업자·엄격 JSON·원본 무계약 보조 본문에서 `x=8` 자동 생성 경로를 실제 CLI로 검사 | 라이브러리 테스트가 통과해도 외부 하네스의 생성 진입점이 끊겨 있을 수 있음 | `make test name=cli/contractGeneration.dfy build=false`; 생성 결과와 원본 소스 해시 대조 |
| C5 `Source/DafnyCore.Test/{PartialEvaluatorTest,UnrollBoundedQuantifiersTest}.cs`, 신규 `Source/DafnyTestGeneration.Test/Contract*Tests.cs`, `Source/IntegrationTests/TestFiles/LitTests/LitTest/cli/unrollBoundedQuantifiers.dfy` | 강화된 경계의 동작·실패 회귀 | 빠르게 단순화하나 틀린 엔진이 통과 가능 | 아래 기존 프로젝트/Makefile 명령 |
| 빌드 전제 `Source/DafnyCore/DafnyCore.csproj::RunCoco` | 실제 디렉토리 `Coco`와 다른 두 `CoCo` 입력 경로의 대소문자를 맞추고 임시 심볼릭 링크를 제거 | Linux에서 입력 파일이 없는 것으로 판단되어 불필요한 파서 재생성·도구 복원을 반복함 | 심볼릭 링크 없이 `dotnet build Source/DafnyCore/DafnyCore.csproj` 및 전체 소유 빌드 |
| 지식 기록 `wiki/contract-testing.md`, `wiki/INDEX.md` 신규 | 검증 원본 URI·모델 진단·원식 판정·재실행·프레임 쓰기 의미와 현재 지원/검증 한계를 기록 | 라이브러리 API의 기본값 때문에 진단 누락이나 모순을 성공으로 오인하는 문제가 반복될 수 있음 | 구현 소스·실제 G0/회귀 명령과 대조; 이 계획과 상호 링크 |

명령 등록 파일·필요 인터페이스는 구현 전 다시 확인하고 구조가 다르면 표를 먼저 수정한다.
생성된 파서·런타임 파일이나 `GeneratedFromDafny` 파일은 직접 수정하지 않는다.

## 5. 부분 평가 강화의 정확성 조건

1. 구체값과 논리적으로 정당화된 경로 사실만 치환한다. 미검증 `assert`나 `assume`를 참이라고 보고 분기를 제거하지 않는다.
2. 단순화 결과는 `값 결정`, `잔여식`, `미지원/예산 소진`으로 구분한다. 예산 소진은 거짓도 참도 아니다.
3. `forall` 완전 전개는 전체 유한 도메인의 논리곱, `exists`는 논리합과 동치여야 한다. 부분 전개에는 잔여 원식을 유지한다.
   C1의 첫 구현은 현재처럼 `instances ∧ original forall` 또는 `instances ∨ original exists`를 유지한다.
   이는 솔버에 인스턴스를 제공하는 효과이며 원래 잔여 도메인이 작아졌다고 표현하지 않는다.
   이미 전개한 할당을 제외한 잔여 도메인 표현은 후속 최적화다. 도입 전 별도 변경표·등가성 테스트가 필요하다.
4. 존재 시퀀스는 길이·원소 제약을 얻더라도 큰 경우에는 슬롯/배열의 잔여 제약으로 넘긴다. `|D|^n` 전부 열거하는 방식의 한도만 늘리지 않는다.
5. 인라이닝·단락 평가·분기에서 정의 가능성 조건을 보존한다. 0 나눗셈, 범위 밖 접근, 함수의 `requires`, 부분적으로 정의된 식이 조용히 사라지지 않게 한다.
6. `reads`/opaque/공개 범위를 해제하여 새로운 가정을 만들지 않는다. 실제 구현 존재와 명세식의 평가 가능성은 다른 문제다.
7. 재귀 인라이닝·한정자·전체 AST·질의 시간 예산을 독립 계수로 기록한다. 로컬 한도 0의 현재 의미(무제한)는 새 검사 정책에서 자동 선택하지 않는다.
8. 전처리를 끈 원본 계약 질의 및 작은 범위의 명시적 평가와 차등 검사한다. 검사 엔진이 낸 반례를 원래 식으로 재검사한다.
9. 작은 시퀀스의 길이·원소 등식부터 전파한다. 현재 `BatchMoveWitnessRelation`의 원본 수 1은
   `|fsBounds|=2`, `fsBounds[0]=H0`, `fsBounds[1]=H1`을 주므로 존재하는 경계열을 `[H0,H1]`로
   치환할 수 있는 구체 최적화 사례다. 길이 1 결과/출력 조각 열도 원래 연결 등식으로 처리하고
   남은 이동 관계를 보존한다. 이 규칙은 `PartialEvaluatorTest`의 원식 등가성 회귀를 먼저 통과해야 한다.

최적화는 소규모 등가성·회귀 검사를 먼저 통과한 뒤 추가한다. 성능 개선은 사실이 아닌 측정 목표다.

## 6. SMT 질의와 신뢰 경계

질의 종류를 타입으로 구분한다. 입력 기호 `U=(x,H0,환경)`과 `W/P/B/F_s/G_i`는
상위 계획 6절의 정의를 따른다.

- 기본 입력: `Γ ∧ W(U) ∧ P(U) ∧ B(U)`.
- 목표 입력: 기본 입력 제약에 구성 상태의 고정 사실 `F_s(U)`, 선택한 입력 경우 `G_i(U)`, `NewInput(U)`를 추가한다.
- 구현 경로 입력: `Γ ∧ W(U) ∧ P_entry(U) ∧ B_k(U) ∧ R_body^k(U,L,H_t) ∧ G_target(L,H_t)`. 실제 본문의 제한된 접두 계산 관계를 사용하며 선언된 사후조건으로 계산을 대체하지 않는다.
- 보조 생성: 필요한 경우에만 `∃V,Z. Case_i(U,V,Z) ∧ Frame(U,V)`를 추가해 한 경우의 실현 가능성으로 입력을 제안한다. 여기서 얻은 `V,Z`는 실제 관찰이 아니다.
- 호출 전제 위반: 고정된 실제 도달 상태에서 `Γ ∧ Path ∧ ¬P_child`.
- 미구현 호출의 실현: `Γ ∧ Path ∧ P_child ∧ Q_child ∧ Frame_child`.
- 관찰된 실행의 위반: 실제 `x,H0,y,H1`을 고정하고 `Γ ∧ ¬Q` 및 필요한 프레임 조건 검사.
- 혼합 실행의 위반 탐색: 상위 경로와 누적 하위 관계 아래에서 `¬Q_parent` 또는 호출 전제 위반을 탐색.

본문 없는 유효한 선언의 명시적 논리 절이 비어 있으면 해당 `P/Q`는 참이며,
타입·프레임은 실제 Dafny 의미대로 남는다. 지원되는 관계의 만족 모델을 얻을 수 있으나
`type_frame_only`/`underconstrained_contract`와 기능 판정 근거 부재를 기록한다.
이를 의미 자체의 부재나 실제 구현의 계약 통과로 표시하지 않는다. 해결되지 않는 선언
요청과 미지원 외부 구현/타입은 별도 입력 오류·미지원 결과다.

검사 대상 사후조건을 자기 질의의 가정으로 넣지 않는다. 본문 있는 선언의 계약을
Boogie가 자동 가정하는 호출로만 표현하여 실제 실행을 대신하지 않는다.
원본 명세의 순수 정의는 허용된 가시성과 의미로 사용하되, 아직 증명되지 않은 보조정리·
`free` 계약·공리성 가정에서 결론을 끌어낸 결과는 신뢰 근거가 완전한 반례/통과로 표시하지 않는다.

`SAT`, `UNSAT`, `UNKNOWN`, `TIMEOUT`, `ERROR`를 분리한다.
`SAT` 모델은 재현 가능한 입력·모델로 변환되어 원래 제약을 만족해야 한다.
`UNSAT`의 의미는 입력·경로·자료형·수치/크기 상한·재귀 경계와 함께 기록한다.
제약 없는 모델 보충이나 미지원 값의 기본값 대입은 성공 경로가 아니다.
검사할 결론을 제외한 전제와 고정 관찰값이 일관적인지 먼저 확인한다.
미증명 가정으로 전제 전체가 모순이 되어 `UNSAT`가 나오는 경우를 속성 통과로 표시하지 않는다.
기존 `GenerateTestsCommand.SequenceLengthLimit`는 모든 시퀀스 길이를 제한하는 공리를 설명한다.
이 옵션을 새 검사기의 전체 논리 환경에 그대로 전달하지 않는다. 생성 상한은 특정 입력·
모델 변수의 지역 제약으로 두고, 한정자의 의미나 원래 명세의 도메인을 바꾸지 않는다.

같은 순수 함수와 읽기 힙의 결과는 시험 안에서 일관되어야 한다.
메서드 호출의 `old`는 호출 직전 힙으로 고정하며, 허용된 `modifies` 밖의 상태는 유지한다.
미구현 계약에서 얻은 모델을 부모 실행에 사용했음을 결과에 남긴다.
어떤 모델이 부모를 깨뜨린다고 해서 없는 자식 본문이 틀렸다고 단정하지 않는다.

### 6.1 입력 경우 추출과 부분 평가의 역할

`ContractScenarioExtractor`는 Core의 해결된 AST와 공개 reducer만 사용한다.
각 노드는 입력·초기 힙, 실제 출력·다음 힙, 바인더 안의 중간 증인에 대한 의존성을
갖는다. ghost 여부만으로 입력 의존성을 결정하지 않는다. 함수 호출에는 공개 정의의
`requires`와 `reads`, 식에는 단락 평가·인덱스 범위 등의 정의 가능성 조건을 보존한다.

- 입력 전용 `if g`는 이전 분기 부정과 `g`/`¬g`를 포함하는 경우로 등록한다.
- 양의 논리곱에서 입력 전용 항은 필요 조건으로 쓸 수 있다. 양의 논리합의 항들은
  서로 겹칠 수 있으며 하나의 실패가 전체 실패를 뜻하지 않는다.
- `∃z.R(U,z) ∧ T(U,V,z)`에서 `∃z.R(U,z)`만 사용하는 것은 해당 항의 필요 조건인
  과대근사(overapproximation)다. 원래 바인더·상관관계·힙 시점을 보존하며 정확한 입력 투영이라고 표시하지 않는다.
- 출력 의존 가드와 음의 위치/임의 한정자 교차는 잔여 AST로 보존한다. 유한 경우의
  등가 변환을 확인한 경우만 정확한 투영으로 분류한다. 불투명 정의를 강제 전개하지 않는다.
- 전체 명세를 먼저 완전 전개하지 않는다. 목표 선택과 작은 상태 구성이 만든 구체값을
  reducer에 넣고, 정확한 유한 전개 뒤 남은 입력 필드·조회 증인만 우선 SMT로 푼다.

예를 들어 원본 수 1과 작은 파일시스템을 먼저 고정하면 원본 인덱스 한정자와 경로 조회를
줄일 수 있다. 그래도 `BatchMoveRelation`의 존재 중간 상태나 이름 변경 관계가 남을 수 있으며,
cap 증가가 이를 모두 결정한다는 기대를 두지 않는다. 모델 선택·상태 구성·부분 평가·잔여 SMT는
서로 다른 단계다. 입력 생성 시 전개되지 않은 조각은 최종 판정기의 원래 식에 남아 있어야 한다.

### 6.2 모델의 입력 복원과 상태 실현

첫 구현은 불리언/정수/문자/작은 시퀀스/재귀 깊이가 정해진 데이터타입의 명시적 생성 구조와
지역 제약을 사용한다. 임의 클래스 힙·inode 파일시스템을 원시 SMT 모델에서 자동 실현하는
기능이 기존 `TestMethod`에 있다고 가정하지 않는다. 새 외부 패키지 없이 기존 복원 부품을
재사용하되, 보충된 값은 전제·타입·선택 목표를 재검사하여 수용하거나 거절한다.

`ContractTypeShapeGenerator`가 원래 타입에서 크기가 제한된 값/객체 슬롯을 만들고,
`ContractHeapFactory`가 지원되는 일반 할당·필드 복원으로 실행 상태를 만든다.
별칭/nullable/null·배열 길이/원소·부분형 조건을 유지하며 초기화할 수 없는 필드는 미지원이다.
합성 초기 힙을 사용하는 단위 모드와 실제 초기화/생성자 접두 실행의 진입점 모드를 구분한다.
모든 클래스에 `Valid()`를 가정하거나, 접근할 수 없는 생성자/필드를 우회해 성공을 꾸미지 않는다.

`IContractInputConstructor`는 선택적 외부 자원/특수 런타임 지원 기능을 선언하고
입력 명세·고정/미정 필드·기한을 받아 구체 상태/산출물 또는 미지원 이유를 반환한다.
기본 타입/메모리 객체는 이 서비스를 주입하지 않고 생성한다. 외부 파일시스템 같은
상태 구성의 구체 계약은 소유 저장소가 제공하며 Driver/상위 하네스에서 선택적으로 연결한다.
TestGeneration→Driver 또는 CoSyn→Dafnyutils 의존성을 추가하지 않는다.

실현 전에는 복원된 입력의 `W/P/G_i`, 실현 후에는 실제 관찰된 초기 상태의 같은 조건을
검사한다. 선택한 진입점의 전처리·초기화 결과는 실제 접두 실행으로 얻는다.
선언의 단위 입력과 진입점에서 도달하는 입력 모집단을 구분한다. 참조 별칭·이름·상태 대응을 유지하고
기록한 범위의 동등한 구체 입력을 차단한다. 생성 증인만 달라진 모델은 새로운 시험이 아니다.
원래 계약이 읽는 필드를 빼고 입력의 동등성을 계산해서는 안 된다.

보조 생성에서 `∃V,Z.Case_i`를 만족하지 못해도 원래 `P`에 맞는 입력 전체를 버리지 않는다.
`P` 기반 입력 공급원을 독립 유지하고 원래 계약의 실현 불가능성도 진단한다.
보조 관계에 도입한 증인 크기 상한은 그 질의의 탐색 범위이며 실제 결과의 원식 판정에는 적용하지 않는다.
실제 실행의 출력·다음 상태를 고정한 뒤 원래 전체 `Q`와 프레임을 새로 검사한다.
생성 가상 출력과 실제 관찰 필드는 타입/직렬화 단계에서 분리한다.

### 6.3 생성기 검증과 진단

필수 회귀는 `P=true`에서도 목표 분기를 나누는 사례, 이전 분기 부정이 빠지면 잘못된 경우로
가는 사례, 조회 결과가 초기 상태와 모순인 모델, 가상 생성 결과는 적합하지만 실제 본문은
다른 결과를 내는 사례, 모순인 사후조건, 부분 모델/배열 미지원, 상태 실현 불일치다.
원식 일부로 빠르게 실패를 판정할 때는 고정 입력에서 `Q ⇒ 필요한 조항`을 확인한다.
선택한 논리합 한 항의 실패나 목표 미도달만으로 프로그램 오류를 보고하지 않는다.

결과는 제안 수·적합 수·실현 수·선택/실제 도달 경우·원식 판정 수·재현된 반례 수와
단계별 소요 시간을 갖는다. 지원하지 않는 목표와 기한 때문에 미시도한 목표도 분모에 남긴다.
입력 생성 `TIMEOUT`, 상태 실현 실패, 원식 판정 `UNKNOWN`을 별개 원인으로 기록한다.
유효 입력 수가 늘었다는 사실을 오류 검출 개선이라고 표현하지 않는다.

### 6.4 실제 본문 경로의 제한적 확장과 재실행

`ContractBodyExpander`는 원본을 보존한 해결된 AST 사본에서 지원되는 호출/루프/재귀를
제한적으로 펼쳐 `ContractBodyExpansionResult`의 프로그램·선언/위치 대응·frontier를 만든다.
새 일반 해석기를 작성하지 않는다. 실제 식·타입·힙의 번역과 단일 대입 변환, SMT 실행은
기존 Dafny/Boogie 부품을 재사용한다. `testInline`이나 기능 사후조건이 없다는 이유로
본문이 있는 호출을 무제약 반환/검증용 요약으로 바꾸지 않는다.

원본의 인자 평가 순서, 대입, 분기, 호출 전후 힙, return/break/continue를 보존한
지원 구문부터 시작한다. 루프 상한에서 가드가 참이면 별도 frontier로 기록하고
정상 종료/원래 사후조건 도달로 세지 않는다. 잔여 재귀 호출도 계약 모델로 조용히 바꾸지 않는다.
미지원 구문은 해당 기호 탐색 범위만 미지원으로 남기며 가능한 구체 실행은 계속 사용할 수 있다.

진단 경로에 필요한 실제 본문이 Boogie에 방출되는지 확인한다. `Impl$$` 이름만 추측하는
문자열 연결 대신 원래 선언 ID와 방출 구현의 대응을 명시적으로 보존한다.
기존 `TranslateForFutureInlining`의 전체 변환을 복사하여 opaque/가시성을 해제하지 않는다.
검증용 루프 요약·불변식 가정·호출 사후조건의 `free` 가정이 남은 질의는 실제 본문 경로로
인증하지 않는다. `RemoveChecks`를 적용하지 않는 계약 질의 경로를 사용한다.

명시적 `assume`·검증 생략·고스트 보조정리의 신뢰 의존성은 별도 기록한다. 본문에 쓴
`assert`나 불변식을 무조건 참으로 가정해서 실패 입력을 제거하지 않는다. 안전성/정의 가능성
검사 실패와 정상 경로 목표는 구별하여 전제 위반/실행 실패로 보고한다.

`ContractPathExplorer`는 확장된 프로그램의 가드·대입·힙 제약과 선택 목표를 연결한다.
현재 블록 플래그 탐색 부품은 경로/모델 획득의 기반으로 재사용할 수 있으나 그 경로 자체가
원래 실행을 증명하는 것은 아니다. `ContractTraceValidator`가 구체 실행의 분기·호출·
중간값·상태를 후보와 대조한다. 불일치는 `path_model_mismatch`이며 버그/도달 성공이 아니다.
본문 없는 계약 호출이 섞이면 모델 선택과 추상 실행 구간을 보존하고 재현한다.

`SAT(P)` 입력·구현 경로 목표·명세 목표를 모두 유지한다. 구현에 없는 분기를 찾기 위해
명세 목표를 버리지 않으며, 명세가 분해되지 않는다고 본문 경로 탐색을 중단하지 않는다.

## 7. 실제 실행과 힙 지원의 수직 구현

G0 안에서 불리언·정수·문자/시퀀스의 최소 본문 실행과 본문 없는 하위 호출을 연결하고,
일반 참조 객체·유한 메모리 힙까지 이어서 완료한다. 도메인 어댑터 없이 이 범위를 먼저 검증한다.
첫 수직 검증은 같은 입력의 실제 본문이 계약과 다른 값을 반환하는 프로그램이어야 한다.
그 반례, 본문 없는 자식의 RPC 반환, 실제 본문으로 교체한 뒤 RPC가 사라지는 실행,
취소 후 남은 프로세스가 없는 상태를 모두 확인해야 C3를 완료한다.
G0부터 원래 Main 없음/있음, 작업자 소스 재해석 뒤 원본 해시/선언/위치 대응,
허용된 외부 DLL 사용과 누락/충돌 실패를 검사한다. 생성 DLL 존재만으로 실제 실행 경로가
연결되었다고 판단하지 않는다.

- 원본 AST에서 실제 본문 유무와 `by method` 구현을 구분하고 지원하지 않는 실행 구성은 명시적으로 거절한다.
- 테스트 전용 스텁은 복제 AST에서 호출/반환/수정 상태만 대체한다. 원본 소스·증명 대상·제출물은 보존한다.
- 객체 식별자 테이블로 별칭을 보존하고 초기 힙·현재 힙·호출별 과거 힙을 분리한다.
- 읽기 전용 관찰, 오류 반환, 출력 누적, 상태 무변경 경로를 구현·테스트한다. 실제 IO 바인딩의 임시 대체는 명시적 테스트 서비스로 기록한다.
- 컴파일에서 제거된 ghost 필드는 실제 힙 직렬화 대상이 아니다. 실행 가능한 시험 상태와 관찰된 IO에서 ghost 모델을 복원하는 어댑터 인터페이스를 분리하고, 구체 바인딩은 공개 상태 계약의 소유자가 제공한다. 복원 관계가 불충분하면 `ghost_state_unavailable`이며 사후조건의 모델값으로 관찰을 대체하지 않는다.
- 입력/관찰한 메모리 값으로 정의된 ghost 술어·한정식은 원래 논리식으로 판정한다. 독립 ghost 필드의 관찰 불가와 ghost 술어 자체를 혼동하지 않으며, 일반 술어에 외부 어댑터를 요구하지 않는다.
- 실제 외부 바인딩은 격리된 임시 시험 환경에서 실행한다. 바인딩이 없는 본문을 명세 실행으로 자동 강등하지 않는다.
- G0는 객체 두 개와 중복 참조가 있는 작은 비순환 그래프를 지원한다. 배열은 C3의 별도 회귀로 확대한다. 지원 범위 밖의 순환/복잡 별칭·배열 차원·고차 모델에 도달하면 위치와 이유를 미확정 결과로 남기며 기본값으로 계속 실행하지 않는다.
- 재실행은 난수 시드뿐 아니라 구체 입력·하위 모델 선택·상태를 고정한다.

## 8. 검증 전략

| 디렉토리 / 실제 명령 | 전제조건 | 예정 범위 |
| --- | --- | --- |
| 이 저장소: `dotnet build Source/Dafny.sln` | .NET 8, 기존 NuGet 패키지, 하위 소스 | 컴파일 |
| 이 저장소: `dotnet test Source/DafnyCore.Test --filter 'FullyQualifiedName~PartialEvaluatorTest\|FullyQualifiedName~UnrollBoundedQuantifiersTest'` | 빌드·Z3 | 부분 평가·전개 기존 및 추가 회귀 |
| 이 저장소: `dotnet test Source/DafnyTestGeneration.Test` | 빌드·Z3 | `ContractEntryTests`/`ContractBodyExpansionTests`/`ContractPathTests`/`ContractHeapTests`/`ContractScenarioTests`/`ContractInputTests` 추가 후 임의 선언·타입/힙·실제 본문 경로·원식 판정·기존 생성 회귀 |
| 이 저장소: `make test name=cli/unrollBoundedQuantifiers.dfy` | 로컬 integration test 구성 | 기존 CLI 회귀 |
| 이 저장소: `make test name=contract-wrappers/AllExterns.dfy` | 로컬 integration test 구성 | 기존 `--test-assumptions`/extern 래퍼 동작 보존. 새 ghost 판정 성공의 근거로 사용하지 않음 |
| 이 저장소: `make test name=cli/contractTesting.dfy` | C5 신규 파일 추가 후 | 새 명령과 구조화 결과. 현재는 미존재 |
| 이 저장소: `make test-dafny name=cli/unrollBoundedQuantifiers.dfy action="verify"` | 로컬 빌드 | 선택한 Dafny 의무 검증 |
| 이 저장소: `make format`, `.dfy` 변경 시 `make format-dfy` | 포맷 도구·관련 파일 지침 | 형식 |
| `/workspace/cosyn`: `make build-dafny` | 위 소스·기존 의존성 | 소유 패키지의 결정적 빌드 경로 확인 |

신규 테스트는 참인 계약뿐 아니라 잘못된 본문·모순 계약·자기 가정·잘못된 모델을 반드시 실패시킨다.
각 테스트는 한 시나리오와 바로 위의 의도 주석을 갖는다.
실행 테스트 통과, Dafny 증명, 변환의 등가성 확인, 성능 결과는 각각 기록한다.
명세·평가기·벤치마크 데이터와 점수는 변경하지 않는다.
설계 단계에서는 위 명령을 실행하지 않았다. 구현 단계의 실제 실행 기록은 아래와 같다.
입력 생성 보완의 독립 검토와 문서 검사는 [후속 기록](../../../plan/2026-09-12-contract-input-generation-design.md)에 남긴다.

### 8.1 구현 중간 검증 기록

검사 기준은 `1eb9fc5fa2661483de151ff85b21eed0b695878a`에 현재 미커밋 구현을 더한 작업 트리다.
.NET SDK 8.0.131과 기존 Z3를 사용하며 유료 제공자는 호출하지 않았다.

- `dotnet build Source/DafnyTestGeneration/DafnyTestGeneration.csproj --no-restore -m:1 -nr:false -p:BuildProjectReferences=false`: 성공. 참조 프로젝트 생략 경로이므로 전체 솔루션 빌드 통과를 의미하지 않는다.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 -nr:false -p:BuildProjectReferences=false --filter 'FullyQualifiedName~ContractModelRealizerTests|FullyQualifiedName~ContractHeapTests' --logger 'console;verbosity=normal'`: 중간 상태 13개 중 모델 실현 8개와 힙 4개 통과, 힙 질의 테스트 1개 실패. 비고스트 필드 대입을 `ghost method`에 둔 테스트 오류를 수정했다.
- 이어 `--filter FullyQualifiedName~ContractHeapTests`로 동일 테스트 명령을 실행해 5개 전부 통과했다. 기존 AST/소스·입력·계약은 수정하지 않았다.
- 모델 실현의 초기 오류는 이름 있는 모듈의 검증 원본 URI와 라이브러리 기본 `NullPrinter`에서 발생했다. 기존 `Utils.Parse`와 질의 전용 프린터를 사용해 실제 SAT 반례 모델을 포착한다. 진단 누락/실패를 SAT나 통과로 처리하지 않았다.
- 모델 실현 8개 통과 뒤 선택값 재실행·잘못된 재실행 거부·다중 출력 상관·void 모순·기능 계약 없는 모델 5개를 추가했다. 이 추가분과 G0 전체 실행은 아직 검증 중이다.
- 로컬 테스트 실행기는 루프백 소켓을 사용하므로 기본 샌드박스에서 `SocketException(13)`이 났고 승인된 로컬 테스트 실행 경로로 수행했다. 전체 빌드의 Gradle 캐시/파서 입력 경로 문제는 별도로 기록하며 미실행 증명을 통과라고 보고하지 않는다.

### 8.2 최종 구현 대응과 검증 (2026-09-12)

최초 변경표의 파일명은 제안이며 최종 구현은 아래 기존 경계로 정리했다.
`ContractExpressionReducer`가 기존 부분 평가·유한 전개 엔진에 누적 예산을 전달하고,
`ContractSolver`는 원식과 축약 사본을 함께 검사한다. `UnrollBoundedQuantifiersRewriter`,
`ExpressionRewriteUtil`, 기존 `ProgramModifier`/`TestGenerator`, `BoogieGenerator` 자체는
수정할 필요 없이 기존 API를 재사용했다. 기존 모드의 일반 검증 의미는 변경하지 않았다.
선택적 외부 자원 생성 인터페이스 `IContractInputConstructor`는 추가하지 않았다.
기본 메모리 상태 구성은 `ContractTypeShapeGenerator`/`ContractHeapFactory`, 관찰은
`ContractStateObserver`가 소유한다. 외부 구현은 명시적 소스/DLL·해시 바인딩으로 제한하며
임의 외부 파일시스템/ghost 상태 생성 어댑터는 이 기본 기능의 전제가 아니다.

모든 요청은 `ContractSourceSnapshot`의 해시를 확인한 폐쇄 소스 묶음으로 파싱·해석한다.
다중 파일/include의 URI·오프셋·파일별 해시를 유지하고 주변 파일시스템으로 암묵적으로
fallback하지 않는다. 명시적 제네릭 타입과 해결된 하위 호출의 타입은 네이티브 파서·타입
특성 검사로 치환하며 재실행에도 보존한다. 실제 함수와 외부 함수의 미증명 사후조건이
판정 질의의 가정으로 유입되지 않게 진단 사본에서 분리한다. 본문 없는 순수 계약의 모델
관계는 유지한다. 진단 이름 충돌·중첩 참조 값·호출별 힙/old·쓰기 후 복구도 회귀로 확인했다.
생성 체크포인트는 원식 재검사가 끝난 입력만 원자적으로 저장하며 Python 감독자 기한에서
프로세스 회수 후 보존한다. CLI 한 줄 JSON 프로토콜과 기존 시간 제한은 유지한다.

최종 작업 트리는 기준 HEAD에 미커밋 변경을 더한 상태다. .NET SDK 8.0.131,
지원 `Binaries/Dafny` 4.11.1+1eb9fc5f, 시스템 Z3 4.8.12를 사용했다.
정확한 명령/로그/소스 해시는 [통합 실행 기록](../../../plan/2026-09-12-hybrid-contract-testing-implementation.md)의
최종 검증 절에 있다. 다음 수치는 중간 제한 빌드 결과를 최종 결과로 재분류한 것이 아니다.

| 작업 디렉토리 / 최종 검사 | 결과·범위 |
| --- | --- |
| `/workspace/cosyn`: `GRADLE_USER_HOME=/tmp/cosyn-contract-gradle make build-dafny` | 전체 솔루션 비증분·결정적 빌드, 경고/오류 0, 지원 래퍼 갱신 |
| 이 저장소: `dotnet test Source/DafnyTestGeneration.Test/DafnyTestGeneration.Test.csproj --no-build --no-restore --logger 'console;verbosity=minimal'` | 독립 검증자가 전체 **209 passed/0 skipped**, 1분 38초 |
| 이 저장소: `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-build --no-restore --filter 'FullyQualifiedName~ContractExpressionReducerTests\|FullyQualifiedName~PartialEvaluatorTest\|FullyQualifiedName~UnrollBoundedQuantifiersTest' --logger 'console;verbosity=minimal'` | Core 관련 **103 passed/0 skipped**; Core 전체가 아님 |
| 이 저장소: `make test name=cli/contractTesting.dfy build=false`, `name=cli/contractGeneration.dfy`, `name=cli/unrollBoundedQuantifiers.dfy` | 각각 1개 통과; 생성/검사 JSON과 기존 한정자 CLI |
| 이 저장소: `DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS=cs make test name=contract-wrappers/AllExterns.dfy build=false`, `name=contract-wrappers/TestedExterns.legacy.dfy` | 각각 1개 통과; C# 기존 외부 래퍼 경계 |
| 이 저장소: `make format`, `make format-dfy`, 최종 변경 C# 47개 `dotnet format whitespace ... --verify-no-changes` | 통과, 최종 변경 0. 형식 작업공간의 Runtime 참조 메타데이터 경고는 기록하고 영향받는 프로젝트 적재를 확인 |
| 이 저장소: 공개 두 fixture의 `Binaries/Dafny verify ... --filter-symbol Fixed --allow-warnings`; `make test-dafny name=cli/unrollBoundedQuantifiers.dfy action='verify --unroll-bounded-quantifiers 1000' build=false` | 수정본 선택 의무 **8 verified/0 errors**, 기존 한정자 의무 **1 verified/0 errors** |
| `/workspace/cosyn`: 최종 실제 CLI 연동 5개 Python 테스트 파일, `COSYN_CONTRACT_INTEGRATION=1` | **92 passed/8 opt-in skipped**, 359.63초. 별도 동일 예산 비교 **8 passed**, 838.24초 |

새로운 생성/실행 API를 기존 테스트로만 판단하지 않고 공개 G0 20개·두 오류/수정 대조·
실제 다중 파일/제네릭/중첩 객체 실행과 정확 재현으로 확인했다. 선택한 증명 외의 전체
벤치마크 증명, 다른 컴파일 대상 전체, 유료 제공자와 평가기 점수는 검증하지 않았다.

## 9. 위험·승인·지식·인계

공통 번역기 오류, 비실행 가능한 모델, 힙의 불완전한 복원, 재귀·한정자 폭증이 주요 위험이다.
정확한 작은 범위부터 확대하고 지원하지 않는 경우를 통과로 표시하지 않는 것이 복구 전략이다.
일반 목적 새 패키지나 라이브러리를 설치하기 전 승인을 받는다. 기존 파일 안의 소규모 연결을
넘어 별도 라이브러리가 필요해지면 우회 구현하지 않고 계획을 다시 작성한다.
유료 제공자 실험·평가기 정책 변경·검증 범위 축소·커밋은 이 요청에서 승인되지 않았다.

검증된 엔진 경계와 실패 원인은 [계약 검사 위키](../wiki/contract-testing.md)에 기록한다.
정확한 중간 실행과 실패·재시도는 [구현 실행 기록](../../../plan/2026-09-12-hybrid-contract-testing-implementation.md)을 함께 참조한다.

- 완료: G0와 C1–C5의 기본 범용 구현, 원식 보존 reducer/SMT·자동 타입/힙/본문/명세 입력·실제 실행/도달 접두·추적/정확 재현·CLI, 소유 빌드/회귀/독립 검토와 위키 기록.
- 남은 필수 작업/차단 요인: 없음. 유한 탐색 밖의 결정 가능성을 주장하지 않는다.
- 지원 한계: 내부 새 객체 할당, 제네릭 수신 객체·다형 재귀/여러 구체 인스턴스, 다차원 배열, 고차/무한 모델, 관찰 불가 ghost 상태는 미지원/미확정으로 보존한다. import 별칭 생성자와 일부 제네릭 도달 목표의 미지원도 명시하며 임의 성공값으로 대체하지 않는다.
- 다음 사용 단계: `Binaries/Dafny test-contracts <request.json>` 또는 `--generate`로 호출하고 원식 판정/재현/기한 산출물을 확인한다. 새 구문·외부 자원 지원은 별도 확대 계획에서 다룬다.
- 호환성: 상위 두 패키지의 도구 체인은 독립이다. 이번 작업으로 평가기 쪽 런타임 일치를 주장하지 않는다.
