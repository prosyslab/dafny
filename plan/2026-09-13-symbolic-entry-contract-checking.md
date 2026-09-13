# 기호 진입점 계약 검사

- 상태: done
- 작성일/갱신일: 2026-09-13
- 상위 계획: [CoSyn 통합 계획](../../plan/2026-09-13-symbolic-entry-contract-checking.md)
- 범위: Dafny 소스 스냅샷의 모듈식 검증 진입점. 벤치마크 변경이나 평가 실행이 아니다.

## 목표와 관찰 가능한 수용 기준

구체 입력·힙 생성과 컴파일 실행 없이 선택한 일반 Dafny 메서드의 구현 계약을 SMT로
검사한다. 기본 범위에서 도달 가능한 내부 구현도 검사하고, 외부 선언은 본문을 제거한
계약 요약으로만 사용한다. ghost 힙을 포함하는 입력 형식이 런타임 구체화 제약 때문에
`unsupported`가 되지 않아야 한다.

구조화 결과는 검사 범위, 결과 상태, 진입 전제 일관성, 검사/요약된 심볼, 외부 계약과
신뢰 의존성, Dafny 진단을 포함한다. 증명 의무 실패를 실제 실행 반례로 표시하지 않는다.

## 조사한 기존 구현

- `ContractSourceSnapshot`: 해시 검증과 snapshot-only include parse/resolve를 재사용한다.
- `ContractSolver`: `Compile=false`인 Dafny→Boogie→Z3 경로와 결과 분류 방식을 재사용하거나
  최소 공통 헬퍼로 추출한다.
- `ContractCallableSelector`: 구체 실행 타입 제한이 있으므로 기호 심볼 선택에는 직접 쓰지 않는다.
- `ContractBodyExpander`: 일부 statement만 유계 전개하고 `old` 힙 보존이 일반적이지 않아
  모듈식 기호 진입점 본체로 사용하지 않는다.
- `ContractTypeShapeGenerator`/`ContractHeapFactory`: ghost 필드를 거부하므로 이 경로에서 사용하지 않는다.

## 변경표

| 파일·심볼 | 무엇을 어떻게 변경 | 왜 필요한가 / 없으면 무엇이 남는가 | 검증 |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractSymbolicModels.cs` | 버전 1 요청, 검사 범위 enum, 결과 상태, 의무/의존성 record 추가 | 실행 DTO의 의미 오용 방지 | JSON 엄격성/왕복 |
| `Source/DafnyTestGeneration/ContractTesting/ContractSymbolicChecker.cs` | parse/resolve, 정확 심볼 선택, call graph 폐쇄, extern body 제거, trust 수집, premise/implementation 검증 | ghost/외부 상태의 완전 기호 경로 제공 | 정상·실패·ghost·extern 테스트 |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs` | 필요하면 프로그램 검증 공통 실행기를 최소 추출 | SMT 실행·분류 중복 방지 | 기존 query 테스트 전체 |
| `Source/DafnyDriver/Commands/TestContractsCommand.cs` | `--symbolic`, `--symbolic-worker` 및 시간 제한 supervisor 추가 | 격리된 CLI 계약 제공 | worker/supervisor 통합 테스트 |
| `Source/DafnyTestGeneration.Test/ContractSymbolicTests.cs` | 일반 본문 오류, ghost IO형 상태, bodyful extern 함수/메서드 무시, 모순 P, 신뢰 의존성 사례 | 의미 퇴행 검출 | 집중 xUnit |
| `Source/IntegrationTests/.../contractSymbolic.*` | JSON CLI의 성공/실패 구조 확인이 필요할 때 추가 | C#/CLI 배선 누락 검출 | Lit 또는 driver 테스트 |
| `wiki/contract-testing.md` | 동적 override/extern 계약 의존성 폐쇄, trust/source evidence 경계 기록 | 검증 범위와 영수증 증거를 구현과 일치시킴 | 링크와 diff 검사 |

## 의미론과 판정

- 진입점 `P`, 원래 본문 `C`, 원래 사후조건 `Q`를 그대로 검증한다. 별도 래퍼가
  `Entry`를 호출하고 `Q`를 검사하는 방식은 사용하지 않는다.
- 내부 구현 호출은 계약 요약을 사용하므로 기본 `reachable_implementations` 범위에서는 그
  구현의 자체 의무도 함께 검사한다. bodyless/extern 호출은 계약 전제로 결과에 기록한다.
- extern 함수는 Dafny fallback body 및 `by method` body를 해결된 진단 AST에서 제거한다.
  extern 메서드 본문도 제거하고 해당 구현 의무를 생성하지 않는다.
- 진입 `P` 일관성은 별도 질의로 확인한다. 모순 P는 `inconsistent_premise`이고 구현 검증
  성공으로 세지 않는다.
- SMT 실패 모델은 `obligation_failed`이며 런타임 재현 반례가 아니다. `verified`도 선택한
  소스와 범위의 모듈식 검증 결과다.

## 비목표·경계·승인

- 유계 path/PBT 탐색, 사용자 지정 사후조건 파싱, 외부 구현 검사, 런타임 컴파일은 후속 범위다.
- 기존 명세/본문/증명, 평가기, 생성/실행 요청의 판정은 변경하지 않는다.
- 새 패키지, 네트워크, 유료 실행, benchmark 실행, 커밋은 없다. 추가 승인은 필요하지 않다.

## 검증 명령

- `dotnet test Source/DafnyTestGeneration.Test --filter FullyQualifiedName~ContractSymbolicTests`
- `dotnet test Source/DafnyTestGeneration.Test --filter FullyQualifiedName~Contract`
- `dotnet test Source/DafnyTestGeneration.Test`
- `dotnet build Source/Dafny.sln --no-restore`
- 변경 파일 대상 `dotnet format ... --verify-no-changes` 또는 저장소 소유 형식 검사
- `git diff --check`

범위가 달라지면 먼저 이 표를 갱신한다.

## 구현 기록

- `ContractSymbolicChecker`는 세 번의 독립 snapshot parse를 사용한다. 첫 parse는 exact
  symbol/closure/trust discovery, 둘째는 진입 `requires` 일관성, 셋째는 원래 구현 의무를
  검사한다. 모든 parse와 Boogie 실행은 같은 program options 인스턴스를 사용한다.
- 첫 버전은 method entry를 명시적으로 요구한다. 함수 entry의 별도 premise 의무를 추측하지
  않고 거부하지만 도달 내부 함수는 구현 폐쇄에 포함한다. 선택한 `{:verify false}` method도
  검사 성공으로 오인하지 않고 invalid input으로 거부한다.
- `test-contracts --symbolic`과 hidden `--symbolic-worker`는 compile/execute/generate 모드와
  상호 배타적이다. Supervisor deadline은 worker와 solver process tree를 종료하고 timeout과
  caller cancellation을 구별한다.
- 집중 xUnit 10개가 정상/잘못된 Q/모순 P/ghost class state/bodyful extern method/extern
  function+by-method/spec call closure/도달 내부 구현/verify-false/JSON strictness를 통과했다.
- `FullyQualifiedName~Contract` 확대 필터도 159/159 통과했다.
- 전체 `DafnyTestGeneration.Test`도 229/229 통과했다.
- Driver project build와 실제 supervisor JSON smoke가 통과했다. 전체 solution build와
  독립 검토는 상위 작업에서 이어서 실행한다.
- 새 durable 구현 경계는 `wiki/contract-testing.md`에 추가했다.
- 독립 검토는 trait 호출의 동적 override 구현과 extern 계약에서만 참조하는 내부 함수가
  기본 도달 폐쇄에서 누락되는 두 soundness 결함을 실패 회귀로 재현했다. 전자는 모든
  override 후보를 추가하고, 후자는 extern body를 제외한 원래 계약/프레임 AST만 탐색해
  수정했다.
- `decreases *`와 `assert {:only}`가 trust 결과에서 누락되는 문제를 Dafny Auditor 가정
  수집으로 수정했다. 모든 닫힌 source snapshot의 path/SHA-256 증거를 결과에 추가하고,
  null source collection은 예외 대신 `invalid_input`으로 거부한다.
- 수정 후 집중 xUnit 14/14, `FullyQualifiedName~Contract` 162/162, 전체 solution build
  경고/오류 0, 변경 파일 `dotnet format --verify-no-changes`, 실제 supervisor CLI smoke와
  `git diff --check`가 통과했다. 독립 검토는 전체 TestGeneration 재실행 대신 변경 의미를
  포함한 162개 contract 필터를 우선했다. 유료 제공자·benchmark·컴파일/네이티브 실행은
  없었다.
- 상위 CoSyn 전체 pytest는 저장소 제약에 맞는 기존 의존 환경에서 272 passed, 39 skipped,
  pyright는 같은 환경 경로를 지정해 0 errors/0 warnings였다. 수용 기준을 충족했다.
