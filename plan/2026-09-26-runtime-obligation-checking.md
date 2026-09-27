# 런타임 의무 검사(runtime obligation checking) 모드

- 상태: done (승인된 구현·로컬 검증 범위; 지원 한계 유지)
- 작성일/갱신일: 2026-09-26 / 2026-09-27
- 소유 저장소: Dafny fork (`/workspace/cosyn/dafny`, 독립 Git 저장소). 평가 실행이 아니다.
- 기준 커밋: `f775837e648a3aede8521a99904fa744b4b8d4c1` (최초 계획 시점에는 계획 파일 외 clean; 최종 dirty 작업 트리는 §0 참조).
- 상위 계획: [통합 계획](../../../plan/2026-09-26-goal-pbt-counterexample-tool.md)
- 소비자 계획: [CoSyn 계획](../../plan/2026-09-26-goal-pbt-tool.md). 이 문서의 §4 와이어 계약이
  정본이고 CoSyn DTO는 이를 그대로 따른다.

## 0. 인계 요약

### 완료 체크포인트 — 2026-09-27

- 사용자가 완료 변경의 커밋과 후속 M2 진행을 요청했다. 본 계획의 엔진 변경과 기록을
  `[Contracts] add goal runtime obligation campaigns` 체크포인트로 커밋한다.
  기존 검증 결과·지원 한계를 그대로 유지하며 M2의 새 구현은 별도 계획에서 진행한다.
  [상위 후속 계획](../../../plan/2026-09-27-pbt-m2-entry-execution.md).
- 승인된 런타임 의무 검사와 R-1–R-7 수정, 소유 저장소 검사, 새 독립 검증을 완료했다.
  아래 각 시점의 대기·실패 기록은 보존된 이력이다. 현재 수락은 이 체크포인트와
  03:43 UTC 최종 검사 기록을 따른다. 기준 커밋 위의 기존 dirty 작업은 보존했다.
- Root의 동결 도구 r5에서 M1/M2 로컬 실행과 원본 산출물 독립 검사가 완료됐다.
  M1 결함 변형은 6/6 탐지, 포함된 증명 공백은 오탐 0/5이며 검증에 성공한 1개는 제외했다.
  M2는 변경하지 않은 IO 초안의 실행 문맥에서 ghost 함수를 호출해 8개 모두 샘플 생성 전
  `unsupported`다. 평가 가능 분모는 0, 비율은 null이며 IO 검사가 동작했다고 주장하지 않는다.
  `IO.Init requires false`와 벤치마크 계약은 유지했다.
- 독립 산출물 보고서: `/workspace/tmp/pbt-r5-artifact-review-20260927/REPORT.md`.
  M1 요약 29항목·M2 26항목, 입력 스냅샷·변형·1409개 도구 파일 해시가 일치한다.
  최종 결과와 제한: [상위 평가 기록](../../../wiki/experiments/pbt-offline-evaluation.md).
  재귀 타입/힙 계약 및 generic datatype 관측 등의 명시된 지원 제한은 남는다.
- 본 범위의 남은 필수 작업·차단 결함·활성 프로세스는 없다. 이전 실패와 부분 실행을 보존했고,
  유료 공급자 실행·새 의존성·커밋은 추가하지 않았다. 별도 IO 지원 확장이나 유료 M5는 후속 범위다.


### 갱신 — 2026-09-27 03:43 UTC (R-7 owner 완료·bounded 독립 검증 승인)

- R-7 output local alias/backend diagnostic capture 수정 완료. 최종 production Driver
  `10d811c8f5b70f6307af073cad2dd116176de039e03eb26726b0e877dbd03489`, TestGeneration
  `36f61694b37cc02cd621bc3722fd11e8ec3b15d4c23203451ffb9d1166305816` (공개/net8.0 동일).
- `make build-dafny` 0 warnings/errors/27.51s; formatter exit0(workspace-load warning), final diff-check clean.
  Focus11/11 이후 최종 영향 범위 Driver **43/43 통과/3m28s**, TestGeneration Contract **279/279 통과/1m26s**.
  Core는 변경하지 않았고 기존27/27 근거를 유지한다. 전체 Driver suite를 R-7에서 다시 돌렸다고 주장하지 않는다.
- 첫 final no-build 시도는 testbin Core.dll/Prelude.bpl 누락으로 Driver12/31·TestGen200/79(passed/failed)였다.
  이 실패 로그를 보존했다. Test-only BuildProjectReferences=false로 의존 파일을 복구한 뒤 위 재검사가 통과했고,
  모든 public/net8.0 production DLL 해시는 복구 전후 동일했다. 빌드와 누락 시점의 연관 외 정확한 원인은 미확정이다.
- Fresh independent R-7 승인:9 multi-result campaigns/18 samples, runtime/legacy backend 진단, legacy worker success,
  ordinary CLI42, CoSyn integration4/4. 보고서 `/workspace/tmp/pbt-engine-output-final-review-20260927-codex/REPORT.md`.
  40개 production source/binary identity가 불변이었다. R-1–R-6 지원 한계는 그대로다.
- Owner source/check/document 인계 완료, 남은 프로세스 없음. 당시 남았던 root의 r5 M1/M2 결과와
  최종 수용 범위 기록은 위 완료 체크포인트에서 마쳤다. Frozen r4 및 모든 과거 결과를 보존했다.


### 갱신 — 2026-09-27 03:36 UTC (R-7 구현·build 완료, 최종 bounded 회귀·독립 검증 대기)

- Root r4 M1에서 multi-output datatype 검사 C# CS1628을 재현했다. 의도적 unsupported나 packaging 문제가 아니며,
  실제 backend 오류를 숨기는 보고 결함도 있었다. 상세 재현은 `/workspace/tmp/r4-m1-compile-investigation-20260927/REPORT.md`.
- R-7은 executable 출력형 검사의 fresh local alias와 backend output 캡처만 추가한다. 원래 계약/검사/관측 이름/와이어 필드는 보존했다.
  general goal/callee multi-output datatype·seq·map 정상/오류와 실제 CS0103의 CLI 전달 검사 **11/11 통과**.
- 최종 `make build-dafny` **exit0, 0 warning/error, 27.51s**, format exit0(workspace-load warning), diff-check clean.
  공개/net8.0 Driver SHA `10d811c8f5b70f6307af073cad2dd116176de039e03eb26726b0e877dbd03489`,
  TestGeneration SHA `36f61694b37cc02cd621bc3722fd11e8ec3b15d4c23203451ffb9d1166305816`.
- 이 production 소스/바이너리를 고정했다. 최종 no-build affected Driver 및 TestGeneration Contract와 fresh 독립 검증은 진행/대기 중이다.
  Root 승인에 따라 전체 Driver 반복 대신 R-7/structural/callee/closed/old/legacy compile를 검사한다. Core는 변경하지 않아 기존27/27 근거를 유지한다.
  Frozen r4와 진행된 M1/M2 원시 결과는 보존하며 root가 독립 승인 후 r5를 동결한다.


### 갱신 — 2026-09-27 03:25 UTC (R-1–R-6 owner 작업 완료·bounded 독립 검증 승인)

- R-1–R-6 수정과 일반 회귀를 완료했다. `make build-dafny` 0 warning/error, formatter exit0, diff-check clean.
  최종 production SHA는 아래 03:11 기록과 같고 test-only rebuild 전후 모든 production DLL 해시도 같다.
- 최종 owner TestGeneration Contract **279/279**, Core reducer **27/27** 통과.
  Driver Contract 전체는 **113 통과/1 실패/114**(기존 전체 의무 개수 가정)이며, 해당 assertion만 목표 postcondition
  선택으로 수정한 단일 재검사는 **1/1 통과**했다. 전체 aggregate를 통과로 재표기하지 않는다.
  Root가 이 scoped correction/recheck를 승인했으며 추가 전체 재실행은 요구하지 않았다.
- Fresh independent bounded review 승인: 요구 probe26개 기대 일치, 선택 Driver10/10, 실제 CoSyn 통합4/4.
  추가 generic datatype 관측 probe2개는 runtime error로 안전하게 제외돼 전체 예측 집계는26/28이다.
  보고서 `/workspace/tmp/pbt-engine-structural-final-review-20260927-codex/REPORT.md`.
- 재귀 타입 domain은 정상값도 unchecked이며, generic datatype 직렬화와 M2 ghost draft의 컴파일 가능성 한계가 남는다.
  §4.2의 오래된 non-null 제외 문구는 실제 formal/constructor-field 검사 범위로 갱신했다. class heap invariant는 제외한다.
- Owner 수정·검사 인계는 완료했고 전체 계획은 root의 새 M1/M2 결과/마감을 기다려 `in-progress`로 유지한다.
  Root가 production identity를 보존한 r4(1408 files, manifest SHA256
  `8ef2ffbbf2f3715b58746afe2d3b878415472c96a11d3807c6ec9c53bcc15863`)를 동결하고 M1을 시작했다고 통지했다.
  완료 결과는 아직 주장하지 않는다. source/build 변경이나 추가 검사 프로세스는 없다.


### 갱신 — 2026-09-27 03:11 UTC (R-6 구조적 선언형 유효성 구현·build 완료)

- R-6: datatype 필드 제약, map range, 깊이 4 cutoff, non-null formal/constructor field 누락을 고쳤다.
  타입 제약이 있는 함수의 발견과 spec/nested 입력형 검사도 연결했다. 일반 집중 검사 17/17 통과.
- 검사할 수 없는 recursive/ghost/codatatype 및 지원 밖 구조는 `unchecked`다. 클래스 heap invariant나 객체 생성은 추가하지 않았다.
- 최종 `make build-dafny`: exit0, 0 warning/error, 27.37s. 공개/net8.0 SHA-256:
  Driver `5cf53cadfd87cdd8a336050ebeb35d8e4b9d5c7874d7e443921069d17dc7727e`,
  TestGeneration `d37a454ffe5f2abb4fc4dca70d9fe70d711aa6bbc5d9d56ec9e764e778e36ba3`.
- 이 소스/바이너리는 고정했다. final no-build owner 3종 회귀와 root 독립 검증이 남아 있다.
  로그 `/workspace/tmp/r8-final-{driver-contract,testgen-contract,core-reducer}-host.log`.


### 갱신 — 2026-09-27 02:55 UTC (R-5 구현·집중 검사·build 완료, final 회귀 진행)

- R-5 helper 렌더링 1줄 수정과 일반 회귀 12개가 들어갔다(12/12 통과). 원본 타입 제약과 와이어 필드는 그대로다.
- 최종 `make build-dafny`는 0 warning/error, 31.34s로 완료됐다. 공개/net8.0 복사본의 SHA-256:
  Driver `56aa056b40ec2cb65ba9530e95a7f397c1f2f29ff7c568d740c83da68a6810f2`,
  TestGeneration `b428ecf9b415f6b6295f87442b106d8ff9c56386ff7e7411aae9dda011980d8b`.
- R-5 소스/바이너리를 고정했다. final `--no-build` 3종 owner 회귀가 실행 중이며 root가 새 독립 검증을 진행한다.
  간접 predicate(`Accept` → 계약 위반 `Bad`) 1표본 probe도 valid=0/callee 위반1로 분리됐다. 추측만으로 traversal을 바꾸지 않았다.


### 갱신 — 2026-09-27 02:43 UTC (R-1–R-4 구현, 최종 로컬 검사·독립 검증 진행)

- 독립 검증 보고서의 네 일반 결함(FBM callee 정의 등식, 미실행 spec requires, 중첩 callee 계약, old 호출)을 수정했다.
  아래 "independent-review follow-up R-1–R-4" 변경표와 진행 기록이 이번 작업 범위다. 원본 계약·IO 생성·와이어 필드·r3 snapshot은 유지한다.
- 최종 `make build-dafny` host 실행은 0 warning/error, 27.42s로 완료됐다. 공개/net8.0 복사본 SHA-256:
  Driver `56aa056b40ec2cb65ba9530e95a7f397c1f2f29ff7c568d740c83da68a6810f2`,
  TestGeneration `61999c4305475f1e9dfbe74f9765f56b762b7b6f749285a1c3b054fdc864b553`.
- 소스/바이너리는 고정했다. 남은 owner 검사는 final `--no-build` Driver Contract, TestGeneration Contract, Core reducer다.
  root가 새 독립 엔진 검증과 r4 snapshot/오프라인 M1/M2 실행을 맡는다. 이 작업들은 아직 완료로 주장하지 않는다.
- 의도적 한계: 같은 callee 계약에 다시 들어갈 때 객체/receiver/datatype/generic 값 또는 reads frame은
  힙 상태 동일성을 증명하지 못하므로 `recursive_heap_contract` unchecked다. 스칼라·재귀적으로 불변인 collection의
  정적 함수는 함수·인자·반환값이 같은 진행 중 의무만 공유한다. 검증하지 않은 by-method frame 순수성은 가정하지 않는다.

### 갱신 — 2026-09-27 (검증자 D-0–D-15 수정, 구현 context 결과, 독립 재검증 전)

- 검증자 결함 D-0–D-14와 root 보고 D-15를 고쳤다(§7 "T8 verifier follow-up" 행, §11 2026-09-27 항목, §4.2 추가 규칙).
  상태는 `in-progress`다. 다음 작업은 새 독립 검증과 root M1/M2 재실행이다.
- 새 바이너리 SHA-256: `Binaries/{,net8.0/}DafnyDriver.dll` = `1782ffe29f85bc3b176c47d09fee03e30f7cc5bf581e249cfcdd6e253ee62824`,
  `Binaries/{,net8.0/}DafnyTestGeneration.dll` = `af4d7318a8d9d7457d7c99cc290d5665e38d7c2c2c85923ef87779b5102ea544`.

### 갱신 — 2026-09-26 15:20 UTC (구현 context 결과, 독립 검증 전)

- H-E1–H-E5 구현과 fixture가 들어갔고 구현 context의 검사는 통과했다(§11 13:55–15:20 기록). 상태는 여전히
  `in-progress`다. 다음 작업은 새 독립 검증 에이전트의 요구사항 기준 재검사와 root M1/M2 재실행이다.
- 새 바이너리(`make build-dafny`, 0 warning/error) SHA-256: `Binaries/net8.0/DafnyDriver.dll` =
  `Binaries/DafnyDriver.dll` = `30949a7b5cdac77136af543d5954d727b75647b97a8f9f20bc685c261a27fd9c`.
- 아래 13:44 표는 역사 기록이다. 각 H-E 항목의 수정 파일/심볼과 fixture는 §11에 있다.

### 현재 인계 지점 — 2026-09-26 13:44 UTC

- 구현은 이미 진행됐다. T0부터 다시 시작하지 않는다. 이 절의 H-E1–H-E5가 다음 작업이다.
  사용자는 일반 메서드와 함께 **function-by-method goal 지원**을 명시적으로 승인했다.
  유료 실험, 새 패키지, 커밋은 승인하지 않았다.
- 마지막 구현/검증 하위 에이전트가 작업공간 spend cap 오류로 종료됐다. 소스 변경을
  보존했으며, 마지막 변경의 빌드/검사 결과는 미확인이다. 상태는 `in-progress`다.
- 마지막 **확인된 전체 Runtime Driver 검사**:
  `/workspace/cosyn/dafny`에서
  `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~ContractRuntime -v minimal`:
  **33 passed / 1 failed**, 34 total, 2m25s.
  로그 `/workspace/tmp/engine-resume-tests-host.log`. 실패는 F25
  `ConstructsHiddenGhostRegion`의 `_default.Read` 해석 오류다. 아래 최신 소스 수정 이후
  완료된 반복 검사 결과는 없다. 예전 20/20 또는 24/25 기록으로 현재 트리를 통과 처리하지 않는다.
- 최신 소스에는 `DiagnosticReachable`, `MakeGeneratorVisible(..., constructors)`,
  goal/generator를 기준으로 한 선택적 ghost 함수/필드/생성자 변환,
  runner의 2단계 생성자 이름 해석, imported `StaticReceiverExpr.ContainerExpression`
  보존이 들어 있다. 이 부분부터 diff와 테스트를 확인한다. 마지막 에이전트가 집중 검사를
  시작했지만 세션/종료 결과를 전달하기 전에 종료됐다.
- 루트가 작성한 `ContractRuntimeSourcePreparation.cs`와 해당 9개 테스트,
  `ContractStubRuntime.cs`의 `SerializeNamed`, `ContractRuntimeInstrumentation.cs`의
  `InputValues`/`Location`, 새 `ContractRuntimeObservationTests.cs` 3개는 같은 공유 트리에
  있다. 이전 담당자 동시 편집은 끝났으므로 새 담당자가 맡을 수 있지만, 기존/다른 작업을
  되돌리지 않는다. 참조 `ContractValue`에는 `fields`를 추가하지 않는다.

| 다음 작업 | 정확한 시작 지점 / 증거 | 필요한 수정과 완료 조건 |
| --- | --- | --- |
| H-E1: 현재 부분 수정 검증 | `ContractRuntimeObligationTransformer.cs`: `DiagnosticReachable`, `MakeGeneratorVisible`, `RuntimeSubstituter`; `ContractRuntimeCampaignRunner.cs`: generator 준비 2단계; F25 | imported receiver와 도달 가능한 생성자만 변환하는 수정이 빌드/집중 테스트를 통과하는지 확인한다. 실제 Process/Digits r3의 IO ghost 할당 실패를 일반 fixture로 줄여 통과시킨다. 관련 없는 포함 파일의 ghost 초기화를 강제로 실행 가능하게 만들지 않는다. |
| H-E2: ghost 필드값 누락 | `/workspace/tmp/fresh-pbt-verification/ghost-field{.json,.result.json}`; `ContractStubRuntime.cs`: `heapShapes.fields`의 `!field.IsGhost`; `ContractCompilerWorker.CompileRuntimeAsync` | `Box`의 `ghost var f := 7`, goal `ensures x.f == 8`는 위반을 찾지만 `x.f` 값이 빠진다. 실제로 컴파일된 ghost 필드만 metadata/캡처에 포함한다. 원본 계약/SMT용 프로그램과 실행 metadata를 혼동하지 않는다. `inputs`/`values`에 flat `x.f` 값이 보이는 컴파일 실행 테스트가 필요하다. |
| H-E3: FBM 정의 등식 | `/workspace/tmp/fresh-pbt-verification/fbm-equivalence{.json,.result.json}`; goal wrapper/기존 callable descriptor | `function Goal(x:int):int {x+1} by method {return x;}`가 `valid=1`, obligations 없이 `no_violation_found`였다. 명시적 `ensures`뿐 아니라 원래 함수 정의와 by-method 반환의 등식 의무를 보존·판정한다. 원래 정의 위치/원문을 보고하고 불일치를 위반으로 찾는 일반 fixture가 필요하다. |
| H-E4: 의무 평가 중 callee 유효성 | `ghost-function-contract`와 `ordinary-spec-function-contract` 요청/결과; `InstrumentCalls`, `Check` | `function Bad(x:int):(b:bool) ensures b {false}`를 goal `ensures Bad(x)`에서만 호출하면 callee의 잘못된 결과를 유효한 goal 반례로 보고했다. 원래 의무 식을 평가하는 함수 호출에도 callee 계약 유효성 검사를 적용하고, 잘못되거나 미검사인 callee는 표본 분모에서 분리한다. 검사 자체의 재귀/중복 래핑을 피하며 ordinary/ghost fixture를 각각 추가한다. |
| H-E5: FBM 미구현 callee handshake | `/workspace/tmp/fresh-pbt-verification/fbm-missing-draft{.json,.result.json}` | FBM by-method 본문에서 본문 없는 `Helper`를 호출하는 요청이 `ExprRhs` clone assertion으로 worker를 종료했다. 원래 `requires`/계약은 유지하고 도달성을 by-method 본문까지 추적하여 실행 전에 `drafts_required`를 돌려준다. 이 재현은 frozen r3에서 관찰했고 최신 소스 재확인이 필요하다. |

모든 fresh probe는 immutable
`/workspace/tmp/experiment/pbt-probe-toolchain-20260926-r3/net8.0/DafnyDriver.dll`로
실행했다. **새 소스에서 아직 재확인되지 않은 결함**이라는 범위를 유지한다.
각 요청은 독립 일반 fixture이며 benchmark 코드를 복사하지 않았다.

실제 cat 요청/결과도 보존되어 있다:

- Process 요청 `/workspace/tmp/dafny-runtime-check-3f1892ea9397407f941b26ceedea0d33/request.json`.
- Digits 요청 `/workspace/tmp/dafny-runtime-check-1e450936ad954c19aaaa18af8f7d320c/request.json`.
- r2/r3 출력 `/workspace/tmp/experiment/pbt-guarded-{process,digits}-probe-20260926-r{2,3}.json`.
  r3는 `Generator resolution failed`, IO.dfy 16개 `only ghost methods can be called from this context`.
  IO.Init는 `requires false`와 비결정적 ghost 초기화를 갖는다. 이 계약을 완화하거나 IO 상태를
  임의로 만들지 않는다. 순수 목표의 관련 없는 IO 의존성이 발목을 잡는 문제부터 분리한다.

다음 검사 순서(이 인계에서는 실행하지 않음):

1. §9의 owner 명령을 사용하되 native 테스트는 `--no-restore -m:1`을 붙인다.
   먼저 F25/H-E1 집중 검사, 다음 Runtime 전체와 H-E2–H-E5 새 fixture를 실행한다.
2. TestGeneration Contract, Driver Contract, Core ContractExpressionReducer 회귀와
   `make format`, `git diff --check`를 끝낸다. 이전 독립 회귀는 각각 279/미완료/27 통과였고,
   현재 변경 이후 결과는 아니다.
3. `/workspace/cosyn`에서 `make build-dafny`를 완료하고 새 바이너리 hash를 기록한다.
   Driver만 빌드하면 공개 `dafny`가 오래된 assembly를 쓸 수 있다. 인계 시 SHA-256:
   `Binaries/net8.0/DafnyDriver.dll` = `8ce31e15bac76ccfc708022957f6c2895bc37110fbc3f9e10afbe7e260d86d4e`,
   `Binaries/DafnyDriver.dll` = `ddb079fef1a8b19910d9a36ab7b8189c5849c0d5fec515421063ba81e166a1ea`.
   서로 다르며 최신 전체 빌드가 보장되지 않는다.
4. 새 독립 검증 에이전트가 요구사항/현재 파일에서 확인하고, root가 새 toolchain snapshot과
   결과 경로에서 M1/M2를 재실행한다. 기존 결과를 덮어쓰지 않는다.

환경: sandbox `dotnet test`는 loopback SocketException(13)으로 중단될 수 있어 승인된
host 실행이 필요하다. 이 제한을 검사 통과로 간주하지 않는다. 기준 HEAD `f775837e`
이후 dirty 트리이며 source-only 수정과 바이너리 checkpoint를 구분한다.

- 먼저 읽을 것: `AGENTS.md`, `CLAUDE.md`, `wiki/contract-testing.md`, 상위 계획의 "Decisions",
  이 문서 §4–§7.
- 구현 순서: T0 → T1 → T2 → T3 → T4 → T5 → T6 (M1 완료) → T7 → T8 (M2) → T9. §4 와이어 계약은
  T1에서 고정하고, 이후 바꾸면 CoSyn 계획의 C-T1 담당에게 알린다(계획 진행 기록에 남김).
- 금지:
  - 벤치마크 전용 구문, 분기, 값을 추가하는 것(`BenchIO`, filesystem, coreutils 이름 등).
  - 기존 `test-contracts` 모드(fixed, `--generate`, `--symbolic`)의 요청·결과·동작을 바꾸는 것.
  - 생성 파일을 손으로 편집하는 것(`AGENTS.md` 목록).
  - 새 NuGet package를 추가하는 것. 필요해지면 먼저 사용자 승인을 받는다.
- 환경:
  - .NET SDK 8, 시스템 Z3.
  - 빌드는 `/workspace/cosyn`에서 `make build-dafny`로 한다. DafnyDriver만 빌드하면
    `Binaries/Dafny` wrapper의 복사된 assembly가 stale해질 수 있다.
  - `/usr/bin/dafny`는 `Binaries/Dafny`를 가리키는 symlink다.
  - 다른 세션(Codex 등)이 CoSyn 쪽을 동시에 편집할 수 있다. 이 저장소의 기존 변경은 보존한다.
- 완료 보고: 각 T의 완료 조건과 실행한 명령·결과를 §11 진행 기록에 남긴다. 검증은 구현과
  분리된 새 에이전트가 수행한다.

## 1. 목표

`dafny test-contracts <request.json> --runtime-check`를 추가한다. 이 모드는 닫힌 source snapshot의
goal 메서드를 모델 작성 generator가 만든 구체 입력으로 여러 번 실행한다. 그리고 다음 세 종류
의무의 위반을 구체값과 함께 보고한다.

1. goal postcondition (반환 시점)
2. goal 본문 loop invariant (진입 시점, 매 loop head 재진입 시점)
3. goal 본문에서 호출한 callee의 precondition (호출 시점)

절(clause) 판정은 ghost를 제거해 컴파일한 코드의 런타임 평가(RAC)가 기본이다. 컴파일할 수 없는
절은 checkpoint에서 캡처한 구체값을 전제로 하는 닫힌 식 SMT 질의(closed SMT)로 판정한다.
unknown, timeout, 값 없음, 예산 소진은 `unchecked`다. 증명 수준 SMT 결과는 증거로 쓰지 않는다.

## 2. 수용 기준

- R1. 일반 fixture에서 세 종류 위반 각각에 대해 다음을 보고한다. 같은 seed와 ordinal로 다시
  실행(replay)하면 같은 위반이 재현된다.
  - obligation ID, 종류, 절 위치와 원문
  - 입력값과 절이 읽는 값
  - 반복 번호(invariant)
  - 판정 방법(`runtime` / `closed_smt`)
- R2. 다음을 포함한 절이 `runtime`으로 판정된다(opaque는 진단 빌드에서 무시한다).
  - ghost 지역변수, ghost 출력 매개변수, ghost 대입
  - 재귀 ghost function, opaque function/predicate
  - subset type/newtype 제약, 유한 set/map comprehension, 경계가 있는 정량자
- R3. 컴파일할 수 없는 절은 `closed_smt`로 판정된다(예: 무한 정량자). 값을 얻을 수 없거나,
  solver가 unknown/timeout이거나, 예산이 소진되면 `unchecked`와 이유를 남긴다.
- R4. draft가 없는데 실행 경로에서 호출될 수 있는 미구현 callee가 있으면 캠페인을 실행하지 않고
  `drafts_required`를 반환한다. 미구현 callee의 기준은 본문 없음, `assert false;`만 있는 본문,
  본문 없는 `{:extern}` 메서드다. generator가 없으면 `generator_required`를 반환한다.
- R5. 표본 유효성 규칙(§6.5)에 따라 유효한 표본에서만 goal 위반을 보고한다. 원본 `requires`
  실패와 callee 계약 위반은 따로 집계한다.
- R6. 결과에 §4의 분모(population)와 obligation별 판정 방법 집계가 들어 있다. 실행 표본 0개는
  `no_violation_found`가 될 수 없다.
- R7. 비종료 표본은 표본별 timeout으로 끊고 `timeout`으로 기록한 뒤 다음 ordinal로 진행한다.
- R8 (M2). 진단 빌드에서 다음을 처리한다.
  - 모든 export set을 `reveals *`로 바꾼다.
  - ghost 필드와 ghost 생성자를 컴파일 대상으로 바꾼다.
  - 클래스의 `{:extern}`을 제거해 generator가 `new`로 객체를 만들 수 있게 한다.
  - `old(E)`는 진입 시점에 E를 미리 계산해 판정한다. `unchanged`는 필드 비교로 전개한다.
    `fresh`/`allocated`는 `unchecked`로 둔다.
  - `{:extern}` 메서드는 draft로 대체한다.
- R9. 기존 모드와 기존 테스트가 그대로 통과한다.

## 3. 비목표

- lemma goal, `assert` 문, frame(`modifies`/`reads`) 위반, 종료성 검사.
- 증명 성공 판정, 기존 contract testing과의 결과 병합.
- JSON 패턴 DSL과 executor baseline의 이 모드 적용(후속 가능). M1 입력원은 모델 generator뿐이다.
- 결과 축소(shrinking). 대신 위반마다 직렬화 크기가 가장 작은 표본을 고른다.
- abstract choice로 draft 부재를 대체하는 것(상위 D2).

## 4. 와이어 계약 (정본)

규약은 기존과 같다(`ContractJson`, `ContractTestModels.cs:8-15`).
- camelCase, `UnmappedMemberHandling.Disallow`, enum은 snake_case 소문자 문자열,
  `SchemaVersion = 1`.
- 새 레코드는 `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeModels.cs`(신규)에 둔다.
- CLI는 기존 명령처럼 결과를 stdout 한 줄 JSON으로 쓰고, 종료 코드는 항상 0이다
  (`TestContractsCommand.cs:138`).

### 4.1 요청 `ContractRuntimeCampaignRequest`

```json
{
  "schemaVersion": 1,
  "sources": [{"path": "src/M.dfy", "content": "...", "sha256": "..."}],
  "dependencies": [],
  "entry": {"symbol": "M.Sum"},
  "drafts": [{"symbol": "M.Helper", "path": ".top-down-pbt/drafts/M.Helper.dfy",
               "content": "...", "sha256": "..."}],
  "generator": {"path": ".top-down-pbt/generators/M.Sum.dfy", "content": "...", "sha256": "..."},
  "seed": "1234567890123",
  "sampleCount": 64,
  "sampleTimeoutMilliseconds": 5000,
  "timeoutMilliseconds": 240000,
  "maxClosedQueries": 16,
  "closedQueryTimeoutMilliseconds": 10000,
  "maxViolationsPerObligation": 3,
  "replayOrdinal": null
}
```

필드 규칙:
- `seed`는 10진 문자열(`ulong`)이다.
- `generator`가 null이면 `generator_required`를 반환한다.
- `replayOrdinal`이 주어지면 그 ordinal 하나만 실행한다.
- `drafts[].symbol`은 원래 선언의 `FullDafnyName`이다. 경로는 source 경로와 겹치면 안 된다.
- 경로 검증은 기존 `ContractSource` 규칙을 따른다(상대 경로, sha256 재계산).

### 4.2 결과 `ContractRuntimeCampaignResult`

```json
{
  "schemaVersion": 1,
  "status": "violation_found",
  "reason": "",
  "seed": "1234567890123",
  "population": {"generated": 64, "preconditionRejected": 10, "preconditionUnchecked": 0,
                  "executed": 54, "valid": 50, "calleeContractViolations": 2,
                  "calleeContractUnchecked": 0, "runtimeErrors": 1, "timeouts": 1,
                  "violatingSamples": 3},
  "obligations": [{"id": "loop_invariant_maintenance:src/M.dfy:12:14:0",
                    "kind": "loop_invariant_maintenance", "path": "src/M.dfy", "line": 12,
                    "column": 14, "clause": "r == Sum(s[i..])", "callee": null,
                    "decisionMethod": "runtime", "uncheckedReason": null,
                    "evaluations": {"runtime": 812, "closedSmt": 0, "unchecked": 0},
                    "violations": 3}],
  "violations": [{"obligationId": "...", "kind": "loop_invariant_maintenance",
                   "sampleOrdinal": 17, "iteration": 4, "decisionMethod": "runtime",
                   "inputs": {"s": {"kind": "sequence", "items": ["..."]}},
                   "values": {"i": {"kind": "integer", "value": "1"}}}],
  "calleeViolations": [{"obligationId": "...", "callee": "M.Helper", "draft": true,
                         "sampleOrdinal": 5, "inputs": {}, "values": {}}],
  "missingDrafts": [],
  "missingGenerator": null,
  "deghostExclusions": [{"symbol": "M.Measure", "reason": "resolver rejected compiled copy: ..."}],
  "runtimeErrors": [{"sampleOrdinal": 9, "message": "index out of range", "location": "src/M.dfy:20:8"}],
  "diagnostics": ""
}
```

- `status`는 `violation_found | no_violation_found | drafts_required | generator_required |
  inconclusive | unsupported | error` 중 하나다.
- `obligations[].kind`의 goal 의무는 `postcondition | loop_invariant_entry |
  loop_invariant_maintenance | call_precondition`이다. 내부 장부용으로
  `entry_precondition | callee_postcondition`이 추가된다.
- `decisionMethod`는 `runtime | closed_smt | unchecked`다.
- 값은 기존 `ContractValue` 인코딩(`ContractTestModels.cs:25-28`)이다.
  참조값은 기존 `reference`와 안정적인 ID를 유지하고, 컴파일된 필드값은
  `inputs`/`values`의 `box.value` 같은 별도 키로 캡처한다. 순환 참조는 같은 ID로
  표시하고 재귀적으로 다시 펼치지 않는다. `reference` 값에 새 `fields`를 붙이지 않는다.
- `missingDrafts[]`는 `{symbol, kind: method|function|extern_method, path, line, signature, contract}`다.
  `signature`와 `contract`는 원문 텍스트다.
- `missingGenerator`는 `{symbol, signature}`다. `signature`는 요구되는 generator 서명의 텍스트이며,
  §5.2 형식에 goal formal을 채운 것이다.
- `runtimeErrors`는 최대 20개까지 담는다. 초과분은 개수만 `population.runtimeErrors`에 남긴다.
- (2026-09-27, 필드 집합 불변) 선언된 subset type/newtype 제약도 같은 경계의 의무다. goal 입력은
  `entry_precondition`(거짓이면 `precondition_rejected`, 실행 불가 제약이면 `precondition_unchecked`), goal 출력은
  `postcondition`, goal 호출 지점의 callee 입력은 `call_precondition`, callee/draft 출력은 `callee_postcondition`으로
  판정한다. spec/nested callee 입력형은 `callee_postcondition` 유효성 경계로 판정한다. 절 원문은
  `<이름>: <형>`, 위치는 formal(호출 지점 입력은 호출 위치)이다. non-null formal과 datatype constructor field도
  명시적으로 검사한다. 유한한 collection 중첩, map key/value, 비재귀 datatype constructor field의 선언형 제약을
  따라간다. recursive/ghost/codatatype 등 실행할 수 없는 구조는 unchecked이며, 임의의 class heap invariant는 제외한다.
- `obligations[].violations`는 그 의무 종류가 표본 분류를 결정한 표본의 실패 평가만 센다: goal 의무는 유효 표본,
  `entry_precondition`은 `precondition_rejected` 표본, `callee_postcondition`은 `callee_contract_violation` 표본.
  `evaluations`는 모든 표본의 평가를 센다.
- `closed_smt` 판정은 값 전제 아래 절이 증명되면 성립, 부정이 증명되면 위반이며, 그 밖은
  `unchecked`(`closed_query_undecided|timeout|error`)다. 계약 있는 함수를 부르는 closed 절은 goal 위반(또는 입력 수용)을
  내지 않고 `callee_contract_unvalidated`로 남는다. 컴파일된 진단에 check가 남지 않은 의무는 `runtime`이 될 수 없고
  closed_smt 또는 `unchecked`(`runtime_check_not_compiled`)다.
- `status = no_violation_found`는 유효 표본에서 goal 의무 평가가 한 번 이상 결정(runtime 또는 closed_smt)됐을 때만
  가능하다. 아니면 `inconclusive`("No goal obligation was decided in a valid sample.").
- 배열 값은 `reference`와 평면 `name.Length`, `name[i]`로 캡처한다. 본문 없는 `{:extern}` function draft의 kind는 `function`이다.
- `deghostExclusions`는 §6.2의 고정점이나 재resolve 복구 루프 때문에 컴파일 대상에서 빠진
  선언·변수와 그 이유다. CoSyn 요약에 그대로 표시된다.
- 책임 경계: draft가 "현재 계약에 맞는 최신 draft"인지 고르는 일은 CoSyn draft 저장소의
  책임이다(계약 지문 키). 엔진은 계약 지문을 모른다. 엔진은 서명 일치만 검사하고, 원래 선언의
  계약으로 draft를 판정한다.

## 5. 모델 작성 파일 형식 (CoSyn prompt가 이 형식을 안내)

### 5.1 draft

- 파일 이름: `.top-down-pbt/drafts/<FullDafnyName>.dfy`
- 내용: 원래 선언과 서명이 같은 선언 하나를 둔다. 원래 선언과 같은 종류, 이름, 타입 매개변수,
  매개변수, 반환이어야 한다. 여기에 `{:pbt_draft "<FullDafnyName>"}` 속성을 붙인다.
- 계약: draft에 적힌 계약은 무시하고 원래 선언의 계약이 기준이다. 본문은 컴파일 가능한 코드여야
  한다.
- 보조 선언: 같은 파일에 컴파일 가능한 보조 선언(function, method, datatype)을 둘 수 있다.
  보조 선언은 대상 모듈의 최상위에 삽입한다. 이름이 충돌하면 `unsupported`로 거부한다.
- 클래스 멤버 draft: 본문은 클래스 멤버 본문에 들어가고, 보조 선언은 모듈 최상위에 들어간다.

```dafny
method {:pbt_draft "M.Helper"} Helper(x: int) returns (y: int)
{
  y := if x < 0 then -x else x;
}
```

### 5.2 generator

- 파일 이름: `.top-down-pbt/generators/<goal FullDafnyName>.dfy`
- 서명: `method {:pbt_generator "<goal>"} Generate(r: PbtRandom.Source) returns (<goal 입력>)`
  - 반환은 goal의 입력 formal을 순서대로, 같은 이름과 타입으로 둔다. ghost formal도 포함한다.
  - 인스턴스 메서드면 첫 반환은 `receiver: <클래스>`다.
- 삽입 위치: goal 모듈 최상위.
- 사용 가능한 것: 컴파일 가능한 코드만 쓸 수 있다. `new` 할당과 goal 모듈이 볼 수 있는 선언을
  사용할 수 있다. M2에서는 export 제한이 없다.
- ghost 입력 formal: 타입이 컴파일 가능하면(예: `seq<int>`, datatype) 일반 반환값으로 만들고,
  진단 빌드에서 goal의 해당 formal은 ghost를 제거한다. 타입이 컴파일 불가이면(`ORDINAL`, `iset`,
  `imap`, ghost 전용 타입 등) generator로 만들 수 없다. 이 경우 캠페인은 `unsupported`
  (`non_compilable_input_type: <formal>`)다.

```dafny
method {:pbt_generator "M.Sum"} Generate(r: PbtRandom.Source) returns (s: seq<int>)
{
  var n := r.Nat(r.Size());
  s := [];
  while |s| < n decreases n - |s| { var v := r.Int(-5, 5); s := s + [v]; }
}
```

### 5.3 엔진 제공 모듈 `PbtRandom` (진단 빌드에만 삽입)

```dafny
module PbtRandom {
  class {:extern "DafnyPbtRuntime", "Source"} Source {
    method {:extern} Int(lo: int, hi: int) returns (v: int) requires lo <= hi ensures lo <= v <= hi
    method {:extern} Nat(bound: nat) returns (v: nat) ensures v <= bound
    method {:extern} Bool() returns (b: bool)
    method {:extern} Char(lo: char, hi: char) returns (c: char) requires lo <= hi ensures lo <= c <= hi
    method {:extern} Index(n: nat) returns (i: nat) requires n > 0 ensures i < n
    method {:extern} Size() returns (s: nat)
  }
}
```

- C# 구현은 `SHA256(seed ‖ ordinal ‖ counter ‖ domain)` counter stream이다. 기존
  `ContractPatternSampler.CounterStream`(`ContractPatternSampler.cs:323-360`)과 같은 바이트 규약을
  쓰고, `domain = "pbt-random"`이다.
- `Size()`는 ordinal에 따라 커지는 크기 힌트다: `min(2 + ordinal / 4, 32)`.
- 모듈 이름이 사용자 코드와 충돌하면 `unsupported`로 거부한다.

## 6. 알고리즘

### 6.1 진단 빌드 구성

기존 방식과 같이 원문에 대한 텍스트 편집 목록(`(position,length,text)`)을 만든다. 이 편집 목록을
한 번에 적용한 뒤 재파싱하고 재resolve한다. 기존 방식은 `ContractHarnessBuilder.RuntimeSourceForFile`
(`ContractHarnessBuilder.cs:175-513`, 적용부 462-486)과 `ContractSourceSnapshot.ApplyEdits`
(`ContractSourceSnapshot.cs:21-49`)에 있다. 위치는 resolve된 AST 토큰 범위에서 얻는다.

### 6.2 ghost 제거 대상 판정 (고정점)

원본 snapshot을 resolve한 뒤 도달 집합을 만든다. 도달 집합은 goal, 실행될 callee 본문,
draft, generator와, 검사 대상 절이 참조하는 선언들이다.

1. 후보 D: 도달 가능하고 본문이 있는 ghost function/predicate 전부. twostate와 `by method` ghost
   부분은 제외한다.
2. f ∈ D를 제거하는 조건: f의 본문(또는 requires)에 다음 중 하나가 있으면 제거하고, 변화가 없을
   때까지 반복한다.
   - D 밖의 ghost function 호출이나 ghost method/lemma 호출. `StmtExpr`의 lemma 부분은 버리고
     식만 남긴다.
   - 컴파일 불가 타입(`iset`, `imap`, `ORDINAL`, ghost 전용 타입).
   - resolver가 유한 경계를 찾지 못한 정량자나 comprehension. `QuantifierExpr.Bounds`의
     unbounded pool로 판정한다.
   - 함수 안의 let-such-that, `old`/`fresh`/`allocated`/`unchanged`.
3. ghost 지역변수와 ghost 출력 매개변수: 타입이 컴파일 가능하고 모든 대입의 우변이 D 기준으로
   컴파일 가능하면 제거 대상 L에 넣는다. 이것도 고정점으로 계산한다.
4. 절 c는 식이 D, L 기준으로 컴파일 가능하면 `runtime`, 아니면 `closed_smt` 후보다.
   `closed_smt` 후보 중 L 밖 ghost 지역변수를 읽는 절은 `unchecked`(`value_unavailable`)다.
5. 편집 규칙:
   - D와 L의 `ghost` 키워드를 제거한다. `{:opaque}`/`opaque`는 제거하고 `reveal`은 삭제한다.
   - 증명 전용 문장을 제거한다: `assert`, `assume`, `calc`, `reveal`, lemma 호출, 증명용 `forall`
     문, 제거 대상 밖 ghost 변수에 대한 대입.
   - 실행 경로에 남은 `assert false`는 `PbtBridge.Unreachable(<위치>)` 호출로 바꾼다.
   - 기존 `ExpressionTester.UsesSpecFeatures`(`DafnyCore/Resolver/ExpressionTester.cs:477`)와
     `CheckIsCompilable`(`:34-35`)을 보조 판정에 재사용한다.
6. 재resolve가 실패하면 다음을 한다. 오류 위치를 포함한 선언이나 변수를 D/L에서 빼고 다시
   시도하되 최대 5회까지 한다. 그래도 실패하면 `unsupported`와 resolver 진단을 반환한다.
   - 조용히 통과시키지 않는다. 뺀 항목은 `diagnostics`에 남긴다.
   - 설계 대안으로 PreResolve AST 재작성기도 가능하다. 다만 기존 엔진이 텍스트 편집 방식이고
     `ExpectContracts`(`DafnyCore/Rewriters/ExpectContracts.cs:18-35`)는 계약 래퍼 선례일 뿐이다.
     그래서 텍스트 편집을 기본으로 한다. T0에서 바꿀 근거가 나오면 이 절을 갱신한다.

### 6.3 의무 검사 삽입

- goal 래퍼: 원래 goal을 호출하는 `<Goal>__pbt_goal` 메서드를 추가한다. 래퍼는 다음 순서로
  동작한다.
  1. 진입 시 `old(E)` 하위식을 모두 미리 계산해 지역변수에 둔다.
  2. goal의 `requires`를 판정한다.
  3. 원래 goal을 호출한다.
  4. `ensures`를 판정한다.

  이렇게 하면 모든 `return` 지점을 한 곳에서 검사한다.
- loop invariant (goal 본문의 `while`/`for`, 중첩 포함):
  - 루프 직전에 `__pbt_iter_k := 0`을 두고 진입 검사(`loop_invariant_entry`)를 한다.
  - 본문 첫 문장 앞에서 `__pbt_iter_k > 0`이면 유지 검사(`loop_invariant_maintenance`,
    iteration = `__pbt_iter_k`)를 한 뒤 `__pbt_iter_k := __pbt_iter_k + 1`을 한다.
  - 루프 뒤에서는 `break`로 나오지 않았을 때만 마지막 유지 검사를 한다. 해당 루프를 대상으로
    하는 `break` 앞에 `__pbt_broke_k := true`를 삽입한다.
  - invariant 안의 `old(E)`는 goal 진입 시 계산한 값을 쓴다.
- callee precondition: goal 본문(래퍼 아님)의 호출 지점마다 전용 래퍼를 만든다.
  - 메서드 호출은 `<Callee>__pbt_site_<n>` 메서드, 식 안의 함수 호출은 같은 이름의 함수 래퍼다.
  - 호출 대상 이름 토큰을 래퍼 이름으로 바꾼다.
  - 래퍼는 `requires`를 판정한다(`call_precondition`, 위치는 호출 지점). 그다음 원래 callee를
    호출하고 반환 후 callee `ensures`를 판정한다(`callee_postcondition`).
  - callee `ensures`의 `old(E)`는 각 호출 지점 래퍼가 callee 호출 직전에 따로 계산한다. 이는 goal
    진입 시점의 old와 다른 상태다.
  - 함수 래퍼는 `var _ := PbtBridge.Check(...); Callee(args)` 형태의 let 식으로 만든다.
  - draft나 다른 callee 내부의 호출은 goal 의무가 아니다. 그 안의 실패는 런타임 오류나 callee
    계약 위반으로 집계된다.
- 판정 삽입 형태:
  - `runtime` 절: `if !(<clause>) { PbtBridge.Violation("<id>", <iter>, <values>); }`
  - `closed_smt` 절: `PbtBridge.Checkpoint("<id>", <iter>, <values>);`
  - `<values>`는 절의 자유 변수(매개변수, 지역변수, 제거된 ghost 변수, 미리 계산한 old 값)를
    기존 `ContractDiagnosticBridge.Serialize`(`ContractStubRuntime.cs` Serialize)로 인코딩한
    `seq<(string,string)>`이다.
  - 절 평가 중 예외(색인 초과 등)는 `clause_evaluation_error` 런타임 오류로 기록한다.
- entry precondition: `runtime` 절이 거짓이면 표본을 즉시 종료하고 `precondition_rejected`로
  기록한다.

### 6.4 캠페인 실행기 (`ContractRuntimeCampaignRunner.cs`, 신규)

1. 요청을 검증하고 snapshot, draft, generator를 파싱한다. 미구현 callee 판정을 먼저 한다.
   - 대상: goal 본문과 draft, generator에서 호출 가능한 모든 callable.
   - 미구현 기준: 본문 없음, `assert false;` 단일 문장 본문(주석과 공백 허용), 본문 없는 `{:extern}`.
   - 누락이 있으면 `drafts_required`, generator가 없으면 `generator_required`로 즉시 반환한다.
     둘 다 없으면 두 목록을 함께 반환한다.
2. §6.2–6.3 편집을 적용하고 `PbtRandom`과 `PbtBridge`를 삽입한 뒤 harness Main을 생성한다.
   - Main 흐름: `Seed/Ordinal` 읽기 → `Generate` → 입력 기록 → goal 래퍼 호출 → 표본 종료 기록.
   - 한 번 컴파일한다. 기존 `ContractCompilerWorker`의 staging, C# backend, SHA-256 검사
     (`ContractCompilerWorker.cs:16-84`)를 재사용하도록 공통부를 분리한다.
3. ordinal을 순회하며 표본마다 `dotnet <assembly> --pbt-seed S --pbt-ordinal k --pbt-out <file>`를
   `ContractExecutionProcess.RunAsync`로 실행한다. timeout은 `sampleTimeoutMilliseconds`이고,
   전체 `timeoutMilliseconds`를 넘으면 중단한다.
   - 이 모드는 동기 RPC가 필요 없다. 관찰은 JSONL 파일에만 쓴다.
4. 후처리(host): 모든 표본 실행이 끝난 뒤에 한다.
   - 예산 순서: 표본 실행 단계는 `timeoutMilliseconds - reserve`에서 멈춘다.
     `reserve = min(maxClosedQueries * closedQueryTimeoutMilliseconds, timeoutMilliseconds / 2)`이다.
   - 표본 timeout과 closed 질의 timeout은 서로 독립이다.
   - `Checkpoint` 관찰을 (obligationId, values 해시)로 중복 제거한다.
   - `maxClosedQueries` 한도 안에서 표본 ordinal 순서로 closed SMT를 판정한다.
   - 질의는 `ContractQueryBuilder`에 새로 추가하는 `BuildClosedClause`로 만든다. 캡처한 변수를
     매개변수로 받는 `ContractDiagnosticQuery` 메서드에 `requires x == <literal>`과
     `assert {:error "contract_query_target"} <clause>`를 넣는다.
   - `ContractSolver.CheckAsync`(`ContractSolver.cs:13-135`)를 새 query kind
     `ClosedClause`로 호출한다. Sat이면 위반, Unsat이면 성립, 그 밖은 `unchecked`다.
   - 한도를 넘은 것은 `unchecked`(`closed_query_budget_exhausted`)다.
5. 표본을 분류하고(§6.5) 결과를 조립한다. 위반은 obligation별로 입력 직렬화 크기가 작은 순서로
   최대 `maxViolationsPerObligation`개를 남긴다.

### 6.5 표본 유효성

- `precondition_rejected`: entry precondition이 `runtime`이나 `closed_smt`에서 거짓이다.
- `precondition_unchecked`: entry precondition이 `unchecked`다. 이 표본은 버린다.
- `callee_contract_violation`: 실행된 callee(draft 포함)의 `ensures`가 거짓이다. 이 표본은 goal
  위반 보고에서 제외한다.
- `callee_contract_unchecked`: 실행된 callee의 `ensures`가 `unchecked`다. 이 표본도 제외하고
  개수만 센다.
- `runtime_error`, `timeout`: 제외한다. 오류 목록에 남긴다.
- `valid`: 위 조건에 걸리지 않은 실행 표본이다. goal 위반(세 종류)은 여기서만 보고한다.
- 상태 결정 순서:
  1. 유효 표본에 goal 위반이 있으면 `violation_found`.
  2. `valid >= 1`이면 `no_violation_found`.
  3. 그 밖은 `inconclusive`(reason에 지배적 원인).

## 7. 작업 단계

| T | 파일·심볼 | 작업 | 완료 조건 |
| --- | --- | --- | --- |
| T0 | scratch 전용 | §6.2 규칙으로 손 변환 fixture 세 개(pure, 중첩 loop, ghost out)를 컴파일해 실행 모델을 확인한다. 편집 방식이 AST 재작성기로 바뀌어야 하는 근거가 있는지 기록한다 | §11에 결과 기록 |
| T1 | `ContractRuntimeModels.cs`(신규), `ContractTestModels.cs`(`ContractQueryKind`에 `ClosedClause` 추가) | §4 레코드와 enum | JSON round-trip 테스트, 알 수 없는 필드 거부 |
| T2 | `ContractRuntimeObligationTransformer.cs`(신규) | §6.2 판정과 편집 목록 생성, 재resolve 복구 루프 | 변환 단위 테스트 §8 F1–F8 통과 |
| T3 | 같은 파일 또는 `ContractRuntimeInstrumentation.cs`(신규), `ContractStubRuntime.cs` | §6.3 래퍼와 loop 편집, `PbtBridge`(Violation/Checkpoint/Check/Unreachable/Sample*)와 `PbtRandom` C# 구현을 bridge 소스에 추가 | F9–F14 실행 테스트 통과 |
| T4 | `ContractCallableSelector.cs`, `ContractSourceSnapshot.cs`, `ContractRuntimeSourcePreparation.cs`, `Source/DafnyTestGeneration.Test/ContractRuntimeSourcePreparationTests.cs` | 미구현 callee 판정, draft·generator 삽입, 서명 일치 검사 | F15–F18 통과 |
| T5 | `ContractRuntimeCampaignRunner.cs`(신규), `ContractCompilerWorker.cs`(공통 staging 추출), `ContractQueryBuilder.cs`(`BuildClosedClause`) | §6.4–6.5 | F19–F24 통과 |
| T6 | `Source/DafnyDriver/Commands/TestContractsCommand.cs` | `--runtime-check` 공개 옵션과 숨은 `--runtime-check-worker <result>` 옵션. 기존 `SuperviseAsync`(:239-265) 패턴을 따른다. 결과를 stdout 한 줄에 쓴다 | CLI 테스트 통과, 기존 옵션 회귀 없음. **M1 완료** |
| T5/T6 observation completeness | `ContractStubRuntime.cs`, `ContractRuntimeInstrumentation.cs`, `Source/DafnyDriver.Test/ContractRuntimeObservationTests.cs` (new) | Root implements runtime-only reference field snapshots as flattened `name.field` entries alongside stable reference identities, with cycle handling, and an explicit current source location plus unhandled-exception observation. This preserves the existing `ContractValue` wire shape (reference values have no nested fields). Engine owner wires named snapshots, source-mapped location markers and runtime-error records into the transformer/runner. Legacy contract serialization remains unchanged when runtime mode is off. | Actual compiled class mutation captures entry/current field values; cyclic references terminate; runtime error carries original statement location. Owner regression checks remain required. |
| T7 (M2) | T2–T4 파일 | export 선언을 `reveals *`로 텍스트 재작성한다. 참고로 `ContractHeapFactory.cs:590-639`는 export 선언을 텍스트로 고치는 선례지만 선택적 `provides`를 추가하는 좁은 방식이므로, 그 로직을 그대로 재사용하지 않는다. ghost 필드·생성자 컴파일, 클래스 `{:extern}` 제거, `old(E)` 사전 계산, `unchanged` 전개, `{:extern}` 메서드 draft 대체 | F25–F29 통과 |
| T8 (M2) | T2–T7 파일, 새 일반 fixture | root R-T7이 cat IO 변이에서 보고한 엔진 실패(`unsupported`, 재resolve 실패, 잘못된 판정)마다 원인을 일반 구조로 줄인 fixture를 만들어 테스트에 추가하고 수정한다. 벤치마크 코드는 복사하지 않는다 | 보고된 실패마다 일반 fixture 테스트가 추가되어 통과한다. root 재실행에서 해당 변이가 `unsupported`가 아니거나, 남는 이유가 §11에 기록된다 |
| T8 independent follow-up H-E2–H-E5 | `ContractStubRuntime.cs`, `ContractRuntimeInstrumentation.cs`, `ContractCompilerWorker.cs`, `ContractRuntimeCampaignRunner.cs`, `ContractRuntimeObligationTransformer.cs`, `ContractRuntimeCheckTests.cs`, `ContractRuntimeObservationTests.cs`; existing callable/query helpers only if required | Preserve concrete deghosted field evidence, original FBM defining equality, callee validity during obligation evaluation and missing-draft handshake through by-method bodies. Exact new files or helper scope must be recorded before additional edits. | §0 probe cases become passing general regressions; existing wire/legacy modes and original contracts remain intact; fresh independent recheck |
| T8 verifier follow-up D-0–D-14 (2026-09-27) | `ContractRuntimeObligationTransformer.cs`(`Check`/`Render`/`RuntimeSubstituter`의 split quantifier 복원, 강제 비-runtime 판정 cap, `CheckedCallee`/`SpecWrapper`/`Wrapper`/`InstrumentCalls`의 generic 형 매개변수, 형 제약 검사 helper, `DiagnosticReachable`의 형 제약·witness·const 초기화·override 간선, forall 문 marker 제외, `MakeGeneratorVisible` export 길이), `ContractRuntimeCampaignRunner.cs`(컴파일된 check 구조 검사와 재변환, 양방향 closed 판정, 유효 표본만 위반 집계, 0 결정 평가 시 `no_violation_found` 금지, trait 추상 멤버 draft 제외, missing-draft 원래 위치, extern function kind, teardown/잘린 JSONL 처리, `DisableScopes`), `ContractQueryBuilder.BuildClosedClause`(부정 질의 선택 인자), `ContractRuntimeSourcePreparation.cs`(`NeedsDraft`의 trait 추상 멤버), `ContractRuntimeInstrumentation.cs`/`ContractStubRuntime.cs`(배열 직렬화), `TestContractsCommand.cs`(임시 디렉터리), `ContractSolver.CheckAsync`(번역을 await 전에 완료), Driver/TestGeneration runtime 테스트 | 독립 검증의 D-0(trigger split 식 출력으로 check가 ghost로 지워짐, 0 평가 `runtime`), D-2(closed 실패를 위반 처리), D-3/D-4(generic·closed 절 callee 유효성 누락), D-6/D-7(generator 입력·draft 출력의 subset/newtype 제약 미검사), D-9(무효 표본 위반 집계), D-5(형 의존·const 초기화 경로 trap), D-1(trait dispatch draft 요구), D-8(generic 호출 wrapper), D-12(forall 문 marker), D-13(배열 직렬화), 부수 항목, D-10/D-14/D-11. §4 와이어 필드 집합은 바꾸지 않는다. 필요해 보이면 멈추고 보고한다 | 각 결함마다 일반 fixture가 실패→통과, 검증자 probe 재실행이 기대 판정, 기존 모드 불변, §9 검사와 `make build-dafny` 통과 |
| T9 | `wiki/contract-testing.md`, `wiki/INDEX.md` | 모드 의미, 판정 방법, 표본 유효성, 한계, 근거 | 링크·diff 검토 |

## 8. 테스트 fixture (모두 일반 Dafny, 벤치마크 코드 사용 금지)

테스트는 `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs`(변환, 빠름)와
`Source/DafnyDriver.Test/ContractRuntimeCheckTests.cs`(컴파일·실행, 느림)에 둔다. 기존
`ContractExternExecutionTests.DiagnosticExecutableSupportsPartialLogicalHeap`(:18-71)의 패턴을
따른다: 인라인 소스, `ContractCompilerWorker.ParseAsync`, 러너 직접 호출. 테스트마다 한 줄 의도
주석을 단다.

| ID | 내용 | 기대 |
| --- | --- | --- |
| F1 | 재귀 ghost function을 쓰는 postcondition | D에 포함, `runtime` |
| F2 | opaque predicate와 set comprehension cardinality를 쓰는 invariant | `runtime` |
| F3 | ghost 지역변수와 ghost out을 쓰는 invariant/ensures | L에 포함, `runtime` |
| F4 | `forall x: int :: ...` 무한 정량자 postcondition | `closed_smt` |
| F5 | `iset`을 쓰는 절 | `unchecked` |
| F6 | lemma 호출과 `calc`가 있는 본문 | 제거 후 재resolve 성공 |
| F7 | ghost method 호출로 대입되는 ghost 지역변수와 이를 읽는 invariant | `unchecked` (`value_unavailable`) |
| F8 | 재resolve 실패를 유도하는 ghost 사용 | 복구 루프 뒤 `unsupported` 또는 제외 기록 |
| F9 | postcondition 버그 | `violation_found`, kind `postcondition`, replay 재현 |
| F10 | invariant 진입 실패 | `loop_invariant_entry`, iteration 0 |
| F11 | 특정 반복에서만 깨지는 invariant | `loop_invariant_maintenance`, 해당 iteration |
| F12 | `break` 뒤 invariant가 성립하지 않는 올바른 루프 | 위반 없음 |
| F13 | 약하지만 참인 invariant(증명만 실패하는 경우) | `no_violation_found` |
| F14 | callee precondition 위반 | `call_precondition`, 위치는 호출 지점 |
| F15 | 본문 없는 helper, draft 없음 | `drafts_required`에 서명과 계약 포함 |
| F16 | `assert false;` scaffold helper, draft 없음 | `drafts_required` |
| F17 | draft 서명 불일치 | `unsupported` 사유 명시 |
| F18 | draft가 자기 ensures를 위반 | `callee_contract_violation`으로 분리, goal 위반 미보고 |
| F19 | generator 없음 | `generator_required`와 요구 서명 |
| F20 | P를 자주 위반하는 generator | `precondition_rejected` 집계 |
| F21 | 비종료 입력 | `timeout` 집계 후 다음 ordinal 진행 |
| F22 | `maxClosedQueries` 초과 | `closed_query_budget_exhausted` |
| F23 | 같은 seed 두 번 실행 | 입력과 결과 동일 |
| F24 | 모든 표본 무효 | `inconclusive` |
| F25 (M2) | 비공개 ghost 생성자와 ghost 필드를 가진 region 클래스, 다른 모듈 generator | 생성 성공 |
| F26 (M2) | `{:extern} {:axiom}` 메서드와 draft | draft 실행과 ensures 검사 |
| F27 (M2) | ensures의 `old(o.f)`, `unchanged(o)` | `runtime` |
| F28 (M2) | `fresh` | `unchecked` |
| F29 (M2) | draft 없는 extern | `drafts_required`, kind `extern_method` |
| F30 | ghost `ORDINAL` 입력 formal | `unsupported` (`non_compilable_input_type`) |
| F31 | 재resolve 복구로 제외된 선언 | `deghostExclusions`에 기록 |

## 9. 검증 명령과 기대 결과

- `/workspace/cosyn`: `make build-dafny`. 경고와 오류가 없어야 한다(기존 기록 기준).
- `/workspace/cosyn/dafny`: `dotnet test Source/DafnyTestGeneration.Test --filter "FullyQualifiedName~ContractRuntime"` → 전부 통과.
- `/workspace/cosyn/dafny`: `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~ContractRuntime"` → 전부 통과(수 분 소요 가능).
- 회귀:
  - `dotnet test Source/DafnyTestGeneration.Test --filter "FullyQualifiedName~Contract"`
  - `dotnet test Source/DafnyDriver.Test --filter "FullyQualifiedName~Contract"`
  - `dotnet test Source/DafnyCore.Test --filter "FullyQualifiedName~ContractExpressionReducer"`
  - 기대: 기존과 같은 통과 수.
- `/workspace/cosyn/dafny`: `make format`, `git diff --check`.
- CLI 수동 확인: F9 요청 JSON을 scratch에 만들고 `dafny test-contracts req.json --runtime-check`를
  실행한다. stdout 한 줄에 `violation_found`가 나와야 한다.

## 10. 위험과 함정

- 자동 ghost 제거가 benchmark ghost 코드의 상당 부분을 D/L에서 뺄 수 있다. 결과에서 제외 항목과
  `unchecked` 비율로 드러나며, root M4가 측정한다.
- ghost predicate가 반복마다 이차 비용으로 평가될 수 있다. 표본 timeout과 `Size()` 힌트로
  제한하고, timeout 비율을 보고한다.
- 텍스트 편집 위치가 겹치면 기존 적용부는 한 번에 적용한다. 편집 충돌은 예외로 실패하게 하고
  테스트로 막는다.
- export 무시와 `{:extern}` 제거는 진단 빌드에만 적용한다. 원본 snapshot, 증명, 후보 소스에는
  영향이 없어야 한다.
- closed SMT 질의는 snapshot을 매번 재파싱하므로 느리다(수 초). 중복 제거와 예산으로 제한한다.
- 계약 중 `reads`/`modifies` 절은 검사 대상이 아니다. frame 위반을 잡았다고 주장하지 않는다.

## 11. 진행 기록

- 2026-09-26: 조사와 사용자 결정 반영으로 작성했다. 인계용으로 와이어 계약, 파일 형식, 알고리즘,
  fixture를 구체화했다. 코드 변경 없음.
  - 근거 탐색은 Sonnet 하위 에이전트가 했다(effort 설정 불가, 기본값).
  - cat `ProcessBytesMethod` 단독 검증은 약 14초 걸렸다. `blankStreak >= 2 → >= 3` 변이에
    `--extract-counterexample`를 주면 값 없는 경고 배너만 나온다(root 계획 근거).
- 2026-09-26: reflected the independent review. Added:
  - the `deghostExclusions` field;
  - the draft contract responsibility boundary;
  - the generator rule for non-compilable ghost input formals (F30);
  - closed-query budget sequencing and per-call-site `old`;
  - the T7 precedent correction and the T8 done criteria.

- 2026-09-26 implementation started after inspecting owner instructions, existing source
  snapshot/compiler/CLI paths, and wiki. Existing dirt was the untracked authorized
  plan plus its index entry; these are preserved. T0 scratch fixtures live under
  `/workspace/tmp/runtime-obligation-t0` and precede automatic transformation.
  The change-table compiler path is corrected to
  `Source/DafnyDriver/ContractTesting/ContractCompilerWorker.cs`; the campaign
  runner also belongs in that directory because compilation depends on Driver.

- 2026-09-26: T0 passed all three manual transformed programs after adding a
  scratch-local closed NuGet.Config (installed packages only). Outputs were
  `postcondition`, `nested ok`, and `ghost out ok`. Text edits remain viable.
  T1 passed 3 wire round-trip/unknown-field tests. Native build uses `-m:1`
  because concurrent MSBuild sometimes exits with no diagnostics in this runtime.
- 2026-09-26: User explicitly authorized function-by-method goals in addition to
  method goals. T2/T3/T5 reuse the existing callable descriptor and execute the
  original function-by-method implementation while checking its original contract.
  T4 exact file list now includes the separate source preparation helper and tests;
  root agent implements that bounded helper in parallel, preserving owner boundaries.

- 2026-09-26 implementation validation checkpoint (implementation context, not independent review):
  - `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeObligation -v minimal`: 7/7 passed.
  - `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter FullyQualifiedName~ContractRuntimeSourcePreparation -v minimal`: 9/9 passed (bounded helper implemented by root agent).
  - `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~ContractRuntime -v minimal`: 20/20 passed in 1m43s.
  - `/workspace/cosyn`: `make build-dafny` passed, 0 warnings/errors, 41.90s.
  - Logs: `/workspace/tmp/runtime-unit-test.log`, `/workspace/tmp/runtime-driver-test.log`, `/workspace/tmp/runtime-full-build.log`.
  - Native test runner needs its local TCP socket; sandbox execution aborted with SocketException (13), then approved host execution passed. No provider calls, packages, benchmark scoring or specifications changed.
  - This checkpoint covers method/function-by-method postconditions, while/for invariants, runtime and closed-SMT decisions, entry rejection, direct callee precondition, draft callee validity, deterministic replay, old/unchanged field checks, and per-sample timeouts.
  - Source-only follow-up adds pre-generator export/ghost-constructor visibility and nested callee validity; not included in the above binary checkpoint.

### Fixture ledger (implementation checks, 2026-09-26; independent review pending)

| Fixtures | Current evidence | Remaining |
| --- | --- | --- |
| F1, F3, F9–F14, F18–F24, F26–F27 | Driver compiled execution tests pass | Regressions and independent review |
| F2, F4–F5, F7, F28 | Native resolved transformation classification tests pass; F4 additionally executes closed SMT | Explicit executable opaque finite-comprehension and unavailable ghost-local samples remain to add |
| F6, F8, F30–F31 | Latest 25-test Driver batch passed these cases (24 passed, one separate F25 failure) | Final repeat after current source corrections |
| F15–F17, F29 | Source preparation tests cover bodyless/scaffold/signature mismatch/extern replacement | Explicit runner missing-draft handshake tests still to add |
| F25 | Original test export was invalid; corrected fixture exposed imported static receiver rendering | General receiver printer correction written, rerun pending |
| T8 actual probes | Frozen root M1 run exposed parser-recovery null ModuleSigs crash | Guard written; await actual parser diagnostics, add general reduced fixture, rerun affected variants |

- The 25-test Driver batch passed 24 tests and failed the original invalid F25 fixture.
  The corrected F25 fixture then exposed a real imported-static-receiver rendering
  defect (`_default.Read`); source correction now matches existing query substitution
  practice by rendering a non-implicit static receiver. It is not yet recorded as passing.
- Runtime knowledge is recorded in [contract-testing](../wiki/contract-testing.md),
  with limits and the original plan linked in both directions.

- Independent owner probes require T8 corrections in existing transformer/runner/CLI/tests: unresolved module traversal, ordinary-function nested calls, local-alias old captures, unavailable ghost output classification, preserved request seed, and campaign-to-replay comparison. Plan remains in-progress; these are correctness fixes within T2–T8.
- Actual M1 r2 diagnostics exposed ghost proof callers of constructors made executable for generator visibility. T3/T4 diagnostic preparation now erases proof-only ghost method bodies (retaining constructors and all original contracts/signatures) using byte-preserving blanks before resolving the generator. This is the existing proof-erasure transformation applied before constructor visibility changes.
- Resume implementation: F25 reproduces `_default.Read` after imported static receiver substitution. Preserve the receiver's original module container and implicitness when rendering diagnostic clauses; the previous generic non-implicit receiver conversion was insufficient. Actual r3 failures reduce to ghost field initialization with converted constructors; selective constructor visibility is being investigated without fabricating unreachable ghost state.
- T8 correction restores the planned §6.2 declaration reachability boundary: use native resolver call graphs rooted at goal and generator for ghost function, local, field, and constructor conversion. Resolve generator names with original constructor ghostness before applying constructor visibility, and require a clean final resolve. Unrelated ghost constructor/field initialization remains logical instead of being forced into executable code. Files: existing transformer/runner and general Driver fixtures; validation includes hidden imported regions and pure goals alongside unrelated ghost allocation/choice initialization.
- 2026-09-26 13:44 UTC handoff: all resumed sub-agent turns terminated on workspace
  spend cap. Retained selective reachability/imported receiver edits are unverified.
  Last complete Runtime Driver run was 33 passed/1 failed (F25), log
  `/workspace/tmp/engine-resume-tests-host.log`. Fresh frozen-r3 probes additionally
  reproduce ghost-field evidence omission, absent FBM defining equality, callee
  validity bypass in obligation expressions and a missing-draft FBM clone assertion.
  §0 lists their exact requests, source symbols, next steps and acceptance conditions;
  T8 change table covers them. The older fixture ledger is historical evidence,
  not acceptance of the latest source. Independent final review is unfinished.
- 2026-09-26 13:55 UTC 재개(Opus 구현 하위 에이전트, effort 설정은 위임 도구가 노출하지 않아 기본값): §0 H-E1–H-E5를
  이어받는다. 수정 범위는 T8 change table의 기존 파일(`ContractRuntimeObligationTransformer.cs`,
  `ContractRuntimeCampaignRunner.cs`, `ContractStubRuntime.cs`, `ContractRuntimeInstrumentation.cs`,
  `ContractCompilerWorker.cs`, `ContractCallableSelector.cs`(H-E5 clone 경로가 필요할 때만), Driver 테스트 2개)로 한정한다.
  기존 dirty 트리를 보존하고 커밋하지 않는다. 결과는 항목마다 여기에 누적한다.
- H-E1 1차 결과(13:58 UTC): 보존된 부분 수정은 빌드됐지만 `MakeGeneratorVisible`이 resolve 전 AST에서
  `Constructor.FullDafnyName`을 읽어 NRE로 실패했다(F25 포함 생성자 있는 모든 요청). 파싱된 선언의
  `ClassDecl.FullDafnyName + "." + Name`으로 이름을 만든다(`ContractRuntimeObligationTransformer.MakeGeneratorVisible`).
  `/workspace/cosyn/dafny`: F25 집중 `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter FullyQualifiedName~ConstructsHiddenGhostRegion`
  1/1 통과(로그 `/workspace/tmp/he-logs/f25-2.log`, 수정 전 실패 `f25-1.log`). 이어
  `--filter FullyQualifiedName~ContractRuntime -v minimal` **37/37 통과**, 2m22s, 로그
  `/workspace/tmp/he-logs/runtime-driver-1.log`. sandbox 안에서 SocketException 없이 실행됐다.
  다음: 실제 Process/Digits r3의 IO ghost 실패를 일반 fixture로 축소.
- 14:25 UTC H-E1/H-E2/H-E5 소스 수정(테스트 추가 전, 개발 바이너리 = `Source/DafnyDriver.Test/bin/Debug/net8.0/DafnyDriver.dll`):
  - 실제 cat Process/Digits 요청을 `sampleCount=4` 복사본(`/workspace/tmp/he-diag/{process,digits}-s4.json`, 읽기 전용 진단)으로
    재실행하며 r3 이후의 연쇄 실패를 차례로 확인했다. r3 IO ghost 생성자 오류는 선택적 생성자 변환으로 더는 나오지 않는다.
    이어서 나온 실패와 일반 원인: (a) native `HideRevealStmt` 범위가 `;`를 포함하지 않아 `reveal F();` 제거 후 `;`만 남음
    → `RemoveStatement`가 reveal/hide의 종결 `;`까지 지운다. (b) runtime bridge가 legacy 관찰 stub용 `ConcreteCalls`를
    계산하다 goal 증명문 속 generic ghost 함수에서 `NotSupportedException` → runtime 모드에서는 계산하지 않는다
    (`ContractStubRuntime.BridgeSource(runtimeReferences: true)`만, legacy 경로 불변). (c) goal/generator 호출 그래프 밖의
    관련 없는 compiled 본문이 native extern(C# 구현 없음)을 호출해 C# 컴파일 실패 → 도달 불가 non-ghost 메서드/함수/by-method
    본문만 `PbtBridge.UnreachableBody()`/`UnreachableValue()` trap으로 바꾼다(`EraseUnreachableBody`; 생성자·override·ghost·계약은
    그대로, 실행되면 runtime error로 표본 무효). 결과: Process 4표본 `no_violation_found`, valid 4, 의무 4개 모두 runtime.
    Digits(FBM goal)는 invariant `Digits(current)…`가 by-method 자신을 재귀 실행해 stack overflow(runtime error 4) → H-E3의
    원래 정의 compiled 사본으로 해결 예정.
  - H-E2: transformer가 실제로 ghost를 제거한 필드를 `ContractRuntimeTransformation.CompiledGhostFields`로 내보내고
    `ContractRuntimeInstrumentation.BridgeSource`가 이를 `ContractStubRuntime.BridgeSource(..., compiledGhostFields)`의
    `heapShapes.fields`에만 추가한다. probe 재실행에서 `inputs`/`values`에 `x.f = 7`이 나온다(`/workspace/tmp/he-diag/ghost-field.dev.result.json`).
  - H-E5: 원인은 missing draft가 아니라 FBM descriptor가 by-method 본문을 복제할 때 method-call 구문(`ApplySuffix`, 타입 없음)에
    `.Resolved`를 불러 `Contract.Assert(WasResolved())`로 process가 죽는 것(본문 있는 helper도 동일). `FunctionDescriptorCloner`가
    미해결 구문은 기본 복제로 넘긴다(`ContractCallableSelector.cs`, 이전에 crash하던 입력만 영향). runner `MissingDrafts`는
    FBM이면 원래 function을 root로 by-method 본문까지 도달성을 본다. probe → `drafts_required`, `M.Helper` 서명/계약 포함.
- 14:45 UTC H-E3/H-E4 소스 수정(테스트 추가 전):
  - H-E3: FBM goal wrapper가 명시적 `ensures` 뒤에 `result == <원래 함수 정의>`를 `postcondition` 의무로 판정한다
    (새 wire kind 없음; 위치/`clause`는 원래 정의 식의 위치/원문, `values`에 입력·구현 결과와 `Goal(x)` 이름의 정의값).
    의무 식 안의 goal 함수 호출은 원래 정의를 컴파일한 `<Name>__pbt_definition` 사본으로 평가한다(재귀도 사본끼리).
    정의가 컴파일 불가이면 goal 함수를 부르는 절은 구현을 실행하지 않고 `closed_smt`로 분류한다. probe:
    `violation_found`, `clause="x+1"`, `1:39`, `values={x:7, contractResult:7, Goal(x):8}`. 실제 Digits 4표본(변이 요청)도
    stack overflow 없이 `violation_found`(정의 등식 4/4, 유지 invariant 14/20 위반).
  - H-E4: goal 의무(entry/postcondition/invariant/call precondition) 절의 최상위 함수 호출 중 계약이 있고 컴파일되는
    비-generic 함수(ordinary 또는 D의 ghost)를 함수별 1개 `<F>__pbt_spec_<n>` wrapper로 평가한다. wrapper는 평가 가능한
    `requires`를 `PbtBridge.RequireInSpec`(거짓이면 runtime error)로, `ensures`를 `callee_postcondition`으로 판정한다.
    callee 검사 안에서는 다시 감싸지 않는다(재귀/중복 방지). generic spec 함수는 감싸지 않는 한계를 남긴다.
    descriptor는 ghost 함수도 받는 `ContractCallableSelector.DescribeFunction`(private→internal)을 쓴다. 부수 수정:
    제거되는 `ghost` 키워드 시작 위치의 삽입이 "제거 범위 내부 편집"으로 버려지던 `Apply` 규칙을 내부 삽입만 버리도록
    고쳤고, callee 사후조건의 위치/원문을 descriptor 복제본이 아닌 원래 함수 절에서 가져온다(이전 `b:bool` 오표시).
    두 probe 모두 `inconclusive`, `calleeContractViolations=1`, goal 위반 0.
- 14:55 UTC 새 fixture(모두 일반 Dafny): `ContractRuntimeCheckTests.IsolatesUnrelatedNativeHostState`(H-E1; frozen r3 toolchain에서
  같은 `Generator resolution failed … only ghost methods can be called from this context` 재현 확인,
  `/workspace/tmp/he-diag/fixture-r3/host-isolation.r3.result.json`), `ChecksFunctionByMethodDefinition`,
  `EvaluatesRecursiveDefinitionInObligations`(H-E3), `SeparatesSpecFunctionContractViolation`(ordinary/ghost theory),
  `ChecksSpecFunctionContractsWithoutRecursiveWrapping`(H-E4), `RequiresDraftInsideFunctionByMethod`,
  `ExecutesDraftInsideFunctionByMethod`(H-E5), `ContractRuntimeObservationTests.CapturesCompiledGhostFieldValue`(H-E2).
  집중 실행 9/9 통과(`/workspace/tmp/he-logs/new-fixtures-1.log`에서 H-E2 fixture 가정 오류 1건 → 도달 가능한 생성자가
  대입하는 ghost 필드는 실제로 컴파일되므로 미사용 필드를 대입하지 않게 고침, `new-fixtures-2.log` 1/1 통과).
- 14:59 UTC `/workspace/cosyn/dafny`: `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter FullyQualifiedName~ContractRuntime -v minimal` **46/46 통과**, 3m06s, 로그 `/workspace/tmp/he-logs/runtime-driver-2.log` (sandbox 실행, SocketException 없음).
- 15:03 UTC TestGeneration `--filter FullyQualifiedName~Contract` 1차: 275/279, 실패 4건은 모두
  `ContractRuntimeObligationTests`의 transform 단위 테스트였다(`testgen-contract-1.log`). 원인은 인계 전부터 있던
  `Transform()`의 필수 `Generate` 탐색(PbtMain 생성)인데 테스트 helper가 generator를 넣지 않았던 것이다(이번 수정과 무관,
  이전 7/7 기록 이후 회귀). helper가 runner처럼 `import PbtRandom`, generator, `PbtRuntime.dfy`를 넣도록 고쳤다.
  `--filter FullyQualifiedName~ContractRuntime` 16/16 통과(`testgen-runtime-1.log`).
- 15:05 UTC TestGeneration `dotnet test Source/DafnyTestGeneration.Test --no-restore -m:1 --filter FullyQualifiedName~Contract -v minimal` **279/279 통과**, 1m25s, 로그 `/workspace/tmp/he-logs/testgen-contract-2.log`.
- 15:06 UTC Core `dotnet test Source/DafnyCore.Test --no-restore -m:1 --filter FullyQualifiedName~ContractExpressionReducer -v minimal` **27/27 통과**, 로그 `/workspace/tmp/he-logs/core-reducer-1.log`. Driver Contract 전체 회귀 시작.
- 15:10 UTC Driver `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~Contract -v minimal` **50/50 통과**, 3m01s, 로그 `/workspace/tmp/he-logs/driver-contract-1.log`.
- 15:12 UTC `make format` exit 0(22s, 로그 `/workspace/tmp/he-logs/make-format-1.log`, 변경 파일 없음: 실행 전후 status/md5 동일), `git diff --check` 출력 없음, untracked 파일 trailing whitespace 없음.
- 15:15 UTC `/workspace/cosyn`: `make build-dafny` exit 0, 0 warning/0 error, 26.5s, 로그 `/workspace/tmp/he-logs/build-dafny-1.log`.
  SHA-256: `Binaries/net8.0/DafnyDriver.dll` = `Binaries/DafnyDriver.dll` =
  `30949a7b5cdac77136af543d5954d727b75647b97a8f9f20bc685c261a27fd9c`; `Binaries/{,net8.0/}DafnyTestGeneration.dll` =
  `2ebca99151ae5d3d0316b6aeb6ea1b072469b65bba569ab20eac4697e18ed544`. 공개 `dafny`(`/usr/bin/dafny` → `Binaries/Dafny`)로
  다섯 probe를 새 파일 `/workspace/tmp/fresh-pbt-verification/<name>.r4.result.json`에 재실행했다(기존 결과 보존):
  `ghost-field` violation_found + `inputs/values["x.f"]=7`; `fbm-equivalence` violation_found, `postcondition` 1:39 `x+1`,
  `Goal(x)=8` vs `contractResult=7`; `ghost-function-contract`/`ordinary-spec-function-contract` inconclusive,
  `calleeContractViolations=1`, goal 위반 0, callee `M.Bad` 절 `b`; `fbm-missing-draft` drafts_required(`M.Helper`, 서명·계약 포함).
  진단용 실제 cat 4표본 복사본도 공개 바이너리로 재실행: Process `no_violation_found`(valid 4, 의무 4개 runtime),
  Digits(변이 FBM) `violation_found`(valid 4, 정의 등식 4/4, 유지 invariant 14/20)
  (`/workspace/tmp/he-diag/{process,digits}-s4.public-r4.result.json`). root의 64표본 M1/M2 재실행은 하지 않았다.
- 15:20 UTC wiki `wiki/contract-testing.md`에 "T8 follow-up findings (H-E1–H-E5)" 절을 추가했다(도달성 기반 진단 범위와
  trap, 컴파일된 ghost 필드 캡처, FBM 정의 등식, spec 함수 callee 유효성, native AST 사실, 검사 수).
  남은 한계: generic spec 함수는 callee 유효성 wrapper 없이 평가, 평가 불가 spec `requires`는 가정하지 않고 건너뜀
  (ensures는 검사), `old(E)` 사전 계산 식 안의 함수 호출은 감싸지 않음, 제외된 표본의 goal 절도 `obligations[].violations`
  집계에는 들어감(기존 의미). 다음 행동: 새 독립 검증 에이전트가 §0/§4 요구사항과 현재 트리에서 재검사하고, root가 새
  toolchain snapshot으로 M1/M2를 새 결과 경로에 재실행한다.
- 00:36 UTC 2026-09-27 새 작업: 독립 검증(`/workspace/tmp/engine-verify-20260926-235506`)이 보고한 D-0–D-14를 고친다.
  §7 change table에 "T8 verifier follow-up D-0–D-14" 행을 먼저 추가했다. 참고: 이전 §11 항목의 "UTC" 시각 표기는
  대략값이었다(파일 mtime 기준 약 30분 이르게 적힘). 이후 항목은 `date -u` 값을 쓴다. 설계 요지:
  D-0은 resolved split quantifier 대신 원래(unsplit) quantifier로 check 식을 출력하고, 재resolve된 진단 프로그램에서
  compiled 문맥의 `PbtBridge.Check/Checkpoint` id를 수집해 빠진 의무를 closed_smt(→unchecked) cap으로 재변환한다.
  결정된(goal) 평가가 0이면 `no_violation_found`가 아니다. D-2는 절과 부정 절 두 질의로 판정한다(부정만 증명되면 위반,
  절만 증명되면 성립, 둘 다면 값 전제 모순으로 unchecked, 그 밖은 unchecked). 예산은 판정 단위 그대로 센다.
- 00:47 UTC 소스 1차 수정(빌드 통과, 테스트 전): transformer(`RuntimeSubstituter` unsplit quantifier, `Check`의
  decision cap·명시 값·형 제약 모드, `TypeConstraintChecks`/`Membership`/`MembershipHelper`/`HasConstraint`,
  generic `TypeParameters`, `HasContract`, `ExecutionReachable`(override·형 제약/witness·const 초기화 간선),
  `CompiledCheckLiterals`/`IsCompiled`/`IdPrefix`, forall 문 marker 제외, export 길이 부족 시 건너뜀), runner(`DisableScopes`,
  compiled check 검사 후 cap 재변환 최대 8회, 최종 미컴파일 의무 unchecked, 양방향 closed 판정 `DecideClosedAsync`,
  closed 절의 미검증 callee → unchecked, 분류별 위반 집계, 결정된 goal 평가 0이면 inconclusive, 잘린 JSONL/완료 후 teardown,
  `MissingDrafts`의 실행 도달성·trait 추상 멤버 제외·원래 위치·function kind), `ContractQueryBuilder.BuildClosedClause(negate)`,
  `ContractRuntimeSourcePreparation.NeedsDraft`(trait 추상 멤버), bridge 배열 참조+평면 원소 캡처(runtime 모드만),
  `TestContractsCommand` 임시 경로. p36(배열) dev 재실행: 이전 runtime error 6 → `violation_found`, valid 6.
- 추가 과제 D-15(root 보고, R-T7→T8형): class `{:extern} {:axiom}` 메서드에 top-level draft를 주면 `SelectMethod`가
  `EnclosingClass` 없는 멤버에서 NRE. 재현 `/workspace/tmp/r-t10-diag-20260927-004054/`. P1 뒤에 일반 fixture로 줄여 원인 수정.
  change table의 T8 verifier 행 범위에 포함한다(파일: `ContractRuntimeSourcePreparation.cs`, runner, Driver 테스트).
- 00:52 UTC dev 바이너리 probe 확인(P1): p28/p29/p30 `no_violation_found`(0 평가) → `violation_found`(runtime 8 평가);
  p31 거짓 goal 위반 → callee 위반 6, goal 위반 0; p10 → `inconclusive`(closed_query_timeout, 위반 0); p27 부정 증명으로 위반 유지;
  p13 → callee 위반 8(generic wrapper, 형 매개변수 값 캡처); p14 → 위반 0, unchecked; p15 → `precondition_rejected` 2;
  p16 → callee 위반 2(`y: nat`); p03 → postcondition 위반 집계 6(유효 표본만). 구조적 안전망 확인용 일반 probe
  (`datatype D = A | B | ghost C`, `ensures d != C && d != A`)는 ghost 추론으로 check가 지워졌고 closed_smt로 낮춰져
  mcq=1에서 위반, mcq=0에서 `inconclusive`. 추가: 렌더된 check가 resolve되지 않으면(비교 불가 형의 `==`) 그 의무만
  closed_smt로 낮춘다. `CompilableType`은 형 매개변수와 그 원소형 collection을 허용한다(p18 call precondition runtime).
- 01:01 UTC D-5/D-1/D-12/D-10/D-14/D-15 dev 확인: p12(교차 모듈 subset 형 검사)·p21(witness)·p22(class const 초기화)
  runtime error 8 → 유효 8(p22는 위반 8); p01/p01b trait dispatch → drafts_required/unsupported 대신 실행, 위반 2;
  p35 compiled forall → unsupported 대신 위반 6; p19 missing draft 줄 9 → 원래 2; p33 → kind `function`.
  형 제약 helper는 호출 위치 모듈의 import 별칭으로 부른다(해석된 UDT 이름은 원문 한정자를 잃음). `MissingDrafts`는
  제공된 snapshot 밖(내장/라이브러리) 선언을 제외한다(실행 도달성 확장 후 `Find` 실패를 막음).
  D-15 원인: draft 본문이 ghost 상태를 써서 상위 모듈 resolve가 실패하면 하위(goal) 모듈 멤버가 등록되지 않아
  `EnclosingClass`가 null이다. draft 멤버가 프로그램에 남는 문제가 아니다. 도달성 단계는 resolve된 멤버에서만 goal을 찾고,
  goal 모듈이 resolve되지 않으면 draft/generator 원래 위치로 사상한 resolver 진단과 함께 `unsupported`를 돌려준다.
  일반 fixture(`Lib.Store`의 `{:extern} {:axiom} Read`, ghost 필드 계약, top-level draft) 재현: NRE → `unsupported`
  (`drafts/Lib.Store.Read.dfy:1:69: a ghost field is allowed only in specification contexts`); 컴파일 가능한 draft는 실행된다.
  실제 root 요청 재구성(`/workspace/tmp/he-diag/d15/request.json`): NRE → `unsupported`, 진단은 네 draft 파일의 ghost 함수
  호출(§5.1 draft 본문은 컴파일 가능해야 함). 진단용으로 draft를 자명한 컴파일 가능 본문으로 바꾸면 다음 상태는
  `unsupported` "Generator resolution failed: IO.dfy … only ghost methods can be called from this context"(generator의
  `new BenchIO.IO.Init()`가 `requires false` 생성자의 ghost region 초기화를 도달 가능하게 함). 사용자 결정에 따라
  새 객체 생성 메커니즘을 추가하지 않고 이 동작은 그대로 둔다.
- 01:09 UTC 새 fixture 추가(`ContractRuntimeCheckTests` 25개, `ContractRuntimeObservationTests.CapturesArrayReferenceElements`),
  기대 변경 2개(`ExecutesWithUnavailableGhostLocal`, `ReportsUnavailableGhostOutput`: 결정된 goal 평가가 없으므로 `inconclusive`).
  `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter FullyQualifiedName~ContractRuntime -v minimal` **71/71 통과**, 4m52s,
  로그 `/workspace/tmp/he-logs/r5-runtime-driver-1.log`. 이전 공개 바이너리(r4, SHA `30949a7b…`)로 같은 모양의 probe를 돌리면
  ghost 생성자 절은 `runtime` 0 평가 `no_violation_found`, extern 멤버 ghost draft는 NRE `error`였다
  (`/workspace/tmp/he-diag/probes/*.r4public.result.json`): fixture가 결함을 재현함을 확인.
- 01:16 UTC 회귀: TestGeneration `~Contract` **279/279**(1m28s, `/workspace/tmp/he-logs/r5-testgen-contract-1.log`),
  Core reducer **27/27**(`r5-core-reducer-1.log`). Driver `~Contract` 1차는 69 통과 후 test host가
  `BoogieGenerator.Translate` assertion으로 죽어 **중단**(통과로 보지 않음, `r5-driver-contract-1.log`). 원인: `ContractSolver`가
  lazy `BoogieGenerator.Translate` 열거 중에 `await BoogieOnce`를 해서 thread-static 형 scope 상태가 다른 thread에서 이어짐
  (기존 위험, 양방향 closed 질의로 빈도 증가). change table 범위에 `ContractSolver.CheckAsync`를 추가하고 번역을 먼저
  `ToList()`로 끝내도록 고쳤다(결과 불변). 같은 패턴이 legacy `ContractSymbolicChecker`에도 있으나 이번 범위 밖으로 남긴다.
- 01:28 UTC 재검사: Driver `dotnet test Source/DafnyDriver.Test --no-build -m:1 --filter FullyQualifiedName~Contract -v minimal`
  **75/75 통과**, 4m50s(`r5-driver-contract-2.log`, 1차 중단 뒤 재실행). TestGeneration `~Contract` 재실행 **279/279**
  (1m26s, `r5-testgen-contract-2.log`; `ContractSolver` 변경 후). `make format` exit 0, 변경 없음(`r5-make-format-1.log`),
  `git diff --check` 출력 없음, untracked trailing whitespace 없음. §4.2에 형 제약 의무, 분류별 위반 집계, closed 판정,
  미컴파일 check, `no_violation_found` 조건, 배열 캡처, extern function kind 규칙을 추가했다(필드 집합 불변).
- 01:28 UTC `/workspace/cosyn`: `make build-dafny` exit 0, 0 warning/error, 26.3s(`r5-build-dafny-1.log`).
  SHA-256 `Binaries/{,net8.0/}DafnyDriver.dll` = `1782ffe29f85bc3b176c47d09fee03e30f7cc5bf581e249cfcdd6e253ee62824`,
  `Binaries/{,net8.0/}DafnyTestGeneration.dll` = `af4d7318a8d9d7457d7c99cc290d5665e38d7c2c2c85923ef87779b5102ea544`.
  공개 `dafny`로 검증자 probe 45개를 새 파일 `/workspace/tmp/he-diag/r5-probes/<name>.r5.result.json`에 재실행(검증자 결과 보존,
  106s, 3 병렬). 기대 변화: p01/p01b/p18/p35 unsupported·drafts_required → 실행, p10/p14 거짓 위반 → inconclusive,
  p13/p16/p31 → callee 위반 분리, p15 → rejected 2, p12/p21/p22/p36 → runtime error 없음, p28/p29/p30 → violation_found,
  p19 줄 2, p33 kind function. 나머지(p02–p09, p11, p17, p20, p23–p27, p32, p34, w1–w5)는 r4와 같은 상태.
  기존 다섯 probe `/workspace/tmp/fresh-pbt-verification/<name>.r5.result.json`: r4와 같은 판정.
  D-15 실제 요청 재구성: `unsupported`(draft 네 개의 ghost 함수 호출, draft 원래 경로/줄). 진단용 자명 draft: `unsupported`
  (IO.Init 경로 ghost region 생성자, 기존 동작 유지). 실제 cat 4표본 복사본: Process `no_violation_found`(형 제약 포함 의무
  모두 runtime), Digits `violation_found` (`/workspace/tmp/he-diag/*public-r5.result.json`).
- 01:29 UTC wiki `wiki/contract-testing.md`에 "Verifier follow-up findings (D-0–D-15)" 절을 추가하고 이전 절의
  "generic spec 함수 미포장" 문장을 갱신했다. 남은 한계/미수정: (1) 잘린 JSONL과 완료 후 teardown 처리는 구현했지만 결정적
  fixture가 없다(프로세스 kill 시점 재현 불가); (2) ghost 필드가 있는 datatype 값은 직렬화되지 않아 그런 값을 읽는 closed
  fallback 표본은 runtime error로 무효가 된다; (3) 형 제약 검사는 collection 원소까지이며 datatype 인자·배열 원소·class 필드의
  제약, snapshot 밖 선언의 제약, call site 모듈이 import하지 않은 모듈의 형은 `unchecked`다; (4) closed 절이 증명되면
  값 전제 모순(지역 변수의 선언형 위반)을 따로 검사하지 않는다(거짓 위반은 아님); (5) legacy `ContractSymbolicChecker`의 같은
  lazy 번역 패턴은 범위 밖; (6) D-15 draft는 §5.1(draft 본문은 컴파일 가능)을 어겨 `unsupported`, 자명 draft로 바꾸면 IO.Init
  generator 경로가 `unsupported`로 남는다(사용자 결정: 새 객체 생성 메커니즘 없음). 다음 행동: 새 독립 검증 에이전트가
  현재 트리와 r5 probe 결과를 요구사항 기준으로 재검사하고, root가 새 toolchain snapshot으로 M1/M2를 새 경로에 재실행한다.


### 2026-09-27 independent-review follow-up R-1–R-4 (ready)

Objective: fix the four general repros in `/workspace/tmp/pbt-engine-review-20260927-codex/REPORT.md` without changing source contracts, IO construction, wire fields, or frozen r3 artifacts. Acceptance: invalid FBM results, unchecked spec domains, invalid nested spec callees, and invalid old-state callees never contribute valid goal violations; valid transitive/recursive cases remain accepted. Owner: Dafny implementation/reporting only; no evaluator/dataset/scoring changes. Existing dirty work is preserved. No paid runs, dependencies, or commits; no new approvals needed.

| Files/symbols | Change/how | Necessity/unmet behavior | Validation |
| --- | --- | --- | --- |
| `ContractRuntimeObligationTransformer.cs`: `HasContract`, `CalleePostconditions`, `Render`, `DefinitionName` | Include FBM defining equality for callees and render recursive definition calls through detached definitions | R-1 otherwise accepts invalid FBM body results | Driver invalid/valid recursive FBM fixtures |
| same: `SpecWrapper`, `Check`, `CaptureOld`, `InternalPrecondition` | Retain non-runtime domains as callee validity checkpoints; wrap nested contract and old-state calls; guard identical pending contract evaluations using original values/result | R-2–R-4 otherwise count unchecked/invalid callees; unguarded wrapping could recurse forever | Driver four repro regressions, valid transitive/mutual/descending cases |
| `ContractRuntimeInstrumentation.cs` | Add diagnostic-only generic enter/exit contract guard keyed by function, receiver, arguments and returned value | Avoid rechecking an identical pending pure-call obligation without suppressing different invocations | Driver recursive cases |
| `ContractRuntimeCampaignRunner.cs` | Treat unresolved closed callee-domain dependencies conservatively using existing callee validity classification if necessary | Closed queries must not validate unchecked dependencies | Driver non-runtime domain fixtures |
| `Source/DafnyDriver.Test/ContractRuntimeCheckTests.cs` | General behavior regressions and valid counterparts; update existing mutual-contract observable expectations | Prove concrete defects and preserve useful acceptance | Driver Contract suite |
| this plan, `plan/INDEX.md`, `wiki/contract-testing.md`, `wiki/INDEX.md` | Record changes, local evidence, durable contract-wrapper facts and limitations | Keep development memory current | diff review |

Validation from `/workspace/cosyn/dafny`: `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~Contract -v minimal`; corresponding `Source/DafnyTestGeneration.Test` Contract filter and `Source/DafnyCore.Test` ContractExpressionReducer filter; `make format`; `git diff --check`. From `/workspace/cosyn`: `make build-dafny`. Prerequisites: SDK 8, cached dependencies, host VSTest loopback permission if sandbox denies sockets. Expected all targeted tests pass and build succeeds; these are local tests, not benchmark/proof/provider evidence. Wait for existing reviewer no-build Driver run before changing build artifacts. Root owns r4 freezing and M1/M2 replay; fresh independent verification remains separate.

- Guard safety refinement (approved by root during implementation): tuple equality does not identify mutable heap states. Reentrant checks whose receiver/input/output types are not supported immutable values must emit an explicit `recursive_heap_contract` unchecked callee obligation instead of sharing pending validation. Static scalar/immutable cycles still share the identical pending obligation. Add a general mutating FBM/mutual-contract regression; this changes no wire fields and assumes no unverified frame purity.

- 02:31–02:33 UTC first implementation compiled with SDK 8.0.131; sandbox VSTest aborted on loopback SocketException(13), log `/workspace/tmp/r6-focused.log`. Approved host focused run passed 9/9 in 46s, `/workspace/tmp/r6-focused-host.log`. Added a closed-false-domain scenario before full Driver regression. Root confirmed prior reviewer session was no longer running; its missing completion remains unverified.
- 02:35 UTC guard safety source refinement added `ImmutableContractKey` and explicit unchecked duplicate-reference validation, with `ExcludesReentrantMutableSpecContracts`. The first broad Driver run had already built its test assembly, so it does not validate this refinement; another current-source run is required. Wiki updated with current implementation facts and explicit reference/datatype/generic cycle limit.

- 02:39 UTC first full Driver Contract run passed 84/84 in 5m44s (`/workspace/tmp/r6-driver-contract-host.log`); this assembly predates the reference-cycle guard refinement. Core reducer `--no-build --no-restore -m:1 --filter FullyQualifiedName~ContractExpressionReducer` passed 27/27 (`r6-core-reducer-host.log`); Core source unchanged. `make format` exit 0 (`r6-format.log`, workspace-load warning), `git diff --check` clean. Versions: .NET SDK 8.0.131, VSTest 17.8.0, system Z3 4.8.12. Current-source guard/domain/old-state focused test run now active before the full owner build.

- 02:40 UTC final guard/domain/old-state/mutual focus passed 6/6 (27s, `/workspace/tmp/r6-guard-focused-host.log`), including concrete FBM heap mutation during mutual-contract evaluation: `calleeContractUnchecked=2`, valid=0, no goal violations. Sharing additionally requires no declared reads frame; this conservative condition is covered by the upcoming final full-source checks. Final `make format` exit 0 (`r6-format-final.log`); owner `make build-dafny` started from `/workspace/cosyn`, log `/workspace/tmp/r6-build-dafny.log`.

- 02:43 UTC 최종 owner build: sandbox `make build-dafny`는 즉시 exit 2(0 warnings/errors, 진단 없음)였고 host 재시도는 성공했지만 nullable reads 경고 1건을 발견했다. null-safe pattern으로 수정 후 host 재빌드 **exit 0, 0 warning/error, 27.42s** (`/workspace/tmp/r6-build-dafny-host-final.log`). 공개 `Binaries/Dafny --version` = `4.11.1+f775837e648a3aede8521a99904fa744b4b8d4c1`. 공개/net8.0 Driver SHA `56aa056b40ec2cb65ba9530e95a7f397c1f2f29ff7c568d740c83da68a6810f2`, TestGeneration SHA `61999c4305475f1e9dfbe74f9765f56b762b7b6f749285a1c3b054fdc864b553`; root도 일치 확인. 이후 source/binary 변경 금지, final `--no-build --no-restore -m:1` Driver Contract·TestGeneration Contract·Core reducer host 검사를 병렬 시작했다. 로그 `/workspace/tmp/r6-final-{driver-contract,testgen-contract,core-reducer}-host.log`. 새 독립 검증 context는 root가 시작했다.

- 02:45 UTC 최종 빌드 기반 `--no-build --no-restore -m:1` host 검사: TestGeneration `FullyQualifiedName~Contract` **279/279 통과**, 1m24s (`r6-final-testgen-contract-host.log`); Core `FullyQualifiedName~ContractExpressionReducer` **27/27 통과**, 251ms (`r6-final-core-reducer-host.log`). Driver Contract는 아직 실행 중이며 통과로 기록하지 않는다. 소스/바이너리 고정 이후 문서만 갱신했다.


### 2026-09-27 R-5 type-constraint callee validity (ready)

Independent evidence: `/workspace/tmp/pbt-engine-final-review-20260927-codex/subset_spec_requires/` and `subset_spec_post/`.
A generated `x: T` is admitted through `Accept(x)` despite Accept's failed requires or ensures. Root authorized this bounded follow-up after the pre-R5 Driver suite completed. No original type constraints, IO construction, wire fields, evaluator logic or dependencies change.

| Files/symbols | Change/how | Necessity/unmet behavior | Validation |
| --- | --- | --- | --- |
| `ContractRuntimeObligationTransformer.MembershipHelper` | Render the constraint through existing callee-validity wrappers instead of raw `Text` | Runtime type-membership predicates otherwise bypass R-1–R-4 validity rules and falsely admit samples | Driver constraint-domain/postcondition regressions |
| `ContractRuntimeCheckTests.cs` | General false/unchecked requires and bad/good ensures cases for subset, nested collections, newtype, datatype-backed subset constraints | Preserve useful accepted samples while invalidating actual predicate executions | Focused TypeConstraintFunction tests; final Driver Contract |
| this plan, plan index, `wiki/contract-testing.md`, wiki index | Record R-5 evidence and superseded build checkpoint | Avoid marking previous build accepted after new defect | diff-check |

Acceptance: failed or unvalidated type-constraint function contracts never admit a valid goal violation; valid predicates continue to admit generated inputs in all covered shapes. Existing support limits for datatype-contained field constraints are not expanded; datatype-backed subset constraints exercise the same MembershipHelper path. Validation: focused host `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter FullyQualifiedName~TypeConstraintFunction -v minimal`, then `make format`, `/workspace/cosyn` `make build-dafny`, and the three final no-build owner suites recorded above. Root owns a fresh r4 freeze and independent review. Source/build freeze from 02:43 UTC is explicitly superseded.

- 02:49 UTC R-5 전 최종 Driver Contract **85/85 통과**, 5m45s (`r6-final-driver-contract-host.log`). 이 결과는 R-5 결함이 없음을 뜻하지 않는다. R-5 계획을 ready로 저장·알린 뒤 in-progress로 전환했다.

- 02:52 UTC R-5 수정은 `MembershipHelper`의 원문 출력 1줄을 `Printer.ExprToString(program.Options, Render(constraint, true))`로 바꾼 것이다. Driver `~TypeConstraintFunction` **12/12 통과**, 55s (`/workspace/tmp/r7-constraint-focused-host.log`). false/unchecked predicate requires는 valid=0이며, 다섯 타입 모양의 정상 predicate는 valid=2/위반2, 잘못된 predicate는 callee 위반2/valid=0/goal위반0을 확인했다. 추가 production 변경은 없다. `make format` 실행 후 owner build와 final no-build 세 suite를 다시 검사한다. Wiki에 같은 원인·지원 범위와 타입 내부 필드 검사 미확장 한계를 기록했다.

- 02:55 UTC R-5 `make format` exit 0 (`r7-format.log`, workspace-load warning), `git diff --check` clean. `/workspace/cosyn` host `make build-dafny` **exit 0, 0 warning/error, 31.34s** (`/workspace/tmp/r7-build-dafny-host.log`). 공개/net8.0 Driver SHA `56aa056b40ec2cb65ba9530e95a7f397c1f2f29ff7c568d740c83da68a6810f2`; TestGeneration SHA `b428ecf9b415f6b6295f87442b106d8ff9c56386ff7e7411aae9dda011980d8b`. 이후 source/binary 변경 없음. 최종 세 suite는 `--no-build --no-restore -m:1`, 로그 `/workspace/tmp/r7-final-{driver-contract,testgen-contract,core-reducer}-host.log`.
- 추가 read-only 간접 호출 probe: `/workspace/tmp/experiment`에서 tmux `pbt-r5-transitive-20260927`, 명령 `python3 /workspace/tmp/r5-transitive-repro/run.py` → 현재 `Binaries/net8.0/DafnyDriver.dll test-contracts request.json --runtime-check`. seed17, sample1, sample timeout5s/campaign60s, closed budget0, provider/auth 없음, 소스는 일반 subset predicate가 계약 없는 Accept를 거쳐 잘못된 Bad를 부르는 형태. 원시 요청·출력·stderr·exit는 `/workspace/tmp/r5-transitive-repro/`에 보존. exit0, `inconclusive`, valid0, calleeContractViolations1, goal위반0. 의심한 간접 경로 결함은 재현되지 않았으므로 traversal/source 수정은 추가하지 않았다. 동일 r7 build identity로 root 독립 검증과 final 회귀를 계속한다.


### 2026-09-27 R-6 structural type-constraint validity (ready)

Independent probes: `/workspace/tmp/pbt-engine-r4-review-20260927-codex/{datatype_nat_invalid,nested_map_invalid,deep_nested_nat_invalid}.{request,result}.json` show invalid nat values in a datatype field, map range, and five nested sequences admitted as valid goal violations. Root explicitly authorized fixes or explicit unchecked support boundaries. Source/build r7 freeze is superseded; reviewer processes ended. Cancelled only owned superseded Driver process tree [915941,916694,916786,955641], not a passing result. Completed r7 TestGeneration 279/279 (1m21s) and Core 27/27 remain recorded for r7 only.

| Files/symbols | Change/how | Necessity/unmet behavior | Validation |
| --- | --- | --- | --- |
| `ContractRuntimeObligationTransformer.HasConstraint` | Traverse map domain and range, datatype constructor formal types with type substitution, and arbitrarily nested finite collection types; detect datatype cycles explicitly | Current map-domain-only and depth>4=false shortcuts silently admit invalid values | Negative/positive map, deep collection, datatype fixtures |
| same: `Membership` | Match nonrecursive datatype constructors and check their formal values; carry visited datatype declarations; return unavailable for recursive/ghost/codatatype or otherwise unsupported membership rather than claiming true | Concrete datatype fields currently receive no validation; actual unsupported recursive shapes must exclude samples | Valid Box(1), invalid Box(-1), nested fields and recursive unchecked fixtures |
| `ContractRuntimeCheckTests.cs` | General supported positive/negative structural constraints and explicit recursive support-boundary tests | Preserve valid controls and prove classification behavior | Focused StructuralTypeConstraint tests, full Driver Contract |
| plan/index and existing contract wiki/index | Superseded run cancellation, new evidence and support boundary | Previous documented datatype-field omission must no longer imply silent acceptance | diff review |

No wire fields, original contracts, budgets, IO construction, benchmark/evaluator inputs, dependencies or provider calls change. No arbitrary traversal depth cap is introduced. Datatype cycles terminate analysis through declaration identity; runtime membership of unsupported recursive shapes is explicitly unchecked. Required validation stays focused host Driver checks, make format, owner make build-dafny, three final no-build owner suites and fresh independent root review.

- R-6 non-null follow-up (root explicitly authorized after concrete probes): `/workspace/tmp/r6-nonnull-repro/{formal,field}.stdout.json` each reports violation_found/valid1 for a null value declared as non-null C, directly and in Box(c:C). Both compiled/resolved; typing is not runtime validation. Add explicit `value != null` membership and null/non-null controls. Apply declared input constraints consistently to function discovery and spec/nested callable wrappers (`HasContract`, `SpecWrapper`, `Wrapper`, `InstrumentCalls`) so formal types are not skipped merely because no explicit requires/ensures exist. Preserve direct goal-call precondition classification; spec/nested domains use existing callee validity classification. No heap-field invariants or construction changes. The structural-only focus passed 10/10 (45s, `r8-structural-focused-host.log`) before this refinement.

- R-6 expected test-shape adjustment: add `Source/DafnyTestGeneration.Test/ContractRuntimeObligationTests.cs:FreshRemainsUnchecked` to the change table. Non-null output types now contribute an additional runtime obligation, so the existing test selects the fresh-expression AST obligation instead of asserting one total obligation. Its original fresh-is-unchecked requirement is preserved. A first edit attempt used the wrong owning working directory and failed before writing; the already-started owner build completed, and this test adjustment is followed by a new formatter/build checkpoint.

- 03:07 UTC R-6 structural/non-null focus **17/17 통과**, 1m18s (`r8-structural-full-focused-host.log`). 최초 구조적 focus 10/10에 non-null formal/Box field의 null·정상값, spec 함수·nested helper의 선언형 domain을 추가했다. Runtime 판단으로 invalid structural inputs는 preconditionRejected, invalid spec/nested formals는 calleeContractViolations, recursive unsupported datatype는 preconditionUnchecked이며 모두 valid0/goal위반0을 확인했다.
- Non-null raw probes: tmux `pbt-r6-nonnull-20260927`, cwd `/workspace/tmp/experiment`, command `python3 /workspace/tmp/r6-nonnull-repro/run.py`, seed17/sample1/5s sample/60s campaign/closed0, provider/auth 없음, .NET8.0.131와 당시 net8.0 engine. `{formal,field}.{request.json,stdout.json,stderr.txt,exit.txt}` 보존, 각각 exit0/violation_found/valid1이었다. source 계약이나 생성 방식은 바꾸지 않고 type membership을 수정했다. Wiki의 typing-enforces-nonnull 주장을 명시적으로 대체했다.

- 03:11 UTC R-6 최종 `make format` exit0 (`r8-format-final.log`, workspace loading warning), `git diff --check` clean. `/workspace/cosyn` host `make build-dafny` **exit0/0 warning/error/27.37s** (`r8-build-dafny-host-final.log`). 공개/net8.0 Driver SHA `5cf53cadfd87cdd8a336050ebeb35d8e4b9d5c7874d7e443921069d17dc7727e`, TestGeneration `d37a454ffe5f2abb4fc4dca70d9fe70d711aa6bbc5d9d56ec9e764e778e36ba3`. Owner 소스/바이너리 고정 후 `--no-build --no-restore -m:1` Driver Contract, TestGeneration Contract, Core reducer 검사 시작. 기존 `ChecksOldState`는 postcondition 선택으로, `FreshRemainsUnchecked`는 fresh AST 의무 선택으로 갱신하여 새 non-null 의무와 기존 의미를 함께 보존한다. 이후 문서만 갱신하며 새 결함 없이는 빌드를 변경하지 않는다.

- 03:14 UTC final Driver run에서 `ClosedQueryDoesNotReportUnprovenClause`의 전체 의무 단일성(assert-single) 가정이 실패했다 (`r8-final-driver-contract-host.log`, 2m39s 지점). R-6가 Sum(k:nat)의 재귀 호출 입력형 의무를 추가하므로 원래 goal postcondition만 선택하도록 해당 기존 테스트를 조정한다. 상태/goal위반 없음/closed-query reason 기대는 유지한다. production 수정은 없다. Root와 조율했으며 현재 suite의 나머지 결과를 수집한 뒤 `BuildProjectReferences=false`로 Driver.Test만 빌드하고 production 해시 보존을 검사한다.

- 03:22 UTC final owner 검사 결과: `/workspace/cosyn/dafny`에서 `dotnet test <project> --no-build --no-restore -m:1 --filter <filter> -v minimal` 사용. `Source/DafnyTestGeneration.Test` / `FullyQualifiedName~Contract`: **279/279 통과**, 1m24s; `Source/DafnyCore.Test` / `FullyQualifiedName~ContractExpressionReducer`: **27/27 통과**, 264ms. `Source/DafnyDriver.Test` / `FullyQualifiedName~Contract`: **113 통과/1 실패/114**, 8m11s. Driver 실패는 위 기존 assertion 한 건이며 aggregate를 통과로 바꾸지 않는다. 로그 `/workspace/tmp/r8-final-{driver-contract,testgen-contract,core-reducer}-host.log`. 모든 해당 실행은 종료됐다.
- Root가 scoped correction/recheck를 승인했다. 독립 검증자의 기존 테스트 실행 종료 후 `dotnet build Source/DafnyDriver.Test --no-restore -m:1 -p:BuildProjectReferences=false -p:PathMap=/workspace/cosyn/dafny=/src/dafny -p:ContinuousIntegrationBuild=true -p:Deterministic=true` → **exit0, 0 warning/error, 4.90s**, `/workspace/tmp/r8-driver-test-only-build.log`. `/workspace/tmp/r8-production-{before,after}-test-build.sha256`는 `Binaries/*.dll Binaries/net8.0/*.dll` 전부를 기록하며 `cmp` 일치. production rebuild/source 수정은 없다. 변경하지 않은 TestGeneration/Core 검사를 다시 돌리지 않는다.
- Fresh independent review **bounded scope accepted**: `/workspace/tmp/pbt-engine-structural-final-review-20260927-codex/REPORT.md`. 자체 요구 probe **26개 기대 일치**, 기존 선택 Driver **10/10 통과**, 실제 CoSyn 통합 **4/4 통과**. 추가 generic `Packet<seq<nat>>` 유효/무효 두 probe는 각각 `inconclusive`, `runtimeErrors=1`, `valid=0`이며 `Unsupported runtime observation type`로 제외됐다. 따라서 전체 예측 집계는 **26/28**이지 28/28 통과가 아니다. 원래 잘못된 generator 이름의 첫 실행도 보고서에 보존돼 있다. 이는 generic datatype 관측 직렬화 지원 한계이며, 요청한 non-generic 구조의 정상 표본 수용과 무효 표본 배제를 확인한 bounded 결과다. 독립 검증 전후 production source/binary maps는 동일했다. 전체 proof나 benchmark 성공을 뜻하지 않는다.
- 남은 지원 한계: recursive datatype domain은 정상값도 `preconditionUnchecked`; 재진입 mutable/reference/reads 계약은 `recursive_heap_contract`; generic datatype 관측은 위 예처럼 runtime error가 될 수 있다. 기존 M2 D-15의 ghost 함수/필드를 실행 불가능한 non-ghost draft 본문에서 사용하는 경우는 §5.1 컴파일 가능 draft 요구를 만족하지 않아 draft 진단과 함께 `unsupported`다. 임의 IO 생성이나 원본 계약 변경은 하지 않았다. Root가 frozen r4와 새 경로의 오프라인 M1/M2 결과를 담당하며, 이 owner 기록으로 그 결과를 선행 주장하지 않는다.

- 03:25 UTC scoped 최종 재검사: `/workspace/cosyn/dafny`에서 `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~ClosedQueryDoesNotReportUnprovenClause -v minimal` → **exit0, 1/1 통과**, `/workspace/tmp/r8-driver-corrected-case-host.log`. Root가 결과와 production 해시 보존을 확인하고 추가 검사/build 없이 owner 문서 인계를 요청했다. 전체 Driver 113/1 실패 기록은 보존한다. `git diff --check` 최종 확인 후 owner 작업은 종료하며 root가 frozen r4 M1/M2와 전체 계획 마감을 맡는다.


### 2026-09-27 R-7 read-only actual M1 compilation investigation (ready)

Root requested explaining r4 M1 `unsupported` before sampling, with no production/source/frozen-artifact changes authorized. `ContractCompilerWorker.CompileSourcesAsync` loses backend compiler output by reporting only BatchErrorReporter messages; public supervision discards worker stdout when a result exists. First completed worker retained generated C# and request under `/tmp/dafny-runtime-check-cc08c9d74ad84b42a9ec5de35e621c77` (seed17328659189822091155). Root campaign artifacts remain untouched.

| File/symbol | Planned action | Necessity / validation |
| --- | --- | --- |
| `/workspace/tmp/r4-m1-compile-investigation-20260927/` probe artifacts only | Copy completed generated C#/bridge/csproj/config/request to independent directory; relocate compile includes only; record original hashes, command, versions, frozen identities; rerun generated C# offline build in tmux from `/workspace/tmp/experiment` | Recover actual compiler diagnostic without changing campaign inputs/source/binaries; compare original generated-source hashes before/after; capture process exit/output |
| This owner plan | Record concrete root cause and minimal proposed next action | No implementation approval inferred from investigation |

Command: independent `dotnet build <copied diagnostic.csproj> -o <probe output>` with existing cleared package sources; cached .NET SDK8/packages only, no provider/auth/network/dependencies. Session `pbt-r4-m1-compile-investigate-20260927`. Expected result: precise backend error or clean build distinguishing transient/environment failure. No benchmark or proof claim, no r4 mutation.

- R-7 investigation in-progress: copied generated C# build exited1 in4.20s. Exact CS1628 at generated lines19163/19177: structural datatype match captures method out parameters `processed`/`renderTrace` inside C# lambda. This is a generated-membership compilation defect, not package failure or intentional unsupported shape. Extend scratch probe only to independent `datatype Box=Box(n:nat)` method-output normal/bad cases plus scalar-output control against frozen r4; one sample, seed17, closed budget0, own tmux/paths, no source edits.


### R-7 generated output membership and backend diagnostics fix (in-progress, root authorized)

Objective: preserve declared datatype/collection output constraints while compiling multi-result method wrappers, and make real backend errors actionable through existing reason fields. No benchmark-specific behavior, dropped checks, source contracts, draft changes, wire additions, frozen r4 writes, packages, paid runs or commits. Initial scratch general-probe launch used the wrong frozen DLL root and exited1 before executing; preserved artifacts. Attempt2 uses `/engine/DafnyDriver.dll`; a single return compiles to a C# return value and does not trigger CS1628, so regression fixtures must use multiple outputs.

| Exact owner file/symbol | Change/how | Why / unmet behavior | Validation |
| --- | --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractRuntimeObligationTransformer.cs:TypeConstraintChecks` | Bind executable method-output formal values to fresh local aliases before Membership evaluation; serialize/report original formal names | C# match expressions capture out parameters when a method has multiple outputs, rejecting supported datatype results | General valid/invalid multi-output datatype and nested collection fixtures, callee variants |
| `Source/DafnyDriver/Legacy/SynchronousCliCompilation.cs:CompileDafnyProgram` | Optional supplied output writer, default existing writer | Allows diagnostic compiler consumer to retain backend errors without globally replacing console output | Existing compile callers unchanged; focused CLI regression |
| `Source/DafnyDriver/ContractTesting/ContractCompilerWorker.cs:CompileSourcesAsync` | Capture backend writer text; include actual compiler output and reporter errors in failed compile reason | Current failed backend reports trigger/induction information only | Deliberately invalid C# dependency through public runtime CLI must produce CS0103 with offending symbol, generated0 |
| `Source/DafnyDriver.Test/ContractRuntimeCheckTests.cs` | General multi-result goal/callee constraints and diagnostic propagation fixtures | Prevent recurrence while preserving valid controls and invalid-result classification | Focused R-7 plus existing structural/closed/spec/old/callee Contract checks |
| Owner plan/index and `wiki/contract-testing.md`, `wiki/INDEX.md` | Record fix, exact checks, source/binary identity, bounded fresh review, remaining limits | Root must freeze r5 only after accepted fix; r4 results remain provenance | Final diff review/hash comparison |

Validation: `/workspace/cosyn/dafny` focused Driver R-7 tests then final no-build affected Driver R-7/structural/callee/closed/old/legacy compiler checks (includes prior corrected test; all four `ContractExternExecutionTests` exercise the legacy compile consumer), TestGeneration Contract; `make format`, `git diff --check`. Root approved bounded affected Driver scope; unchanged Core reducer retains previous27/27 evidence and is not rerun. `/workspace/cosyn` `make build-dafny`, 0 warnings/errors. Use cached prerequisites/approved VSTest host loopback. Root requests a fresh independent R-7 review before freezing r5; only scratch general probes may run until production implementation is ready. Actual r4 M1/M2 continue on frozen toolchain without mutation.

- 03:34 UTC R-7 focused `dotnet test Source/DafnyDriver.Test --no-restore -m:1 --filter 'FullyQualifiedName~ChecksMultipleStructuralOutputs|FullyQualifiedName~ChecksMultipleCalleeStructuralOutputs|FullyQualifiedName~CliReportsBackendCompilationError' -v minimal` **11/11 통과**,49s, `/workspace/tmp/r9-focused-host.log`. Goal Box/seq<Box>/map<int,seq<Box>>의 정상·잘못된 결과, callee Box/seq<Box> 정상·잘못된 결과, 실제 C# CS0103 오류의 공개 JSON 전달을 확인했다. 출력 의무는 원래 formal 이름 `b`로 값을 보고한다.
- Frozen-r4 independent scratch: attempt2 single-output valid datatype/scalar → no_violation_found/valid1, invalid datatype → violation_found/valid1; attempt3 multiple-output valid/invalid datatype → unsupported/generated0, scalar → no_violation_found/valid1. `probe-v2.py`, `probe-v3.py`, `attempt{2,3}/`에 별도 보존. 최초 잘못된 경로의 process exit1과 구분하며 수정 실행으로 덮어쓰지 않았다. 원래 completed worker의 복사 대상7개 SHA256를 다시 비교해 변경 없음 확인. 이 probe는 frozenr4만 사용했고 실제 benchmark 계약/원시 결과에는 쓰지 않았다.

- 03:36 UTC final `make format` exit0 (`r9-format.log`, workspace-load warning), `git diff --check` clean. `/workspace/cosyn` host `make build-dafny` exit0/0 warnings/errors/27.51s (`r9-build-dafny-host.log`). Public/net8 Driver/TestGeneration SHA는 최신 §0에 있다. SDK8.0.131/VSTest17.8.0/Dafny4.11.1+f775837e 기준 dirty owner 구현이며 dependency/provider 변경은 없다. Source/binaries 고정 후 final no-build 검사를 시작했고 root에 independent review 준비를 통지했다.
- Final Driver command from `/workspace/cosyn/dafny`: `dotnet test Source/DafnyDriver.Test --no-build --no-restore -m:1 --filter 'FullyQualifiedName~ChecksMultiple|FullyQualifiedName~CliReportsBackendCompilationError|FullyQualifiedName~StructuralTypeConstraint|FullyQualifiedName~FunctionByMethodCallee|FullyQualifiedName~SpecFunctionDomain|FullyQualifiedName~NestedSpecFunctionContract|FullyQualifiedName~OldState|FullyQualifiedName~ClosedQueryDoesNotReportUnprovenClause|FullyQualifiedName~ContractExternExecutionTests|FullyQualifiedName~ChecksConjunctiveQuantifiedCalleePostcondition' -v minimal`, log `/workspace/tmp/r9-final-driver-affected-host.log`. Parallel TestGeneration command: `dotnet test Source/DafnyTestGeneration.Test --no-build --no-restore -m:1 --filter FullyQualifiedName~Contract -v minimal`, log `/workspace/tmp/r9-final-testgen-contract-host.log`. Both pending at this checkpoint; no aggregate pass claim.

- R-7 final no-build first attempt failed prerequisites: Driver **12 passed/31 failed/43**,39s; TestGeneration **200 passed/79 failed/279**,41s. Exact failures include missing `Source/DafnyDriver.Test/bin/Debug/net8.0/DafnyCore.dll` and TestGeneration testbin `DafnyPrelude.bpl`. Public Binaries copies exist. Test directories' modification times03:36:29–30 precede test starts≈03:36:36 and match full solution build, supporting incomplete test output copying at build completion rather than a source behavior regression; exact MSBuild copy/cleanup cause is not established. No tool/source mutations occurred after that build, and reviewer confirms no build/clean. Neither aggregate is passing.
- Validation repair (ready, root informed/reviewer coordinated): sequential `dotnet build Source/DafnyDriver.Test --no-restore -m:1 -p:BuildProjectReferences=false -p:PathMap=/workspace/cosyn/dafny=/src/dafny -p:ContinuousIntegrationBuild=true -p:Deterministic=true` and matching TestGeneration.Test command, only after completed failed runs. Hash every `Binaries/*.dll Binaries/net8.0/*.dll` before/after; verify required test dependency files explicitly; rerun identical filters with unique `r9-retry-*` logs. No source or production rebuild required. Reviewer uses public CLI and has released/avoided test bins.

- Test prerequisite repair completed: Driver test-only build2.10s, TestGeneration test-only build1.79s, both exit0/0 warnings/errors (`r9-{driver,testgen}-test-repair-host.log`). Both test output folders now contain DafnyCore.dll and DafnyPrelude.bpl. All production DLL manifests `/workspace/tmp/r9-production-{before,after}-test-repair.sha256` compare identical. Identical no-build filters restarted into `/workspace/tmp/r9-retry-{driver-affected,testgen-contract}-host.log`; first failed logs retained. No source change or production rebuild. Reviewer continues independent public-CLI probes.

- Repaired TestGeneration Contract retry **279/279 통과**,1m26s, exit0 (`/workspace/tmp/r9-retry-testgen-contract-host.log`). This replaces no failed record: original200/79 missing-prelude run remains preserved. Driver43 retry and independent verdict still pending at this checkpoint.

- Fresh independent R-7 review **accepted bounded compiler follow-up**: `/workspace/tmp/pbt-engine-output-final-review-20260927-codex/REPORT.md`. Independent9 structural multi-result campaigns/18 samples all matched (goal/callee/draft datatype and nested seq/map positive/negative); runtime backend CS0103 visibility, legacy compile worker success/failure, ordinary CLI multi-return output42 all passed. Actual CoSyn integration **4 passed/9.57s**. All40 selected production source/binary hashes unchanged before/final. This is local bounded behavior evidence, not proof/full-plan or benchmark acceptance. Owner Driver43 retry still running when report received; final freeze remains root-owned after that result.

- 03:43 UTC final affected Driver retry **43/43 통과**,3m28s,exit0 (`/workspace/tmp/r9-retry-driver-affected-host.log`). 모든 지정 owner 검사가 완료됐고 root에 즉시 r5 freeze 준비를 통지했다. 최초 실패43-case aggregate와 TestGeneration279-case aggregate는 별도 기록으로 유지한다. Source edits/builds 이후 production identity 변경 없음; 마지막 작업은 계획/wiki와 index 갱신, `git diff --check`다. Core/전체 Driver/benchmark/proof 검사를 추가 실행하지 않으며 root가 새r5 M1/M2를 맡는다.
