# 외부 호출의 계약 실현 경계 확장

- 상태: done
- 작성일/갱신일: 2026-09-13
- 소유 저장소: Dafny (`/workspace/cosyn/dafny`).
- 기준 커밋: `1eb9fc5fa2661483de151ff85b21eed0b695878a`의 기존 dirty 작업 트리.
- 상위 계획: [CoSyn 계획](../../plan/2026-09-13-symbolic-extern-contracts.md).

## 목표

계약 검사 진단 프로그램에서 `{:extern}` 선언의 네이티브 구현을 호출하지 않는다. 해결된
원래 선언의 `requires`, `ensures`, `reads`/`modifies`를 기존 계약 모델 실현 질의에 넣고,
구체 출력과 유한 후힙을 얻어 원식과 프레임을 다시 확인한다. 본문 경로 생성에서도 같은
호출을 abstract call로 보존한다.

## 수용 기준과 비목표

- 정적 외부 메서드, 유한 객체를 변경하는 외부 메서드, 외부 함수의 계약 선택을 지원한다.
- 호출 전 P 위반, 모순된 Q, 불완전 모델, 시간 초과는 각각 기존 구조화 상태로 남긴다.
- 외부 계약 선택은 replay choice에 기록되고 같은 출력·후힙으로 정확 재생된다.
- 테스트용 외부 구현의 marker 부작용이 발생하지 않는다.
- ghost 전용 `BenchIO.IO` 전체 지원, 생성자/동적 할당, 새 값 종류, 무한 힙은 이번 범위가 아니다.
- 외부 구현의 정확성을 주장하지 않으며 검증 정책이나 사용자 명세를 변경하지 않는다.

## 변경표

| 파일·심볼 | 변경 방법 | 검증 |
| --- | --- | --- |
| `Source/DafnyTestGeneration/ContractTesting/ContractHarnessBuilder.cs` | 도달 외부 선언을 진단용 bodyless 계약 모델로 낮추고 해당 `extern` 속성만 소스 사본에서 제거한다. 기존 `Realize`/`Choose` 본문, precondition RPC, heap snapshot 경계를 재사용한다. | 외부 정적/힙 실행 및 marker 미생성 테스트 |
| `Source/DafnyTestGeneration/ContractTesting/ContractModelRealizer.cs` | 외부 선언을 실제 body가 아닌 계약 모델 대상으로 분류하고 heap-independent 실현의 extern 거부를 제거한다. | 출력 모델, P/Q, replay 단위 테스트 |
| `Source/DafnyTestGeneration/ContractTesting/ContractHeapModelRealizer.cs` | 외부 선언의 유한 힙 전이를 `modifies`로 제한해 기존 상관 모델에 허용한다. | modifies 밖 보존 및 alias 회귀 |
| `Source/DafnyTestGeneration/ContractTesting/ContractSolver.cs` | 새 진단 질의 AST에서 extern 함수의 Dafny/`by method` 정의를 제거하고 원래 P/Q는 명시적 질의 식으로 유지한다. | bodyful extern 함수가 구현값이 아니라 Q를 따르는 모델·입력 생성 회귀 |
| `Source/DafnyCore/ContractTesting/ContractBodyExpander.cs` | extern 메서드/함수를 본문 유무보다 우선해 abstract call로 캡처한다. | 경로 생성 goal/frontier 테스트 |
| `Source/DafnyTestGeneration.Test/*Contract*Tests.cs` | 위 정상·오류·미호출·replay 사례를 한 테스트 한 시나리오 규칙으로 추가/갱신한다. | 선택 xUnit 및 프로젝트 전체 |
| `Source/DafnyDriver.Test/ContractExternExecutionTests.cs` | marker를 쓰는 통제된 C# extern 의존성을 포함한 실제 compiler worker/runner 실행으로 네이티브 구현 미호출을 확인한다. | 진단 실행 성공, 계약 모델 출력, marker 파일 미생성 |

## 사운드니스 조건

1. 진단 소스에서 제거하는 것은 선택된 도달 외부 선언의 `extern` 속성뿐이며 원래 계약식과 위치·소스 해시는 영수증에 유지한다.
2. Q를 모델 생성에 사용할 수 있지만 구체화 뒤 Q를 가정하지 않은 별도 질의로 전체 원식을 재검사한다.
3. 힙 모델은 기존 객체 신원만 사용하고 `modifies`가 허용한 셀만 변화시킨다. 미지원 프레임식은 `unsupported`다.
4. 외부 호출을 실제 실행한 것으로 표기하지 않고 `UsedContractModels`와 `ContractAbstractChoice`를 유지한다.
5. 원래 외부 계약이 불충분하면 그 허용된 임의성을 그대로 보존하며 의도한 동작을 추가하지 않는다.

## 검증 명령

- `dotnet test Source/DafnyTestGeneration.Test --filter 'FullyQualifiedName~Contract'`
- `dotnet test Source/DafnyTestGeneration.Test`
- `dotnet build Source/Dafny.sln`
- 변경 파일에 대한 `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include ...`
- `git diff --check`

새 의존성·네트워크·유료 실행은 필요하지 않다. 구현 후 실제 명령, 환경, 결과와 미실행
범위를 이 문서에 기록한다.

## 실행 기록

2026-09-13에 계획 범위를 구현했다. `ContractBodyExpander`는 extern 메서드와 함수를 본문
유무보다 먼저 abstract call로 캡처한다. 런타임 사본은 도달 extern 선언의 해당 속성만
제거하고 메서드는 `Realize`, 함수는 `Choose` 본문으로 바꾼다. 함수의 원래 Dafny 본문과
`by method` 구간도 함께 제거한다. 모델 실현기는 기존 P 검사, Q를 사용한 상관 모델 선택,
Q를 가정하지 않은 구체 재검사, 유한 `modifies`/`old` 후힙, 정확 replay를 extern에도 그대로
적용한다. 새 질의를 해석한 뒤에는 extern 함수의 Dafny/`by method` 본문을 제거하여 SMT
모델이 네이티브 또는 Dafny 구현 정의에 제약되지 않게 했다.

독립 읽기 전용 검토에서 body가 있는 extern 함수의 SMT 정의 잔존과 `by method` 실행 가능성
두 건을 발견했다. 위 수정과 전용 회귀를 추가한 뒤 bodyful 함수의 모델·입력 생성이 Q를
따르고 런타임 사본에 외부 이름·본문 marker·by-method 반환문이 남지 않음을 확인했다.

검증 환경은 .NET SDK `8.0.131`, 기준 커밋은 위와 같고, 계약 엔진 전체가 아직 untracked인
기존 dirty 작업 트리를 보존했다.

- `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractBodyExpansionTests.External|FullyQualifiedName~ContractModelRealizerTests.RealizesExternal|FullyQualifiedName~ContractModelRealizerTests.RejectsExternal|FullyQualifiedName~ContractModelRealizerTests.ReplaysExternal|FullyQualifiedName~ContractInputTests.ExternalMethodIsCaptured|FullyQualifiedName~ContractEntryTests.ReachableExternalBody' --logger 'console;verbosity=normal'`: 8/8 통과.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~Contract' --logger 'console;verbosity=minimal'`: 147/147 통과.
- `dotnet test Source/DafnyTestGeneration.Test --no-restore --logger 'console;verbosity=minimal'`: 217/217 통과.
- `dotnet build Source/Dafny.sln --no-restore --verbosity minimal`: 성공, 경고 0, 오류 0.
- 독립 검토 수정 후 `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractModelRealizerTests.RealizesExternalFunctionContract|FullyQualifiedName~ContractEntryTests.ReachableExternalByMethodCannotInvokeNativeImplementation|FullyQualifiedName~ContractEntryTests.ReachableExternalBodyCannotInvokeNativeImplementation|FullyQualifiedName~ContractBodyExpansionTests.External' --logger 'console;verbosity=normal'`: 5/5 통과.
- 최종 bodyful SMT 회귀 `dotnet test Source/DafnyTestGeneration.Test --no-restore --filter 'FullyQualifiedName~ContractInputTests.ExternalFunctionBodyDoesNotConstrainContractChoice|FullyQualifiedName~ContractModelRealizerTests.RealizesExternalFunctionContract|FullyQualifiedName~ContractEntryTests.ReachableExternalByMethodCannotInvokeNativeImplementation' --logger 'console;verbosity=normal'`: 3/3 통과.
- `dotnet test Source/DafnyDriver.Test --no-restore --filter 'FullyQualifiedName~ContractExternExecutionTests.DiagnosticExecutableDoesNotInvokeNativeExtern' --logger 'console;verbosity=normal'`: 1/1 통과. 실제 compiler worker와 `ContractTestRunner`가 marker를 쓰는 통제된 C# extern 소스를 함께 컴파일했으며, 계약 모델 출력 `7`, `UsedContractModels=true`, marker 파일 미생성을 확인했다.
- 변경 C# 파일의 `dotnet format whitespace Source/Dafny.sln --no-restore --verify-no-changes --include ...`: 성공. 솔루션 로드 경고 문구만 출력되었고 형식 차이는 없었다.
- `git diff --check`: 통과.

전체 217개와 솔루션 build는 독립 검토 수정 전에 실행했고, 수정 뒤에는 위 5개와 3개
집중 회귀를 다시 빌드·실행했다. 새 패키지, 네트워크나 유료 실행은 사용하지 않았다.
마지막 종단 간 회귀에서는 marker 부작용만 가진 로컬 C# extern 의존성을 해시 검증된 입력으로
연결했다. 실제 진단 실행이 완료된 뒤 marker가 없음을 검사하여 외부 구현 미호출을 확인했다.

`BenchIO.IO`의 ghost 전용 상태는 계획대로 지원하지 않는다. 이를 다루려면 별도
symbolic-entry 단계에서 ghost 상태 관찰·전달·재생 경계를 설계해야 한다. 생성자/동적 할당,
새 값 종류와 무한 힙도 이번 결과에 포함하지 않는다.

No durable findings. 이번 변경의 재사용 가능한 경계와 제한은 이 계획과 코드의 계약 주석에
모두 기록되어 있어 별도 wiki 페이지를 만들지 않았다.
