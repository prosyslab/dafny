# ContractConcrete ConversionExpr 처리 계획

- 상태: done
- 작성일/갱신일: 2026-09-14
- 소유 저장소: Dafny (`/workspace/cosyn/dafny`).
- 상위 계획: [통합 계획](../../../plan/2026-09-14-contract-conversion-reduction.md)
- 선행 계획: [입력 패턴·P 자동 판정](2026-09-13-pattern-guided-contract-pbt.md)

## 목표와 수용 기준

`ContractExpressionReducer`가 사용하는 `ContractConcrete` profile에서 concrete literal conversion을
평가하고, conversion을 포함한 datatype을 pure function/predicate 인라인에 사용할 수 있게 한다.
첫 대상은 실제 r17 concrete filesystem의 `(493 as bv32)`이며 구현은 일반 resolved Dafny AST와
target type을 기준으로 한다.

- 지원되는 integral literal conversion은 target bitvector 폭의 typed literal로 결정된다.
- symbolic operand, 지원하지 않는 target과 잘못된 resolved AST는 residual로 보존한다.
- conversion normalize, equality, hashing과 inline eligibility가 서로 다른 값을 만들지 않는다.
- 기본 profile은 기존 동작을 유지한다.
- 일반 회귀에서 conversion 포함 nested datatype predicate가 더 이상 최상위 호출에서 residual이
  되지 않는다.

## 구현 범위와 위험

| 파일·심볼 | 변경 | 이유 | 검증 |
| --- | --- | --- | --- |
| `Source/DafnyCore/Rewriters/PartialEvaluatorVisitor.cs`: expression dispatch/conversion simplifier | contract profile에서 operand를 먼저 줄이고 안전한 resolved literal conversion을 typed literal로 치환 | nested datatype의 conversion node 제거 | focused test |
| `Source/DafnyCore/Rewriters/PartialEvaluatorEngine.cs`: contract concrete recognition/normalization/identity | 방문 전 function-call eligibility에서도 동일 conversion을 concrete로 인식 | `ValidInodeFileSystemData` 인라인 gate 해제 | identity/equality와 recursive predicate regression |
| `Source/DafnyCore.Test/ContractExpressionReducerTests.cs` | 일반 bv field datatype과 predicate 회귀 | benchmark 과적합 없이 차단을 고정 | focused/전체 reducer |
| `wiki/contract-testing.md`, 이 계획 | 검증된 변환 의미와 남은 한계 기록 | durable 경계 보존 | diff review |

bitvector conversion은 폭에 따른 modulo 의미를 보존해야 한다. 이번 입력 모델은 이미 폭 안의
비음수 bitvector literal만 생성하지만 reducer는 source AST만 보고 동작하므로 target type을 확인해
typed literal을 만든다. conversion을 열고 나서 나타나는 재귀·quantifier residual은 별도 원인으로
기록하고, 원 assertion을 SMT에 유지하는 soundness 경계는 바꾸지 않는다.

## 검증

- `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore --filter FullyQualifiedName~<new-conversion-test> --logger "console;verbosity=minimal" -m:1`
- `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore --filter FullyQualifiedName~ContractExpressionReducerTests --logger "console;verbosity=minimal" -m:1`
- `dotnet test Source/DafnyCore.Test/DafnyCore.Test.csproj --no-restore --filter 'FullyQualifiedName~PartialEvaluatorTest|FullyQualifiedName~UnrollBoundedQuantifiersTest' --logger "console;verbosity=minimal" -m:1`
- relevant `ContractPatternTests`, `dotnet build Source/Dafny.sln --no-restore -m:1`, scoped whitespace,
  `git diff --check`.
- 상위 계획에서 packaged wrapper build와 actual fixed P-only preflight를 별도로 실행한다.

implementation/Q/replay, `spec_check`, provider와 `/workspace/dafnyutils` 수정은 제외한다. 새 package는
추가하지 않는다.

## 구현 결과

`PartialEvaluatorVisitor`는 `ContractConcrete` profile에서만 conversion operand를 먼저 줄이고,
engine의 공통 normalization helper가 안전하다고 판정한 경우 target-typed literal로 치환한다.
helper는 resolved source를 int 계열, bitvector, char로 제한한다. target은
`NormalizeExpandKeepConstraints`에서 subset이 아니고 `ConstantFolder.AsUnconstrainedType`을
통과하는 int 또는 bitvector만 허용한다. `ConstantFolder.TryFoldInteger`로 conversion의 정의
여부와 bitvector 범위를 판정한다.
따라서 nested datatype/collection의 `493 as bv32`는 concrete identity와 equality, function-call
eligibility에서 같은 `bv32` 값으로 취급된다. `256 as bv8`, exact real-to-int, symbolic operand,
`nat`, 사용자 subset, constrained newtype과 지원하지 않는 domain은 residual로 남는다. 기본
profile은 conversion을 새로 fold하지 않는다.

일반 회귀는 focused conversion 5/5, 전체 reducer 27/27, 기존 partial evaluator 58/58,
bounded quantifier unrolling 39/39, pattern contract 54/54가 통과했다. 전체 solution과 CoSyn
`make build-dafny`도 warning/error 0으로 성공했다. `git diff --check`는 관련 source/test에서
통과했다.

독립 검증이 actual r17 concrete filesystem을 재현했다. 기본 10,000-node budget에서는
argument의 contract-concrete 판정이 `true`가 되어 conversion 이전 차단을 통과하지만,
predicate/quantifier expansion 예약이 `ExpressionNodeLimit`에 닿아 top-level 원식을 residual로
복구한다. 1,000,000-node 진단에서는 conversion과 `ValidInodeFileSystemData` 호출이 없어지고,
set comprehension 세 개 및 `InodeNamespaceIds`/`InodeNamespaceIdPaths` 호출만 다음 residual로
남았다. 이는 conversion 지원의 수용 기준을 충족하며 예산/comprehension 강화는 후속 범위다.

기본 substituted 식 50노드에 남은 expansion 예산은 9,950이었지만, 현재 사전 상한 공식
`template nodes * (1 + sum(substitution value nodes))`이 세 quantifier 뒤 9,346을 예약해 다음
치환 전에 exhaustion을 냈다. 1,000,000-node 진단에서는 누적 14,351을 예약했지만 실제 reduced
식은 187노드였다. formal 출현 횟수를 세는 occurrence-aware 상한과 실패한 subexpression만
residual로 보존하는 방식이 후속 개선점이다.

건전성 보정 후 상위 계획의 fixed P-only r19는 유효 입력 2개를 모두 승인했다. 첫 `FileSystem` residual은 원본
membership SMT query가 `Unsat`이었고 두 번째는 obligation cache를 재사용했다. r18은 보정 전
결과라 최종 근거에서 제외했다. r19 raw artifact도 검증 당시 로컬로 생성했지만 사용자 요청에
따라 삭제했고 Git에는 보존하지 않는다.

## 독립 검증 차단 결함

독립 verifier가 `(-1) as nat`과 constrained subset `0 as Positive`를 확인했다. 두 식은 Dafny
verifier가 target constraint 불충족으로 거부하지만 첫 구현 reducer는 conversion을 literal로
치환하고 무관한 predicate를 `True`로 판정했다. 원인은 target guard가 모든 int-based type을
허용하고 `ConstantFolder`의 constrained-newtype 검사에 subset type까지 포함된다고 가정한 것이다.
plain/unconstrained integer와 bitvector target만 허용하고 subset/refinement target은 residual로
보존하는 fail-closed 수정과 두 회귀를 추가했다. 독립 재검증은 invalid `nat`/subset이 residual로
남고 in-range int-to-bv, nested bv-to-int, char-to-int만 축약됨을 확인했다. real, symbolic,
out-of-range와 valid/invalid subset target은 모두 residual이었다. 독립 regression/build/format과
최종 actual r19가 통과해 계획을 `done`으로 닫는다.
