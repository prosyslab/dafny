# 구현 계획

| 계획 | 상태 | 목표 | 갱신일 |
| --- | --- | --- | --- |
| [2026-09-29-recursive-and-nested-heap-construction](2026-09-29-recursive-and-nested-heap-construction.md) | done | `object` 참조·순환 fixed-state 힙과 중첩 `pbt_heap_constructor` 경로/기본 할당; Core93·TestGen649·Driver251, 독립 검증 통과 | 2026-09-29 |
| [2026-09-29-pbt-readability-refactor](2026-09-29-pbt-readability-refactor.md) | done | 커밋 전 PBT 코드 동작 보존 리팩토링; Core93·TestGen645·Driver244 기준선 동일, 독립 검증 1건 수정 | 2026-09-29 |
| [2026-09-29-runtime-classification-deadline](2026-09-29-runtime-classification-deadline.md) | done | Independent23/23; h11 returns a result without late initial phases; h13 exact sentinel preserved | 2026-09-29 |
| [2026-09-29-ordered-runtime-check-fragments](2026-09-29-ordered-runtime-check-fragments.md) | done | Independent22/22 and all6 paired byte-prefix audits pass; exact two-ordinal runtime limits retained | 2026-09-29 |
| [2026-09-29-exact-membership-proof-reuse](2026-09-29-exact-membership-proof-reuse.md) | done | Independent21/21, artifact audit and cancellation-during-hit pass; exact campaign-local proof reuse | 2026-09-29 |
| [2026-09-29-observed-ghost-inputs](2026-09-29-observed-ghost-inputs.md) | done | Independent native133/Driver12 pass; h15 actual return capture added but original dependency proof blocks Q | 2026-09-29 |
| [2026-09-29-compositional-contract-proofs](2026-09-29-compositional-contract-proofs.md) | done | Independent Core93/query87 and h07 both polarities pass; known negated-witness timeout and h08 sequence limits remain explicit | 2026-09-29 |
| [2026-09-29-sequential-contract-optimization](2026-09-29-sequential-contract-optimization.md) | done | Bounded ordered stages independently accepted; six fixed campaigns/replay complete with coverage limits | 2026-09-29 |
| [2026-09-29-scalar-clause-dependencies](2026-09-29-scalar-clause-dependencies.md) | done | Certify exact original scalar-clause logical dependencies before accepting closed decisions | 2026-09-29 |
| [2026-09-29-runtime-prefix-counterexamples](2026-09-29-runtime-prefix-counterexamples.md) | done | Validate original loop-invariant counterexamples from exact finite prefixes without later evidence | 2026-09-29 |
| [2026-09-29-runtime-structural-reuse](2026-09-29-runtime-structural-reuse.md) | done | Reuse immutable preparation names and reflection metadata while preserving runtime observations | 2026-09-29 |
| [2026-09-29-checked-witness-reduction](2026-09-29-checked-witness-reduction.md) | done | Admit concrete structured captures and add bounded exact existential reduction with checked proof gates | 2026-09-29 |
| [2026-09-29-inconclusive-runtime-optimization](2026-09-29-inconclusive-runtime-optimization.md) | done | Correct serialization, checked reduction and runtime bottlenecks for six historical inconclusive cases | 2026-09-29 |
| [2026-09-29-closed-clause-types](2026-09-29-closed-clause-types.md) | done | Qualify captured types/constructors and cross-context nat; independent12/12, actual h13 reaches native queries; remaining proof/encoding limits recorded | 2026-09-29 |
| [2026-09-29-ghost-initial-validity](2026-09-29-ghost-initial-validity.md) | done | 지원되는 ghost 진입 입력을 원본 초기 상태 검증에 허용; 집중8개·독립 native44/Core42/Driver7 통과, 기존 실행 경계 유지 | 2026-09-29 |
| [2026-09-27-runtime-query-optimization](2026-09-27-runtime-query-optimization.md) | done (사용자 결정으로 종료; 전체 모집단 수용은 후속) | frozen10 M1 탐지6/6·M2 탐지3/4. frozen11 기록 보존18/18; 원본 CatSpec warm7.128초 검증; 논리/실행 증명 역할 분리 구현·집중98/98 및 Driver14/14 통과, frozen12 논리/상태 인증 통과·음성 Q 시간초과, 상태 인식 PE 집중 Core98/98·native141/141·Driver15/15 통과, 원본 범위를 보존하는 PE 잔여 경계·scope 수정 완료; Core100/100·native157/157; Q28 iff 통과·원본 target nonproof8.214초, Q29 timeout10.113초; 최종 검증·역사 rerun root 인계 | 2026-09-29 |
| [2026-09-27-runtime-entry-heap-checking](2026-09-27-runtime-entry-heap-checking.md) | done | 범위를 한정한 엔진 구현 독립 검증 완료: TestGeneration313/313·Driver168/168·원시 재현10개·build 통과. 생략된 중첩 refinement 상태는 unchecked 유지; root r6 평가 별도 | 2026-09-27 |
| [2026-09-26-runtime-obligation-checking](2026-09-26-runtime-obligation-checking.md) | done | 승인된 구현·bounded 독립 검증 완료; R7 Driver43/43·TestGen279/279·build 통과. Root r5 독립 집계 승인: M1 탐지6/6·오탐0/5, M2 ghost draft로8개unsupported; 지원 한계 유지 | 2026-09-27 |
| [2026-09-14-contract-conversion-reduction](2026-09-14-contract-conversion-reduction.md) | done | ContractConcrete reducer가 구체 ConversionExpr를 안전하게 평가 | 2026-09-14 |
| [2026-09-13-pattern-guided-contract-pbt](2026-09-13-pattern-guided-contract-pbt.md) | done | 일반 Dafny 입력 패턴에서 후보를 생성하고 원본 P를 부분 평가·잔여 SMT로 자동 판정 | 2026-09-14 |
| [2026-09-13-symbolic-entry-contract-checking](2026-09-13-symbolic-entry-contract-checking.md) | done | ghost·외부 상태를 구체화하지 않고 일반 Dafny 진입점 구현 계약을 SMT로 검사 | 2026-09-13 |
| [2026-09-13-symbolic-extern-contracts](2026-09-13-symbolic-extern-contracts.md) | done | 외부 구현을 호출하지 않고 원래 계약·프레임으로 SMT 후상태를 실현 | 2026-09-13 |
| [2026-09-12-expecto-residual-constraint-solving](2026-09-12-expecto-residual-constraint-solving.md) | done | 범용 타입/힙·구현 경로 생성·부분 평가·실제 실행·잔여 SMT를 연결 | 2026-09-12 |
# Current work

- [Remove legacy contract testing](2026-10-03-remove-legacy-contract-testing.md) — done; keep only the runtime PBT campaign mode and its shared helpers.
- [PBT Runtime/SMT naming](2026-10-02-pbt-runtime-smt-naming.md) — done; replace ambiguous Bridge names with Runtime/Smt/Random roles.
- [PBT runtime library command](2026-10-02-pbt-runtime-library-command.md) — done; print embedded PbtRuntime.dfy and locate generator/draft parse errors.
- [Static contract-runtime library](2026-10-02-static-contract-runtime-library.md) — done; task-independent PBT Dafny/C# runtime text moved to checked-in, ahead-of-time-checked library files.
- [PBT call-state evidence, fact reuse and profiling](2026-10-01-pbt-call-state-memo-profile.md) — done; independent native65 plus corrective15, artifact13, supported packaging/integration4, root all15 and exact replay acceptance.
- [Bounded call heaps and exact successful facts](2026-10-01-call-heap-facts-implementation.md) — done; invocation-bound old/current evidence, exact successful facts and quantifier source-edit correction independently accepted.
- [Runtime profiling sidecars](2026-10-01-runtime-profile-sidecars.md) — done; aggregate runtime and campaign costs without changing raw observations.
