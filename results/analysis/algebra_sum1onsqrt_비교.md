# algebra_sum1onsqrt2to1onsqrt10000lt198 — 세 실행 비교

같은 조건에서 세 번 돌려 **한 번 성공하고 두 번 실패한** 문제다.
현재 조건(Lean v4.16 + 코드 수정 전부 적용)에서 결과가 갈리는 유일한 사례이므로,
스케치 품질 연구의 핵심 표본이다.

```
정리   theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
           (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198

접근   1/√x 가 단조 감소 → 합을 적분으로 상계 → 적분값 계산 → 결론
       ∫₁^10000 1/√x = 2√10000 - 2√1 = 200 - 2 = 198
```

---

## 1. 실행 이력

| 시각               | mathlib | 결과 | 소요   | 호출   | prover | reasoner |
|------------------|---------|----|------|------|--------|----------|
| 2026-08-21T10:03 | v4.26   | 실패 | 35분  | 84   | 4      | 80       |
| 2026-08-31T10:31 | v4.26   | 실패 | 33분  | 84   | 4      | 80       |
| 2026-09-02T14:48 | v4.26   | 실패 | 423분 | 1743 | 241    | 1502     |
| 2026-09-03T22:01 | v4.16   | 실패 | 300분 | 1854 | 352    | 1502     |
| 2026-09-04T14:39 | v4.16   | 실패 | 547분 | 1759 | 257    | 1502     |
| 2026-09-05T07:43 | v4.16   | 실패 | 379분 | 1702 | 200    | 1502     |
| 2026-09-05T16:14 | v4.16   | 성공 | 509분 | 1692 | 319    | 1373     |

```
앞의 두 실행(8월)은 정리문의 `∑ k in` 이 v4.26 에서 파싱되지 않아
서브골을 하나도 만들지 못하고 35분·33분에 죽었다.

v4.16 로 내린 뒤 네 번 돌렸고 마지막 한 번만 성공했다.
```

**실패는 전부 reasoner 한도 소진이다.**

```
실패 4회   reasoner 1502 회  ← 한도 1500 초과
성공 1회   reasoner 1373 회  ← 한도 안에서 끝남
```

시간 초과가 아니다. 600분 제한에는 아무도 걸리지 않았다.

## 2. 최상위 스케치 — 여기서 갈렸다

세 실행의 최상위 스케치를 나란히 놓는다. 수학적 전략은 셋 다 같다.

### r1 (실패) — `have` 6개

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function `x ↦ 1 / Real.sqrt x` is antitone on `[1,10000]`.
  have h_antitone : AntitoneOn (fun x : ℝ => (1 / Real.sqrt x)) (Set.Icc (1 : ℝ) (10000 : ℝ)) := by sorry
  -- 2️⃣  Compute the integral of `1 / sqrt x` from `1` to `10000`.
  have h_integral_eq :
      ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) =
        (2 * Real.sqrt (10000 : ℝ) - 2 * Real.sqrt (1 : ℝ)) := by sorry
  -- 3️⃣  Simplify the value of the integral to `198`.
  have h_integral_val : (∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x)) = (198 : ℝ) := by sorry
  -- 4️⃣  Relate the finite sum to the integral using the monotonicity of the integrand.
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) ≤
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 5️⃣  Strengthen the inequality to a strict one (the function is strictly decreasing).
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) <
        ∫ x in (1 : ℝ)..(10000 : ℝ), (1 / Real.sqrt x) := by sorry
  -- 6️⃣  Conclude the desired bound `< 198` by combining the strict inequality with the integral value.
  have h_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 / Real.sqrt k)) < (198 : ℝ) := by sorry
  exact h_lt_198
```

### r2 (실패) — `have` 4개

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1. The function x ↦ 1 / √x is antitone on [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2. Bounding the sum by the integral using `sum_Ico_le_integral_of_le`.
  have h_sum_le_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) ≤
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 3. Evaluate the integral explicitly: ∫₁^{10000} 1/√x = 2·(√10000 - √1) = 198.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = 198 := by sorry
  -- 4. The inequality is strict because the function is strictly decreasing.
  have h_strict :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 5. Conclude the desired inequality.
  have : (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < 198 := by sorry
  exact this
```

### r3 (성공) — `have` 4개

```lean
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  -- 1️⃣  The function x ↦ 1/√x is antitone on the interval [1,10000].
  have h_antitone :
      AntitoneOn (fun x : ℝ => (1 : ℝ) / Real.sqrt x) (Set.Icc (1 : ℝ) 10000) := by sorry
  -- 2️⃣  Compute the integral of 1/√x from 1 to 10000.
  have h_integral_eq :
      (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) = (198 : ℝ) := by sorry
  -- 3️⃣  Show that the finite sum is strictly smaller than this integral.
  have h_sum_lt_integral :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) <
        ∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x := by sorry
  -- 4️⃣  Conclude the desired inequality by rewriting the integral.
  have h_sum_lt_198 :
      (∑ k in Finset.Icc (2 : ℕ) 10000, (1 : ℝ) / Real.sqrt k) < (198 : ℝ) := by sorry
  exact h_sum_lt_198
```

### 차이

```
r3 (성공)  4단계, 군더더기 없음
   h_antitone → h_integral_eq(=198) → h_sum_lt_integral(<) → h_sum_lt_198

r2 (실패)  5단계, 중복 하나
   h_sum_le_integral (∑ ≤ ∫)  와  h_strict (∑ < ∫)
   → 강한 쪽이 약한 쪽을 함의하므로 약한 쪽은 논리적으로 불필요

r1 (실패)  6단계, 중복 둘
   h_integral_eq (∫ = 2√10000 - 2√1)  와  h_integral_val (∫ = 198)
      → 같은 적분을 두 단계로 쪼갬
   h_sum_le_integral (≤)  와  h_strict (<)
      → 같은 비교를 두 버전으로
```

**r3 만 처음부터 엄격 부등식(`<`)으로 갔다.** 목표가 `< 198` 이므로 결국 엄격성이
필요한데, r1·r2 는 `≤` 로 간 뒤 엄격성을 별도 서브골(`h_strict`)로 붙이려 했다.

## 3. 중복이 재귀 부담을 만든다

|    | 결과 | 중복 서브골 | 깊이1 재귀 | 전체 스케치 | 서브골 | 파싱 실패 |
|----|----|--------|--------|--------|-----|-------|
| r3 | 성공 | 0      | 2      | 28     | 74  | 3     |
| r2 | 실패 | 1      | 3      | 19     | 66  | 4     |
| r1 | 실패 | 2      | 4      | 24     | 65  | 14    |

### 재귀 분해된 서브골

```
r3 (성공)  2종: h_integral_eq, h_sum_lt_integral
r2 (실패)  3종: h_integral_eq, h_strict, h_sum_le_integral
r1 (실패)  4종: h_integral_eq, h_integral_val, h_strict, h_sum_le_integral

r3 에는 h_strict 가 없다. 엄격성을 별도 서브골로 떼지 않았으므로
그것을 재귀 분해할 일도 없었다.
```

### 깊이 분포

```
r1 (실패)  깊이0  1개  깊이1 11개  깊이2  6개  깊이3  1개  깊이4  5개
r2 (실패)  깊이0  1개  깊이1  4개  깊이2  3개  깊이3  5개  깊이4  6개
r3 (성공)  깊이0  1개  깊이1  7개  깊이2  9개  깊이3  4개  깊이4  7개
```

세 실행 모두 깊이 4까지 내려갔다. **깊이가 부족해서 실패한 것이 아니다.**

## 4. 인과 사슬

```
최상위 스케치에서 ≤ 로 갈까 < 로 갈까
        ↓
h_strict 라는 별도 서브골이 생기느냐 마느냐
        ↓
그것을 재귀 분해하며 서브골이 불어남
        ↓
응답이 길고 복잡해져 형식 오류 증가
        ↓
reasoner 예산 1500 소진 → 실패
```

**중간 지표만 보면 원인을 놓친다.** 예산 소진이나 형식 오류 횟수가 성패를 가른 것처럼
보이지만 그것은 결과다. 원인은 최상위 스케치의 한 가지 선택이다.

## 5. 잎사귀는 다 닫히는데 위로 올라가지 못한다

| | 결과 | 제출된 서브골 | 결판남 | 성공 | 실패 | 미완 | 최상위 상태 |
|--|------|------------|-------|-----|-----|-----|-----------|
| r1 | 실패 | 66 | 65 | 65 | 0 | 1 | 🔄 진행 중 |
| r2 | 실패 | 66 | 66 | 66 | 0 | 0 | 🔄 진행 중 |
| r3 | 성공 | 74 | 74 | 72 | 2 | 0 | ✅ 완료 |


**실패한 r1·r2 는 결판난 서브골을 하나도 실패하지 않았다.** 성공한 r3 이 오히려 2개를 놓쳤다.
언뜻 모순처럼 보이는데, `Job finished` 기록의 범위를 알면 풀린다.

### 재귀로 빠진 부모는 "실패"로 기록되지 않는다

```
h_strict           ← 못 닫아서 재귀 분해 (Job finished 기록 없음)
  ├─ h_a   ✅
  ├─ h_b   ✅
  └─ h_c   ← 또 못 닫아서 재귀 분해
       ├─ h_c1 ✅
       └─ h_c2 ← 또...
```

`_verify_and_correct_subgoal`(1264행)은 병렬 4회가 전부 실패하면 `Job finished (False)` 를
내는 대신 **`subgoal_decomp(depth+1)` 로 빠진다.** 그러니 그 노드는 실패 집계에 안 잡힌다.

닫힌 66개는 전부 잎사귀다. 그것들로 부모를 조립하지 못하면 부모가 다시 쪼개지고,
새 잎사귀가 생긴다. **아래에서는 계속 이기는데 위로 올라가지 못하는 상태**다.

로그의 마지막 진행 트리가 그 상태를 보여준다.

```
r1  🔄  최상위 정리가 여전히 "진행 중" 으로 끝남
r2  🔄  같음
r3  ✅  완료
```

### 그래서 실패의 성격이 이렇다

```
"서브골을 못 풀어서" 가 아니다 — 잎사귀는 100% 닫았다
"조립이 안 돼서 계속 쪼개다가 예산이 떨어져서" 다
```

## 6. 실행마다 스케치가 거의 겹치지 않는다

```
서브골 집합의 자카드 유사도
  r1 ∩ r2   공통  3개 / 합집합 19개   0.16
  r1 ∩ r3   공통  1개 / 합집합 21개   0.05
  r2 ∩ r3   공통  1개 / 합집합 23개   0.04
```

**5% 도 겹치지 않는다.** 같은 문제, 같은 조건, 같은 코드인데 재귀 트리가 완전히
다르게 자란다. seed 가 없고 temperature 0.6 이기 때문이다.

표면 지표로는 이 차이가 안 잡힌다.

```
깊이별 have 중앙값
  r1 (실패)   6, 4, 4, 3, 4
  r2 (실패)   4, 5, 3, 4, 4
  r3 (성공)   4, 5, 3, 4, 4      ← r2 와 완전히 동일
```

## 7. 성공한 증명의 마지막 조각

성공은 깊이 4 에서 났다. 이름이 재귀 경로를 그대로 담고 있다.

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_algebra_sum1onsqrt2to1onsqrt10000lt198
    (h_int_big_strict :
        (∫ x in (1 : ℝ)..10000, (1 : ℝ) / Real.sqrt x) > (1 : ℝ) / Real.sqrt (2)) :
    (∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x) ≠ (1 : ℝ) / Real.sqrt (2) := by
  -- continuity of the antiderivative on the interval
  have hF_cont :
      ContinuousOn (fun x : ℝ => (2 : ℝ) * Real.sqrt x) (Icc (1 : ℝ) 2) := by sorry
  -- derivative of the antiderivative on the open interval
  have hF_deriv :
      ∀ x ∈ Ioo (1 : ℝ) 2,
        HasDerivAt (fun x => (2 : ℝ) * Real.sqrt x) (1 / Real.sqrt x) x := by sorry
  -- integral equals the difference of the antiderivative at the bounds
  have h_int_eq :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x =
        (2 : ℝ) * Real.sqrt 2 - (2 : ℝ) * Real.sqrt 1 := by sorry
  -- simplify the right‑hand side using `sqrt 1 = 1`
  have h_int_simpl :
      ∫ x in (1 : ℝ)..2, (1 : ℝ) / Real.sqrt x = (2 : ℝ) * Real.sqrt 2 - 2 := by sorry
  -- the evaluated integral is not equal to `1 / sqrt 2`
  have h_not_eq :
      (2 : ℝ) * Real.sqrt 2 - 2 ≠ (1 : ℝ) / Real.sqrt 2 := by sorry
  -- conclude by contradiction
  intro h_eq_int
  have : (2 : ℝ) * Real.sqrt 2 - 2 = (1 : ℝ) / Real.sqrt 2 := by sorry
  exact h_not_eq this
```

```
h_ne ← h_int_12_strict ← h_int_gt_f2 ← h_sum_lt_integral ← (최상위)
```

각 조각이 독립적이고 구체적이다. `h_sqrt_lt : √2 < 3/2` 같은 것은 `norm_num` 으로
바로 닫힌다. 최종 증명 파일은 1,582줄이다.

## 8. 자원 배분

| 시각          | 결과 | 형식 재요청 | 서브골 오류수정 | 검색  | shallow_solve | generate_proof |
|-------------|----|--------|----------|-----|---------------|----------------|
| 09-03T22:01 | 실패 | 389    | 348      | 207 | 98            | 352            |
| 09-04T14:39 | 실패 | 332    | 351      | 276 | 103           | 257            |
| 09-05T07:43 | 실패 | 403    | 386      | 236 | 104           | 200            |
| 09-05T16:14 | 성공 | 278    | 332      | 231 | 100           | 319            |

```
성공 회차는 형식 재요청이 가장 적고(278), prover 를 가장 많이 썼다(319).
실패 회차는 reasoner 로 씨름하다 예산을 소진했다.

다만 이것도 결과다 — 재귀가 깊고 넓어질수록 응답이 길어지고 형식이 어긋난다.
```

## 9. 이 사례에서 나오는 신호 후보

```
논리적 중복 검사 — 구문만으로 상당 부분 가능하다

  같은 좌변을 가진 서브골 쌍을 찾는다
     h_sum_le_integral 과 h_strict     좌변 동일, 부등호만 다름 (≤ vs <)
     h_integral_eq 과 h_integral_val   좌변 동일, 우변 형태만 다름

  한쪽이 다른 쪽을 함의하면 약한 쪽은 불필요
     ∑ < ∫  ⟹  ∑ ≤ ∫

  목표의 부등호 방향이 주 경로에 반영돼 있는가
     목표가 < 인데 주 경로가 ≤ 면 엄격성 보조정리가 따로 필요해진다
```

이것은 크기·가정 개수·재귀 깊이·전술 난이도 같은 표면 지표와 성격이 다르다.
**조각들이 이루는 논증 구조**를 본다.

## 10. 예산 부족이 아니라 정체였다

"예산을 늘렸으면 r1·r2 도 풀렸을까" 를 확인하려 했다. **재실행은 답이 되지 못한다** —
새로운 추첨이라 좋은 스케치가 나오면 1,500 안에 풀리고, 나쁜 스케치가 나오면 2,500 도
모자랄 수 있다. r1·r2 의 상태를 이어서 돌릴 수단이 없다(체크포인트도 seed 도 없다).

대신 로그에서 **서브골 생성과 완료의 추이**를 봤다. 비용 0 이고 실제 궤적을 본다.

### 서브골 활동 추이 (시간을 5구간으로 나눔)

```
r1 (실패, 514분)          r2 (실패, 359분)          r3 (성공, 496분)
구간   신규 완료 미해결      구간   신규 완료 미해결      구간   신규 완료 미해결
 0~102  26   10   16        0~ 71  24   18    6        0~ 99  15   14    1
102~205   8   22    2       71~143   5    9    2       99~198  18   13    6
205~308   9    8    3      143~215  25   25    2      198~297  10   13    3
308~411  32   23   12      215~287  11   12    1      297~396  57   56    4   ← 폭발
411~513  22   31    3      287~358  13   12    2      396~495  23   23    4
```

**셋 다 발산하지 않았다.** 끝날 때 미해결 노드가 2~4개뿐이고, 생성과 완료가 균형을 이룬다.

```
발산 중이었다면   "예산을 늘려도 소용없다" 고 말할 수 있다   → 아니다
수렴 중이었다면   "조금만 더 있으면 됐다" 고 말할 수 있다    → 이것도 아니다

실제로는 정체다. 미해결이 줄지도 늘지도 않는 평형이다.
```

미해결이 적은데 안 끝났다는 것은, **남은 소수의 노드가 계속 안 닫혀 반복 시도되고 있었다**는
뜻이다. 재귀 분해로 새 서브골이 생기고 그것들은 닫히지만, 부모는 여전히 안 닫힌다.
생성과 완료가 균형을 이루면서 진전이 없다.

**예산을 늘리면 그 평형이 더 오래 지속될 뿐일 가능성이 높다.**

## 11. r3 의 돌파구 — 구간 분할

r3 만 297~396분 구간에서 폭발적 진전이 있었다(신규 57 / 완료 56). 무엇이 달라졌는지 본다.

### 폭발 직전 (198~297분) — 막혀 있던 상태

```
h_strict_h_sum_lt_integral        5회
h_le_h_sum_lt_integral            4회
h_pos_h_sum_lt_integral           4회
h_lt_integral_h_sum_lt_integral   3회
h_le2_h_sum_lt_integral           3회
```

전부 `h_sum_lt_integral`(합 < 적분)의 자식이다. `strict`, `le`, `pos`, `le2` 같은 이름으로
**같은 자리를 계속 다르게 쪼개고 있었다.** 10장에서 본 정체 상태다.

### 폭발 구간 (297~396분) — 세 축으로 갈라짐

```
깊이 3   h_sum_strict       10건
         h_int_big_strict   10건
         h_int_12_strict    10건

그 아래   h_sqrt2_pos, h_one_div_sqrt2_pos, h_pointwise,
         h_integral_le, h_const_integral, h_lower_bound ...
```

이름이 전략의 변화를 보여준다.

```
이전   h_sum_lt_integral 을 통째로 증명하려 함

이후   h_sum_strict       합 자체의 엄격성
       h_int_big_strict   전체 적분 ∫₁^10000 이 1/√2 보다 큼
       h_int_12_strict    부분 적분 ∫₁² 이 1/√2 와 다름
```

**적분 구간을 [1,2] 와 [2,10000] 로 쪼갰다.** 그리고 최종 조각이 정확히 그것이다.

```lean
theorem h_ne_h_int_12_strict_h_int_gt_f2_h_sum_lt_integral_...
    (h_int_big_strict : ∫₁^10000 1/√x > 1/√2) :
    ∫₁² 1/√x ≠ 1/√2 := by
  have hF_deriv  : ∀ x ∈ Icc 1 2, HasDerivAt (fun y => 2√y) (1/√x) x := by sorry
  have h_int_eq  : ∫₁² 1/√x = 2√2 - 2 := by sorry
  have h_sqrt_lt : √2 < 3/2 := by sorry
  have h_lt      : 1/√2 < 2√2 - 2 := by sorry
  exact ne_of_gt h_lt
```

### 왜 이것이 돌파구인가

엄격 부등식 `∑ < ∫` 를 보이려면 **어딘가에서 등호가 깨진다**는 것을 보여야 한다.
이전 시도들은 그것을 전 구간에 대해 일반적으로 보이려 했다.

r3 는 **첫 구간 하나만 잡았다.** `[1,2]` 구간의 적분값 `2√2 - 2 ≈ 0.828` 이
`1/√2 ≈ 0.707` 보다 크다는 것을 명시적으로 계산하면 거기서 엄격성이 나온다.
나머지 구간은 `≤` 로 충분하다.

```
일반적 접근   모든 구간에서 엄격성을 보이려 함   →  어려움
r3 의 접근    한 구간만 엄격, 나머지는 ≤        →  쉬움
```

**이것도 스케치 선택이다.** r1·r2 는 이 분할에 도달하지 못했다. 2장에서 본 중복 서브골
문제와 같은 층위에서, **분해의 착상**이 성패를 갈랐다.

## 12. 아직 확인하지 못한 것

```
중복 검사가 다른 문제에서도 신호가 되는가
   지금 근거는 이 문제 3회 비교 하나뿐이다.

r1 은 r2 와 같은 선택(≤)을 했는데 깊이1 재귀가 4종 대 3종으로 달랐다
   중복 외에 다른 요인이 있다.

"구간 분할" 같은 착상을 사전에 유도할 수 있는가
   r3 는 297분이 지나서야 도달했다. 처음부터 그 방향으로 가게 할 수 있다면
   3~4시간을 아낀다. 다만 이것은 스케치 평가가 아니라 스케치 생성의 문제다.
```

## 자료 위치

```
r1  logs/variance_r1_20260904_044253.log
r2  logs/variance_r2_20260905_012324.log
r3  logs/variance_r3_20260905_074359.log

results/archive/variance_r{1,2,3}_*/proofs/proof_stats/
성공 증명  results/archive/variance_r3_20260905_074359/proofs/
           algebra_sum1onsqrt2to1onsqrt10000lt198.lean  (1,582줄)

집계  python scripts/analyze_variance.py
```
