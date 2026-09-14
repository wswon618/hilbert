# 중간 바인딩 검사 — 스케치가 값을 꺼내면 분리될 때 사슬이 끊긴다

flip3 r1 (2026-09-12, 240분) 실패 / flip3 r2 (2026-09-13, 600분) 성공
대상: `amc12b_2002_p4`

원본 로그: `results/archive/flip3_r1_20260912_203357/`, `results/archive/flip3_r2_20260913_150200/`

---

## 0. 한 줄 요약

같은 문제 · 같은 코드 · 하루 차이로 r1 은 실패, r2 는 성공했다. 스케치는
양쪽 다 3개였고 have 이름도 비슷했다. 차이는 **개수가 아니라 서브골을
어디서 끊었는가** 였다. r1 은 `obtain` 과 `Classical.choose` 로 증인을
꺼낸 뒤 그것을 참조했고, r2 는 존재성과 그 값을 **한 명제 안에** 가뒀다.

HILBERT 는 각 `have` 를 **독립 정리로 쪼개 따로 증명**한다. 그 순간 스케치
안에서만 유효하던 지역 바인딩이 끊어진다.

---

## 1. 원 문제

```lean
theorem amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. ↑n).den = 1) : n = 42 := by
```

> $\frac12+\frac13+\frac17+\frac1n$ 이 정수가 되는 양의 정수 $n$ 은 42 뿐임을 보여라.

수학적 경로는 세 스케치가 모두 같다.

    세 분수를 더해 (41n + 42) / (42n)
      → 분모가 1 이므로 42n ∣ 41n + 42
      → 몫 k 가 1
      → n = 42

즉 **전략의 차이가 아니다.** 같은 길을 어떻게 토막 내느냐의 차이다.

---

## 2. 성공한 스케치 — r2 #3 (have 6개)

```lean
have h_sum_eq      : (1/.2 + 1/.3 + 1/.7 + 1/.n) = ((41*n + 42) / (42*n)) := by sorry
have h_den_eq_one  : ((41*n + 42 : ℚ) / (42*n)).den = 1 := by sorry
have h_42n_ne_zero : (42*n : ℕ) ≠ 0 := by sorry
have h_div         : (42*n) ∣ (41*n + 42) := by sorry
have h_k_eq_one    : ∃ k : ℕ, 41*n + 42 = k*(42*n) ∧ k = 1 := by sorry
have h_final       : n = 42 := by sorry
exact h_final
```

`h_k_eq_one` 이 핵심이다. **존재성과 그 값을 하나의 닫힌 명제로 묶었다.**
`k` 는 명제 안에 갇혀 있고 바깥으로 새지 않는다. 모든 서브골이
자기완결적이므로 독립 정리로 쪼개도 그대로 성립한다.

`h_final : n = 42` 이 목표와 같은 문장이라 얼핏 논리적 중복으로 보이지만,
분리될 때 앞의 다섯 가설을 모두 받으므로 `h_k_eq_one` 에서 41n+42 = 42n,
즉 n = 42 가 바로 나온다. 퇴화 분해가 아니다.

---

## 3. 실패한 스케치 ① — r1 #1 (have 6개), `obtain` 으로 끊음

```lean
have h_div : (42*n) ∣ (41*n + 42) := by sorry
obtain ⟨k, hk_eq⟩ := h_div          -- ← 스케치 한가운데서 증인을 꺼낸다
have hk_one : k = 1 := by sorry
have h_n_eq : n = 42 := by sorry
exact h_n_eq
```

`obtain` 으로 꺼낸 `k` 는 이후 두 `have` 가 참조한다. 그런데 HILBERT 가
이것을 독립 정리로 추출하면 `k` 가 **전칭 인자로 승격**된다.

```lean
theorem hk_one_amc12b_2002_p4 (n k : ℕ) (h₀ : 0 < n)
    (hk_eq : (41 * n + 42) = (42 * n) * k) : k = 1 := by
  sorry

theorem h_n_eq_amc12b_2002_p4 (n k : ℕ) (hk_one : k = 1)
    (hk_eq : (41 * n + 42) = (42 * n) * k) : n = 42 := by
  sorry
```

"그 `k`" 에 대한 주장이 "**모든** `k`" 에 대한 주장이 됐다. 이 경우는
다행히 참이다 — Lean 으로 확인했다.

    example (n k : ℕ) (h₀ : 0 < n) (hk_eq : (41*n + 42) = (42*n) * k) : k = 1 := by
      nlinarith [hk_eq, h₀]
      ✅ 통과

(41n+42 = 42nk 에서 k ≥ 2 면 좌변 < 우변, k = 0 이면 좌변 ≠ 0 이므로 k = 1
이 강제된다.)

**참이지만 대가가 있다.** 하나였던 논증이 두 정리로 쪼개졌고, 둘 다
증명한 뒤 다시 이어붙여야 한다. 실패 지점이 두 배로 늘어난다.

---

## 4. 실패한 스케치 ② — r1 #3 (have 10개), `Classical.choose`

```lean
have h_exists_k : ∃ k : ℕ, 41*n + 42 = k*(42*n) := by sorry
have h_eq : 42 = n * (42 * (Classical.choose h_exists_k) - 41) := by sorry
have h_n_dvd_42 : n ∣ 42 := by sorry
have h_n_eq_42 : n = 42 := by sorry
```

존재성과 값을 **두 단계로 쪼개면서 중간에 `Classical.choose`** 를 썼다.
추출된 정리는 이렇게 된다.

```lean
theorem h_eq_amc12b_2002_p4 (n : ℕ) (h_exists_k : ∃ k : ℕ, 41 * n + 42 = k * (42 * n)) :
    42 = n * (42 * (Classical.choose h_exists_k) - 41) := by
  sorry

theorem h_n_dvd_42_amc12b_2002_p4 (n k : ℕ) (h_eq : 42 = n * (42 * k - 41)) : n ∣ 42 := by
  sorry
```

두 가지가 겹친다.

1. **불투명한 증인에 대한 산술 주장이다.** 증명하려면 `Classical.choose_spec`
   을 꺼내 명세를 복원한 뒤 계산해야 한다.
2. **사슬이 끊긴다.** `h_eq` 가 내놓는 것은 `Classical.choose h_exists_k` 에
   대한 명제인데, 다음 `h_n_dvd_42` 는 자유변수 `k` 를 받는다. 두 정리가
   같은 대상을 말하는지 연결 고리가 없다.

Lean 으로 두 형태를 나란히 시도했다.

    Classical.choose 판
      example (n : ℕ) (h : ∃ k : ℕ, 41*n + 42 = k*(42*n)) :
          42 = n * (42 * (Classical.choose h) - 41) := by
        have hs := Classical.choose_spec h
        set k := Classical.choose h
        nlinarith [hs]
      ❌ 실패 — "linarith failed to find a contradiction"

    r2 의 통합 판
      example (n : ℕ) (h₀ : 0 < n) (h_div : (42*n) ∣ (41*n + 42)) :
          ∃ k : ℕ, 41*n + 42 = k*(42*n) ∧ k = 1 := by
        obtain ⟨k, hk⟩ := h_div
        refine ⟨k, by linarith [hk], ?_⟩
        nlinarith [hk, h₀]
      ✅ 통과

**같은 수학인데 한쪽만 닫힌다.**

---

## 5. 품질 차이 정리

| | r1 #1 | r1 #3 | **r2 #3 (성공)** |
|---|---|---|---|
| have 수 | 6 | 10 | **6** |
| 중간 바인딩 | `obtain` | `Classical.choose` | **없음** |
| 서브골 자기완결성 | 부분적 | 깨짐 | **완전** |
| 존재성과 값 | 분리 (2단계) | 분리 (2단계) | **통합 (1단계)** |

r1 의 두 스케치는 "증인을 꺼낸 뒤 그것에 대해 말하는" 구조다. 사람이 손으로
증명할 때는 지극히 자연스럽다 — 지역 문맥이 유지되기 때문이다. 하지만
HILBERT 는 각 `have` 를 독립 정리로 쪼개 **따로** 증명하므로 그 문맥이
사라진다. r2 는 증인을 꺼내지 않아 그 문제를 피했다.

---

## 6. 검사 명세

### 6.1 무엇을 보는가

스케치 텍스트에서 다음을 찾는다.

- `obtain ⟨x, …⟩ := …`
- `rcases … with ⟨x, …⟩`
- `Classical.choose …` / `Classical.choose_spec …`
- `set x := …` (스케치 중간에서)
- `let x := …`

그리고 **그 뒤의 `have` 가 도입된 이름을 참조하는지** 확인한다. 참조한다면
분리 시 사슬이 끊어질 위험이 있다.

### 6.2 무엇을 하는가

경고하고 **재작성 방향을 제시한다**.

    발견: obtain ⟨k, hk⟩ := h_div  뒤의 have 가 k 를 참조합니다.
    각 have 는 독립 정리로 분리되므로 k 의 바인딩이 끊어집니다.
    존재성과 그 값을 하나의 서브골로 합치세요. 예:
        have h : ∃ k, <식 with k> ∧ <k 에 대한 주장> := by sorry

### 6.3 왜 비용이 좋은가

앞서 정리한 검사 넷 중 유일하게 **Lean 호출이 필요 없다.**

| 검사 | 비용 | 적용 범위 (실측) |
|---|---|---|
| 반증 시도 (`decide`) | 서브골당 Lean 1회 | 5건 중 2건 |
| 가설 누락 | 서명 비교 | 1건 |
| ∀ 좁힘 | 서명 비교 | 1건 |
| **중간 바인딩** | **텍스트만** | **본 사례** |

스케치 텍스트만 보고 판정되고, 수정 방향도 기계적으로 제시할 수 있다.

### 6.4 한계

- **오탐 가능성** — `obtain` 을 쓰고도 이후 `have` 가 그 이름을 안 쓰면
  문제없다. 참조 여부를 반드시 함께 봐야 한다.
- **이 사례 하나로 세운 기준이다.** r1 두 스케치 모두 이 성질을 가졌고
  r2 의 성공 스케치는 갖지 않았다는 것이 근거의 전부다. 다른 회차의
  스케치들에서 이 성질과 성패의 상관을 재야 한다. 디스크에 스케치가
  385개 이상 쌓여 있으므로 GPU 없이 할 수 있다.

---

## 7. 함께 정정할 것 — `numbertheory_fxeq4powx…` 는 스케치 갈림이 아니다

flip3 r1 을 분석하다 발견했다. 이 문제의 성공 회차는 **1단계 prover 가
직접 풀었고 스케치를 한 개도 만들지 않았다.**

    flip10    ✅  prover 3회, 스케치 0개, 15.8분
    flip3 r1  ❌  prover 4회 실패 → 분해 추락 → 스케치 3개 전부 실패, 240분
    flip3 r2  ✅  prover 3회, 스케치 0개, 18.5분

`generate_single_proof` (903행) 는 한 번만 분기한다. prover 4회
(`formal_proof_attempts: 4`) 가 다 빗나가면 `subgoal_decomp` 로 넘어가고,
`_single_subgoal_decomp_attempt` (972행) 안에는 **최상위 목표를 다시
prover 에 보내는 경로가 없다.** 이후 prover 호출 116회는 전부 서브골용이다.

즉 최상위 정리는 평생 prover 시도를 4번만 받는다. 성공한 두 회차 모두
**3번째 호출**에서 풀었으므로 시도당 성공률은 대략 1/3 이고, 그러면
4연속 실패가 다섯 번에 한 번꼴로 난다.

이 문제는 갈림 표본에서 빼야 한다. 스케치 품질이 아니라 **1단계 prover 의
4회 추첨**이 결과를 결정한다.

개입 여지가 있는 결함이기도 하다. 분해가 정체했을 때 더 깊이 파고드는
대신 **최상위 prover 로 되돌아가는** 선택지를 주면 이 문제는 호출 4회로
풀린다. 나쁜 스케치에 갇혔을 때의 탈출구다.

### 갱신된 갈림 표본

    amc12b_2002_p4   ❌✅❌❌✅   2/5  40%   ← 스케치 갈림 (본 문서의 사례)
    imo_2019_p1      ❌❌✅✅✅   3/5  60%   ← 스케치 갈림
    numbertheory_fxeq4powx…       제외 (prover 분산)
