#!/usr/bin/env python3
"""스케치가 만든 서브골이 실제로 참인지 Lean 으로 판정한다.

왜 필요한가
-----------
flip10 r1 (2026-09-11) 에서 닫히지 않은 depth-0 서브골 5건을 검증했더니
전부 거짓이었다. 원인은 네 가지였다.

  - `∑`/`∏` 본문의 결합 우선순위   `∑ k ∈ range 8, 2*k + 1` 은
      `(∑ k ∈ range 8, 2*k) + 1` 로 읽혀 57 이 된다. 스케치는 64 를 주장했다.
  - 산술 오류                      `f 997 = 997` (실제 998)
  - 가설 누락                      `0 < r` 없이 rpow 항등식 주장
  - ∀ 가설을 단일 사례로 좁힌 뒤 재일반화

현재 `verify_and_correct_proof_sketch_with_theorems` 는 컴파일 가능성만 보므로
`have h : 57 = 64 := by sorry` 가 통과한다. 거짓 서브골은 어떤 전술로도
닫히지 않으므로, 스케치 단계에서 걸러내야 한다.

자세한 분석: results/analysis/flip10_r1_거짓서브골.md

사용법
------
    python scripts/verify_subgoal_truth.py <정리문 파일> [--url http://localhost:10001/]

정리문 파일은 `theorem ... := by` 로 시작하는 블록을 빈 줄 두 개로 구분해
나열한다. 각 블록에 대해 세 가지를 시도한다.

    1) decide / norm_num 으로 반증되는가   → 거짓 확정
    2) 사소한 전술로 닫히는가              → 참이며 쉬움
    3) 둘 다 아님                          → 판정 보류 (어려운 참일 수 있음)
"""
import argparse
import asyncio
import re
import sys

sys.path.insert(0, "/data/ml-hilbert")
from src.inference.AsyncLeanVerifier import AsyncLeanVerifier  # noqa: E402

HEADER = (
    "import Mathlib\n"
    "import Aesop\n"
    "set_option maxHeartbeats 400000\n"
    "open BigOperators Real Nat Topology Rat\n\n"
)

# 반증 시도용 전술. decide 가 거짓을 증명하면 Lean 이
# "tactic 'decide' proved that the proposition is false" 를 낸다.
REFUTE_TACTICS = ["decide", "norm_num", "simp_arith"]
# 참이며 쉬운지 확인할 전술
EASY_TACTICS = ["decide", "norm_num", "simp", "omega",
                "simp [Finset.sum_range_succ, Finset.prod_range_succ]"]

FALSE_MARKERS = ("proved that the proposition", "is false")


def split_theorems(text: str):
    """빈 줄 두 개로 구분된 정리문 블록을 나눈다."""
    out = []
    for blk in re.split(r"\n\s*\n\s*\n", text):
        blk = blk.strip()
        if blk.startswith("theorem") or blk.startswith("example"):
            out.append(blk)
    return out


def body_with_tactic(thm: str, tactic: str) -> str:
    """정리문의 증명 본문을 주어진 전술 하나로 바꾼다."""
    # `:= by` 이후를 전부 버리고 전술을 넣는다
    m = re.search(r":=\s*by\b", thm)
    if m:
        return thm[:m.end()] + "\n  " + tactic
    m = re.search(r":=", thm)
    if m:
        return thm[:m.start()] + ":= by\n  " + tactic
    return thm + " := by\n  " + tactic


def name_of(thm: str) -> str:
    m = re.match(r"\s*(?:theorem|example)\s+(\S+)", thm)
    return m.group(1) if m else "(익명)"


async def judge(verifier, thm: str, timeout: int):
    """한 정리문을 판정한다. 반환: (판정, 근거 전술)"""
    # 1) 반증
    for t in REFUTE_TACTICS:
        ok, err = await verifier.verify_proof(
            HEADER + body_with_tactic(thm, t),
            timeout=timeout, return_error_message=True, is_sorry_ok=False)
        if not ok and err and all(k in err for k in FALSE_MARKERS):
            return "거짓", t
    # 2) 사소하게 참
    for t in EASY_TACTICS:
        ok, _ = await verifier.verify_proof(
            HEADER + body_with_tactic(thm, t),
            timeout=timeout, return_error_message=True, is_sorry_ok=False)
        if ok:
            return "참(쉬움)", t
    return "보류", ""


async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path", help="정리문 파일")
    ap.add_argument("--url", default="http://localhost:10001/")
    ap.add_argument("--timeout", type=int, default=180)
    a = ap.parse_args()

    thms = split_theorems(open(a.path).read())
    if not thms:
        print("정리문을 찾지 못했습니다. 블록은 빈 줄 두 개로 구분하세요.")
        return

    v = AsyncLeanVerifier(base_url=a.url)
    counts = {"거짓": 0, "참(쉬움)": 0, "보류": 0}
    print(f"  정리문 {len(thms)}건 판정\n")
    for thm in thms:
        verdict, tac = await judge(v, thm, a.timeout)
        counts[verdict] += 1
        mark = {"거짓": "❌", "참(쉬움)": "✅", "보류": "· "}[verdict]
        extra = f"  ({tac})" if tac else ""
        print(f"  {mark} {verdict:8s} {name_of(thm)[:58]}{extra}")
    print()
    print(f"  거짓 {counts['거짓']} / 참(쉬움) {counts['참(쉬움)']} / 보류 {counts['보류']}")
    if counts["거짓"]:
        print("\n  거짓 서브골이 있습니다. 이 스케치는 국소 수리로 닫히지 않으므로")
        print("  폐기하고 다시 세워야 합니다.")
    try:
        await v.close()
    except Exception:
        pass


if __name__ == "__main__":
    asyncio.run(main())
