#!/usr/bin/env python3
"""
prover 단독 성능(pass@k)을 잰다. HILBERT 파이프라인을 거치지 않는다.

  왜 필요한가
  -----------
  HILBERT 실행 통계에 나오는 "prover 증명 유효율 22%" 는 모델 성능 지표가 아니다.
  그것은 (a) 생성 1회가 컴파일될 확률이고, (b) 대상이 miniF2F 문제가 아니라
  reasoner 가 지어낸 서브골이며, (c) 표본이 이미 Phase 1 에서 실패한 문제들이다.

  논문이 보고하는 prover-only 수치(Goedel-Prover-V2-32B, miniF2F ~76%)와 비교하려면
  miniF2F 정리문 자체를 prover 에게 직접 주고 pass@k 를 재야 한다. 이 스크립트가
  그것을 한다.

  무엇을 맞췄나
  -------------
  저장소가 prover 를 부르는 방식을 그대로 따른다.
    - 프롬프트: src/prompts/formal_to_formal.py 의 NON_COT_PROMPT
    - temperature 0.6 (src/inference/AsyncProverLLM.py:51)
    - max_tokens 는 설정값(기본 16384)
  다른 점은 useful_theorems(검색 결과)를 주지 않는다는 것뿐이다. 저장소도 Phase 1
  직접 증명에서는 주지 않는다 (HILBERTWorker.py:740).

  k 개 표본은 vLLM 의 n 파라미터로 한 요청에 받는다. 프롬프트 prefill 을 공유하므로
  k 번 따로 부르는 것보다 훨씬 빠르다.

  사용법
  ------
    # 예열 겸 소규모
    python scripts/prover_only_baseline.py --num-problems 10 --k 4

    # 본 측정
    python scripts/prover_only_baseline.py --num-problems 40 --k 16 --out results/analysis/prover_only.json
"""

import argparse
import asyncio
import json
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.prompts.formal_to_formal import NON_COT_PROMPT   # noqa: E402

# ---------------------------------------------------------------------------
# 표본
# ---------------------------------------------------------------------------

def source_of(name: str) -> str:
    """문제 이름에서 출처를 뽑는다 (층화 표본용)."""
    for pre in ("amc12", "aime", "imo", "mathd_algebra", "mathd_numbertheory",
                "induction", "algebra", "numbertheory", "imosl"):
        if name.startswith(pre):
            return pre
    return "기타"


def stratified(items, n, seed=0):
    """출처별 비율을 유지하며 n개를 고른다. 같은 seed 면 같은 표본이 나온다."""
    buckets = {}
    for it in items:
        buckets.setdefault(source_of(it["name"]), []).append(it)
    for v in buckets.values():
        v.sort(key=lambda x: x["name"])
    total = len(items)
    # 최대잉여법으로 몫을 배분한다
    quota = {k: len(v) * n / total for k, v in buckets.items()}
    base = {k: int(q) for k, q in quota.items()}
    rest = n - sum(base.values())
    for k in sorted(buckets, key=lambda k: -(quota[k] - base[k]))[:rest]:
        base[k] += 1
    rng = random.Random(seed)
    out = []
    for k, cnt in base.items():
        out += rng.sample(buckets[k], min(cnt, len(buckets[k])))
    out.sort(key=lambda x: x["name"])
    return out


# ---------------------------------------------------------------------------
# 생성
# ---------------------------------------------------------------------------

# 언어 태그는 문자 클래스로 받는다. (?:lean|lean4) 처럼 교대로 쓰면 ```lean4 에서
# `lean` 만 매치되고 "4" 가 본문에 딸려온다 (저장소 string.py 에도 같은 버그가 있었다).
_FENCE = re.compile(r"```[a-zA-Z0-9_+-]*\s*\n?(.*?)\n?```", re.DOTALL)
_IMPORT = re.compile(r"^\s*(import|open|set_option)\b.*$", re.M)


def extract_proof(text: str, statement: str) -> str:
    """응답에서 증명 본문을 꺼낸다.

    prover 는 보통 정리문까지 통째로 다시 쓴다. 코드블록이 있으면 그 안을 쓰고,
    없으면 응답 전체를 쓴다. import/open 줄은 header 에서 이미 주므로 지운다.
    """
    if not text:
        return ""
    m = _FENCE.findall(text)
    body = m[-1] if m else text
    return _IMPORT.sub("", body).strip()


async def generate(session_url, model, prompt, k, max_tokens, temperature, timeout):
    """vLLM 에 한 요청으로 k개 표본을 받는다 (n 파라미터)."""
    payload = json.dumps({
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": max_tokens,
        "temperature": temperature,
        "n": k,
    }).encode()

    def _post():
        req = urllib.request.Request(
            session_url.rstrip("/") + "/chat/completions",
            data=payload,
            headers={"Content-Type": "application/json", "Authorization": "Bearer EMPTY"},
        )
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.load(r)

    d = await asyncio.to_thread(_post)
    return [c["message"]["content"] for c in d["choices"]]


# ---------------------------------------------------------------------------
# 검증
# ---------------------------------------------------------------------------

async def verify_batch(url, codes, timeout):
    """kimina-lean-server 에 여러 건을 한 번에 보낸다."""
    payload = json.dumps({
        "codes": [{"custom_id": str(i), "proof": c} for i, c in enumerate(codes)],
        "timeout": timeout,
    }).encode()

    def _post():
        req = urllib.request.Request(
            url.rstrip("/") + "/verify", data=payload,
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=timeout + 300) as r:
            return json.load(r)["results"]

    try:
        res = await asyncio.to_thread(_post)
    except Exception as e:
        return [(False, f"{type(e).__name__}: {e}")] * len(codes)

    out = [(False, "no response")] * len(codes)
    for item in res:
        i = int(item["custom_id"])
        resp = item.get("response", {}) or {}
        msgs = resp.get("messages", []) or []
        errs = [m.get("data", "") for m in msgs if m.get("severity") == "error"]
        has_sorry = bool(resp.get("sorries")) or any(
            "declaration uses 'sorry'" in m.get("data", "") for m in msgs
        )
        ok = (not errs) and (not has_sorry)
        out[i] = (ok, errs[0][:200] if errs else ("sorry 포함" if has_sorry else ""))
    return out


# ---------------------------------------------------------------------------
# 본체
# ---------------------------------------------------------------------------

async def run_problem(sem, args, item, stats):
    """문제 하나에 대해 k개 표본을 생성하고 검증한다."""
    async with sem:
        stmt = item["formal_statement"]
        header = item.get("header") or "import Mathlib\n"
        prompt = NON_COT_PROMPT.format(formal_statement=stmt)

        t0 = time.time()
        try:
            texts = await generate(args.prover_url, args.model, prompt, args.k,
                                   args.max_tokens, args.temperature, args.gen_timeout)
        except Exception as e:
            stats["gen_error"] += 1
            return {"name": item["name"], "source": source_of(item["name"]),
                    "error": f"{type(e).__name__}: {e}", "results": []}
        gen_s = time.time() - t0

        codes = [header.rstrip() + "\n\n" + extract_proof(t, stmt) + "\n" for t in texts]
        t1 = time.time()
        verdicts = await verify_batch(args.verifier_url, codes, args.verify_timeout)
        ver_s = time.time() - t1

        oks = [v[0] for v in verdicts]
        stats["done"] += 1
        first = oks.index(True) + 1 if any(oks) else None
        print(f"    [{stats['done']}/{stats['total']}] {item['name'][:42]:42s} "
              f"{sum(oks)}/{args.k} 통과" + (f"  (첫 성공 {first}번째)" if first else "  (전부 실패)")
              + f"   생성 {gen_s:.0f}s 검증 {ver_s:.0f}s", flush=True)
        return {
            "name": item["name"], "source": source_of(item["name"]),
            "num_pass": sum(oks), "k": args.k,
            "first_success_index": first,
            "gen_seconds": round(gen_s, 1), "verify_seconds": round(ver_s, 1),
            "errors": [v[1] for v in verdicts if not v[0]][:3],
        }


def pass_at_k(records, k):
    """표본 K개 중 앞 k개만 썼다고 볼 때의 pass@k.

    표본은 순서가 무의미하므로, 조합 확률로 기대값을 낸다:
        pass@k = 1 - C(K-c, k) / C(K, k)      (c = 통과한 표본 수)
    이것이 Codex 논문의 불편추정량이다. 실제로 앞 k개를 잘라 세는 것보다
    분산이 작다.
    """
    from math import comb
    tot = 0.0
    for r in records:
        if not r.get("k"):
            continue
        K, c = r["k"], r.get("num_pass", 0)
        if K - c < k:
            tot += 1.0
        else:
            tot += 1.0 - comb(K - c, k) / comb(K, k)
    return tot / len(records) if records else 0.0


async def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", default="data/minif2f/minif2f_lean4_26.jsonl")
    ap.add_argument("--split", default="test")
    ap.add_argument("--num-problems", type=int, default=40)
    ap.add_argument("--k", type=int, default=16, help="문제당 표본 수")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--prover-url", default="http://localhost:11212/v1")
    ap.add_argument("--model", default="Goedel-LM/Goedel-Prover-V2-32B")
    ap.add_argument("--verifier-url", default="http://localhost:10001/")
    ap.add_argument("--max-tokens", type=int, default=16384)
    ap.add_argument("--temperature", type=float, default=0.6)
    ap.add_argument("--concurrency", type=int, default=4, help="동시에 처리할 문제 수")
    ap.add_argument("--gen-timeout", type=int, default=3600)
    ap.add_argument("--verify-timeout", type=int, default=180)
    ap.add_argument("--out", help="결과 JSON 저장 경로")
    args = ap.parse_args()

    items = []
    with open(args.dataset, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            if args.split != "all" and d.get("split") != args.split:
                continue
            items.append(d)
    sample = stratified(items, min(args.num_problems, len(items)), args.seed)

    print(f"  데이터셋 {args.dataset}  split={args.split}  전체 {len(items)}문제")
    print(f"  표본 {len(sample)}문제 (층화, seed={args.seed}), 문제당 k={args.k}")
    print(f"  모델 {args.model}  temperature={args.temperature}  max_tokens={args.max_tokens}")
    print(f"  동시 {args.concurrency}문제 → 한 번에 최대 {args.concurrency * args.k} 표본 생성\n")

    stats = {"done": 0, "total": len(sample), "gen_error": 0}
    sem = asyncio.Semaphore(args.concurrency)
    t0 = time.time()
    # 244문제를 3시간 돌리는 동안 중간에 끊길 수 있다. 하나 끝날 때마다 저장한다.
    records = []
    partial = (args.out + ".partial") if args.out else None
    tasks = [asyncio.ensure_future(run_problem(sem, args, it, stats)) for it in sample]
    for fut in asyncio.as_completed(tasks):
        records.append(await fut)
        if partial:
            os.makedirs(os.path.dirname(partial), exist_ok=True)
            json.dump({"config": vars(args), "records": records},
                      open(partial, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    elapsed = time.time() - t0

    valid = [r for r in records if r.get("k")]
    print(f"\n  === 결과 ===  ({elapsed/60:.0f}분, 생성 오류 {stats['gen_error']}건)")
    print(f"  {'k':>4s} {'pass@k':>9s}")
    ks = [x for x in (1, 2, 4, 8, 16, 32, 64) if x <= args.k]
    curve = {}
    for k in ks:
        p = pass_at_k(valid, k)
        curve[k] = p
        print(f"  {k:4d} {p*100:8.1f}%")

    print("\n  === 출처별 pass@%d ===" % args.k)
    bysrc = {}
    for r in valid:
        bysrc.setdefault(r["source"], []).append(r)
    for s, rs in sorted(bysrc.items()):
        solved = sum(1 for r in rs if r["num_pass"] > 0)
        print(f"    {s:22s} {solved}/{len(rs)}")

    never = [r["name"] for r in valid if r["num_pass"] == 0]
    print(f"\n  한 번도 못 푼 문제 {len(never)}개")
    for n in never[:15]:
        print(f"    {n}")
    if len(never) > 15:
        print(f"    ... 외 {len(never)-15}개")

    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump({
            "config": vars(args), "elapsed_seconds": round(elapsed, 1),
            "pass_at_k": curve, "records": records,
        }, open(args.out, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
        print(f"\n  저장: {args.out}")


if __name__ == "__main__":
    asyncio.run(main())
