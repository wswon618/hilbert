#!/usr/bin/env python3
"""
조각이 끝나기 전에 중단된 실행에서, 지금까지 처리된 문제만 모아 결과 JSON 을 만든다.

왜 필요한가
-----------
src/run.py 는 조각 안의 문제를 "전부" 끝낸 뒤에야 결과 JSON 을 저장한다.
그런데 어려운 문제 하나가 재귀 탐색에 갇히면(실측: 한 문제가 11시간 이상) 나머지
19문제를 다 풀어놓고도 집계 파일이 안 나온다.

다행히 HILBERT 는 문제 하나가 끝날 때마다 아래 두 가지를 즉시 저장한다.
  results/proofs/<name>.lean                     성공한 증명
  results/proofs/proof_stats/<name>_stats.json   문제별 통계 (성공/실패 포함)

이 스크립트는 그것들을 모아 src/run.py 와 같은 형식의 JSON 을 만든다.

--since 가 왜 필요한가
----------------------
results/proofs/ 는 실행 간에 누적된다. 게다가 AsyncHILBERT 는 .lean 이 이미 있는
문제를 "Skipping problem ... as proof already exists" 로 건너뛴다. 실제로 이번
실행에서 aime_1989_p8 이 9일 전 결과 때문에 평가되지 않았다.
따라서 파일 수정 시각으로 이번 실행분만 걸러야 집계가 정확하다.

사용 예
-------
  python scripts/aggregate_results.py \
      --chunk data/minif2f/chunks/strat_000.jsonl \
      --since "2026-08-19 08:20" \
      --out results/async_hilbert/partial_strat_000.json
"""

import argparse
import json
import os
import re
import time

SOURCE_PATTERNS = [
    "mathd_algebra", "mathd_numbertheory",
    "amc12a", "amc12b", "amc12",
    "aime", "imo", "induction",
    "algebra", "numbertheory",
]


def source_of(name):
    for pat in SOURCE_PATTERNS:
        if name.startswith(pat):
            return pat
    return "other"


def main():
    p = argparse.ArgumentParser(description="중단된 실행의 부분 결과 집계")
    p.add_argument("--chunk", required=True, help="조각 JSONL 경로")
    p.add_argument("--since", required=True,
                   help='이 시각 이후 파일만 집계. "YYYY-MM-DD HH:MM"')
    p.add_argument("--proofs-dir", default="results/proofs")
    p.add_argument("--out", default=None, help="결과 JSON 저장 경로")
    args = p.parse_args()

    cut = time.mktime(time.strptime(args.since, "%Y-%m-%d %H:%M"))
    stats_dir = os.path.join(args.proofs_dir, "proof_stats")

    entries = [json.loads(l) for l in open(args.chunk, encoding="utf-8") if l.strip()]

    results, proofs, formal_statements, details = {}, {}, {}, []
    skipped, pending = [], []

    for e in entries:
        name = e["name"]
        sp = os.path.join(stats_dir, f"{name}_stats.json")
        lp = os.path.join(args.proofs_dir, f"{name}.lean")

        stats_new = os.path.exists(sp) and os.path.getmtime(sp) > cut
        lean_new = os.path.exists(lp) and os.path.getmtime(lp) > cut
        lean_old = os.path.exists(lp) and os.path.getmtime(lp) <= cut

        if not stats_new:
            # 이번 실행에서 통계가 안 나온 문제.
            #   .lean 이 예전 것이면 건너뛴 것이고, 아무것도 없으면 아직 진행 중이다.
            (skipped if lean_old else pending).append(name)
            continue

        success = lean_new
        results[name] = success
        formal_statements[name] = e.get("formal_statement", "")
        if success:
            proofs[name] = open(lp, encoding="utf-8").read()

        d = {}
        try:
            d = json.load(open(sp, encoding="utf-8"))
        except Exception:
            pass
        calls = d.get("total_llm_calls") or {}
        details.append({
            "name": name,
            "source": source_of(name),
            "success": success,
            "duration_min": round(d.get("duration", 0) / 60, 1),
            "max_depth_reached": d.get("max_depth_reached"),
            "total_attempts": d.get("total_attempts"),
            "prover_calls": calls.get("prover_llm"),
            "reasoner_calls": calls.get("informal_llm"),
            "verifications": len(d.get("verification_operations") or []),
        })

    n = len(results)
    ok = sum(1 for v in results.values() if v)

    # 출처별 집계 — 표본의 어느 계열에서 실패했는지 보려는 것
    by_source = {}
    for d in details:
        b = by_source.setdefault(d["source"], {"total": 0, "solved": 0})
        b["total"] += 1
        b["solved"] += 1 if d["success"] else 0

    out = {
        # src/run.py 와 같은 필드 (비교·병합이 쉽도록 형식을 맞춘다)
        "total_problems": n,
        "completed_problems": n,
        "successful_problems": ok,
        "results": results,
        "failure_cases": [k for k, v in results.items() if not v],
        "pass_rate": (ok / n) if n else 0.0,
        "proofs": proofs,
        "formal_statements": formal_statements,
        # 이 스크립트가 추가로 넣는 정보
        "_partial": True,
        "_note": "조각 미완료 상태에서 문제별 파일을 모아 집계한 부분 결과",
        "_chunk": args.chunk,
        "_since": args.since,
        "_chunk_size": len(entries),
        "_skipped_old_proof": skipped,   # 이전 실행 .lean 때문에 건너뛴 문제
        "_pending": pending,             # 아직 처리 중인 문제
        "_by_source": by_source,
        "_details": sorted(details, key=lambda d: -(d["duration_min"] or 0)),
    }

    print(f"조각 {len(entries)}문제 중")
    print(f"  이번 실행 평가 : {n}개")
    print(f"  성공           : {ok}개")
    print(f"  pass rate      : {out['pass_rate']*100:.1f}%")
    if skipped:
        print(f"  건너뜀(옛 증명): {len(skipped)}개 — {', '.join(skipped)}")
    if pending:
        print(f"  진행 중        : {len(pending)}개 — {', '.join(pending)}")
    print()
    print(f"  {'출처':22s} {'표본':>5s} {'성공':>5s} {'비율':>7s}")
    for s in sorted(by_source):
        b = by_source[s]
        print(f"  {s:22s} {b['total']:5d} {b['solved']:5d} {b['solved']/b['total']*100:6.0f}%")

    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(out, f, indent=2, ensure_ascii=False)
        print(f"\n저장: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
