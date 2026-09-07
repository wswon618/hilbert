#!/usr/bin/env python3
"""
스케치 분산 측정 결과를 집계한다.

  무엇을 재는가
  -------------
  같은 문제를 여러 번 돌렸을 때 결과가 갈리는지, 그리고 그 갈림이 스케치와
  어떤 관계인지 본다. HILBERT 는 스케치 생성을 독립시행으로 다루므로
  (프롬프트에 과거 시도가 없고, 재시도 8회가 같은 인자, seed 없음)
  같은 문제가 실행마다 다른 결과를 낸다.

  집계하는 것
  -----------
    성공률          관측 n회 중 몇 번 성공했나 (신뢰구간 포함)
    스케치 횟수     성공한 실행과 실패한 실행에서 각각 몇 개를 만들었나
    첫 스케치 크기  have 개수
    재방문율        같은 have 조합을 다시 만든 비율
    소요·호출       분산의 크기

  사용법
  ------
    python scripts/analyze_variance.py
    python scripts/analyze_variance.py --tag variance --include-old
"""

import argparse
import collections
import glob
import json
import math
import os
import re
import statistics

# 로그에서 스케치를 뽑는 데 쓰는 패턴.
#   스케치는 "REPLACING HAVE STATEMENTS WITH SORRY" 라벨 다음의 **** 구간에 찍힌다.
STAR = re.compile(r'^\[.*?\]\[.*?\]\[INFO\] - \*{20,}$')
LINE = re.compile(r'^\[(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d),\d+\]\[([^\]]+)\]\[(\w+)\] - (.*)$')
HAVE = re.compile(r'^\s*have\s+([^\s:(]+)', re.M)
THM = re.compile(r'^\s*theorem\s+(\S+)', re.M)


def wilson(k, n, z=1.96):
    """이항비율의 Wilson 신뢰구간. n이 작을 때 정규근사보다 낫다."""
    if n == 0:
        return (0.0, 1.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def extract_sketches(path):
    """로그에서 (정리 이름 → 스케치 목록) 을 뽑는다."""
    out = collections.defaultdict(list)
    if not os.path.exists(path):
        return out
    lines = open(path, encoding='utf-8', errors='replace').read().splitlines()
    star = [i for i, l in enumerate(lines) if STAR.match(l)]
    for a, b in zip(star, star[1:]):
        if b - a < 2:
            continue
        lab = ''
        for k in range(a - 1, max(0, a - 4), -1):
            m = LINE.match(lines[k])
            if m and m.group(4).strip():
                lab = m.group(4).strip()
                break
        if lab != 'REPLACING HAVE STATEMENTS WITH SORRY':
            continue
        body = "\n".join(
            (LINE.match(lines[k]).group(4) if LINE.match(lines[k]) else lines[k])
            for k in range(a + 1, b)
        ).strip()
        tm = THM.search(body)
        out[tm.group(1) if tm else "?"].append({
            "haves": HAVE.findall(body),
            "sig": re.sub(r'\s+', '', body),
        })
    return out


def collect(tag, include_old):
    """보관된 회차 디렉터리에서 (문제 → 관측 목록) 을 모은다."""
    obs = collections.defaultdict(list)
    dirs = sorted(glob.glob(f'results/archive/{tag}_r*_*/'))
    if include_old:
        dirs += sorted(glob.glob('results/archive/*/'))
    seen_dirs = set()
    for d in dirs:
        if d in seen_dirs:
            continue
        seen_dirs.add(d)
        stats = glob.glob(os.path.join(d, 'proofs/proof_stats/*.json'))
        if not stats:
            continue
        logs = glob.glob(os.path.join(d, '*.log'))
        sk = extract_sketches(logs[0]) if logs else {}
        for f in stats:
            if 'proof_tree' in f:
                continue
            try:
                s = json.load(open(f))
            except Exception:
                continue
            su = s.get('summary', {})
            if not su:
                continue
            n = os.path.basename(f).replace('_stats.json', '')
            ok = os.path.exists(os.path.join(d, 'proofs', f'{n}.lean'))
            series = sk.get(n, [])
            sigs = [x['sig'] for x in series]
            combos = [tuple(x['haves']) for x in series]
            c = collections.Counter(combos)
            obs[n].append({
                "dir": os.path.basename(d.rstrip('/')),
                "when": s.get('generated_at', '')[:16],
                "ok": ok,
                "dur": su.get('total_duration_seconds', 0) / 60,
                "calls": su.get('total_llm_calls', 0),
                "sk_gen": su.get('strategy_attempts', {}).get('sketch_generation', 0),
                "n_sketch": len(series),
                "first_haves": len(series[0]['haves']) if series else None,
                "exact_dup": len(sigs) - len(set(sigs)),
                "revisit": sum(v - 1 for v in c.values() if v > 1),
            })
    return obs


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tag", default="variance")
    ap.add_argument("--include-old", action="store_true",
                    help="이 실험 이전의 보관본도 함께 집계 (조건이 다르니 주의)")
    ap.add_argument("--out", help="결과를 JSON 으로 저장")
    args = ap.parse_args()

    obs = collect(args.tag, args.include_old)
    if not obs:
        print(f"  결과 없음. results/archive/{args.tag}_r*_* 를 확인하세요.")
        return

    print(f"  === 문제별 성공률 ({len(obs)}문제) ===\n")
    print(f"  {'문제':42s} {'n':>2s} {'성공':>4s} {'성공률':>7s} {'95% 구간':>14s}  {'소요(분)':>18s}")
    rows = []
    for n, v in sorted(obs.items(), key=lambda kv: -len(kv[1])):
        k = sum(1 for r in v if r['ok'])
        lo, hi = wilson(k, len(v))
        durs = ",".join(f"{r['dur']:.0f}" for r in sorted(v, key=lambda r: r['when']))
        print(f"  {n[:42]:42s} {len(v):2d} {k:4d} {k/len(v)*100:6.0f}% "
              f"{lo*100:5.0f}~{hi*100:3.0f}%  {durs[:18]:>18s}")
        rows.append((n, len(v), k))

    print("\n  === 갈리는 문제 (한 번은 성공, 한 번은 실패) ===")
    flip = [n for n, v in obs.items() if len({r['ok'] for r in v}) > 1]
    if flip:
        for n in flip:
            v = sorted(obs[n], key=lambda r: r['when'])
            print(f"    {n}")
            for r in v:
                print(f"        {r['when']}  {'성공' if r['ok'] else '실패':4s}  "
                      f"스케치 {r['n_sketch']:2d}개(첫 have {r['first_haves']})  "
                      f"{r['dur']:5.0f}분  호출 {r['calls']:4d}  재방문 {r['revisit']}")
    else:
        print("    없음")

    print("\n  === 스케치 지표: 성공 vs 실패 ===")
    S = [r for v in obs.values() for r in v if r['ok'] and r['n_sketch']]
    F = [r for v in obs.values() for r in v if not r['ok'] and r['n_sketch']]
    for lab, g in (("성공", S), ("실패", F)):
        if not g:
            continue
        fh = [r['first_haves'] for r in g if r['first_haves'] is not None]
        print(f"    {lab} {len(g):2d}건   스케치 중앙값 {statistics.median(r['n_sketch'] for r in g):.0f}개   "
              f"첫 have 중앙값 {statistics.median(fh) if fh else 0:.0f}   "
              f"재방문 합계 {sum(r['revisit'] for r in g)}")

    tot_sk = sum(r['n_sketch'] for v in obs.values() for r in v)
    tot_rev = sum(r['revisit'] for v in obs.values() for r in v)
    if tot_sk:
        print(f"\n  전체 스케치 {tot_sk}개, 같은 have 조합 재방문 {tot_rev}개 ({tot_rev/tot_sk*100:.0f}%)")
        print("  (기존 로그 1,828개 기준선: 36%)")

    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        json.dump({k: v for k, v in obs.items()}, open(args.out, 'w', encoding='utf-8'),
                  ensure_ascii=False, indent=2)
        print(f"\n  저장: {args.out}")


if __name__ == "__main__":
    main()
