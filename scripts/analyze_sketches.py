#!/usr/bin/env python3
"""
HILBERT 가 만든 증명 스케치를 라벨링하고 분석한다.

  왜 만드나
  ---------
  HILBERT 는 스케치가 실패하면 통째로 버리고 새로 만든다. 프롬프트에 과거 시도가
  들어가지 않고(generate_proof_sketch, 398행), 재시도 8회가 같은 인자로 호출된다
  (subgoal_decomp, 1027행). 그래서 같은 곳을 반복해서 시도한다.

  선행 연구(EditableSketch/ICML 2026, BlueprintRepair)는 "실패한 뒤 국소 수리"를
  다룬다. 반응형이다. 이 스크립트는 그 앞단을 본다 — 스케치를 만든 직후,
  증명에 투자하기 전에 그것이 좋은지 판단할 수 있는가.

  라벨링 방식
  -----------
  로그에서 스케치와 그 결과를 짝짓는다.

    "REPLACING HAVE STATEMENTS WITH SORRY"  스케치 생성 시점
    "No sorries found in proof sketch"      그 스케치의 서브골이 전부 닫혀
                                            완전한 증명이 됨 = 조립 성공
    "Job 'theorem_X' finished with result"  개별 서브골의 성패

  스케치와 다음 스케치 사이에 나온 신호를 그 스케치의 결과로 본다.

  분류
  ----
  실패한 스케치를 두 부류로 나눈다. 대응 방법이 다르기 때문이다.

    국소 실패   서브골 대부분이 닫혔는데 일부만 안 닫힘  → 국소 수정으로 충분
    전역 실패   서브골 상당수가 안 닫힘 또는 아예 진행 못 함 → 다른 분해가 필요

  사용법
  ------
    python scripts/analyze_sketches.py
    python scripts/analyze_sketches.py --top-only     # 최상위 정리만
    python scripts/analyze_sketches.py --out results/analysis/sketches.json
"""

import argparse
import collections
import glob
import json
import os
import re
import statistics

STAR = re.compile(r'^\[.*?\]\[.*?\]\[INFO\] - \*{20,}$')
LINE = re.compile(r'^\[(\d{4}-\d\d-\d\d \d\d:\d\d:\d\d),\d+\]\[([^\]]+)\]\[(\w+)\] - (.*)$')
HAVE = re.compile(r"^\s*have\s+([^\s:(]+)", re.M)
THM = re.compile(r'^\s*theorem\s+(\S+)', re.M)
JOB_FIN = re.compile(r"Job '(theorem_\S+)' finished with result: \((True|False)")
# 주의: "No sorries found in proof sketch" 는 성공 신호가 아니다.
#
#   이 로그는 _use_sketch_and_theorems_to_generate_proof 뒤에 찍힌다. 그 함수는
#   스케치와 "아직 증명되지 않은" 서브골 정리들을 reasoner 에게 주고, 서브골을
#   호출하는 형태로 최상위 증명을 조립하게 한다. sorry 가 없다는 것은 조립된
#   텍스트가 완결됐다는 뜻이지 서브골이 닫혔다는 뜻이 아니다.
#   서브골 증명은 그 다음 단계(_correct_theorems_from_sketch)에서 일어난다.
#
#   진짜 성공 신호는 "Proof saved for problem X" 이다.
ASSEMBLED = 'No sorries found in proof sketch'
SAVED = re.compile(r'Proof saved for problem (\S+):')

# 국소 실패로 볼 기준. 서브골의 이 비율 이상이 닫혔으면 "조금만 더 하면 되는" 상태로 본다.
LOCAL_THRESHOLD = 0.7


def load_problem_names(path='data/minif2f/minif2f.jsonl'):
    """최상위 정리를 식별하기 위한 이름 집합."""
    names = set()
    if os.path.exists(path):
        for l in open(path, encoding='utf-8'):
            l = l.strip()
            if l:
                try:
                    names.add(json.loads(l)['name'])
                except Exception:
                    pass
    return names


def parse_log(path, problem_names):
    """로그 하나에서 스케치를 뽑고 결과를 붙인다."""
    try:
        lines = open(path, encoding='utf-8', errors='replace').read().splitlines()
    except Exception:
        return []
    if not any('REPLACING HAVE' in l for l in lines):
        return []

    star = [i for i, l in enumerate(lines) if STAR.match(l)]
    sketches = []
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
        thm = tm.group(1) if tm else "?"
        haves = HAVE.findall(body)
        sketches.append({
            "pos": a, "thm": thm, "haves": haves, "n_have": len(haves),
            "n_lines": len([x for x in body.splitlines() if x.strip()]),
            "sig": re.sub(r'\s+', '', body),
            "top": thm in problem_names,
            # 재귀 깊이 추정: 서브골 정리는 부모 이름을 이어붙여 만들어진다.
            # 원 문제 이름을 떼고 남은 '_h' 조각 수로 깊이를 가늠한다.
            "depth_hint": 0 if thm in problem_names else thm.count('_h'),
        })

    ns_pos = [i for i, l in enumerate(lines) if ASSEMBLED in l]
    # 문제별 최종 성공 시점
    saved = {}
    for i, l in enumerate(lines):
        m = SAVED.search(l)
        if m:
            saved.setdefault(m.group(1), []).append(i)
    jobs = []
    for i, l in enumerate(lines):
        m = JOB_FIN.search(l)
        if m:
            jobs.append((i, m.group(1), m.group(2) == 'True'))

    for idx, s in enumerate(sketches):
        lo = s['pos']
        hi = sketches[idx + 1]['pos'] if idx + 1 < len(sketches) else len(lines)
        s['assembled'] = any(lo < x < hi for x in ns_pos)   # 조립 텍스트가 완결됨
        # 이 스케치가 최종 증명으로 이어졌는가:
        #   같은 정리의 'Proof saved' 시점 직전의 마지막 스케치이면 성공으로 본다.
        s['winning'] = False
        for sv in saved.get(s['thm'], []):
            if lo < sv and not any(lo < o['pos'] < sv for o in sketches
                                   if o is not s and o['thm'] == s['thm']):
                s['winning'] = True
                break
        # 이 구간에서 결판난 서브골들
        seg = [(n, ok) for p, n, ok in jobs if lo < p < hi]
        closed = sum(1 for _, ok in seg if ok)
        s['subgoal_done'] = len(seg)
        s['subgoal_closed'] = closed
        s['close_rate'] = closed / len(seg) if seg else None
        # pos 는 winning 판정에 쓰이므로 마지막에 지운다
    for s in sketches:
        s.pop('pos', None)
    return sketches


def classify(s):
    """스케치의 결과를 부류로 나눈다."""
    if s.get('winning'):
        return '최종 성공'
    if s['subgoal_done'] == 0:
        return '전역 실패(진행 못 함)'
    if s['close_rate'] is not None and s['close_rate'] >= LOCAL_THRESHOLD:
        return '국소 실패(대부분 닫힘)'
    return '전역 실패(많이 안 닫힘)'


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--logs", default="outputs/*/*/run.log")
    ap.add_argument("--top-only", action="store_true", help="최상위 정리의 스케치만")
    ap.add_argument("--out", help="라벨된 스케치를 JSON 으로 저장")
    args = ap.parse_args()

    names = load_problem_names()
    allsk = []
    for p in sorted(glob.glob(args.logs)):
        sk = parse_log(p, names)
        if sk:
            for s in sk:
                s['log'] = p
            allsk += sk
    if args.top_only:
        allsk = [s for s in allsk if s['top']]
    if not allsk:
        print("  스케치를 찾지 못했습니다.")
        return

    print(f"  스케치 {len(allsk)}개  (최상위 {sum(1 for s in allsk if s['top'])}, "
          f"재귀 서브골 {sum(1 for s in allsk if not s['top'])})\n")

    # ── 결과 분류 ────────────────────────────────────────────────────────
    cls = collections.Counter(classify(s) for s in allsk)
    print("  === 스케치 결과 분류 ===")
    for k in ('최종 성공', '국소 실패(대부분 닫힘)', '전역 실패(많이 안 닫힘)', '전역 실패(진행 못 함)'):
        v = cls[k]
        print(f"    {k:26s} {v:5d}  ({v/len(allsk)*100:5.1f}%)")
    fails = len(allsk) - cls['최종 성공']
    if fails:
        loc = cls['국소 실패(대부분 닫힘)']
        print(f"\n    실패 {fails}개 중 국소 수정으로 될 만한 것 {loc}개 ({loc/fails*100:.0f}%)")
        print(f"    나머지 {fails-loc}개는 다른 분해가 필요")

    # ── 수준별 ───────────────────────────────────────────────────────────
    print("\n  === 최상위 vs 재귀 서브골 ===")
    for lab, g in (("최상위", [s for s in allsk if s['top']]),
                   ("재귀", [s for s in allsk if not s['top']])):
        if not g:
            continue
        ok = sum(1 for s in g if s.get('winning'))
        hs = [s['n_have'] for s in g]
        print(f"    {lab:6s} {len(g):5d}개   최종 성공 {ok/len(g)*100:5.1f}%   "
              f"have 중앙값 {statistics.median(hs):.0f}")

    # ── 크기와 성패 ──────────────────────────────────────────────────────
    print("\n  === have 개수별 조립 성공률 ===")
    for lab, g in (("최상위", [s for s in allsk if s['top']]),
                   ("재귀", [s for s in allsk if not s['top']])):
        if not g:
            continue
        print(f"    [{lab}]")
        buck = collections.defaultdict(list)
        for s in g:
            n = s['n_have']
            key = '0-2' if n <= 2 else '3-5' if n <= 5 else '6-9' if n <= 9 else '10-14' if n <= 14 else '15+'
            buck[key].append(bool(s.get('winning')))
        for key in ('0-2', '3-5', '6-9', '10-14', '15+'):
            v = buck.get(key, [])
            if not v:
                continue
            r = sum(v) / len(v)
            print(f"      have {key:6s} n={len(v):4d}  최종 성공 {r*100:5.1f}%  {'█'*int(r*30)}")

    # ── 같은 정리 안에서의 비교 (문제 난이도 통제) ──────────────────────
    print("\n  === 같은 (로그, 정리) 안에서 성공/실패 스케치 비교 ===")
    ser = collections.defaultdict(list)
    for s in allsk:
        ser[(s['log'], s['thm'])].append(s)
    pairs = [(k, v) for k, v in ser.items()
             if any(x.get('winning') for x in v) and any(not x.get('winning') for x in v)]
    print(f"    성공과 실패가 함께 있는 계열 {len(pairs)}개")
    if pairs:
        d_have, d_line = [], []
        for _, v in pairs:
            ok = [x['n_have'] for x in v if x.get('winning')]
            ng = [x['n_have'] for x in v if not x.get('winning')]
            d_have.append(statistics.mean(ok) - statistics.mean(ng))
            ok = [x['n_lines'] for x in v if x.get('winning')]
            ng = [x['n_lines'] for x in v if not x.get('winning')]
            d_line.append(statistics.mean(ok) - statistics.mean(ng))
        pos = sum(1 for d in d_have if d > 0)
        print(f"    성공 스케치가 더 굵은(have 많은) 계열  {pos}/{len(d_have)}")
        print(f"    have 개수 차이 중앙값   {statistics.median(d_have):+.1f}")
        print(f"    줄 수 차이 중앙값       {statistics.median(d_line):+.1f}")

    # ── 재방문 ───────────────────────────────────────────────────────────
    print("\n  === 재방문 (같은 have 조합을 다시 만듦) ===")
    rev = tot = 0
    for k, v in ser.items():
        if len(v) < 2:
            continue
        c = collections.Counter(tuple(x['haves']) for x in v)
        rev += sum(n - 1 for n in c.values() if n > 1)
        tot += len(v)
    if tot:
        print(f"    2개 이상 계열의 스케치 {tot}개 중 재방문 {rev}개 ({rev/tot*100:.0f}%)")

    if args.out:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        for s in allsk:
            s['label'] = classify(s)
            s.pop('sig', None)
        json.dump(allsk, open(args.out, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
        print(f"\n  저장: {args.out}  ({len(allsk)}개)")


if __name__ == "__main__":
    main()
