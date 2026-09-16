#!/usr/bin/env python3
"""스케치의 have 들 사이에서 '진짜 의존'만 찾아낸다.

왜 필요한가
-----------
HILBERT 는 각 have 를 독립 정리로 쪼개 병렬로 증명한다. 이때 선행 have 를
가설로 넘길지는 추출 프롬프트의 "relevant context" 라는 말에 맡겨져 있고,
실측 결과 4,958개 추출 묶음 중 74% 가 아무것도 넘기지 않았다.

그런데 전부 넘기는 것도 답이 아니다. imo_2019_p1 의 두 스케치를 비교하면
분명하다.

  A (성공, have 5개)  각 단계가 원래 가설 h 에서 직접 나온다. 선행 have 가
                      필요 없다. 전부 넘기면 불필요한 가설만 늘어난다.
  B (실패, have 9개)  미세 단계의 사슬이다. h_rewrite 의 좌변에 있는
                      `2 * f a - f 0` 은 h_double 의 우변 그대로다.
                      h_double 없이는 h 만으로 처음부터 유도해야 한다.

즉 필요한 곳에만, 필요한 것만 넘겨야 한다.

판정 규칙
---------
have_j 의 최상위 관계 기호 한쪽 변 '전체' 가 have_i 의 문장 안에 부분식으로
나타나면 i 가 j 에 의존한다고 본다. 단 그 변은 연산자를 품은 복합식이어야
한다.

세 조건이 각각 오탐 하나씩을 막는다.

  1) 바인더(∀ x,) 를 걷어낸 뒤 최상위 관계로 분할
     - 문장 전체가 아니라 실제 좌·우변을 잡기 위함
  2) 조각이 아니라 '변 전체' 가 등장할 것
     - h00 : f (2*0) + 2*f 0 = f (f (0+0))
       h_a0: f (2*0) + 2*f b = f (f (0+b))
       둘 다 h 에 대입해 독립적으로 나오는데, 괄호 조각 `2*(0:ℤ)` 가
       겹친다는 이유로 연결될 뻔했다.
  3) 그 변이 연산자(+ - * / ^ ∑ ∏ ∫)를 품을 것
     - h_pos_sqrt2 : (0:ℝ) < Real.sqrt (2:ℝ) 의 우변은 `Real.sqrt(2:ℝ)`
       라는 단순 항이라, √2 를 언급하는 모든 문장에 걸린다. 실제로
       h_int_val 과 잘못 연결됐다.

사용법
------
    python scripts/detect_subgoal_deps.py [--logs 'logs/*.log'] [--out 리포트.md]
"""
import argparse
import collections
import glob
import os
import re
import statistics as st

TS = re.compile(r"^\[\d{4}-\d\d-\d\d")
MARK = "Printing Informal Proof Sketch Before Self Reflection"
RELS = ("↔", "→", "=", "≤", "≥", "<", ">", "∣", "≠")
OPS = set("+-*/^∑∏∫")
MIN_SIDE = 6          # 정규화 후 이보다 짧은 변은 우연 일치가 많아 버린다


def norm(s):
    return re.sub(r"\s+", "", s)


def strip_binders(stmt):
    """앞쪽 `∀ x…,` / `∃ x…,` 를 걷어내 본문만 남긴다."""
    s = stmt.strip()
    while True:
        m = re.match(r"^\s*[∀∃]\s*[^,]{0,40},\s*", s)
        if not m:
            break
        s = s[m.end():]
    return s.strip()


def top_sides(stmt):
    """최상위(괄호 깊이 0) 관계 기호로 쪼갠 좌·우변. 없으면 빈 리스트."""
    s = strip_binders(stmt)
    depth = pos = ln = 0
    pos = None
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            for op in RELS:
                if s.startswith(op, i):
                    pos, ln = i, len(op)
    if pos is None:
        return []
    return [norm(s[:pos]), norm(s[pos + ln:])]


def substantial(side):
    """단순 항은 배제하고 연산자를 품은 복합식만 인정한다."""
    return len(side) >= MIN_SIDE and any(c in OPS for c in side)


def find_links(haves, parent=""):
    """[(의존하는 have, 의존받는 have, 공유한 변)]

    parent 는 부모 정리의 서명+목표. 거기 이미 나오는 식은 have 가 만들어낸
    것이 아니라 문제에서 물려받은 것이므로 의존의 근거가 못 된다.
    """
    pnorm = norm(parent)
    out = []
    for i in range(1, len(haves)):
        body = norm(haves[i][1])
        for j in range(i):
            for side in top_sides(haves[j][1]):
                if not substantial(side):
                    continue
                if side in pnorm:          # 원 문제에 이미 있는 항
                    continue
                if side in body:
                    out.append((haves[i][0], haves[j][0], side))
                    break
    return out


def parse_sketch(txt):
    """(정리명, 부모 서명+목표, [(have 이름, have 문장)])"""
    m = re.search(r"theorem\s+(\S+)([\s\S]*?):=\s*by", txt)
    if not m:
        return None
    parent = m.group(2)
    body = txt[m.end():]
    haves = [(h.group(1), re.sub(r"\s+", " ", h.group(2)).strip())
             for h in re.finditer(
                 r"\bhave\s+([^\s:(]+)\s*(?:\([^)]*\))?\s*:([\s\S]*?):=\s*by", body)]
    return m.group(1), parent, haves


def sketches_in(path):
    lines = open(path, errors="ignore").read().split("\n")
    for i, l in enumerate(lines):
        if MARK not in l:
            continue
        blk = []
        for l2 in lines[i + 1:i + 200]:
            x = l2.split("] - ", 1)[-1] if TS.match(l2) else l2
            if TS.match(l2) and ("****" in l2 or "Correction" in l2 or "REPLACING" in l2):
                if blk:
                    break
                continue
            blk.append(x)
        p = parse_sketch("\n".join(blk))
        if p and len(p[2]) >= 2:
            yield p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--logs", default="logs/*.log")
    ap.add_argument("--out", default=None, help="상세 리포트를 쓸 마크다운 경로")
    a = ap.parse_args()

    rows = []
    for path in sorted(glob.glob(a.logs)):
        for name, parent, haves in sketches_in(path):
            rows.append((os.path.basename(path), name, haves,
                         find_links(haves, parent)))
    if not rows:
        print("스케치를 찾지 못했습니다.")
        return

    nl = [len(r[3]) for r in rows]
    nh = [len(r[2]) for r in rows]
    zero = sum(1 for x in nl if x == 0)
    print(f"  스케치 {len(rows)}개   have 중앙 {st.median(nh):.0f}개")
    print(f"    연결 0개 (주입 불필요) : {zero}개 ({100*zero/len(rows):.0f}%)")
    print(f"    연결 수 중앙 {st.median(nl):.0f}  평균 {st.mean(nl):.1f}  최대 {max(nl)}")
    dist = collections.Counter(min(x, 5) for x in nl)
    print("\n  연결 수 분포:")
    for k in sorted(dist):
        lab = f"{k}개" if k < 5 else "5개+"
        print(f"    {lab:5s} {dist[k]:5d}")

    if a.out:
        with open(a.out, "w") as f:
            f.write("# 스케치별 서브골 의존 검출 결과\n\n")
            f.write(f"스케치 {len(rows)}개 · 연결 0개 {zero}개 "
                    f"({100*zero/len(rows):.0f}%) · 연결 중앙 {st.median(nl):.0f}개\n\n")
            for log, name, haves, links in sorted(rows, key=lambda r: -len(r[3])):
                f.write(f"## {name}\n\n`{log}` · have {len(haves)}개 · "
                        f"연결 {len(links)}개\n\n")
                if links:
                    for i, j, s in links:
                        f.write(f"- `{i}` ← `{j}`  공유한 변 `{s}`\n")
                else:
                    f.write("- 연결 없음 (주입 불필요)\n")
                f.write("\n")
        print(f"\n  리포트: {a.out}")


if __name__ == "__main__":
    main()
