#!/usr/bin/env python3
"""
벤치마크 JSONL 을 split 별로 걸러서 작은 조각(chunk)으로 나누는 스크립트.

왜 나눠야 하는가
----------------
HILBERT 는 문제 하나당 12분쯤 걸린다. MiniF2F test 244문제면 동시 실행을 감안해도
8시간 이상이다. 그런데 src/models/AsyncHILBERT.py 의 _run_from_file_async 에는
두 가지 제약이 있다.

  1) split 필드를 무시하고 파일 안의 모든 문제를 돌린다.
     → 488개짜리 원본을 그대로 주면 valid 244 + test 244 를 다 돌려 시간이 두 배가 된다.

  2) 중단된 지점부터 재개하는 기능이 없다. 게다가 random.shuffle 에 시드가 없어서
     실행할 때마다 순서가 바뀐다.
     → 8시간짜리 실행이 7시간째에 끊기면 처음부터 다시 해야 한다.

그래서 미리 split 을 거르고, 작은 조각으로 나눠 둔다. 조각 하나가 끝날 때마다
results/ 에 JSON 이 저장되므로, 중간에 끊겨도 그 조각만 다시 돌리면 된다.

사용 예
-------
  # MiniF2F test split 을 20문제씩 나누기 (기본값)
  python scripts/split_dataset.py --input data/minif2f/minif2f.jsonl --split test

  # 조각 크기를 바꾸고 싶을 때
  python scripts/split_dataset.py --input data/minif2f/minif2f.jsonl --split test --chunk-size 10

  # 먼저 10문제만 실측해보고 싶을 때
  python scripts/split_dataset.py --input data/minif2f/minif2f.jsonl --split test --limit 10
"""

import argparse
import json
import os
import re
from collections import Counter

# HILBERT 가 실제로 읽는 필드.
#   src/models/AsyncHILBERT.py:_run_from_file_async 는 이 셋만 꺼내 쓴다.
#   (informal_prefix 는 데이터에 있어도 코드가 참조하지 않는다 — HILBERT 는
#    formal_statement 만 보고 스스로 informal reasoning 을 만들어낸다)
REQUIRED_FIELDS = ["name", "header", "formal_statement"]


# 문제 이름 앞부분으로 출처를 구분한다. miniF2F 는 이름 규칙이 일정하다.
#   예) mathd_algebra_478, aime_1984_p7, imo_1969_p2, amc12a_2019_p21
#
# 순서가 중요하다 — 긴 접두어를 먼저 매칭해야 amc12a 가 amc12 로,
# mathd_algebra 가 algebra 로 잘못 분류되지 않는다.
SOURCE_PATTERNS = [
    "mathd_algebra", "mathd_numbertheory",
    "amc12a", "amc12b", "amc12",
    "aime", "imo", "induction",
    "algebra", "numbertheory",
]


def source_of(name):
    """문제 이름에서 출처를 뽑는다. 못 찾으면 'other'."""
    for pat in SOURCE_PATTERNS:
        if name.startswith(pat):
            return pat
    return "other"


def stratified_sample(entries, n):
    """출처별 비율을 유지하면서 n개를 뽑는다.

    왜 필요한가
    -----------
    이름순으로 정렬해 앞에서부터 자르면 난이도가 심하게 편향된다. 실제로
    miniF2F test 244문제를 20개씩 나눴더니 첫 조각에 aime_* 15개가 전부 몰렸다.
    AIME 는 이 벤치마크에서 가장 어려운 축이라, 그 조각만 3시간 30분을 돌려도
    한 문제도 완료되지 않았다.

    반대로 쉬운 문제(mathd_*)만 골라 뽑으면 pass rate 가 부풀려져서 논문 수치와
    비교할 수 없게 된다. 필요한 것은 "전체 구성을 그대로 축소한 표본"이다.
    그래야 표본의 pass rate 가 전체의 추정치가 된다.

    배분 방법
    ---------
    출처별 목표 개수 = (그 출처의 문제 수 / 전체) * n
    소수점 때문에 합이 n 에 안 맞으므로 최대잔여법(largest remainder)으로 보정한다.
    즉 내림한 뒤, 소수부가 큰 순서대로 1개씩 더 준다.

    같은 출처 안에서는 이름순으로 고르게 간격을 두고 뽑는다. 앞에서부터 k개를
    가져오면 연도가 이른 문제에만 몰리므로(예: aime_1983_* 만) 균등 간격을 쓴다.
    난수를 쓰지 않으므로 같은 명령이면 항상 같은 표본이 나온다.
    """
    groups = {}
    for e in entries:
        groups.setdefault(source_of(e.get("name", "")), []).append(e)
    for g in groups.values():
        g.sort(key=lambda e: e.get("name", ""))

    total = len(entries)
    # 내림한 목표치와 소수부를 함께 구한다.
    quotas, remainders = {}, {}
    for src, g in groups.items():
        exact = len(g) * n / total
        quotas[src] = min(int(exact), len(g))
        remainders[src] = exact - int(exact)

    # 최대잔여법으로 n 에 맞춘다. (더 줄 수 있는 출처만 대상)
    while sum(quotas.values()) < n:
        cand = [s for s in groups if quotas[s] < len(groups[s])]
        if not cand:
            break
        src = max(cand, key=lambda s: (remainders[s], len(groups[s])))
        quotas[src] += 1
        remainders[src] = -1     # 한 번 받은 출처는 우선순위를 낮춘다

    picked = []
    for src in sorted(groups):
        g, k = groups[src], quotas[src]
        if k <= 0:
            continue
        if k == 1:
            idxs = [len(g) // 2]                    # 하나면 가운데
        else:
            step = (len(g) - 1) / (k - 1)           # 균등 간격
            idxs = sorted({round(i * step) for i in range(k)})
        picked.extend(g[i] for i in idxs)

    picked.sort(key=lambda e: e.get("name", ""))
    return picked, quotas, {s: len(g) for s, g in groups.items()}


def load_jsonl(path):
    """JSONL 을 읽어 dict 리스트로 반환. 깨진 줄은 건너뛰고 경고만 남긴다."""
    entries = []
    with open(path, "r", encoding="utf-8") as f:
        for line_num, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                entries.append(json.loads(line))
            except json.JSONDecodeError as e:
                print(f"  [경고] {line_num}번째 줄 파싱 실패, 건너뜀: {e}")
    return entries


def validate(entries):
    """HILBERT 가 요구하는 필드가 다 있는지 확인한다.

    여기서 걸러두지 않으면 8시간 돌린 뒤에야 KeyError 를 만나게 된다.
    """
    bad = []
    for i, e in enumerate(entries):
        missing = [f for f in REQUIRED_FIELDS if f not in e]
        if missing:
            bad.append((i, e.get("name", f"<{i}번째>"), missing))
    return bad


def main():
    p = argparse.ArgumentParser(
        description="벤치마크 JSONL 을 split 별로 걸러 조각내기",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    p.add_argument("--input", required=True,
                   help="원본 JSONL 경로 (예: data/minif2f/minif2f.jsonl)")
    p.add_argument("--split", default="test",
                   help="추출할 split. 'all' 이면 전부. (기본: test)")
    p.add_argument("--chunk-size", type=int, default=20,
                   help="조각 하나에 넣을 문제 수 (기본: 20). "
                        "작을수록 중단에 강하지만 파일이 많아진다.")
    p.add_argument("--limit", type=int, default=None,
                   help="앞에서 N개만 사용. 소규모 실측용.")
    p.add_argument("--stratified", action="store_true",
                   help="출처별 비율을 유지하며 --sample 개수만큼 뽑는다. "
                        "이름순으로 자르면 난이도가 편향되므로 소규모 실험에는 이쪽을 쓸 것.")
    p.add_argument("--sample", type=int, default=None,
                   help="--stratified 와 함께 쓸 표본 크기 (예: 20)")
    p.add_argument("--exclude", nargs="*", default=None,
                   help="이미 사용한 조각 JSONL 경로들. 그 안의 name 을 후보에서 뺀다. "
                        "2차 표본을 만들 때 1차와 겹치지 않게 하려는 용도.")
    p.add_argument("--prefix", default=None,
                   help="조각 파일 이름 앞부분 (기본: split 이름). "
                        "층화 표본은 'strat' 처럼 따로 두면 기존 조각과 안 섞인다.")
    p.add_argument("--output-dir", default=None,
                   help="조각을 저장할 디렉토리 "
                        "(기본: <원본이 있는 폴더>/chunks)")
    args = p.parse_args()

    # ── 1. 읽기 ────────────────────────────────────────────────────────────
    print(f"읽는 중: {args.input}")
    entries = load_jsonl(args.input)
    print(f"  총 {len(entries)}개")

    # split 분포를 먼저 보여준다. 어떤 값이 있는지 모르고 --split 을 잘못 주면
    # 결과가 0개가 되는데, 그걸 바로 알아채게 하려는 것.
    dist = Counter(e.get("split", "<없음>") for e in entries)
    print(f"  split 분포: {dict(dist)}")

    # ── 2. split 필터링 ────────────────────────────────────────────────────
    if args.split.lower() == "all":
        selected = entries
        print(f"\nsplit 필터 없음 → {len(selected)}개 전부 사용")
    else:
        selected = [e for e in entries if e.get("split") == args.split]
        print(f"\nsplit='{args.split}' 필터 → {len(selected)}개")
        if not selected:
            print(f"  [오류] 해당 split 이 하나도 없습니다. "
                  f"위의 split 분포를 보고 값을 확인하세요.")
            return 1

    # ── 2-2. 이미 쓴 문제 제외 (--exclude) ─────────────────────────────────
    #
    # 같은 조건으로 2차 실험을 하려면 1차에서 쓴 문제와 겹치면 안 된다.
    # 겹치면 두 결과가 독립이 아니고, HILBERT 는 results/proofs/ 에 .lean 이
    # 남아 있는 문제를 아예 건너뛰기 때문에 재평가도 안 된다.
    if args.exclude:
        used = set()
        for path in args.exclude:
            if not os.path.exists(path):
                print(f"  [경고] --exclude 파일 없음, 무시: {path}")
                continue
            for e in load_jsonl(path):
                used.add(e.get("name"))
        before = len(selected)
        selected = [e for e in selected if e.get("name") not in used]
        print(f"--exclude 적용: {len(used)}개 제외 → {before} - {before - len(selected)} = {len(selected)}개")

    # ── 3. 정렬 ────────────────────────────────────────────────────────────
    # name 기준으로 정렬해서 조각 구성을 재현 가능하게 만든다.
    #
    # AsyncHILBERT 는 실행 시점에 random.shuffle(examples) 을 하므로 조각 "안"의
    # 처리 순서는 어차피 무작위다. 하지만 어떤 문제가 어느 조각에 들어가는지는
    # 여기서 고정되므로, 같은 명령을 다시 실행하면 같은 조각이 나온다.
    selected.sort(key=lambda e: e.get("name", ""))

    # ── 4. 개수 제한 ───────────────────────────────────────────────────────
    if args.limit is not None:
        selected = selected[:args.limit]
        print(f"--limit {args.limit} 적용 → {len(selected)}개")

    # ── 4-2. 층화 표집 (--stratified) ──────────────────────────────────────
    if args.stratified:
        if not args.sample:
            print("  [오류] --stratified 를 쓰려면 --sample N 도 지정해야 합니다.")
            return 1
        if args.sample > len(selected):
            print(f"  [오류] --sample {args.sample} 이 전체 {len(selected)}개보다 큽니다.")
            return 1

        picked, quotas, sizes = stratified_sample(selected, args.sample)
        print(f"\n층화 표집: {len(selected)}개 → {len(picked)}개")
        print(f"  {'출처':22s} {'전체':>6s} {'비율':>7s} {'표본':>5s}")
        for src in sorted(sizes):
            share = sizes[src] / len(selected)
            print(f"  {src:22s} {sizes[src]:6d} {share*100:6.1f}% {quotas.get(src,0):5d}")
        selected = picked

    # ── 5. 필드 검증 ───────────────────────────────────────────────────────
    bad = validate(selected)
    if bad:
        print(f"\n[오류] 필수 필드가 빠진 항목 {len(bad)}개:")
        for i, name, missing in bad[:5]:
            print(f"  - {name}: {missing} 없음")
        if len(bad) > 5:
            print(f"  ... 외 {len(bad) - 5}개")
        print(f"  HILBERT 는 {REQUIRED_FIELDS} 를 요구합니다.")
        return 1
    print(f"필드 검증 통과 ({', '.join(REQUIRED_FIELDS)})")

    # ── 6. 조각내서 저장 ───────────────────────────────────────────────────
    out_dir = args.output_dir or os.path.join(os.path.dirname(args.input), "chunks")
    os.makedirs(out_dir, exist_ok=True)

    n = len(selected)
    chunk_size = args.chunk_size
    num_chunks = (n + chunk_size - 1) // chunk_size   # 올림 나눗셈

    print(f"\n{n}개를 {chunk_size}개씩 → 조각 {num_chunks}개")
    print(f"저장 위치: {out_dir}/")

    written = []
    for idx in range(num_chunks):
        chunk = selected[idx * chunk_size:(idx + 1) * chunk_size]
        # 파일명에 0 패딩을 넣어 ls 했을 때 순서대로 보이게 한다.
        prefix = args.prefix or args.split
        path = os.path.join(out_dir, f"{prefix}_{idx:03d}.jsonl")
        with open(path, "w", encoding="utf-8") as f:
            for e in chunk:
                # ensure_ascii=False: Lean 코드에 ℝ, ∑ 같은 유니코드가 많아서
                # \uXXXX 로 이스케이프되면 파일이 읽기 어려워진다.
                f.write(json.dumps(e, ensure_ascii=False) + "\n")
        written.append((path, len(chunk)))
        print(f"  {os.path.basename(path)}  ({len(chunk)}문제)")

    # ── 7. 실행 방법 안내 ──────────────────────────────────────────────────
    # configs/data/*.yaml 을 조각마다 만들 필요 없이, Hydra 의 인자 덮어쓰기로
    # file_path 만 바꿔주면 된다.
    print(f"\n{'=' * 70}")
    print("실행 방법 — data.file_path 로 조각을 지정한다:")
    print(f"{'=' * 70}")
    first = written[0][0]
    print(f"""
  CUDA_VISIBLE_DEVICES=1 OPENAI_API_KEY=empty \\
      python -m src.run data=minif2f data.file_path={first}

전체를 순서대로 돌리려면 (tmux 안에서 권장):

  for f in {out_dir}/{args.prefix or args.split}_*.jsonl; do
      echo "=== $f ==="
      CUDA_VISIBLE_DEVICES=1 OPENAI_API_KEY=empty \\
          python -m src.run data=minif2f data.file_path=$f
  done

조각 하나가 끝날 때마다 results/async_hilbert/ 에 JSON 이 저장되므로,
중간에 끊기면 남은 조각만 다시 돌리면 된다.
""")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
