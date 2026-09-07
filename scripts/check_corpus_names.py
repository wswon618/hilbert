#!/usr/bin/env python3
"""
검색 코퍼스에 실린 정리 이름들이 현재 mathlib 에 실제로 존재하는지 전수 검사한다.

  왜 필요한가
  -----------
  cache/mathlib_informal.jsonl 은 mathlib v4.16 시점에 만들어졌는데, 지금 돌리는
  Lean 은 v4.26 이다. 그 사이 이름이 바뀌거나 삭제된 정리가 있고, 검색기가 그런
  이름을 모델에게 건네면 모델은 없는 정리를 인용하다 `unknown constant` 로 실패한다.

  어떻게 세는가
  -------------
  추측하지 않고 Lean 에게 직접 묻는다. `Environment.contains` 로 이름 하나하나의
  존재 여부를 확인하는 Lean 코드를 만들어 서버에 보낸다:

      run_cmd do
        let env ← getEnv
        for s in ns do
          unless env.contains s.toName do ...   -- 없는 것만 보고

  `#check` 를 쓰면 존재하는 이름마다 타입을 다 출력해 응답이 거대해지므로,
  없는 것만 되돌려받는 이 방식이 훨씬 가볍다.

  사용법
  ------
    python scripts/check_corpus_names.py                    # 전수 검사
    python scripts/check_corpus_names.py --limit 20000      # 앞부분만 (빠른 확인)
    python scripts/check_corpus_names.py --out cache/stale_names.txt
"""

import argparse
import json
import sys
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor

# 이름 목록을 Lean 리스트 리터럴 `["a", "b", ...]` 로 넘기면, 원소가 2천 개를
# 넘는 순간 "maximum recursion depth reached in the code generator" 로 죽는다.
# (묶음 4000 으로 돌렸을 때 47묶음 중 46묶음이 이 오류로 실패했다.)
# 그래서 리스트 대신 개행으로 이어 붙인 문자열 하나를 넘기고 Lean 쪽에서 쪼갠다.
# 문자열 리터럴은 코드 생성기 재귀를 타지 않으므로 묶음 크기 제약이 사라진다.
TEMPLATE = """import Mathlib
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ns := ({names}).splitOn "\\n"
  let mut missing := #[]
  for s in ns do
    unless env.contains s.toName do missing := missing.push s
  logInfo (String.intercalate "\\n" missing.toList)
"""


def full_name(rec: dict):
    """코퍼스의 name 필드(문자열로 저장된 리스트)를 점으로 이어 붙인 전체 이름."""
    raw = rec.get("name")
    if not raw:
        return None
    if isinstance(raw, str):
        try:
            raw = json.loads(raw.replace("'", '"'))
        except Exception:
            return raw
    if isinstance(raw, list):
        return ".".join(str(x) for x in raw)
    return str(raw)


def query(url: str, names: list, timeout: int) -> tuple:
    """이름 묶음 하나를 Lean 에 보내고 (없는 이름 목록, 오류) 를 돌려준다."""
    # Lean 문자열 리터럴로 감싼다. 이름에 따옴표나 역슬래시는 없지만 방어적으로 이스케이프.
    joined = "\\n".join(n.replace("\\", "\\\\").replace('"', '\\"') for n in names)
    code = TEMPLATE.format(names='"' + joined + '"')
    payload = json.dumps(
        {"codes": [{"custom_id": "chunk", "proof": code}], "timeout": timeout}
    ).encode()
    req = urllib.request.Request(
        url.rstrip("/") + "/verify", data=payload,
        headers={"Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout + 120) as r:
            resp = json.load(r)["results"][0].get("response", {})
    except Exception as e:
        return [], f"{type(e).__name__}: {e}"

    errs = [m.get("data", "") for m in resp.get("messages", []) if m.get("severity") == "error"]
    if errs:
        return [], " / ".join(e[:120] for e in errs[:2])

    out = []
    for m in resp.get("messages", []):
        if m.get("severity") == "info":
            out += [x for x in m.get("data", "").splitlines() if x.strip()]
    return out, None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus", default="cache/mathlib_informal.jsonl")
    ap.add_argument("--url", default="http://localhost:10001/")
    ap.add_argument("--chunk", type=int, default=20000,
                    help="한 요청에 담을 이름 수. 문자열로 넘기므로 크게 잡아도 된다.")
    ap.add_argument("--workers", type=int, default=4,
                    help="동시 요청 수. Lean 서버 REPL 하나가 Mathlib 을 통째로 들고 있어 무거우므로 작게.")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--limit", type=int, help="앞에서 이만큼만 검사 (빠른 확인용)")
    ap.add_argument("--out", help="없는 이름 목록을 이 파일에 저장")
    args = ap.parse_args()

    # --- 이름 수집 (중복 제거, 순서 유지) ---------------------------------
    names, seen = [], set()
    with open(args.corpus, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                n = full_name(json.loads(line))
            except Exception:
                continue
            if n and n not in seen:
                seen.add(n)
                names.append(n)
            if args.limit and len(names) >= args.limit:
                break
    print(f"  코퍼스 {args.corpus}")
    print(f"  검사할 이름 {len(names):,}개 (중복 제거 후)")

    chunks = [names[i:i + args.chunk] for i in range(0, len(names), args.chunk)]
    print(f"  {len(chunks)}묶음 × 최대 {args.chunk}개, 동시 {args.workers}\n")

    missing, failed = [], 0
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        for i, (miss, err) in enumerate(
            ex.map(lambda c: query(args.url, c, args.timeout), chunks), 1
        ):
            if err:
                failed += 1
                print(f"    [{i}/{len(chunks)}] 실패: {err}", flush=True)
            else:
                missing += miss
            if i % 5 == 0 or i == len(chunks):
                print(f"    {i}/{len(chunks)}  누적 미존재 {len(missing):,}", flush=True)

    ok = len(names) - len(missing)
    print("\n  === 결과 ===")
    print(f"    현재 mathlib 에 존재      {ok:,}개  ({ok / len(names) * 100:.1f}%)")
    print(f"    존재하지 않음 (노후)      {len(missing):,}개  ({len(missing) / len(names) * 100:.1f}%)")
    if failed:
        print(f"    검사 실패한 묶음          {failed}개 — 위 수치는 그만큼 과소집계")

    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write("\n".join(sorted(missing)) + "\n")
        print(f"    저장: {args.out}")
    else:
        print("\n  --- 없는 이름 예시 ---")
        for n in missing[:25]:
            print(f"    {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
