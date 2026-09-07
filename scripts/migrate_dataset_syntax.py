#!/usr/bin/env python3
"""
miniF2F 정리문의 구버전 Lean 문법을 현재 mathlib 문법으로 옮긴다.

  왜 필요한가
  -----------
  miniF2F 는 mathlib 이 `∑ x in s, f x` 표기를 쓰던 시절에 만들어졌다. 이후
  mathlib 이 이 표기를 없애고 `∑ x ∈ s, f x` 만 남기면서, 현재 Lean(v4.26)에서는
  구 표기가 아예 파싱되지 않는다:

      ∑ k in S, k   →   unexpected token 'in'; expected ','

  정리문 자체가 컴파일되지 않으므로 모델이 무엇을 하든 그 문제는 실패한다.
  miniF2F test 244문제 중 31문제(12.7%)가 여기 해당한다.

  왜 정규식 치환을 믿을 수 있는가
  --------------------------------
  믿지 않는다. 대신 검증한다.

  데이터셋의 각 항목에는 `goal` 필드가 있다. 이건 데이터셋을 만들던 당시의
  (구 표기를 파싱할 수 있던) Lean 이 정리문을 elaborate 한 뒤 출력한 목표 상태다.
  그 출력에는 이미 `∈` 이 쓰여 있다 — Lean 자신이 `in` 을 받아 `∈` 으로
  정규화했다는 뜻이고, 따라서 두 표기는 같은 항(term)이다.

  우리 Lean 은 구 표기를 읽지 못하니 이 값을 스스로 만들 수 없다. 그래서
  데이터셋에 남아 있는 이 값을 오라클로 쓴다:

      구 표기 ──(옛 Lean)──▶ goal_A          [데이터셋에 이미 있는 값]
             ──(치환)──▶ 신 표기 ──(우리 Lean)──▶ goal_B

  goal_A == goal_B 이면, 서로 다른 두 버전의 Lean 이 같은 항에 도달했다는 뜻이다.
  치환이 의미를 보존했음을 정규식의 정확성이 아니라 두 컴파일러의 합의로 확인한다.

  사용법
  ------
    # 검사만 (파일을 쓰지 않는다)
    python scripts/migrate_dataset_syntax.py

    # 검증을 통과한 항목만 반영해 새 파일로 저장
    python scripts/migrate_dataset_syntax.py --output data/minif2f/minif2f_v4.jsonl

    # 전체 문제를 컴파일해 구 문법 외의 다른 파손도 찾는다 (느림, 244건)
    python scripts/migrate_dataset_syntax.py --check-all
"""

import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor

# ---------------------------------------------------------------------------
# 치환
# ---------------------------------------------------------------------------

# 구 표기를 쓰는 큰 연산자(big operator)들.
#   ∑ ∏ 는 Finset.sum / Finset.prod, ⨆ ⨅ 는 supr / infi, ⋃ ⋂ 는 집합 합/교집합.
#   miniF2F 에서 실제로 나오는 건 ∑ ∏ 뿐이지만, 나머지도 같은 binder 문법을 쓰므로
#   함께 처리해 둔다.
BIG_OPERATORS = "∑∏⨆⨅⋃⋂"

# binder 안에서만 등장하는 ` in ` 을 찾기 위한 패턴.
#   Lean 의 큰 연산자 문법은  <연산자> <binder> in <집합>, <본문>  이다.
#   즉 연산자와 첫 쉼표 사이에 있는 `in` 하나만 바꾸면 된다.
#   본문에 있는 `in`(예: 다른 곳의 식별자)은 건드리면 안 되므로 쉼표까지만 본다.
_OP_RE = re.compile(f"[{BIG_OPERATORS}]")
_IN_RE = re.compile(r"(?<![\w'])in(?![\w'])")


# 타입 표기가 붙은 binder:  `∑ k : ℤ in s,`  또는  `∑ k:ℤ in s,`
#
#   새 문법에는 `∑ (k : ℤ) ∈ s,` 형태가 없다. Lean 에 직접 물어 확인했다:
#       ∑ (k : ℤ) ∈ Finset.Icc 1 12   →  unexpected token '∈'
#   그래서 타입을 binder 가 아니라 집합 쪽으로 옮긴다:
#       ∑ k ∈ (Finset.Icc 1 12 : Finset ℤ)   →  통과
#   miniF2F 에서는 valid 의 2문제(amc12a_2019_p21, amc12a_2010_p22)가 여기 해당한다.
_ASCRIBED_RE = re.compile(
    r"^(\s*)([A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*)\s*:\s*(.+?)(?<![\w'])in(?![\w'])\s*(.+)$",
    re.DOTALL,
)


def _migrate_binder(seg: str) -> str:
    """큰 연산자의 binder 구간 하나를 새 문법으로 옮긴다."""
    m = _ASCRIBED_RE.match(seg)
    if m:
        lead, name, typ, setexpr = m.groups()
        return f"{lead}{name} ∈ ({setexpr.strip()} : Finset {typ.strip()})"
    return _IN_RE.sub("∈", seg)


def migrate(text: str) -> str:
    """구 표기 `∑ x in s,` 를 `∑ x ∈ s,` 로 바꾼다.

    연산자를 하나씩 찾아 그 뒤 첫 쉼표까지의 구간(= binder 부분)에서만 손을 댄다.
    괄호 깊이를 세어, 집합 표현식 안의 쉼표를 binder 의 끝으로 착각하지 않게 한다.
    """
    out = []
    pos = 0
    for m in _OP_RE.finditer(text):
        if m.start() < pos:
            # 앞 구간에 포함된 연산자(중첩된 ∑)는 이미 함께 처리됐다.
            continue

        depth = 0
        end = None
        for i in range(m.end(), len(text)):
            c = text[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                if depth == 0:      # 우리 구간을 벗어났다.
                    end = i
                    break
                depth -= 1
            elif c == "," and depth == 0:
                end = i
                break
        if end is None:
            end = len(text)

        out.append(text[pos:m.end()])
        out.append(_migrate_binder(text[m.end():end]))
        pos = end

    out.append(text[pos:])
    return "".join(out)


def notation_only(orig: str, new: str) -> bool:
    """편집이 `in` → `∈` 표기 치환에 그쳤는지 확인한다.

    양쪽에서 `∈` 을 `in` 으로 되돌리고 공백을 지웠을 때 같으면, 바뀐 것은
    이 표기뿐이라는 뜻이다. (타입 표기 binder 는 괄호가 늘어나므로 여기서
    False 가 나오고, 그건 정상이다 — 그 경우는 goal 대조로만 판단한다.)
    """
    def canon(s):
        return re.sub(r"\s+", "", s.replace("∈", "in"))
    return canon(orig) == canon(new)


# ---------------------------------------------------------------------------
# Lean 서버
# ---------------------------------------------------------------------------

def verify(url: str, custom_id: str, code: str, timeout: int) -> dict:
    """Lean 서버에 코드 한 덩이를 보내고 응답을 돌려준다.

    kimina-lean-server 는 여러 건을 한 요청에 받을 수 있지만, 한 건이 오래 걸리면
    나머지도 함께 늦어진다. 여기서는 건당 하나씩 보내고 파이썬 쪽에서 병렬화한다.
    """
    payload = json.dumps(
        {"codes": [{"custom_id": custom_id, "proof": code}], "timeout": timeout}
    ).encode()
    req = urllib.request.Request(
        url.rstrip("/") + "/verify",
        data=payload,
        headers={"Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout + 60) as r:
            return json.load(r)["results"][0].get("response", {})
    except (urllib.error.URLError, OSError, KeyError, IndexError, ValueError) as e:
        return {"_transport_error": f"{type(e).__name__}: {e}"}


def goal_of(resp: dict):
    """응답에서 sorry 자리의 목표 상태를 꺼낸다. 컴파일 실패면 None."""
    sorries = resp.get("sorries") or []
    if not sorries:
        return None
    return sorries[0].get("goal")


def errors_of(resp: dict):
    """severity 가 error 인 메시지만 추린다."""
    if "_transport_error" in resp:
        return [resp["_transport_error"]]
    return [
        m.get("data", "")
        for m in resp.get("messages", [])
        if m.get("severity") == "error"
    ]


def binders(goal) -> list:
    """goal 문자열에서 큰 연산자의 binder 구간만 뽑는다.

    `∑ k ∈ Finset.Icc 1 12,` 에서 `∑ k ∈ Finset.Icc 1 12` 부분. 우리가 편집한
    곳이 바로 여기이므로, 여기만 대조하면 편집의 영향과 출력기 변경의 영향을
    분리할 수 있다.
    """
    text = goal or ""
    found = []
    for m in _OP_RE.finditer(text):
        depth = 0
        end = len(text)
        for i in range(m.end(), len(text)):
            c = text[i]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                if depth == 0:
                    end = i
                    break
                depth -= 1
            elif c == "," and depth == 0:
                end = i
                break
        found.append(" ".join((text[m.start():end]).split()))
    return found


def norm(goal) -> str:
    """목표 상태 비교용 정규화 — 줄바꿈/공백 차이만 흡수한다.

    기호나 항의 차이는 그대로 남겨서, 의미가 달라진 경우를 놓치지 않는다.
    """
    return " ".join((goal or "").split())


# ---------------------------------------------------------------------------
# 본체
# ---------------------------------------------------------------------------

def build_code(item: dict, statement: str) -> str:
    """header + 정리문 + sorry 로 컴파일 가능한 한 덩이를 만든다."""
    header = item.get("header") or "import Mathlib\n"
    stmt = statement.rstrip()
    # 정리문이 `:= by` 로 끝나면 그 뒤에 sorry 를, 아니면 `:= sorry` 를 붙인다.
    if re.search(r":=\s*by\s*$", stmt):
        body = stmt + "\n  sorry"
    else:
        body = stmt + "\n  := by sorry" if not stmt.endswith(":=") else stmt + " sorry"
    return header.rstrip() + "\n\n" + body + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dataset", default="data/minif2f/minif2f.jsonl")
    ap.add_argument("--split", default="test", help="'all' 이면 전체 split")
    ap.add_argument("--url", default="http://localhost:10001/",
                    help="kimina-lean-server 주소")
    ap.add_argument("--timeout", type=int, default=120,
                    help="정리문 하나당 Lean 컴파일 제한 시간(초)")
    ap.add_argument("--workers", type=int, default=8,
                    help="동시 요청 수. Lean 서버의 REPL 수보다 작게 잡는다.")
    ap.add_argument("--check-all", action="store_true",
                    help="치환 대상이 아닌 문제까지 전부 컴파일해 다른 파손도 찾는다")
    ap.add_argument("--output", help="검증을 통과한 결과를 이 경로에 jsonl 로 저장")
    args = ap.parse_args()

    # --- 1. 적재 -----------------------------------------------------------
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
    print(f"  데이터셋 {args.dataset}  split={args.split}  {len(items)}문제")

    # --- 2. 치환 -----------------------------------------------------------
    changed, unchanged = [], []
    for d in items:
        new_stmt = migrate(d["formal_statement"])
        (changed if new_stmt != d["formal_statement"] else unchanged).append((d, new_stmt))
    print(f"  구버전 문법 포함 {len(changed)}문제 / 그대로 {len(unchanged)}문제")

    targets = changed + (unchanged if args.check_all else [])
    if not targets:
        print("  치환할 것이 없습니다.")
        return 0

    # --- 3. 컴파일 ---------------------------------------------------------
    print(f"  Lean 서버에 {len(targets)}건 컴파일 요청 (동시 {args.workers})...")

    def work(pair):
        d, stmt = pair
        resp = verify(args.url, d["name"], build_code(d, stmt), args.timeout)
        return d, stmt, resp

    results = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        for i, r in enumerate(ex.map(work, targets), 1):
            results.append(r)
            if i % 20 == 0 or i == len(targets):
                print(f"    {i}/{len(targets)}", flush=True)

    # --- 4. 판정 -----------------------------------------------------------
    #   ok        : 컴파일 성공 + 데이터셋 goal 과 일치 (치환이 의미를 보존)
    #   mismatch  : 컴파일은 됐으나 goal 이 다르다 → 손대면 안 된다
    #   no_ref    : 데이터셋에 goal 이 없어 대조 불가 → 컴파일 성공만 확인
    #   fail      : 컴파일 실패 → 구 문법 외의 다른 문제
    # 판정 기준
    #
    #   goal 을 통째로 비교하면 안 된다. Lean v4.26 의 출력기가 바뀌어서, 우리가
    #   전혀 손대지 않은 문제에서도 goal 이 달라진다 (--check-all 대조군에서
    #   test 30건 / valid 28건 확인):
    #
    #       n !          vs  n.factorial
    #       (π/7).cos    vs  cos (Real.pi/7)
    #       Nat.Prime p  vs  p.Prime
    #       Finset.filter (fun x => p x) s  vs  {x ∈ s | p x}
    #
    #   차이가 우리 편집 탓인지 버전 탓인지 가르려면, 우리가 실제로 건드린
    #   부분만 봐야 한다. 그래서 goal 에서 큰 연산자의 binder 구간만 뽑아 비교한다.
    #
    #   ok        : 컴파일 성공 + binder 구간 일치
    #   mismatch  : 컴파일 성공 + binder 구간 불일치 → 우리 편집이 의심되므로 보류
    #   no_ref    : 데이터셋에 goal 이 없어 대조 불가 → 컴파일 성공만 확인
    #   fail      : 컴파일 실패
    buckets = {"ok": [], "mismatch": [], "no_ref": [], "fail": []}
    exact = 0
    for d, stmt, resp in results:
        errs = errors_of(resp)
        g_new = goal_of(resp)
        if errs or g_new is None:
            buckets["fail"].append((d, stmt, errs))
            continue
        g_ref = d.get("goal")
        if not g_ref:
            buckets["no_ref"].append((d, stmt, None))
            continue
        if norm(g_ref) == norm(g_new):
            exact += 1
        # 받아들이는 조건 (둘 중 하나면 충분):
        #
        #   (a) 편집이 `in`→`∈` 표기 치환뿐이다.
        #       데이터셋의 goal 은 옛 Lean 이 `in` 을 받아 `∈` 으로 출력한 결과이므로,
        #       두 표기가 같은 항임은 이미 증명돼 있다. 표기만 바꿨고 컴파일이
        #       되었다면 의미는 보존된다.
        #
        #   (b) goal 의 binder 구간이 일치한다.
        #       타입 표기 binder 처럼 괄호가 늘어난 경우는 (a) 가 성립하지 않는다.
        #       그때는 우리가 편집한 자리인 binder 구간을 직접 대조한다.
        if notation_only(d["formal_statement"], stmt) or binders(g_ref) == binders(g_new):
            buckets["ok"].append((d, stmt, None))
        else:
            buckets["mismatch"].append(
                (d, stmt, (" | ".join(binders(g_ref)), " | ".join(binders(g_new))))
            )

    changed_names = {d["name"] for d, _ in changed}
    print("\n  === 결과 ===")
    print(f"    (참고) goal 전체가 문자 단위로 일치한 것: {exact}건")
    for k, label in [("ok", "일치 (치환 안전)"),
                     ("no_ref", "참조 goal 없음 (컴파일만 성공)"),
                     ("mismatch", "binder 불일치 (치환 보류)"),
                     ("fail", "컴파일 실패")]:
        n = len(buckets[k])
        nc = sum(1 for d, *_ in buckets[k] if d["name"] in changed_names)
        print(f"    {label:32s} {n:3d}건" + (f"  (치환 대상 {nc}건)" if args.check_all else ""))

    # 치환한 항목의 편집이 표기 치환에 그쳤는지 별도로 확인한다.
    pure = sum(1 for d, stmt in changed if notation_only(d["formal_statement"], stmt))
    print(f"    (참고) 편집이 `in`→`∈` 치환뿐인 것: {pure}/{len(changed)}건"
          f"  (나머지는 타입 표기 binder)")

    for k in ("mismatch", "fail"):
        if not buckets[k]:
            continue
        print(f"\n  --- {k} 상세 ---")
        for d, _stmt, info in buckets[k][:20]:
            print(f"    {d['name']}")
            if k == "fail":
                for e in (info or ["(메시지 없음)"])[:2]:
                    print(f"        {' '.join(str(e).split())[:150]}")
            else:
                print(f"        기대 binder: {info[0][:110]}")
                print(f"        실제 binder: {info[1][:110]}")
        if len(buckets[k]) > 20:
            print(f"    ... 외 {len(buckets[k]) - 20}건")

    # --- 5. 저장 -----------------------------------------------------------
    if args.output:
        # 검증을 통과한 항목만 새 정리문을 반영한다.
        # mismatch / fail 은 원본을 그대로 둔다 — 확인되지 않은 변경은 넣지 않는다.
        safe = {d["name"]: stmt for d, stmt, _ in buckets["ok"] + buckets["no_ref"]}
        written = applied = 0
        with open(args.dataset, encoding="utf-8") as fin, \
             open(args.output, "w", encoding="utf-8") as fout:
            for line in fin:
                line = line.strip()
                if not line:
                    continue
                d = json.loads(line)
                new = safe.get(d["name"])
                if new and new != d["formal_statement"]:
                    d["formal_statement"] = new
                    applied += 1
                fout.write(json.dumps(d, ensure_ascii=False) + "\n")
                written += 1
        print(f"\n  저장: {args.output}  ({written}행, 정리문 수정 {applied}건)")

    return 1 if buckets["mismatch"] else 0


if __name__ == "__main__":
    sys.exit(main())
