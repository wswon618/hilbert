#!/usr/bin/env python3
"""의존이 있는데 가설로 전달되지 않은 스케치를 찾는다.

두 단계를 교차한다.

  (a) 의존이 있는가  - detect_subgoal_deps.find_links() 로 검출
  (b) 전달됐는가     - 로그에서 그 스케치 직후에 추출된 정리
                       `theorem <have이름>_<문제>` 의 가설 이름 목록에
                       의존 대상이 들어 있는지 확인

(a) 는 있는데 (b) 가 없으면 의존 누락이다.

배경
----
HILBERT 는 각 have 를 독립 정리로 쪼개 병렬로 증명한다. 선행 have 를
가설로 넘길지는 추출 프롬프트의 "relevant context" 라는 표현에 맡겨져
있어 실행마다 달라진다. 실측 4,958개 추출 묶음 중 74% 가 아무것도
넘기지 않았다.

한계
----
- rcases 를 거치면 이름이 바뀌어(h_kc -> hkc) 전달됐는데도 누락으로
  셀 수 있다. 따라서 누락을 과대추정한다.
- 누락이 곧 실패 원인이라고 단정할 수 없다. 서브골 하나가 어려워
  실패했고 누락은 부수 현상일 수 있다.

결과 문서: results/analysis/의존_누락_스케치.md
"""
import re,glob,os,json,collections,importlib.util,pickle
spec=importlib.util.spec_from_file_location("d","/data/ml-hilbert/scripts/detect_subgoal_deps.py")
d=importlib.util.module_from_spec(spec); spec.loader.exec_module(d)
TS=d.TS; MARK=d.MARK
PROBS={json.loads(l)["name"] for l in open("data/minif2f/minif2f_lean4_26.jsonl")}
RES={}
for f in glob.glob("results/async_hilbert/*.json"):
    m=re.search(r"minif2f_(.+?)_results_",os.path.basename(f))
    if not m: continue
    try: dd=json.load(open(f))
    except Exception: continue
    r=dd.get("results")
    if isinstance(r,dict):
        RES[m.group(1)]={k:(v.get("success") if isinstance(v,dict) else bool(v)) for k,v in r.items()}
def parent_problem(name):
    if name in PROBS: return name
    for p in PROBS:
        if name.endswith("_"+p): return p
    return None
def scan(path):
    lines=open(path,errors="ignore").read().split("\n")
    idxs=[i for i,l in enumerate(lines) if MARK in l]
    for n,i in enumerate(idxs):
        end = idxs[n+1] if n+1<len(idxs) else min(len(lines), i+8000)
        blk=[]
        for l2 in lines[i+1:i+200]:
            x=l2.split("] - ",1)[-1] if TS.match(l2) else l2
            if TS.match(l2) and ("****" in l2 or "Correction" in l2 or "REPLACING" in l2):
                if blk: break
                continue
            blk.append(x)
        p=d.parse_sketch("\n".join(blk))
        if not p: continue
        name,parent,haves=p
        if len(haves)<2: continue
        hyp={}
        for j in range(i,end):
            body=lines[j].split("] - ",1)[-1] if TS.match(lines[j]) else lines[j]
            m=re.match(r"\s*theorem\s+(\S+)",body)
            if not m: continue
            sig=[body]
            for l2 in lines[j+1:j+18]:
                if TS.match(l2): break
                sig.append(l2)
                if ":= by" in l2: break
            hyp.setdefault(m.group(1), set(re.findall(r"\(([A-Za-z_][A-Za-z0-9_₀-₉']*)\s*[:(]","\n".join(sig))))
        yield name,parent,haves,hyp
tab=collections.Counter(); rows=[]
for path in sorted(glob.glob("logs/*.log")):
    rn=re.sub(r"_\d{8}_\d{6}\.log$","",os.path.basename(path))
    res=RES.get(rn) or {}
    for name,parent,haves,hyp in scan(path):
        links=d.find_links(haves,parent)
        if not links: continue
        prob=parent_problem(name)
        ok=res.get(prob) if prob else None
        miss=[];kept=[]
        for i,j,side in links:
            cand=[t for t in hyp if t==i or t.startswith(i+"_")]
            if not cand: continue
            (miss if j not in hyp[cand[0]] else kept).append((i,j,side))
        if not miss and not kept: continue
        st = "누락" if miss else "전달"
        if ok is not None: tab[(st,ok)]+=1
        rows.append(dict(log=os.path.basename(path),thm=name,prob=prob,nh=len(haves),
                         miss=miss,kept=kept,ok=ok))
print("  === 검출된 의존이 가설로 전달됐는가 × 문제 성패 ===")
print(f"  {'':8s} {'성공':>5s} {'실패':>5s} {'n':>5s} {'성공률':>8s}")
for st in ["전달","누락"]:
    s=tab[(st,True)]; f=tab[(st,False)]; n=s+f
    if n: print(f"  {st:8s} {s:5d} {f:5d} {n:5d} {100*s/n:7.1f}%")
pickle.dump(rows,open("/tmp/claude-0/-data-ml-hilbert/f0c3bbf2-4302-425b-b512-7850d78ea1c1/scratchpad/rows2.pkl","wb"))
fail=[r for r in rows if r["ok"] is False and r["miss"]]
print(f"\n  실패 회차 + 의존 누락 스케치: {len(fail)}개")
byp=collections.Counter(r["prob"] for r in fail)
print("  문제별:")
for p,c in byp.most_common(10): print(f"    {p[:52]:52s} {c}개")
