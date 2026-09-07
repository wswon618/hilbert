#!/usr/bin/env bash
#
# 스케치 분산 측정 — 같은 문제를 여러 번 돌려 성공률을 잰다.
#
#   왜 필요한가
#   -----------
#   HILBERT 는 스케치 생성을 독립시행으로 다룬다. 프롬프트에 과거 시도가 들어가지
#   않고(HILBERTWorker.generate_proof_sketch, 398행), 재시도 8회가 완전히 같은
#   인자로 호출된다(subgoal_decomp, 1027행). seed 도 없다. 그래서 같은 문제가
#   실행마다 갈린다.
#
#   실측 사례 — aime_1991_p9, 같은 날 7시간 간격, 조건 동일:
#       2026-08-11 02:19   실패   스케치 15회   887분   호출 2954
#       2026-08-11 09:20   성공   스케치  1회    50분   호출   49
#
#   지금 조건(Lean v4.16 + 코드 수정 전부 적용)에서 각 문제의 성공률이 얼마인지
#   모른다. 대부분 1회 이하만 돌려봤다. 이 스크립트가 그 기준선을 만든다.
#
#   회차 구성
#   ---------
#   문제마다 필요한 반복 횟수가 다르다. 이미 관측이 쌓인 문제는 적게 돌린다.
#   회차 r 의 청크에는 "r회 이상 필요한 문제"만 들어 있다.
#
#       1회차  9문제   전부
#       2회차  4문제   유효 표본이 2개 이하인 문제
#       3회차  3문제   유효 표본이 1개인 문제
#
#   주의 — 회차 사이에 results/proofs 를 반드시 비운다
#   ------------------------------------------------
#   HILBERT 는 증명 파일이 이미 있는 문제를 조용히 건너뛴다
#   (AsyncHILBERT._single_problem_worker, 166행). 안 비우면 1회차에 성공한 문제가
#   2회차에서 스킵되고 "성공"으로 기록된다. 실제로 그런 사고가 있었다.
#
#   사용법
#   ------
#     bash scripts/run_variance.sh              # 1~3회차 전부
#     bash scripts/run_variance.sh 2            # 2회차만
#     ROUNDS="1 2" bash scripts/run_variance.sh # 1,2회차
#
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1
ROOT="$PWD"

ROUNDS="${ROUNDS:-${*:-1 2 3}}"
TAG="${TAG:-variance}"
ARCHIVE_ROOT="results/archive"
CHILD=""

# ---------------------------------------------------------------------------
# 정리 — Ctrl+C 로 끊어도 자식 프로세스를 남기지 않는다.
#
#   패턴 매칭(pkill -f)으로 죽이면 안 된다. 예전에 data.name 패턴으로 죽였다가
#   같은 이름의 새 프로세스까지 함께 죽인 적이 있다. PID 로만 다룬다.
# ---------------------------------------------------------------------------
cleanup() {
    if [ -n "$CHILD" ] && kill -0 "$CHILD" 2>/dev/null; then
        echo "  [정리] 실행 중인 프로세스 $CHILD 종료"
        kill "$CHILD" 2>/dev/null
        for _ in $(seq 1 15); do
            kill -0 "$CHILD" 2>/dev/null || break
            sleep 1
        done
        kill -0 "$CHILD" 2>/dev/null && kill -9 "$CHILD" 2>/dev/null
    fi
}
trap cleanup INT TERM EXIT

# ---------------------------------------------------------------------------
# 사전 점검
# ---------------------------------------------------------------------------
check_env() {
    local py; py="$(command -v python)"
    case "$py" in
        *"/envs/hilbert/"*) ;;
        *) echo "  [중단] conda 환경이 hilbert 가 아니다: $py"
           echo "         conda activate hilbert 후 다시 실행"; exit 1 ;;
    esac
    echo "  python  $py"
}

check_servers() {
    local ok=0
    if curl -s -m 8 -o /dev/null http://localhost:10001/ 2>/dev/null; then
        echo "  Lean     (:10001)  OK"
    else echo "  Lean     (:10001)  무응답"; ok=1; fi
    for pp in "11211 reasoner" "11212 prover"; do
        set -- $pp
        if curl -s -m 8 "http://localhost:$1/v1/models" >/dev/null 2>&1; then
            echo "  $2 (:$1)  OK"
        else echo "  $2 (:$1)  무응답"; ok=1; fi
    done
    [ "$ok" -eq 0 ] || { echo "  [중단] 서버가 준비되지 않았다"; exit 1; }
}

# Lean 버전 확인 — /data/kimina-lean-server(v4.26) 와 헷갈린 적이 있다.
check_lean_version() {
    local v
    v=$(curl -s -m 120 -X POST http://localhost:10001/verify \
          -H 'Content-Type: application/json' \
          -d '{"codes":[{"custom_id":"v","proof":"import Mathlib\n#eval Lean.versionString\n"}],"timeout":100}' \
        2>/dev/null | grep -oP '\\"4\.\d+\.\d+\\"' | head -1)
    echo "  Lean 버전  ${v:-확인 실패}"
}

# ---------------------------------------------------------------------------
# 회차 실행
# ---------------------------------------------------------------------------
run_round() {
    local r="$1"
    local chunk="data/minif2f/chunks/${TAG}_r${r}.jsonl"
    [ -f "$chunk" ] || { echo "  [건너뜀] 청크 없음: $chunk"; return; }

    local n; n=$(grep -c . "$chunk")
    local stamp; stamp="$(date +%Y%m%d_%H%M%S)"
    local name="${TAG}_r${r}"
    local log="logs/${name}_${stamp}.log"

    echo
    echo "════════════════════════════════════════════════════════════"
    echo "  ${r}회차   ${n}문제   $(date '+%Y-%m-%d %H:%M:%S')"
    echo "  청크  $chunk"
    echo "  로그  $log"
    echo "════════════════════════════════════════════════════════════"

    # 이전 회차의 증명을 치운다. 안 치우면 이번 회차가 그 문제를 건너뛴다.
    if [ -n "$(find results/proofs -type f 2>/dev/null | head -1)" ]; then
        local arc="${ARCHIVE_ROOT}/${TAG}_before_r${r}_${stamp}"
        mkdir -p "$arc"
        mv results/proofs "$arc/proofs"
        echo "  [보관] 이전 결과 → $arc"
    fi
    mkdir -p results/proofs

    python -m src.run \
        experiment=async_hilbert \
        data=minif2f \
        "data.name=minif2f_${name}" \
        "data.file_path=${chunk}" \
        > >(tee "$log") 2>&1 &
    # 주의: `| tee` 가 아니라 프로세스 치환을 쓴다. `| tee` 면 $! 가 tee 의 PID 가 된다.
    CHILD=$!
    wait "$CHILD"
    local rc=$?
    CHILD=""

    echo "  [종료] 코드 $rc   $(date '+%H:%M:%S')"

    # 이번 회차 결과를 회차 이름으로 보관한다.
    local arc="${ARCHIVE_ROOT}/${TAG}_r${r}_${stamp}"
    mkdir -p "$arc"
    if [ -n "$(find results/proofs -type f 2>/dev/null | head -1)" ]; then
        cp -a results/proofs "$arc/proofs"
    fi
    cp results/async_hilbert/*"${name}"* "$arc/" 2>/dev/null
    cp "$log" "$arc/" 2>/dev/null

    local solved total
    solved=$(ls results/proofs/*.lean 2>/dev/null | wc -l)
    total=$(ls results/proofs/proof_stats/*.json 2>/dev/null | wc -l)
    echo "  [결과] ${solved}/${total} 성공   보관 $arc"
}

# ---------------------------------------------------------------------------
echo "════════════════════════════════════════════════════════════"
echo "  스케치 분산 측정   회차 [$ROUNDS]"
echo "════════════════════════════════════════════════════════════"
check_env
check_servers
check_lean_version
echo

START=$(date +%s)
for r in $ROUNDS; do
    run_round "$r"
done
END=$(date +%s)

echo
echo "════════════════════════════════════════════════════════════"
echo "  전체 종료   소요 $(( (END-START)/3600 ))시간 $(( ((END-START)%3600)/60 ))분"
echo "  집계:  python scripts/analyze_variance.py"
echo "════════════════════════════════════════════════════════════"
