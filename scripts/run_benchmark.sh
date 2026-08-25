#!/usr/bin/env bash
#
# 조각(chunk)으로 나눠둔 벤치마크를 순서대로 전부 실행하는 스크립트.
# MiniF2F, PutnamBench 등 여러 벤치마크를 같은 방식으로 돌릴 수 있다.
#
#
# 왜 이런 스크립트가 필요한가
# ===========================
#
# MiniF2F test 244문제는 실측 기준 100시간 안팎이 걸린다. 그렇게 긴 실행에서는
# 아래 세 가지가 반드시 필요하다.
#
#   1) 재개(resume)
#      HILBERT 자체에는 중단 지점부터 이어서 하는 기능이 없다. 게다가
#      src/models/AsyncHILBERT.py 의 _run_from_file_async 는 random.shuffle 을
#      시드 없이 호출해서 매 실행마다 순서가 바뀐다.
#      → 조각 단위로 쪼개두고, 끝난 조각은 건너뛰는 방식으로 해결한다.
#
#   2) 결과 구분
#      src/run.py:28 은 결과 파일명을 이렇게 만든다.
#          f"{cfg.experiment.name}_{cfg.data.name}_results_{timestamp}.json"
#      cfg.data.name 은 configs/data/minif2f.yaml 에서 항상 'minif2f' 다.
#      그냥 돌리면 조각 13개 결과가 전부 같은 이름 패턴이 되어,
#      어느 조각 결과인지 알 수 없고 재개 판정도 못 한다.
#      → data.name 을 '<벤치마크>_<조각태그>' 로 덮어써서 파일명에 남긴다.
#        예: async_hilbert_minif2f_test_003_results_2026-08-10_11-20-33.json
#            async_hilbert_putnam_test_003_results_2026-08-11_04-02-15.json
#      벤치마크 이름이 들어가므로 MiniF2F 와 PutnamBench 결과가 섞이지 않는다.
#
#   3) 서버 점검
#      LLM 서버 2개(reasoner, prover)와 Lean 검증기가 모두 살아있어야 한다.
#      하나라도 죽은 채로 돌리면 모든 문제가 실패하면서 시간만 태운다.
#      실제로 그런 일이 있었다 — prover 가 죽은 줄 모르고 실험이 계속 돌았다.
#      → 시작 전과 매 조각 전에 확인하고, 죽었으면 즉시 멈춘다.
#
#
# 사용법
# ======
#
#   반드시 tmux 안에서 실행할 것. SSH 가 끊겨도 살아남아야 한다.
#
#     tmux new -s hilbert
#     conda activate hilbert
#     cd /data/ml-hilbert
#
#     bash scripts/run_benchmark.sh minif2f      # MiniF2F 전체
#     bash scripts/run_benchmark.sh putnam       # PutnamBench 전체
#
#     # Ctrl+B 누르고 D 로 빠져나오기
#     # tmux attach -t hilbert 로 다시 들어가기
#
#   중단했다가 같은 명령을 다시 실행하면 끝난 조각은 건너뛰고 이어서 한다.
#
#   조각 일부만 돌리고 싶으면 CHUNK_GLOB 으로 좁힌다.
#     CHUNK_GLOB='test_00[0-2].jsonl' bash scripts/run_benchmark.sh minif2f
#
#
# 새 벤치마크를 추가하려면
# ========================
#   1. configs/data/<이름>.yaml 이 있어야 한다 (name, file_path 필드).
#   2. scripts/split_dataset.py 로 조각을 만든다.
#        python scripts/split_dataset.py --input data/<이름>/<원본>.jsonl --split test
#   3. 아래 BENCH_CONFIGS 에 한 줄 추가한다.

set -u   # 정의되지 않은 변수를 쓰면 즉시 에러. 오타로 인한 조용한 실패를 막는다.
         # set -e 는 일부러 쓰지 않는다 — 조각 하나가 실패해도 나머지는 계속해야 하므로.

# ── 벤치마크 정의 ────────────────────────────────────────────────────────────
#
# "벤치마크이름|configs/data 의 config 이름|조각 디렉토리"
#
#   두 번째 칸은 `data=<값>` 으로 Hydra 에 넘어간다. configs/data/<값>.yaml 이
#   실제로 존재해야 한다.
#
BENCH_CONFIGS=(
    "minif2f|minif2f|data/minif2f/chunks"
    "putnam|putnam|data/putnam/chunks"
)

# ── 인자 처리 ────────────────────────────────────────────────────────────────
if [ "$#" -lt 1 ]; then
    echo "사용법: bash scripts/run_benchmark.sh <벤치마크>"
    echo
    echo "사용 가능한 벤치마크:"
    for entry in "${BENCH_CONFIGS[@]}"; do
        IFS='|' read -r bname cfgname cdir <<< "$entry"
        # 조각이 준비돼 있는지도 같이 보여준다.
        n=$(ls -1 "$cdir"/*.jsonl 2>/dev/null | wc -l)
        echo "  $bname   (config: data=$cfgname, 조각 $n개, $cdir)"
    done
    exit 1
fi

BENCH="$1"

# 정의에서 해당 벤치마크를 찾는다.
BENCH_CONFIG=""
CHUNK_DIR=""
for entry in "${BENCH_CONFIGS[@]}"; do
    IFS='|' read -r bname cfgname cdir <<< "$entry"
    if [ "$bname" = "$BENCH" ]; then
        BENCH_CONFIG="$cfgname"
        CHUNK_DIR="$cdir"
        break
    fi
done

if [ -z "$BENCH_CONFIG" ]; then
    echo "모르는 벤치마크입니다: $BENCH"
    echo "스크립트 상단의 BENCH_CONFIGS 를 확인하세요."
    exit 1
fi

# ── 설정 (환경변수로 덮어쓸 수 있다) ─────────────────────────────────────────
CHUNK_GLOB="${CHUNK_GLOB:-*.jsonl}"       # 어떤 조각을 돌릴지
LOG_DIR="${LOG_DIR:-logs/$BENCH}"         # 벤치마크별로 로그를 나눈다
RESULT_DIR="results/async_hilbert"        # src/run.py 가 결과를 쓰는 곳 (고정)

# 임베딩 모델(all-mpnet-base-v2)이 올라갈 GPU.
#   GPU 0,1 은 prover, 2,3 은 reasoner 가 꽉 채우고 있다. 남는 공간이 있는
#   카드를 지정하지 않으면 sentence-transformers 가 cuda:0 을 잡으려다 OOM 난다.
#   인덱스가 이미 만들어진 뒤라면 짧은 쿼리만 인코딩하므로 "" (CPU) 도 괜찮다.
export CUDA_VISIBLE_DEVICES="${CUDA_VISIBLE_DEVICES:-1}"

# 로컬 vLLM 이라 실제 키는 필요 없지만, openai 클라이언트가 값이 있어야 동작한다.
export OPENAI_API_KEY="${OPENAI_API_KEY:-empty}"

# 점검할 서버들. "이름|헬스체크 URL" 형식.
#   - Lean 검증기(kimina)는 / 가 {"status":"ok"} 를 준다.
#   - vLLM 은 /v1/models 로 확인한다.
#   포트를 바꿨다면 여기도 같이 고쳐야 한다.
#   (configs/experiment/async_hilbert.yaml 의 base_url 들과 일치해야 함)
SERVERS=(
    "Lean검증기|http://localhost:10001/"
    "reasoner|http://localhost:11211/v1/models"
    "prover|http://localhost:11212/v1/models"
)

# 조각 실행 "도중"에 감시자가 지켜볼 서버들. Lean 검증기는 일부러 제외한다.
#
# 왜 Lean 을 빼는가
#   Lean 은 header 의 set_option maxHeartbeats 0 때문에 시간 제한 없이 돌아간다.
#   어려운 증명 하나가 REPL 을 오래 붙잡으면 서버 응답이 그만큼 밀리는데, 이건
#   고장이 아니라 정상 동작 범위다. 실제로 감시자가 Lean 을 "사망"으로 오판해
#   1시간 43분치 작업을 폐기한 적이 있다 — 프로세스는 죽은 적이 없었고
#   메모리도 281GB 여유였으며 잠시 뒤 스스로 회복했다.
#
#   Lean 이 영구히 죽었던 유일한 사고는 REPL 이 64개까지 늘어 메모리를 고갈시킨
#   경우였고, 그건 LEAN_SERVER_MAX_REPLS 로 이미 막았다.
#
#   반면 vLLM 서버는 CUDA OOM 으로 실제로 프로세스가 죽는다(engine core 사망).
#   한 번 죽으면 회복하지 않으므로 감시가 실질적으로 필요한 쪽은 이 둘이다.
#
#   Lean 은 여전히 시작 전 점검과 조각 사이 점검에서는 확인한다(위 SERVERS).
#   아예 안 떠 있으면 실험이 무의미하기 때문이다.
WATCH_SERVERS=(
    "reasoner|http://localhost:11211/v1/models"
    "prover|http://localhost:11212/v1/models"
)

# ── 종료 처리 (Ctrl+C, kill 등) ──────────────────────────────────────────────
#
# 왜 필요한가
#   이 스크립트는 python 을 백그라운드(&)로 띄우고 감시자 서브셸도 따로 띄운다.
#   Ctrl+C 를 누르면 SIGINT 는 포그라운드에 있는 이 스크립트에만 전달되고,
#   백그라운드 자식들은 살아남아 부모가 죽은 뒤 고아(PPID=1)가 된다.
#
#   실제로 그런 일이 있었다. 배치를 Ctrl+C 로 멈췄는데 python -m src.run 이
#   2시간 49분째 계속 돌고 있었고, 새로 시작한 배치와 같은 서버·같은 결과 파일을
#   두고 경쟁했다. 옛 설정으로 도는 프로세스와 새 설정 프로세스가 섞이면
#   결과를 신뢰할 수 없다.
#
#   pkill 로 패턴 매칭해서 지우는 것도 위험하다. 정리하려다 새로 띄운 같은
#   이름의 프로세스까지 죽인 적이 있다. 그래서 PID 를 정확히 기억해 두었다가
#   그것만 종료한다.
#
# 무엇을 정리하나
#   CHILD_PIDS 에 현재 조각의 python PID 와 감시자 PID 를 담아 두고,
#   INT/TERM/EXIT 어느 경로로 끝나든 그 둘을 종료시킨다.
CHILD_PIDS=()

cleanup() {
    local sig="${1:-EXIT}"
    # 이미 정리했으면 다시 하지 않는다 (EXIT 트랩이 중복 호출될 수 있다).
    [ "${CLEANED:-0}" = "1" ] && return
    CLEANED=1

    local alive=()
    for p in "${CHILD_PIDS[@]}"; do
        kill -0 "$p" 2>/dev/null && alive+=("$p")
    done
    [ "${#alive[@]}" -eq 0 ] && return

    echo
    echo "[$sig] 자식 프로세스 정리 중: ${alive[*]}"
    kill -TERM "${alive[@]}" 2>/dev/null

    # 최대 15초 기다렸다가, 그래도 살아있으면 강제 종료.
    for _ in $(seq 1 15); do
        local still=()
        for p in "${alive[@]}"; do kill -0 "$p" 2>/dev/null && still+=("$p"); done
        [ "${#still[@]}" -eq 0 ] && break
        sleep 1
    done
    for p in "${alive[@]}"; do
        kill -0 "$p" 2>/dev/null && { echo "  강제 종료: $p"; kill -KILL "$p" 2>/dev/null; }
    done
    echo "정리 완료."
}

# Ctrl+C(INT), kill(TERM), 정상/비정상 종료(EXIT) 모두에서 정리한다.
trap 'cleanup INT;  exit 130' INT
trap 'cleanup TERM; exit 143' TERM
trap 'cleanup EXIT' EXIT

# ── 파이썬 환경 점검 ─────────────────────────────────────────────────────────
#
# tmux 로 새 창을 만들면 conda 환경이 초기화되어 base 로 돌아간다.
# 그 상태로 실행하면 조각 13개가 전부 "No module named 'hydra'" 로 0분 만에
# 실패한다. 실제로 그런 일이 있었다. 시작 전에 미리 걸러낸다.
check_python_env() {
    local missing=()
    for mod in hydra omegaconf openai faiss sentence_transformers; do
        python -c "import $mod" 2>/dev/null || missing+=("$mod")
    done

    if [ "${#missing[@]}" -gt 0 ]; then
        echo "    현재 python : $(which python)"
        echo "    conda 환경  : ${CONDA_DEFAULT_ENV:-<없음>}"
        echo "    없는 모듈   : ${missing[*]}"
        return 1
    fi

    echo "    OK   python 환경 (${CONDA_DEFAULT_ENV:-?}) — $(which python)"
    return 0
}

# ── 서버 점검 함수 ───────────────────────────────────────────────────────────
# 반환값 0 = 전부 정상, 1 = 하나라도 죽음
# timeout 초를 인자로 받는다(기본 10). 감시자는 더 긴 값을 쓴다.
# 공통 구현. 첫 인자는 timeout(초), 나머지는 "이름|URL" 항목들.
_check_list() {
    local timeout="$1"; shift
    local all_ok=0
    for entry in "$@"; do
        local name="${entry%%|*}"
        local url="${entry##*|}"
        local code
        code=$(curl -s -o /dev/null -m "$timeout" -w "%{http_code}" "$url" 2>/dev/null)
        if [ "$code" = "200" ]; then
            echo "    OK   $name"
        else
            echo "    죽음 $name  (HTTP $code)"
            all_ok=1
        fi
    done
    return $all_ok
}

# 시작 전 / 조각 사이 점검 — Lean 포함 3개 전부
check_servers() { _check_list "${1:-10}" "${SERVERS[@]}"; }

# 조각 실행 중 감시자용 — vLLM 2개만 (Lean 제외, 이유는 WATCH_SERVERS 주석 참고)
check_watched() { _check_list "${1:-10}" "${WATCH_SERVERS[@]}"; }

# ── 시작 ─────────────────────────────────────────────────────────────────────
mkdir -p "$LOG_DIR"

# 조각 목록을 이름순으로 수집. test_000, test_001, ... 순서가 보장된다.
mapfile -t CHUNKS < <(ls -1 "$CHUNK_DIR"/$CHUNK_GLOB 2>/dev/null | sort)

if [ "${#CHUNKS[@]}" -eq 0 ]; then
    echo "조각 파일이 없습니다: $CHUNK_DIR/$CHUNK_GLOB"
    echo
    echo "먼저 데이터를 나누세요:"
    echo "  python scripts/split_dataset.py --input data/$BENCH/<원본>.jsonl --split test"
    exit 1
fi

echo "============================================================"
echo " 벤치마크 배치 실행: $BENCH"
echo "============================================================"
echo "  Hydra config  : data=$BENCH_CONFIG"
echo "  조각 디렉토리 : $CHUNK_DIR"
echo "  조각 수       : ${#CHUNKS[@]}"
echo "  로그          : $LOG_DIR/"
echo "  임베딩 GPU    : ${CUDA_VISIBLE_DEVICES:-<CPU>}"
echo "  시작 시각     : $(date '+%Y-%m-%d %H:%M:%S')"
echo

echo "환경 점검:"
if ! check_python_env; then
    echo
    echo "필요한 패키지가 없습니다. conda 환경을 활성화한 뒤 다시 실행하세요:"
    echo "  conda activate hilbert"
    exit 1
fi
echo

echo "서버 점검:"
if ! check_servers; then
    echo
    echo "서버가 하나 이상 죽어 있습니다. 띄운 뒤 다시 실행하세요."
    # LEAN_SERVER_MAX_REPLS 를 반드시 지정할 것.
    #   지정하지 않으면 CPU 수 기준으로 최대 79개까지 REPL 을 띄우는데,
    #   REPL 하나가 mathlib 을 통째로 올려 6.3GB 를 쓴다. 실제로 64개까지 늘어나
    #   376GB 메모리를 고갈시켰고, 서버 프로세스는 살아있지만 HTTP 응답을 못 하는
    #   상태가 되어 배치가 46분 만에 중단됐다.
    #   16 이면 약 100GB 로, config 의 max_concurrent_requests: 16 과도 맞는다.
    echo "  Lean : cd /data/kimina-lean-server && source \$HOME/.elan/env && LEAN_SERVER_PORT=10001 LEAN_SERVER_MAX_REPLS=16 python -m server"
    echo "  reasoner : python run_vllm_server.py"
    echo "  prover   : python run_prover_server.py"
    exit 1
fi
echo

# ── 조각별 실행 ──────────────────────────────────────────────────────────────
TOTAL="${#CHUNKS[@]}"
DONE_COUNT=0
SKIP_COUNT=0
FAIL_COUNT=0
START_ALL=$(date +%s)

for i in "${!CHUNKS[@]}"; do
    chunk="${CHUNKS[$i]}"
    tag=$(basename "$chunk" .jsonl)          # test_003.jsonl → test_003
    run_name="${BENCH}_${tag}"               # minif2f_test_003

    echo "------------------------------------------------------------"
    echo "[$((i+1))/$TOTAL] $BENCH / $tag   ($(date '+%H:%M:%S'))"

    # 이미 끝난 조각인가?
    #   run_name 이 파일명에 들어가므로 조각별·벤치마크별로 구분된다.
    if ls "$RESULT_DIR"/async_hilbert_"${run_name}"_results_*.json >/dev/null 2>&1; then
        echo "    이미 완료됨 → 건너뜀"
        SKIP_COUNT=$((SKIP_COUNT+1))
        continue
    fi

    # 매 조각 전에 서버를 다시 확인한다.
    #   며칠짜리 실행에서는 중간에 서버가 죽을 수 있다. 죽은 채로 계속 돌리면
    #   남은 조각이 전부 0% 로 기록되어 결과를 통째로 버려야 한다.
    #   그래서 여기서는 건너뛰지 않고 아예 멈춘다.
    if ! check_servers; then
        echo
        echo "서버가 죽었습니다. 여기서 중단합니다."
        echo "서버를 살린 뒤 같은 명령을 다시 실행하면 $tag 부터 이어서 합니다."
        exit 1
    fi

    log_file="$LOG_DIR/${tag}.log"
    chunk_start=$(date +%s)

    # ────────────────────────────────────────────────────────────────────────
    # 조각 실행 + 감시자(watchdog)
    #
    # 왜 감시자가 필요한가
    #   조각 하나가 8시간 이상 걸린다. 그 도중에 서버가 죽으면 HILBERT 는
    #   멈추지 않는다. 남은 문제들이 전부 "서버 연결 실패"로 실패 처리되면서
    #   계속 돌고, python 은 정상 종료(0)하고 결과 JSON 까지 저장한다.
    #
    #   실제로 그런 일이 있었다:
    #     11:32  조각 시작
    #     12:36  prover 가 CUDA OOM 으로 사망
    #     21:13  마지막 문제 처리 (prover 없이 나온 결과라 무의미)
    #     02:15  5시간째 아무 진전 없이 헛돌던 것을 발견 → 14시간 낭비
    #
    #   조각과 조각 "사이"의 점검만으로는 이걸 못 잡는다. 실행 "도중"에도
    #   주기적으로 확인해야 한다.
    #
    # 어떻게 동작하나
    #   1. python 을 백그라운드로 띄우고 PID 를 기억한다.
    #   2. 별도 서브셸에서 WATCH_INTERVAL 초마다 서버 3개를 확인한다.
    #   3. 하나라도 죽으면 python 을 종료시킨다(TERM → 안 죽으면 KILL).
    #   4. 본 흐름은 wait 로 python 이 끝나기를 기다린다.
    #   5. python 이 정상적으로 끝나면 감시자를 정리한다.
    #
    # 출력 처리
    #   `| tee` 를 쓰면 $! 가 python 이 아니라 tee 의 PID 가 되어 감시자가
    #   엉뚱한 프로세스를 죽인다. 그래서 프로세스 치환 `> >(tee ...)` 을 써서
    #   python 의 PID 를 직접 잡는다. 화면 출력과 파일 기록은 그대로 유지된다.
    # ────────────────────────────────────────────────────────────────────────

    # 감시 설정.
    #
    #   WATCH_INTERVAL   확인 주기(초)
    #   WATCH_TIMEOUT    헬스체크 curl 타임아웃(초)
    #   WATCH_FAILS      연속 몇 번 실패해야 "죽었다"고 판단할지
    #
    # 왜 "연속" 실패를 따지는가
    #   한 번의 실패로 즉시 중단시켰더니 오탐이 났다. 03:13 에 감시자가 배치를
    #   죽였는데, 정작 기록된 진단에는 서버 3개가 전부 OK 였다. prover 가 부하를
    #   받는 동안 헬스체크 응답이 타임아웃 안에 못 돌아온 것뿐이었다.
    #   그 오탐 하나로 40분치 작업이 폐기됐다.
    #
    #   진짜로 죽은 서버는 계속 죽어 있으므로, 연속 실패를 요구하면 일시적인
    #   지연과 실제 사망을 구분할 수 있다.
    #
    # 왜 3회(6분)에서 5회(10분)로 늘렸나
    #   3회로도 오탐이 났다. Lean 검증기가 14:03 에 "사망 확정"으로 판정되어
    #   1시간 43분치 작업이 폐기됐는데, 정작 프로세스는 죽은 적이 없었고 잠시 뒤
    #   스스로 회복했다(메모리도 281GB 여유였다).
    #
    #   원인은 header 의 set_option maxHeartbeats 0 이다. 시간 제한이 없으니
    #   어려운 증명 하나가 REPL 을 오래 붙잡으면 서버 응답이 그만큼 밀린다.
    #   Lean 검증기는 몇 분간 무응답이었다가 회복하는 것이 정상 동작 범위다.
    #
    #   애초에 감시자를 넣은 이유는 Lean 이 메모리 고갈로 "영구히" 죽어 14시간을
    #   낭비한 사고였다. 그 원인(REPL 64개 폭주)은 LEAN_SERVER_MAX_REPLS 로 이미
    #   막았으므로, 감시자는 진짜 사망만 잡으면 된다. 10분이면 충분하다.
    WATCH_INTERVAL="${WATCH_INTERVAL:-120}"
    WATCH_TIMEOUT="${WATCH_TIMEOUT:-30}"
    WATCH_FAILS="${WATCH_FAILS:-5}"

    watchdog_flag="$LOG_DIR/.${tag}.server_died"
    rm -f "$watchdog_flag"

    python -m src.run \
        data="$BENCH_CONFIG" \
        data.file_path="$chunk" \
        data.name="$run_name" \
        > >(tee "$log_file") 2>&1 &
    run_pid=$!
    CHILD_PIDS=("$run_pid")   # 트랩이 정리할 대상으로 등록

    # 감시자. python 이 살아있는 동안만 돈다.
    (
        consecutive=0     # 연속 실패 횟수
        while kill -0 "$run_pid" 2>/dev/null; do
            sleep "$WATCH_INTERVAL"
            # python 이 그사이 끝났으면 확인할 필요 없다.
            kill -0 "$run_pid" 2>/dev/null || break

            if check_watched "$WATCH_TIMEOUT" >/dev/null 2>&1; then
                # 한 번이라도 성공하면 카운터를 되돌린다.
                # 일시적인 지연은 여기서 걸러진다.
                if [ "$consecutive" -gt 0 ]; then
                    echo "    (감시자: 서버 응답 회복, 연속 실패 $consecutive → 0)"
                fi
                consecutive=0
                continue
            fi

            consecutive=$((consecutive+1))
            echo "    (감시자: 서버 응답 실패 ${consecutive}/${WATCH_FAILS} — $(date '+%H:%M:%S'))"

            # 아직 임계치에 못 미치면 지켜본다.
            [ "$consecutive" -lt "$WATCH_FAILS" ] && continue

            # 여기까지 왔으면 진짜로 죽은 것으로 판단한다.
            # 서브셸이라 변수로는 부모에게 알릴 수 없으므로 파일로 신호를 남긴다.
            {
                echo "감시자: $(date '+%H:%M:%S') 서버 사망 확정 (${WATCH_FAILS}회 연속 실패)"
                check_watched "$WATCH_TIMEOUT"
            } > "$watchdog_flag"
            echo
            echo "!!! 감시자: 실행 도중 서버가 죽었습니다. 조각을 중단합니다."
            cat "$watchdog_flag"
            kill -TERM "$run_pid" 2>/dev/null
            # 10초 기다렸다가 안 죽으면 강제 종료.
            for _ in $(seq 1 10); do
                kill -0 "$run_pid" 2>/dev/null || break
                sleep 1
            done
            kill -KILL "$run_pid" 2>/dev/null
            break
        done
    ) &
    watch_pid=$!
    CHILD_PIDS=("$run_pid" "$watch_pid")   # 감시자도 정리 대상에 추가

    # python 이 끝날 때까지 기다린다. 감시자가 죽였다면 여기서 0 이 아닌 값이 온다.
    wait "$run_pid"
    status=$?

    # 감시자 정리. 이미 끝났을 수도 있으므로 실패는 무시한다.
    kill "$watch_pid" 2>/dev/null
    wait "$watch_pid" 2>/dev/null
    CHILD_PIDS=()   # 이 조각의 자식들은 끝났으므로 정리 대상에서 뺀다

    chunk_elapsed=$(( $(date +%s) - chunk_start ))

    # 감시자가 개입했다면, 이 조각 결과는 신뢰할 수 없다.
    if [ -f "$watchdog_flag" ]; then
        echo "    감시자가 중단시킴 ($((chunk_elapsed/60))분) → 결과 폐기"
        for f in "$RESULT_DIR"/async_hilbert_"${run_name}"_results_*.json; do
            [ -e "$f" ] || continue
            mv "$f" "${f}.invalid"
            echo "      $(basename "$f") → .invalid 로 보관"
        done
        echo
        echo "서버를 살린 뒤 같은 명령을 다시 실행하면 $tag 부터 이어서 합니다."
        echo "감시 기록: $watchdog_flag"
        exit 1
    fi

    # 조각이 끝난 뒤에도 서버가 살아있는지 확인한다.
    #
    #   서버가 조각 실행 "도중에" 죽으면, 남은 문제들이 전부 "풀지 못함"이 아니라
    #   "서버에 연결 못 함"으로 실패한다. 그런데 python 은 정상 종료(0)하고 결과
    #   JSON 도 그럴듯한 pass_rate 와 함께 저장된다. 실제로 그런 일이 있었다 —
    #   20문제가 6분 만에 "끝나고" pass_rate 0.15 가 기록됐다.
    #
    #   그 파일을 그대로 두면 재개할 때 "이미 완료"로 판정해서 영영 건너뛴다.
    #   그래서 결과를 .invalid 로 이름을 바꿔 보관하고, 다음 실행 때 다시 하게 한다.
    #   (지우지 않고 남기는 이유: 나중에 무슨 일이 있었는지 확인할 수 있도록)
    if ! check_servers >/dev/null 2>&1; then
        echo "    조각 실행 중 서버가 죽었습니다 → 이 결과는 신뢰할 수 없음"
        for f in "$RESULT_DIR"/async_hilbert_"${run_name}"_results_*.json; do
            [ -e "$f" ] || continue
            mv "$f" "${f}.invalid"
            echo "      $(basename "$f") → .invalid 로 보관"
        done
        echo
        echo "서버를 살린 뒤 같은 명령을 다시 실행하면 $tag 부터 이어서 합니다."
        echo "현재 서버 상태:"
        check_servers
        exit 1
    fi

    if [ "$status" -eq 0 ]; then
        echo "    완료 ($((chunk_elapsed/60))분)"
        DONE_COUNT=$((DONE_COUNT+1))
    else
        echo "    실패 (종료코드 $status, $((chunk_elapsed/60))분) → 로그: $log_file"
        FAIL_COUNT=$((FAIL_COUNT+1))
        # 실패해도 계속 진행한다. 한 조각의 문제로 나머지를 포기할 이유가 없다.
        # 나중에 이 조각만 다시 돌리면 된다(결과 JSON 이 없으므로 자동으로 재실행됨).
    fi

    # 누적 진행 상황.
    #   results/proofs/*.lean 은 성공한 증명만,
    #   results/proofs/proof_stats/*.json 은 시도한 모든 문제에 대해 저장된다.
    #   두 개수를 비교하면 대략의 pass rate 가 보인다.
    #   주의: 이 카운트는 벤치마크를 구분하지 않는다. 여러 벤치마크를 돌렸다면
    #        정확한 집계는 결과 JSON 을 봐야 한다.
    attempted=$(ls results/proofs/proof_stats/*_stats.json 2>/dev/null | wc -l)
    solved=$(ls results/proofs/*.lean 2>/dev/null | wc -l)
    total_elapsed=$(( $(date +%s) - START_ALL ))
    echo "    누적(전체 벤치마크 합산): 시도 $attempted / 성공 $solved"
    echo "    경과: $((total_elapsed/3600))시간 $(((total_elapsed%3600)/60))분"
done

# ── 마무리 ───────────────────────────────────────────────────────────────────
TOTAL_ELAPSED=$(( $(date +%s) - START_ALL ))
echo
echo "============================================================"
echo " 배치 종료: $BENCH   ($(date '+%Y-%m-%d %H:%M:%S'))"
echo "============================================================"
echo "  실행한 조각 : $DONE_COUNT"
echo "  건너뛴 조각 : $SKIP_COUNT"
echo "  실패한 조각 : $FAIL_COUNT"
echo "  총 소요     : $((TOTAL_ELAPSED/3600))시간 $(((TOTAL_ELAPSED%3600)/60))분"
echo
echo "  결과 JSON   : $RESULT_DIR/async_hilbert_${BENCH}_*_results_*.json"
echo "  증명        : results/proofs/"
echo "  로그        : $LOG_DIR/"
