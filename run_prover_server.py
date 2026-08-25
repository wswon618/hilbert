"""
Prover 서버 — Goedel-LM/Goedel-Prover-V2-32B

GPU 0, 1번 두 장을 사용한다. (2, 3번은 reasoner 몫 → run_vllm_server.py)
실행:  python run_prover_server.py
종료:  Ctrl+C

첫 실행 때는 가중치 65.5GB 를 내려받으므로 시간이 걸린다.
한 번 받으면 ~/.cache/huggingface 에 남아서 다음부터는 1분 안에 뜬다.
"""

import os
import sys

# ---------------------------------------------------------------------------
# torch/vllm import 전에 설정해야 하는 환경변수들 (자세한 설명은 run_vllm_server.py 참고)
# ---------------------------------------------------------------------------

# 이 프로세스에게 GPU 0, 1번만 보여준다.
#
# 0, 1번에는 우리 것이 아닌 다른 컨테이너의 프로세스가 3GiB 정도 상주해 있다.
# 아래 --gpu-memory-utilization 은 그걸 감안한 값이다.
os.environ.setdefault("CUDA_VISIBLE_DEVICES", "0,1")

# KV 캐시 계산에 CUDA graph 메모리를 포함시킨다. (없으면 기동 중 OOM)
os.environ.setdefault("VLLM_MEMORY_PROFILER_ESTIMATE_CUDAGRAPHS", "1")

from vllm.entrypoints.cli.main import main

if __name__ == "__main__":
    sys.argv = [
        "vllm",
        "serve",
        "Goedel-LM/Goedel-Prover-V2-32B",

        # reasoner 가 11211 을 쓰므로 여기는 11212.
        "--port", "11212",
        "--host", "0.0.0.0",

        # 위에서 GPU 2장만 보이게 했으므로 2.
        "--tensor-parallel-size", "2",

        # GPU 0,1 에는 외부 프로세스가 3GiB 정도 있으므로 그만큼 여유를 둔 값.
        # 그 프로세스가 커지면 여기를 낮춰야 한다.
        "--gpu-memory-utilization", "0.85",

        # 주의: 이 값은 "프롬프트 + 생성" 합계 한도다. 생성만의 한도가 아니다.
        #
        #   configs/experiment/async_hilbert.yaml 의 prover_llm.max_tokens 가 16384(생성 한도)이므로,
        #   여기를 16384 로 두면 프롬프트가 조금만 있어도 한도를 넘어 요청이 거부된다.
        #   그래서 프롬프트 몫 8192 를 더해 24576 으로 잡았다.
        #
        # 이 모델은 32B 인데도 4-bit 양자화가 안 된 bf16 이라 가중치가 65.5GB 로 무겁고,
        # KV 캐시도 토큰당 128KiB 로 reasoner(gpt-oss)의 3.5배를 먹는다.
        # 따라서 이 값을 키울수록 동시 처리 가능한 요청 수가 그만큼 줄어든다.
        # (모델 자체 한계는 40960)
        "--max-model-len", "24576",
    ]
    main()
