"""
Reasoner 서버 — openai/gpt-oss-120b

GPU 2, 3번 두 장을 사용한다. (0, 1번은 prover 몫 → run_prover_server.py)
실행:  python run_vllm_server.py
종료:  Ctrl+C
"""

import os
import sys

# ---------------------------------------------------------------------------
# 여기서부터는 반드시 torch/vllm 를 import 하기 "전에" 실행돼야 한다.
# 이 환경변수들은 CUDA 컨텍스트가 만들어지는 시점에 한 번만 읽히기 때문에,
# import 뒤에 바꾸면 아무 효과가 없다.
# ---------------------------------------------------------------------------

# 이 프로세스에게 GPU 2, 3번만 보여준다.
# prover(run_prover_server.py)는 0, 1번을 쓰므로 서로 메모리를 침범하지 않는다.
# 주의: 이렇게 하면 프로세스 안에서는 2,3번이 각각 cuda:0, cuda:1 로 보인다.
os.environ.setdefault("CUDA_VISIBLE_DEVICES", "2,3")

# KV 캐시 크기를 정할 때 "CUDA graph 가 나중에 쓸 메모리"까지 미리 빼놓게 한다.
#
# 이걸 켜지 않으면 vLLM 은 남은 메모리를 전부 KV 캐시로 잡아버리고,
# 그 다음 단계인 CUDA graph capture 에서 쓸 공간이 없어서 OOM 으로 죽는다.
# (--gpu-memory-utilization 을 낮춰도 그만큼 KV 캐시를 더 키우기 때문에 해결이 안 된다)
# vLLM 0.20 부터는 이게 기본값이 된다.
os.environ.setdefault("VLLM_MEMORY_PROFILER_ESTIMATE_CUDAGRAPHS", "1")

from vllm.entrypoints.cli.main import main

# ---------------------------------------------------------------------------
# 참고: 예전 버전에는 src/models 에서 GptOssForCausalLM 을 찾아 ModelRegistry 에
# 등록하는 코드가 있었지만, 그런 클래스는 애초에 존재하지 않아 아무 동작도 하지
# 않았다. vLLM 0.19.1 은 gpt-oss 를 네이티브로 지원하므로 등록이 필요 없다.
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    sys.argv = [
        "vllm",
        "serve",
        "openai/gpt-oss-120b",

        # prover 는 11212 번을 쓴다. 겹치지 않게 유지할 것.
        "--port", "11211",
        "--host", "0.0.0.0",

        # 위에서 GPU 2장만 보이게 했으므로 2 여야 한다.
        # (CUDA_VISIBLE_DEVICES 의 GPU 개수와 반드시 일치해야 함)
        "--tensor-parallel-size", "2",

        # GPU 한 장(47.5GiB) 중 몇 %까지 쓸지.
        #   가중치 34.5GiB + KV 캐시 + CUDA graph 를 모두 여기 안에서 해결한다.
        #   OOM 이 나면 0.90 → 0.88 처럼 낮추고, 여유가 많으면 올려도 된다.
        "--gpu-memory-utilization", "0.93",

        # 요청 하나가 쓸 수 있는 최대 토큰 수 (모델 자체 한계는 131072).
        #
        #   KV 캐시 총량은 위 utilization 으로 이미 정해져 있고,
        #   "동시에 처리 가능한 요청 수 ≈ KV 캐시 총량 / max-model-len" 이다.
        #   즉 이 값을 낮출수록 동시 처리량이 올라간다.
        #   131072 로 두면 동시 요청이 1~2개로 떨어지므로 32768 로 잡았다.
        #   더 긴 컨텍스트가 필요하면 올리되, 동시성이 줄어드는 걸 감안할 것.
        "--max-model-len", "32768",
    ]
    main()
