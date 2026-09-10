#
# For licensing see accompanying LICENSE file.
# Copyright (C) 2025 Apple Inc. All Rights Reserved.
#
import re
import json
from typing import List, Dict, Optional
import logging
logger = logging.getLogger(__name__)

def extract_jsonl_contents(file_path: str):
    """
    Extracts the contents of a jsonl file.
    """
    with open(file_path, 'r') as f:
        examples = []
        for line in f:
            examples.append(json.loads(line))
        return examples

def extract_proof_ds_prover_v2(response: str) -> str:
    """
    Extracts a code block from a string response, handling various delimiters.

    This function searches for code blocks in a specific order of precedence to
    handle both correctly formed and malformed delimiter pairs. The search order is:
    1. Standard triple backticks (```...```)
    2. Triple single quotes ('''...''')
    3. Malformed mixed delimiters ('''...```)
    4. Malformed mixed delimiters (```...''')

    It uses a non-greedy search (`.*?`) and returns the content of the *last*
    matching block found for the first successful pattern. This makes it robust
    to responses containing conversational text followed by a code block.

    Args:
        response: The string potentially containing the code block(s).

    Returns:
        The extracted code as a string, stripped of leading/trailing whitespace.
        If no code block is found using any pattern, it prints the original
        response for debugging and returns the string "error".
    """
    # Define regex patterns in order of precedence.
    # The non-capturing group (?:...) for the optional language hint is robust.
    # The (.*?) captures the content non-greedily.
    # re.DOTALL allows '.' to match newline characters.
    patterns_in_order = [
        # 1. Primary, standard case: ```...```
        re.compile(r"```(?:[a-zA-Z0-9_-]*)\n?(.*?)\n?```", re.DOTALL),
        # 2. Secondary, alternative case: '''...'''
        re.compile(r"'''(?:[a-zA-Z0-9_-]*)\n?(.*?)\n?'''", re.DOTALL),
        # 3. Malformed case (as requested): '''...```
        re.compile(r"'''(?:[a-zA-Z0-9_-]*)\n?(.*?)\n?```", re.DOTALL),
        # 4. Malformed case (inverse, for completeness): ```...'''
        re.compile(r"```(?:[a-zA-Z0-9_-]*)\n?(.*?)\n?'''", re.DOTALL)
    ]

    # Iterate through the patterns. The first one that finds a match wins.
    for pattern in patterns_in_order:
        matches = pattern.findall(response)
        if matches:
            # If one or more blocks are found, return the content of the last one.
            # .strip() removes leading/trailing whitespace and newlines.
            return matches[-1].strip()

    # If the loop completes without finding any matches, handle the error.
    logger.info(80 * "*")
    logger.info("ERROR: Could not extract a code block with any known delimiter pattern.")
    logger.info("GENERATED RESPONSE:")
    logger.info(80 * "*")
    logger.info(response)
    return "error"

# 응답이 울타리 없이 Lean 코드로 바로 시작하는지 판별하는 패턴.
#
#   모델이 코드블록으로 감싸지 않고 `by ...` 처럼 코드를 바로 내놓는 경우가 잦다.
#   로그에서 파싱 실패 194건을 본문까지 복원해 분류한 결과:
#
#       ```lean/```lean4 로 감싼 것        14건 ( 7%)
#       태그 없는 ``` 블록                  0건 ( 0%)
#       울타리 없는 순수 Lean 코드          94건 (49%)   ← 여기서 버려지고 있었다
#       산문 (모델이 못 하겠다고 답한 것)    86건 (44%)
#
#   전형적인 손실 사례는 내용에 아무 문제가 없다:
#
#       by
#         have h_num_div_den : (a.num : ℚ) / a.den = a := ...
#         exact h_goal
#
#   버려질 때마다 "형식 맞춰 다시 달라"는 재요청이 최대 3회 나간다.
#   imo_2019_p1 한 문제에서만 이 재요청이 124회(전체 호출의 17%)였다.
#
#   시작 토큰을 제한하는 것이 안전장치다. "I'm sorry, but the statement as given
#   cannot be proved..." 같은 산문은 이 패턴에 걸리지 않아 지금처럼 실패로 남는다.
#   즉 이 완화로 산문이 Lean 코드로 오인될 일은 없다.
_BARE_LEAN_START = re.compile(
    r"^\s*(?:by\b|theorem\b|lemma\b|example\b|have\b|import\b|open\b|set_option\b|·|--)"
)


def extract_lean_block(response):
    """응답에서 Lean 코드를 꺼낸다.

    단계적으로 물러나며 시도한다. 앞 단계가 성공하면 뒤는 보지 않는다.

      1. ```lean / ```lean4     저장소 원래 규칙. 가장 신뢰도가 높다.
      2. ``` + 아무 태그         언어 태그를 빠뜨린 경우.
      3. 울타리 없는 순수 코드    응답이 Lean 으로 시작할 때만.

    셋 다 아니면 None 을 돌려주고, 호출부가 형식 오류 수정 경로로 보낸다.
    """
    if not response:
        logger.info("No Lean 4 code blocks detected.")
        return None

    # --- 1단계: 언어 태그가 붙은 코드블록 (원래 규칙 그대로) ---------------
    # 주의: (?:lean|lean4) 로 쓰면 안 된다.
    #
    #   정규식 교대는 왼쪽부터 시도하고, 성공하면 되돌아가지 않는다. 그래서
    #   ```lean4 를 만나면 `lean` 이 먼저 매치되고 남은 "4" 가 본문 앞에 딸려온다:
    #       입력  ```lean4\ntheorem a : True := by trivial\n```
    #       결과  '4\ntheorem a : True := by trivial'      ← 코드가 4 로 시작
    #   Lean 에 그대로 넣으면 "unexpected token; expected command" 가 난다.
    #
    #   같은 파일의 extract_proof_ds_prover_v2 는 문자 클래스
    #   (?:[a-zA-Z0-9_-]*) 를 써서 이 문제가 없다. 긴 것을 먼저 쓰도록 순서를 바꾼다.
    TRIPLE_TICK_PATTERN = re.compile(r"```(?:lean4|lean)\n?(.*?)\n?```", re.DOTALL)
    match = TRIPLE_TICK_PATTERN.findall(response)
    if len(match) == 1:
        return match[0]
    elif len(match) > 1:
        logger.info("WARNING! Multiple Lean 4 blocks detected. Choosing the last one...")
        logger.info("Full response:")
        logger.info(response)
        return match[-1]

    # --- 2단계: 언어 태그가 없거나 다른 코드블록 ---------------------------
    ANY_FENCE_PATTERN = re.compile(r"```(?:[a-zA-Z0-9_+-]*)\n?(.*?)\n?```", re.DOTALL)
    match = ANY_FENCE_PATTERN.findall(response)
    if match:
        logger.info("No ```lean4 tag; falling back to an untagged code block.")
        return match[-1]

    # --- 3단계: 울타리 없이 Lean 코드만 온 경우 ----------------------------
    stripped = response.strip()
    if _BARE_LEAN_START.match(stripped):
        logger.info("No code fence; the response itself looks like Lean. Using it as-is.")
        return stripped

    logger.info("No Lean 4 code blocks detected.")
    return None

def extract_all_lean_blocks(response: str) -> Optional[List[str]]:
    """
    Parse all Lean blocks from string.
    
    Args:
        response: string containing Lean blocks
        
    Returns:
        List of extracted Lean blocks, or None if no Lean blocks found
    """

    # LLM 응답이 None 일 수 있다. 실제로 그랬다.
    #
    #   gpt-oss-120b 를 reasoning effort=high 로 부르면 추론 토큰만 쓰고 본문이
    #   비어 오는 경우가 있다. 그때 chat_completion 이 None 을 돌려준다.
    #   호출부에는 `if missing_theorems is None: continue` 처리가 있지만,
    #   그 앞의 re.findall 에서 먼저 터진다:
    #       TypeError: expected string or bytes-like object
    #   이 예외는 문제 하나를 통째로 죽인다 (imo_2019_p1, 2026-09-02 실행).
    if not response:
        return None

    # Try to extract Lean code blocks first
    lean_pattern = r'```(?:lean4?|LEAN4?)\s*\n(.*?)\n```'
    theorems = re.findall(lean_pattern, response, re.DOTALL | re.IGNORECASE)
    if not theorems:
        return None  # No lean blocks found, don't try to parse forcefully

    return theorems
  
def extract_search_queries(text):
    """Extract content from <search> tags in a string."""
    # LLM 응답이 None 으로 올 수 있다 (gpt-oss 가 추론 토큰만 쓰고 본문을 비우는 경우).
    # 정규식에 None 을 넘기면 TypeError 로 문제 하나가 통째로 죽는다.
    if not text:
        return []
    pattern = r'<search>(.*?)</search>'
    matches = re.findall(pattern, text, re.DOTALL)
    return [match.strip() for match in matches]

def extract_theorems_queries(text):
    """Extract content from <theorem> tags in a string."""
    if not text:            # extract_search_queries 의 주석 참고
        return []
    pattern = r'<theorem>(.*?)</theorem>'
    matches = re.findall(pattern, text, re.DOTALL)
    return [match.strip() for match in matches]


def extract_tag(text: str, tag: str):
    """
    Extract the content between given tags.
    """
    if not text:            # extract_search_queries 의 주석 참고
        return None
    pattern = re.compile(rf"<{tag}>\s*(.*?)\s*</{tag}>", re.DOTALL)
    match = pattern.search(text)
    if match:
        return match.group(1).strip()
    return None

def extract_informal_proof(text: str) -> Optional[str]:
    """
    Extracts the informal proof content from between <informal_proof> tags.
    
    Args:
        text: Input text containing informal proof tags
        
    Returns:
        The informal proof content as a string, or None if not found
    """
    return extract_tag(text, 'informal_proof')

def extract_answer(text: str) -> Optional[str]:
    """
    Extracts the answer in between <answer> </answer> tags.
    
    Args:
        text: Input text containing informal proof tags
        
    Returns:
        The extracted answer as a string, or None if not found
    """
    return extract_tag(text, 'answer')

def extract_reason(text: str):
    return extract_tag(text, 'reason')

def extract_lemmas_from_outline(text: str) -> List[str]:
    """
    Extracts lemmas from the proof outline section.
    
    Args:
        text: Input text containing proof outline with lemma tags
        
    Returns:
        List of lemma strings extracted from the proof outline
    """
    # First extract the proof outline section
    outline_pattern = re.compile(r"<proof_outline>\s*(.*?)\s*</proof_outline>", re.DOTALL)
    outline_match = outline_pattern.search(text)
    
    if not outline_match:
        return []
    
    outline_content = outline_match.group(1)
    
    # Extract all lemmas from the outline
    lemma_pattern = re.compile(r"<lemma>\s*(.*?)\s*</lemma>", re.DOTALL)
    lemmas = lemma_pattern.findall(outline_content)
    
    return [lemma.strip() for lemma in lemmas]

def parse_proof_structure(text: str) -> Dict[str, any]:
    """
    Parses a structured proof text and extracts both informal proof and lemmas.
    
    Args:
        text: Input text containing informal proof and proof outline sections
        
    Returns:
        Dictionary with keys:
        - 'informal_proof': The extracted informal proof text (str or None)
        - 'lemmas': List of extracted lemmas (List[str])
    """
    informal_proof = extract_informal_proof(text)
    lemmas = extract_lemmas_from_outline(text)
    proof_sketch = extract_tag(text, 'proof_sketch')
    return {
        'informal_proof': informal_proof,
        'lemmas': lemmas,
        'proof_sketch': proof_sketch
    }

def remove_think_block(text: str) -> str:
    """
    Removes the <think> block from the given text.

    Args:
        text: Input text containing the <think> block
    Returns:
        Text with the <think> block removed
    """
    if '<think>' in text:
        think_pattern = re.compile(r"<think>(.*?)</think>", re.DOTALL)
        return think_pattern.sub("", text).strip()
    else:
        return text

def collapse_repeated_blocks(text: str,
                             max_block: int = 40,
                             min_repeats: int = 3) -> str:
    """연속으로 되풀이되는 줄 블록을 한 번만 남기고 접는다.

    왜 필요한가
      prover 가 증명을 못 찾으면 같은 사고 과정을 주석으로 수십 번 되풀이한
      출력을 낸다. 그 전문이 Lean 오류 메시지에 실려 다음 교정 프롬프트로
      들어가면서 컨텍스트 한도를 넘긴다.

      sketch6 r1 (2026-09-09) 실측: 오류 메시지 최대 63,130자 = 약 18,000 토큰.
      가장 큰 것은 7줄 블록이 78회 되풀이된 것이었고, reasoner 요청이
      33,582 토큰으로 한도(32,768)를 814 토큰 넘겨 거부됐다. 거부된 요청은
      빈 응답으로 돌아와 같은 프롬프트를 계속 재시도하는 루프가 됐다.

    왜 단순 줄 중복 제거가 아닌가
      같은 실측에서 "연속 동일 줄"은 0개였다. 반복 주기가 7줄이라 줄 단위로는
      안 잡힌다. 또 Lean 증명은 `ring`, `simp` 같은 줄이 정당하게 여러 번
      나오므로, 전역 줄 중복 제거는 증명 본문을 망가뜨려 모델이 고칠 수
      없게 만든다. 그래서 "연속으로 min_repeats 회 이상 되풀이되는 블록"만
      접는다. 정보량은 유지되고 중복만 사라진다.

    Args:
        text: 접을 대상 문자열.
        max_block: 탐지할 블록의 최대 줄 수. 주기가 이보다 길면 접지 않는다.
        min_repeats: 이 횟수 이상 되풀이될 때만 접는다. 2 로 두면 정당한
            반복(예: 같은 두 줄이 우연히 붙은 경우)까지 건드리므로 3 을 쓴다.

    Returns:
        접힌 문자열. 접을 것이 없으면 원본과 동일하다.
    """
    if not text:
        return text

    lines = text.split("\n")
    n = len(lines)
    out = []
    i = 0
    while i < n:
        hit = None
        # 주기가 짧은 것부터 찾는다. L=7 이 78회 반복이면 L=14 도 39회로
        # 걸리지만, 가장 작은 주기를 잡는 편이 접은 결과가 읽기 쉽다.
        for L in range(1, max_block + 1):
            if i + 2 * L > n:
                break
            block = lines[i:i + L]
            # 빈 줄만으로 된 블록은 접어도 의미가 없고 오히려 구조를 깬다
            if not any(x.strip() for x in block):
                continue
            k = 1
            j = i + L
            while j + L <= n and lines[j:j + L] == block:
                k += 1
                j += L
            if k >= min_repeats:
                hit = (L, k, j, block)
                break
        if hit:
            L, k, j, block = hit
            out.extend(block)
            out.append(
                f"-- <앞의 {L}줄 블록이 {k}회 되풀이되었습니다. "
                f"중복 {k - 1}회를 생략합니다.>"
            )
            i = j
        else:
            out.append(lines[i])
            i += 1

    return "\n".join(out)
