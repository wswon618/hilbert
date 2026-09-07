#
# For licensing see accompanying LICENSE file.
# Copyright (C) 2025 Apple Inc. All Rights Reserved.
#
from dataclasses import dataclass
from typing import Dict, Any


@dataclass
class ProofAttemptConfig:
    """Configuration for all proof attempt limits and retry counts in HILBERTWorker.
    
    This class centralizes all the various iteration limits and attempt counts
    used throughout the proof generation pipeline, replacing the scattered
    num_passes variables with more descriptive names.
    """
    
    # Main proof generation attempts - parallel execution
    subgoal_decomp_attempts: int = 4           # For main subgoal decomposition attempts
    formal_proof_attempts: int = 4             # For formal prover LLM attempts
    
    # Error correction attempts - sequential execution with conversation context
    main_theorem_error_corrections: int = 4    # For correcting syntax/semantic errors in main theorem
    subgoal_error_corrections: int = 6         # For correcting errors in individual subgoals  
    missing_tags_error_corrections: int = 3    # For error correction when required tags/code blocks are missing from responses  
    
    # Verification and validation attempts
    parallel_subgoal_proof_attempts: int = 4    # For parallel verification of extracted subgoals
    
    # Sketch refinement attempts
    proof_sketch_corrections: int = 8          # For iteratively refining proof sketches when subgoals are invalid
    missing_subgoal_extraction_attempts: int = 3       # For attempting to extract missing subgoals from sketches
    
    # Timeout configurations
    proof_verification_timeout: int = 60       # Timeout for Lean proof verification

    # Limit LLM calls per worker
    max_prover_llm_calls: int = None  # Max calls to prover LLM per worker, None for unlimited
    max_reasoner_llm_calls: int = None  # Max calls to reasoning LLM per worker, None for unlimited
    # 문제 하나에 허용할 최대 실행 시간(초). None 이면 무제한.
    #
    #   호출 횟수 한도만으로는 실행 시간을 못 묶는다. 어려운 문제는 700회를
    #   소진하는 데 14시간이 걸렸고, 취소분이 예산을 갉아먹던 버그를 고친 뒤로는
    #   같은 한도를 채우는 데 그 두 배가 걸린다.
    #
    #   보관된 기록 109건으로 측정한 손익:
    #       제한 없음  성공 84/84  누적 182시간
    #        60분     성공 70/84  누적  48시간
    #       120분     성공 77/84  누적  67시간   ← 성공 92% 유지, 시간 63% 절감
    #       180분     성공 80/84  누적  83시간
    #   성공한 문제의 소요 중앙값은 9.5분인 반면, 실패한 문제는 13~18시간씩 태운다.
    per_problem_timeout_seconds: int = None
    
    @classmethod
    def from_dict(cls, config_dict: Dict[str, Any]) -> 'ProofAttemptConfig':
        """Create ProofAttemptConfig from dictionary, using defaults for missing keys."""
        return cls(
            subgoal_decomp_attempts=config_dict.get('subgoal_decomp_attempts', 4),
            formal_proof_attempts=config_dict.get('formal_proof_attempts', 4),
            main_theorem_error_corrections=config_dict.get('main_theorem_error_corrections', 4),
            subgoal_error_corrections=config_dict.get('subgoal_error_corrections', 6),
            missing_tags_error_corrections=config_dict.get('missing_tags_error_corrections', 3),
            parallel_subgoal_proof_attempts=config_dict.get('parallel_subgoal_proof_attempts', 4),
            proof_sketch_corrections=config_dict.get('proof_sketch_corrections', 8),
            missing_subgoal_extraction_attempts=config_dict.get('missing_subgoal_extraction_attempts', 3),
            proof_verification_timeout=config_dict.get('proof_verification_timeout', 60),
            max_prover_llm_calls=config_dict.get('max_prover_llm_calls', None),
            max_reasoner_llm_calls=config_dict.get('max_reasoner_llm_calls', None),
            per_problem_timeout_seconds=config_dict.get('per_problem_timeout_seconds', None),
        )
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert ProofAttemptConfig to dictionary."""
        return {
            'subgoal_decomp_attempts': self.subgoal_decomp_attempts,
            'formal_proof_attempts': self.formal_proof_attempts,
            'main_theorem_error_corrections': self.main_theorem_error_corrections,
            'subgoal_error_corrections': self.subgoal_error_corrections,
            'missing_tags_error_corrections': self.missing_tags_error_corrections,
            'parallel_subgoal_proof_attempts': self.parallel_subgoal_proof_attempts,
            'proof_sketch_corrections': self.proof_sketch_corrections,
            'missing_subgoal_extraction_attempts': self.missing_subgoal_extraction_attempts,
            'proof_verification_timeout': self.proof_verification_timeout,
            'max_prover_llm_calls': self.max_prover_llm_calls,
            'max_reasoner_llm_calls': self.max_reasoner_llm_calls,
            'per_problem_timeout_seconds': self.per_problem_timeout_seconds
        }
