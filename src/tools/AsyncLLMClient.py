#
# For licensing see accompanying LICENSE file.
# Copyright (C) 2025 Apple Inc. All Rights Reserved.
#
import asyncio
import logging
import copy
import traceback
from typing import List, Dict, Any, Optional
import httpx
import openai

logger = logging.getLogger(__name__)
OPENAI_REASONING_MODELS = {'o1', 'o3', 'o4-mini', 'gpt-5-nano', 'gpt-5-mini', 'gpt-5'}

class AsyncLLMClient:
    """
    An async unified wrapper class for sending requests to LLM endpoints.
    
    This class provides a clean async interface for interacting with OpenAI API, with support for direct URL configuration,
    and multi-turn conversation management.
    """
    
    def __init__(
        self,
        base_url: Optional[str] = None,
        model_name: str = None,
        timeout: int = 2400,
        default_headers: Optional[Dict[str, str]] = None
    ):
        """
        Initialize the async LLM client wrapper.
        
        Args:
            base_url: Direct base URL for the API endpoint
            timeout: Request timeout in seconds (default: 2400)
            model_name: Which model name to use for API endpoint
            default_headers: Additional headers to include in requests
        """
        self.timeout = timeout
        self.base_url = base_url
        self.default_headers = default_headers or {}
        self.model_name = model_name
        
        # Initialize clients and session
        self.client = None
        self.http_client = None
        self._initialized = False
        
        # Multi-turn conversation support
        self.conversation_history: List[Dict[str, str]] = []
        self.system_message: Optional[str] = None
        
        # Store last response for extended thinking access
        self._last_response = None

        logger.info("OpenAI async client initialized with base URL: %s", self.base_url)

    async def __aenter__(self):
        """Async context manager entry."""
        await self._initialize()
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        await self.close()
    
    async def _initialize(self):
        """Initialize the async clients."""
        if self._initialized:
            return
        
        # Default to OpenAI client

        if not self.base_url:
            raise ValueError("`base_url` is not provided")
            
        # httpx 기본 설정을 그대로 쓰면 커넥션 교착이 발생한다.
        #
        # 무슨 일이 있었나
        #   17시간짜리 배치가 16:00 에 조용히 멈췄다. 서버(prover, Lean)는 모두
        #   정상이었고(HTTP 200, finish_reason error 0), Lean 은 0.02초에 응답했다.
        #   그런데 클라이언트 소켓 15개가 전부 CLOSE_WAIT 였고 ESTABLISHED 는 0개,
        #   프로세스는 ep_poll 에서 잠든 채 11시간 동안 요청을 한 건도 보내지 않았다.
        #
        # 왜
        #   httpx 기본값은 keepalive 연결을 풀에 유지한다(keepalive_expiry=5초,
        #   max_keepalive_connections 무제한). 서버가 닫은 연결이 CLOSE_WAIT 로
        #   풀에 남고, 그걸 재사용하려다 막히면 새 요청을 만들지 못한다.
        #   게다가 timeout 을 스칼라로 주면 connect/read/write/pool 이 모두 그 값이
        #   되어(2400초), 풀 대기까지 40분씩 잡아먹는다.
        #
        # 대응
        #   max_keepalive_connections=0 : 요청마다 새 연결을 쓰고 끝나면 닫는다.
        #                                 CLOSE_WAIT 가 쌓일 자리가 없어진다.
        #                                 로컬 vLLM 이라 연결 비용은 무시할 수준이다.
        #   pool=60                     : 풀이 막히면 60초 뒤 예외가 난다. 그 문제
        #                                 하나만 실패하고 배치는 계속된다.
        #   connect=10                  : 로컬 서버 연결에 40분을 줄 이유가 없다.
        #   read=self.timeout           : 생성 대기는 기존대로 길게 유지한다.
        self.http_client = httpx.AsyncClient(
            limits=httpx.Limits(
                max_connections=64,
                max_keepalive_connections=0,
            ),
        )
        self.client = openai.AsyncOpenAI(
            base_url=self.base_url,
            default_headers=self.default_headers,
            timeout=httpx.Timeout(
                connect=10.0,
                read=float(self.timeout),
                write=60.0,
                pool=60.0,
            ),
            max_retries=3,
            http_client=self.http_client,
        )
        
        self._initialized = True
    
    async def close(self):
        """Close async clients and clean up resources."""
        if self.client and hasattr(self.client, 'close'):
            await self.client.close()
        if self.http_client:
            await self.http_client.aclose()
        self._initialized = False
    
   
    async def chat_completion(
        self,
        messages: List[Dict[str, str]],
        max_tokens: int = 200,
        temperature: float = 0.6,
        **kwargs
    ) -> str:
        """
        Send an async chat completion request to the LLM endpoint.
        
        Args:
            messages: List of message dictionaries with 'role' and 'content' keys
            temperature: Sampling temperature (default: 0.6)
            max_tokens: Maximum tokens to generate (default: 200)
            **kwargs: Additional parameters to pass to the API
            
        Returns:
            String containing the assistant's response
            
        Raises:
            Exception: If the API request fails
        """
        if not self._initialized:
            await self._initialize()
        
        try:
            if 'reasoning' in kwargs and self.model_name not in OPENAI_REASONING_MODELS:
                # ignore it
                kwargs.pop('reasoning', None)
            return await self._openai_chat_completion(messages, max_tokens, temperature, **kwargs)
            
        except Exception as e:
            logger.error("Async chat completion request failed: %s", e)
            traceback.print_exc()
            raise
    
    async def _openai_chat_completion(
        self,
        messages: List[Dict[str, str]],
        max_tokens: int,
        temperature: float,
        **kwargs
    ) -> str:
        """Handle async OpenAI chat completion requests."""
        if self.model_name in OPENAI_REASONING_MODELS:
            temperature = 1.0
        temperature_error_count = 0
        while True:
            try:
                completion = await self.client.chat.completions.create(
                    messages=messages,
                    model=self.model_name,
                    max_completion_tokens=max_tokens,
                    temperature=temperature,
                    **kwargs
                )
                self._last_response = completion
                output_text = completion.choices[0].message.content
                
                logger.debug("Async OpenAI chat completion request successful")
                return output_text
            except openai.RateLimitError:
                logger.warning("Rate limited (429), sleeping for 5 seconds...")
                await asyncio.sleep(5)
                continue  # Retry without counting towards retry limit
            except openai.BadRequestError as e:
                if "Unsupported value: 'temperature'" in str(e):
                    # set temperature to 1 and retry
                    temperature = 1.0
                    temperature_error_count += 1
                    if temperature_error_count > 1:
                        raise e

            except Exception as e:
                logger.error("Async chat completion request failed: %s", e)
                raise e

    async def simple_chat(
        self,
        prompt: str,
        system_message: Optional[str] = None,
        max_tokens: int = 200,
        temperature: float = 0.6,
        **kwargs
    ) -> str:
        """
        Send an async simple chat request with a single user prompt.
        
        Args:
            prompt: User prompt/question
            system_message: Optional system message to set context
            **kwargs: Additional parameters to pass to chat_completion
            
        Returns:
            String containing the assistant's response
            
        Raises:
            Exception: If the API request fails
        """
        messages = []
        
        if system_message:
            messages.append({"role": "system", "content": system_message})
        
        messages.append({"role": "user", "content": prompt})
        
        try:
            response = await self.chat_completion(messages=messages, 
                                                max_tokens=max_tokens,
                                                temperature=temperature,
                                                **kwargs)
            return response
        except Exception as e:
            logger.error("Failed to get response: %s", e)
            raise
    
    async def health_check(self) -> bool:
        """
        Check if the LLM endpoint is healthy and responding.
        
        Returns:
            True if the endpoint is healthy, False otherwise
        """
        try:
            test_messages = [{"role": "user", "content": "Hello"}]
            await self.chat_completion(
                messages=test_messages,
                max_tokens=1,
                temperature=0.0
            )
            logger.info("Async health check passed")
            return True
        except Exception as e:
            logger.warning("Async health check failed: %s", e)
            return False
    
    def set_system_message(self, system_message: str) -> None:
        """
        Set the system message for multi-turn conversations.
        
        Args:
            system_message: The system message to use for conversations
        """
        self.system_message = system_message
        logger.debug("System message set for multi-turn conversations")
    
    def start_conversation(self, system_message: Optional[str] = None) -> None:
        """
        Start a new multi-turn conversation, clearing any existing history.
        
        Args:
            system_message: Optional system message to set for this conversation
        """
        self.conversation_history = []
        if system_message:
            self.system_message = system_message
        logger.debug("Started new multi-turn conversation")
    
    def add_message(self, role: str, content: str) -> None:
        """
        Add a message to the conversation history.
        
        Args:
            role: The role of the message sender ('user', 'assistant', or 'system')
            content: The content of the message
        """
        if role not in ['user', 'assistant', 'system']:
            raise ValueError(f"Invalid role: {role}. Must be 'user', 'assistant', or 'system'")
        
        self.conversation_history.append({"role": role, "content": content})
        logger.debug("Added %s message to conversation history", role)
    
    def get_conversation_history(self) -> List[Dict[str, str]]:
        """
        Get the current conversation history.
        
        Returns:
            List of message dictionaries with 'role' and 'content' keys
        """
        return copy.deepcopy(self.conversation_history)
    
    def clear_conversation(self) -> None:
        """Clear the conversation history."""
        self.conversation_history = []
        logger.debug("Cleared conversation history")
    
    async def continue_conversation(
        self,
        user_message: str,
        n: int = 1,
        max_tokens: int = 200,
        temperature: float = 0.6,
        **kwargs
    ) -> str:
        """
        Continue the multi-turn conversation with a new user message.
        
        Args:
            user_message: The user's message to add to the conversation
            temperature: Sampling temperature (default: 0.6)
            n: Number of completions to generate (default: 1)
            **kwargs: Additional parameters to pass to the API
            
        Returns:
            String containing the assistant's response
            
        Raises:
            Exception: If the API request fails
        """
        # Add user message to conversation history
        self.add_message("user", user_message)
        
        # Build messages list for API call
        messages = []
        if self.system_message:
            messages.append({"role": "system", "content": self.system_message})
        messages.extend(self.conversation_history)
        
        try:
            response = await self.chat_completion(
                messages=messages,
                n=n,
                max_tokens=max_tokens,
                temperature=temperature,
                **kwargs
            )

            assistant_response = response
            
            # Add assistant response to conversation history
            self.add_message("assistant", assistant_response)
            
            return assistant_response
            
        except Exception as e:
            logger.error("Failed to get conversation response: %s", e)
            raise
    
    def get_conversation_length(self) -> int:
        """
        Get the number of messages in the conversation history.
        
        Returns:
            Number of messages in conversation history
        """
        return len(self.conversation_history)
    
    def truncate_conversation(self, max_messages: int) -> None:
        """
        Truncate conversation history to keep only the most recent messages.
        
        Args:
            max_messages: Maximum number of messages to keep
        """
        if max_messages < 0:
            raise ValueError("max_messages must be non-negative")
        
        if len(self.conversation_history) > max_messages:
            self.conversation_history = self.conversation_history[-max_messages:]
            logger.debug("Truncated conversation history to %d messages", max_messages)

    def get_last_response_raw(self) -> Optional[Any]:
        """
        Get the raw response object from the last API call.
        
        Returns:
            The raw response object, or None if no response has been made
        """
        return self._last_response
    
    def get_model_info(self) -> Dict[str, Any]:
        """
        Get information about the current model configuration.
        
        Returns:
            Dictionary containing model information
        """
        return {
            'model_name': self.model_name,
            'base_url': self.base_url,
            'timeout': self.timeout,
            'async': True
        }