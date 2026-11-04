# Current main lineup and reasoning settings

Updated for Darsh's ten-repeat decision, 2026-11-04. Earlier six-model proposals are historical and are not the current matrix.

| Config key / exact model ID | Provider | Effort sent | Source / availability |
|---|---|---|---|
| sol / `gpt-6.1-sol` | OpenAI Responses API | `reasoning.effort: high` | [Official model](https://developers.openai.com/api/docs/models/gpt-6.1-sol); ten earlier smoke completions |
| opus / `claude-opus-5-5` | Anthropic Messages API | `output_config.effort: high` | [Latest Opus](https://platform.claude.com/docs/en/models/opus-5-5/overview); optional, key pending |
| `deepseek-v4.1-flash` | AgentFanClub Chat Completions | `reasoning_effort: high` | Authenticated router catalog; one accepted check |
| `deepseek-v4-flash` | AgentFanClub Chat Completions | `reasoning_effort: high` | Authenticated router catalog; one accepted check |
| `glm-5.3` | AgentFanClub Chat Completions | `reasoning_effort: high` | Authenticated router catalog; one accepted check |
| `qwen3.8-flash` | AgentFanClub Chat Completions | `reasoning_effort: xhigh` | HIGH rejected; router reports XHIGH as supported default |

All future matrix requests cap total provider output at 4,096 tokens (`max_output_tokens` for OpenAI, `max_tokens` for Chat Completions and Anthropic). No temperature/top-p/seed overrides or model tools are sent. Effort is per model in `configs/models.json`, not merely an agent preference. Exact body and URL are saved durably in the attempt ledger before network access and in response records, including failures. Frozen manifests contain all selected config and source hashes. Opus is excluded from default active selection and missing optional credentials never consume budget or block other models.

Anthropic's latest Opus page identifies `claude-opus-5-5`, with adaptive thinking always on and a default effort of medium; the runner explicitly selects HIGH. No Anthropic requests have been made. Its documented standard rates are $4 input / $20 output per million tokens, with $5 for 5-minute cache writes. Sol's documented rates are $2/$10 with $2.50 for cache writes. APIs remain provider model aliases, not invented immutable dated snapshots.

Router IDs/prices are documented in the captured [catalog](../configs/router-catalog-2026-11-04.json) and [connectivity report](router-connectivity.md). Routing effort acceptance, Qwen's catalog/error inconsistency and unconfirmed price units are retained explicitly. No local GPU or Delta allocation is needed for the new all-API matrix.

## Ten-repeat budget proposal

21 tasks × two prompt variants × ten repeats × five enabled models = **2,100 calls**, 420 per model. Claude is pending; including it would make 2,520 calls. Planning uses actual prompt-byte sizes plus framing margin and the 4,096 output cap, with no retry, batch or cache-hit discounts.

| Model | Calls without Claude | API envelope, USD |
|---|---:|---:|
| gpt-6.1-sol | 420 | 28.813275 |
| deepseek-v4.1-flash | 420 | 2.793868 |
| deepseek-v4-flash | 420 | 1.390699 |
| glm-5.3 | 420 | 13.445148 |
| qwen3.8-flash | 420 | 1.442295 |
| **Without Claude** | **2,100** | **47.885284** |
| Pending Claude addition | +420 | +57.626550 |
| All six, if enabled later | 2,520 | 105.511834 |

Router prices are assumed to be USD/MTok because its catalog omits units. Confirm that assumption before paid matrix approval; these are planning envelopes, not invoice guarantees. Baseline-only active five-model option is 1,050 calls, approximately $19.664098 under the same assumptions.

The old Sol smoke is preserved at five repeats per arm and is not relabeled as ten-repeat data. It called OpenAI directly at `https://api.openai.com/v1/responses` using exact request/returned ID `gpt-6.1-sol`, `reasoning.effort=high`, `max_output_tokens=4096`, `store=false` and no sampling overrides. Its usage-based estimate remains $0.012844, subject to provider billing.
