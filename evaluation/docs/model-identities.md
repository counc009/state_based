# Verified model identity and pricing

Checked against primary provider documentation on 2026-11-04. The candidate models are publicly documented text/code-capable models. Provider availability to this account remains separate from documentation: only OpenAI Sol was actually sampled. Names used as internal config keys are not sent as agent-model aliases.

| Config key | Provider; exact requested model ID | Primary identity source | Standard input / output USD per MTok |
|---|---|---|---:|
| astra | OpenAI; `gpt-6-astra` | [Official model page](https://developers.openai.com/api/docs/models/gpt-6-astra) | 10 / 50 |
| sol | OpenAI; `gpt-6.1-sol` | [Official model page](https://developers.openai.com/api/docs/models/gpt-6.1-sol) | 2 / 10 |
| fable | Anthropic; `claude-fable-5-1` | [Official model page](https://platform.claude.com/docs/en/models/fable-5-1/overview) | 10 / 50 |
| sonnet | Anthropic; `claude-sonnet-5-5` | [Official model page](https://platform.claude.com/docs/en/models/sonnet-5-5/overview) | 2 / 10 |
| qwen4 | Qwen publisher; `Qwen/Qwen3.5-4B` | [Publisher card](https://huggingface.co/Qwen/Qwen3.5-4B) | Local compute, unpriced |
| qwen9 | Qwen publisher; `Qwen/Qwen3.5-9B` | [Publisher card](https://huggingface.co/Qwen/Qwen3.5-9B) | Local compute, unpriced |

The two OpenAI pages provide pricing and cache-write/read rates. [Anthropic's pricing page](https://platform.claude.com/docs/en/about-claude/pricing) independently confirms both Claude rates, 5-minute cache writes at 1.25× input, one-hour writes at 2×, and current read prices. The implementation does not request one-hour caching, tools, search, fast mode or regional processing. It conservatively reserves the higher of base input and configured 5-minute-write rates. API aliases are not immutable dated snapshots; retain returned IDs and dates. The Qwen weight revision SHAs are in `configs/models.json`; no local inference has been performed.

## Exact smoke identity

- Transport: Python `urllib.request` over HTTPS to **`https://api.openai.com/v1/responses`** with the securely supplied OpenAI API key.
- Request body model: **`gpt-6.1-sol`**, ten requests; no agent CLI, model router, tools or browsing.
- Response body model: **`gpt-6.1-sol`** on all ten responses; raw bodies and usage are retained locally.
- Official suitability: the provider lists this API model for complex coding/text work, with selectable reasoning effort. The experiment used `high`, not the default medium.
- Therefore “Sol” in the smoke report is shorthand for the documented OpenAI API ID, not a substitute inferred from the coding agent's name. The API's returned ID does not expose immutable underlying weight identity; that remains a provider reproducibility limitation.

## Budget for a decision

All options below keep five repetitions and the same 21 task prompts. These are conservative envelopes from actual prompt-byte sizes plus framing margin and the 4,096 billable-output cap. They include configured 5-minute cache-write overhead, no cache/batch discount, no retries and no extra judging calls. Local compute/storage cost must be added separately.

| Option | API completions | Local completions | API planning envelope |
|---|---:|---:|---:|
| Full six models, baseline only | 420 | 210 | $71.80 |
| Sol only, both prompts | 210 | 0 | $14.41 |
| Sol + Sonnet, both prompts | 420 | 0 | $28.81 |
| Astra + Sol, both prompts | 420 | 0 | $86.44 |
| Full six models, both prompts | 840 | 420 | $172.88 |

The earlier $158.94756 estimate used base input rates; it is superseded for new full-run decisions because it omitted explicit cache-write overhead. The old manifests and actual $0.62773 smoke reservation are preserved as historical records. Reported smoke usage reconciles to $0.012844 at current standard/cache/write prices, not an invoice. A full matrix has not been authorized or run.
