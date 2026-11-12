# Router identity and parameter checks, 2026-11-04

Source: authenticated GET `https://api.router.agentfan.club/api/models`, snapshot in `configs/router-catalog-2026-11-04.json`. The requested IDs match this primary router catalog. These are route IDs; underlying immutable publisher weight revisions are not exposed. Successful replies report `metadata.weight_version: default`, which is not an immutable research snapshot.

Transport: POST `https://api.router.agentfan.club/inference/v1/chat/completions`, bearer key from `AGENTFANCLUB_API_KEY`, base URL from `AGENTFANCLUB_BASE_URL`. Requests use `User-Agent: Astrogator-Evaluation/1.0`; the default Python user agent encountered HTTP 403 on initial catalog access. No provider key is in request artifacts or Git.

Each connectivity request used user content `Reply exactly OK.`, `max_tokens: 512` and `stream: false`. These are connectivity tests, not Astrogator results. No model received more than the authorized two requests.

| Route | Requests | Actual effort sent | Result and future configuration |
|---|---:|---|---|
| deepseek-v4.1-flash | 1 | `reasoning_effort: high` | HTTP 200, matching returned ID; HIGH configured |
| deepseek-v4-flash | 1 | `reasoning_effort: high` | HTTP 200, matching returned ID; HIGH configured |
| glm-5.3 | 1 | `reasoning_effort: high` | HTTP 200, matching returned ID; HIGH configured |
| qwen3.8-flash | 2 | First omitted; second `high` | First HTTP 200; second HTTP 400: `Unexpected reasoning effort high. Supported types are xhigh (default), medium, and low.` Explicit XHIGH configured from the reported default; no third call |

The catalog marks Qwen `reasoning: false`, yet its successful default response reports reasoning tokens and its error lists supported effort levels. Preserve that inconsistency rather than claiming the Boolean fully specifies behavior. All three HIGH requests were accepted, but HTTP acceptance does not independently prove how the router maps effort internally. The explicit XHIGH request has not been independently live-tested; its support is established by the router's supported-values error, with the first default-XHIGH call as connectivity evidence.

Raw requests, responses, token usage, timestamps and the rejected Qwen body are preserved in ignored `results/router-connectivity-2026-11-04/`. Four calls completed and one parameter-validation request was rejected. No matrix cells were collected.

## Prices and unit limitation

The catalog reports these `cost.input` / `cost.output` values:

| ID | Input | Output |
|---|---:|---:|
| deepseek-v4.1-flash | 0.256856 | 0.930653 |
| deepseek-v4-flash | 0.161857 | 0.371460 |
| glm-5.3 | 1.321413 | 4.248318 |
| qwen3.8-flash | 0.142798 | 0.452902 |

The response does not label currency or token denominator. Current estimates **assume USD per million tokens** and explicitly carry that assumption in config and estimate metadata. `/docs` and `/openapi.json` returned 404; no public schema confirming units was found. Confirm units with the router operator before approving the paid matrix. The runner's budget reservation cannot turn an unverified unit assumption into a billing guarantee.
