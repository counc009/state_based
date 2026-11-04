# V3 prompt and funding update — 2026-11-04

V3 is 1,069 whitespace-delimited words versus V2's 1,488: 419 fewer (28.2%). Compact-v1 and V2 remain unchanged. Demonstrations and target requests remain byte-for-byte identical between variants. V3 has not had a paid evaluation run.

## Current matrix

21 tasks × 10 repeats × 2 prompt variants × 6 models = 2,520 calls (420 per model). Variants: compact-v1 and handbook-v3. Opus is now enabled. No matrix run is authorized until Darsh approves the prompts and budget.

| Model | Calls | Conservative USD envelope |
|---|---:|---:|
| deepseek-v4-flash | 420 | $1.300523 |
| deepseek-v4.1-flash | 420 | $2.650766 |
| glm-5.3 | 420 | $12.708949 |
| opus | 420 | $54.840900 |
| qwen3.8-flash | 420 | $1.362738 |
| sol | 420 | $27.420450 |

Full matrix envelope: **$100.284326**; without Claude: **$45.443426**. Router catalog does not label currency/denominator; its quote assumes USD per million tokens and needs confirmation before paid approval. These are reservations using UTF-8 input bytes plus 4,096 framing tokens, the higher input/cache-write rate, and 4,096 output tokens per call, not predicted invoices.

## Claude token estimate and top-up

Official models endpoint and Anthropic documentation agree on latest Opus `claude-opus-5-5`. Standard rates: $4 input / $20 output per million tokens; 5-minute cache writes $5. Sources: https://platform.claude.com/docs/en/models/opus-5-5/overview and https://platform.claude.com/docs/en/build-with-claude/token-counting .

The free count_tokens endpoint counted all 42 unique task/variant messages, including the unchanged demonstrations. Multiplying by 10 repeats gives compact-v1 **143,810** and handbook-v3 **661,880**, total **805,690 input tokens**. At the 4,096-output-token cap for all 420 calls, token-count-based cost is **$37.629160** ($3.222760 input + $34.406400 output). This is an estimate; actual output consumption and billing are unknown. No explicit prompt caching is requested.

One authorized connectivity call used model `claude-opus-5-5`, `max_tokens:512`, `output_config:{"effort":"high"}`, and user text `Reply exactly OK.` It completed with 17 input / 4 output tokens (estimated $0.000148), no retries. This is connectivity evidence, not a prompt evaluation.

The user's approximately $24 balance permits a $22 matrix guard, retaining approximately $2. Based on provider input counts and maximum output, the estimated additional funding to retain that $2 is **$15.63**. To fund the runner's stricter conservative Claude reservation of **$54.840900**, retain the same $2, and cover the connectivity call, the calculated minimum top-up rounded up to cents is **$32.85**, assuming the starting balance was exactly $24 and no other spending. An exact invoice or exact top-up cannot be asserted from an approximate balance and unknown output usage. **$32.85 is the conservative approval figure; $15.63 is the token-count estimate.**

## Budget and resumption

`evaluation/configs/models.json` freezes `provider_budgets_usd.anthropic=22`. The runner reserves each call before sending it and counts all past attempts, including interruptions and errors, against that cap. It skips Claude cells that do not fit and continues other funded providers. Skipped cells have no attempt receipt and remain resumable. Credentials are never recorded.

After a top-up and explicit approval, resume the same immutable manifest/output directory with the same run command and `--anthropic-budget-usd 54.8409`; also supply an approved overall `--budget-usd` and `--max-calls`. The override changes accounting only. Existing calls are not repeated and their reservations are not reset. Raising the guard does not itself authorize a matrix run. The guard is a conservative local reservation limit, not a live account balance check; other account spending is outside it.

## Actual validation and remaining access

16 Python tests pass, including a simulated Claude cap, continued Sol calls, resumed remaining Claude calls, and zero duplicate calls on another resume. `opam exec -- dune build @all`, `opam exec -- dune runtest`, and `git diff --check` pass. Native compiler acceptance is separate from semantic adequacy; prior narrow semantic checks and reference limitations remain documented in `evaluation/docs/native-validation.md`. No V3 accuracy claim is available.

GitHub direct SDK read and branch-create attempts both reject with `Workspace has no GitHub repositories.` No PR exists. Attach counc009/state_based or an authorized fork to the connected workspace/environment to publish the preserved patch. No GitHub/Slack credentials were retrieved from the VPS.
