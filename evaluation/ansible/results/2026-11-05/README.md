# NL-to-Ansible handoff for Aaron

Generation only: Appendix B prompt, 21 original tasks × six models × ten samples = 1,260 planned calls. HIGH effort is sent for five models; Qwen receives XHIGH. The initial output cap was 4,096 tokens, including provider-counted reasoning. Only the 133 original length-limited cells were rerun at 32,768 tokens; the 1,127 originally completed cells retain their original answers and cap. There is one user message and no added system prompt, temperature, top-p or seed. The six connectivity/preflight cells are included in the 1,260, not extra samples.

## Feed into executor.py

1. Copy the six model directories here into the working directory containing the original `astrogator-eval/executor.py`. Keep `p01`–`p20`, including separate `p11a` and `p11b`, and the original `response0.yml`–`response9.yml` filenames.
2. Set its model list to `gpt-6.1-sol`, `claude-opus-5-5`, `deepseek-v4.1-flash`, `deepseek-v4-flash`, `glm-5.3`, and `qwen3.8-flash`.
3. Remove the upstream debugging assignment `problems = [('p19', vms, 1, None)]` to restore the full problem list. Use Aaron’s existing VM snapshots and setup/verify fixtures.
4. Read the status/check columns before execution. Missing files are explicit extraction failures, provider failures or budget-pending cases. Incomplete responses remain labeled, even when they extract successfully. No substitute playbooks were invented.

## Artifacts

- `offline-checks.csv`: all 1,260 planned cells, generation statuses, YAML/nonempty/syntax checks, prohibited-module flags, usage, costs and timings. Diagnostic newlines are escaped.
- `model-summary.csv`: counts per model. These measure format/tool acceptance, **not correctness**.
- `manifest.json`: exact prompt, task text/mapping, model IDs/settings, source hashes, timestamps, usage, per-attempt accounting and per-sample hashes; full diagnostics retained.
- `raw-completions.jsonl`: each sampled answer before extraction, including empty and incomplete outcomes. Credentials and private reasoning are excluded.
- `task-map.csv`: explicit original problem mapping; dataset IDs a01–a21 are not sequential paper problem numbers.

Extraction follows the original `new_extract.py` fence regex and native `processing.ml` wrapper, preserving its host sets and task/handler/vars behavior. The adapter changes only model arguments and missing-file handling. Raw answers preserve any fields discarded by that historical wrapper.

Only free YAML parsing, extracted nonemptiness, nonempty tasks, Ansible syntax acceptance and shell/command/raw/script flags were checked. Syntax checks use Ansible-core 2.19.11/builtin collections in a restricted local process with no network or credentials. Missing external collections can cause failures. **No generated tasks, VMs, Docker runtime, Astrogator verifier or LLM judge were run.**

The verbatim Appendix B text was supplied by Darsh; the POPL PDF itself was in the orchestrator’s workspace. Durable resume/retries and the $25 total/$15 Anthropic guards apply to this run independently of the historical FQL ledger. The manifest reports token-priced local accounting plus any unknown-billing reserve, not provider invoices; router rates assume USD/MTok.

See the [generation guide](../../README.md) for setup, protocol and credential-free integrity/extraction replay commands, with optional repeated free syntax checks.

## Run outcome after the cap amendment

The original 133 length-limited samples reflected the operator’s 4,096-token budget, not model failure. All 133 were rerun with the same prompt/reasoning and seed-free sampling at 32,768 tokens, within the authenticated router catalog limits. The only request-body change is `max_tokens`. A separate **$5 extra** guard bounds the resumable amendment; the larger streams have a 3,600-second overall deadline and the same 180-second idle timeout.

Of those reruns, 132 completed and one again reached the cap: **DeepSeek V4 Flash, a21/p20, repeat index 5 (`response5.yml`)**. All 32,768 reported output tokens were reasoning, so that cell has no extracted playbook. No generation API failures, retries or budget-pending cells occurred. The other 1,127 originally completed cells received no new calls and their raw answers and 1,115 extracted files remain unchanged.

The canonical 1,260 rows now contain 1,259 completed answers and one capped answer. There are **1,247 nonempty files**, **1,216 syntax passes**, **31 syntax failures**, and **four prohibited-module flags**. Thirteen cells have no extracted file, including the twelve originally completed but unparseable answers that were outside the authorized rerun selection. All checks remain format/tool acceptance counts, not correctness.

Extra token-accounted spend: **$0.508369224183**. Cumulative spend including the original run: **$4.450298371772**; Anthropic remains **$2.111640**, with no new Anthropic calls. Unknown-billing reserve is $0. These are frozen-rate local costs, not provider invoices.

`history/cap-4096/` preserves the original manifest, CSVs, raw answers, validation and selected old files. `attempt-history.csv` and `.jsonl` retain all **1,393 attempts**, including phase, cap, stop reason, usage and cost; JSONL also retains answer text without private reasoning. Canonical `offline-checks.csv` usage/cost fields aggregate all attempts; `canonical_*` fields identify the chosen answer’s usage, attempt and phase. Per-cell `max_output_tokens` and manifest cap overrides make the mixed budget profile explicit. `still_at_cap` records a budget-limited outcome, not a correctness failure.

See `validation.json` for 35 passing tests, native build, complete export/history integrity, unchanged-completed-cell proofs, actual request-body hashes and byte-for-byte public extraction replay. The initial run began November 5 UTC; this amendment completed November 6 UTC. No generated tasks, VMs, Docker runtime, Astrogator verifier or LLM judge ran.
