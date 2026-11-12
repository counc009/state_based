# NL-to-Ansible handoff for Aaron

Generation only: Appendix B prompt, 21 original tasks × six models × ten samples = 1,260 planned calls. HIGH effort is sent for five models; Qwen receives XHIGH. Output is capped at 4,096 tokens, including provider-counted reasoning where applicable. There is one user message and no added system prompt, temperature, top-p or seed. The six connectivity/preflight cells are included in the 1,260, not extra samples.

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

## Run outcome

All 1,260 cells returned in one attempt each: 1,127 completed and 133 output-limited. There were zero provider/transport failures and zero budget-pending cells. The historical extractor produced 1,119 nonempty files; 1,110 pass syntax and nine fail; four responses flag prohibited modules. Missing files remain explicit rows.

Token-accounted spend was **$3.941929147589 total**, including **$2.111640 Anthropic**, with zero unknown-billing reserve. Both guards were respected. See `validation.json` for test/build, integrity and full byte-for-byte extraction-replay results. This run began November 5 UTC and finished/checks completed November 6 UTC.
