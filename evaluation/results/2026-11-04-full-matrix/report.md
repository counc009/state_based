# Full matrix results — 2026-11-04

All **2,520** planned cells reached a terminal status in **2,758** API attempts, from 2026-11-04T21:58:57.322614+00:00 to 2026-11-04T22:55:23.131491+00:00. There are 2,442 completed responses, 32 output-limited responses and 46 exhausted HTTP 524 gateway failures, all on DeepSeek V4.1. No cells remain pending and no budget guard was reached. Successful terminal outputs were not regenerated; a raw-attempt audit found zero cells with more than one completed attempt.

Primary “correct” means **structural normalized reference-effect agreement**, not independently established intent correctness or the paper's VM execution-test correctness. There are **1,479 / 2,520** matches overall. V3 has a higher observed match rate for each model. Opus V3 has 181/210 and Sol V3 180/210; their one-match difference and overlapping intervals do not establish a model ranking.

| Model | Prompt | n | Matches | Rate | 95% Wilson CI | Parse fail | Interp fail | Cost USD | Mean latency s |
|---|---|---:|---:|---:|---|---:|---:|---:|---:|
| claude-opus-5-5 | baseline | 210 | 85 | 40.5% | 34.1–47.2% | 10 | 103 | 1.4532 | 3.1 |
| claude-opus-5-5 | v3 | 210 | 181 | 86.2% | 80.9–90.2% | 1 | 1 | 3.5536 | 3.2 |
| deepseek-v4-flash | baseline | 210 | 71 | 33.8% | 27.8–40.4% | 32 | 121 | 0.0907 | 19.3 |
| deepseek-v4-flash | v3 | 210 | 165 | 78.6% | 72.5–83.6% | 1 | 12 | 0.1429 | 17.5 |
| deepseek-v4.1-flash | baseline | 210 | 85 | 40.5% | 34.1–47.2% | 22 | 93 | 0.7762 | 120.1 |
| deepseek-v4.1-flash | v3 | 210 | 165 | 78.6% | 72.5–83.6% | 1 | 7 | 1.3093 | 131.4 |
| glm-5.3 | baseline | 210 | 82 | 39.0% | 32.7–45.8% | 45 | 115 | 0.1689 | 1.8 |
| glm-5.3 | v3 | 210 | 149 | 71.0% | 64.5–76.7% | 16 | 27 | 0.6089 | 2.0 |
| gpt-6.1-sol | baseline | 210 | 88 | 41.9% | 35.4–48.7% | 10 | 94 | 0.5495 | 4.4 |
| gpt-6.1-sol | v3 | 210 | 180 | 85.7% | 80.3–89.8% | 0 | 1 | 0.3513 | 3.3 |
| qwen3.8-flash | baseline | 210 | 74 | 35.2% | 29.1–41.9% | 34 | 115 | 0.0740 | 5.5 |
| qwen3.8-flash | v3 | 210 | 154 | 73.3% | 67.0–78.9% | 2 | 32 | 0.1442 | 7.5 |


The denominator includes every planned cell, including API failures. Wilson intervals are descriptive and do not adjust for task/repeat correlation. Parse and interpretation failures overlap; interpretation failures include unsuccessfully processed returned outputs, while API failures have null native diagnostic fields. Mean latency sums request durations across attempts, excludes backoff, and omits cells with unknown interrupted duration. HIGH reasoning differs across providers; these are not equal-compute speed measurements.

## Costs and Claude funding

Matrix accounting: **$9.222650**. Including the $0.02 prior-smoke reserve: **$9.242650**, below $110. Claude matrix cost estimate/reservations: **$5.006835**; including the earlier single connectivity call: **$5.006983**, below $22. All 420 Claude cells are finished. Remaining Claude cells: **0**. **Required top-up: $0.00.** The earlier $54.84 figure was a conservative maximum-output reservation, not an expected invoice.

Costs use reported token usage at frozen rates; interrupted and unknown-billing gateway attempts retain conservative reservations. They are not invoices. Router rates assume USD/MTok because its catalog does not label units. Historical cache-write details were reconciled in the export (adjustment $0.001889). There are 272 recorded provider-error attempts and 12 interrupted unknown-billing attempts in addition to the returned responses. All remain in per-attempt files; no errors were dropped.

## Native diagnostics and reference limits

Across returned outputs, 2,300 parse, 1,757 pass semantic/effect processing and 1,753 complete native symbolic interpretation. The narrow independent NL directory/path obligation is present in 118 cases; it abstains on unsupported wording and is not a general intent judge. No LLM judge or generated Ansible execution was used in this matrix. Reference-playbook symbolic checks are recorded per cell.

The two supplied-reference control discrepancies remain unchanged and flagged: **a03**'s reference playbook fails program lowering (`string` versus `file_state`); **a20**'s rejects verification, with a separate earlier tab-versus-eight-spaces diagnostic. All 21 reference FQL queries process successfully. Primary results include these tasks; summary CSVs also give counts excluding their 20 cells per model/variant. See per-task files and `metadata.json` for the flags and sensitivity counts.

The paper's Table 2 is in `paper-baseline.csv`: GPT-4o 107/210, GPT-5 mini 89/210, and all other original models are included. Its total is 746/2,310. That study generated Ansible and called a program correct only if it passed all tests on all applicable VM systems. The new NL-to-FQL reference-effect rates are not directly comparable.

## Validation and reproducibility

22 Python tests pass; native `dune build @all` and `dune runtest` pass; `git diff --check` passes. The inherited Dune test source is empty, so substantive native controls come from the Python/native tests. Export validation checks 2,520 unique cells, ten repeats per task/model/variant, twelve 210-cell model/variant groups, 252 task groups, matching JSON/CSV counts and cost/summary totals, limits and original paper totals. `validation.json` records the result.

Public CSV/JSON omit secrets and raw private prompts/playbooks. Full immutable messages, references, raw attempts and native stdout/stderr remain preserved locally. `protocol.json`, model/prompt sources, module/binary hashes and the initial/resumed runner snapshots document execution. No charts were created. No additional paid run or open resource blocker remains for this completed cohort; the 46 exhausted provider failures are explicit outcomes requiring a separately approved rerun if desired.
