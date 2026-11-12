> Current canonical exports include the separately authorized missing-cell fill. All six models now have 300 responses; earlier partial counts below describe the preserved initial phase. Frozen initial files are in fill-in-2026-11-12/pre-fill/ (relative to the parent dataset directory). Current counts and cumulative phase costs are in fill-in-2026-11-12/report.md.

# Open package/service catalog prompt experiment

This is a separate generation experiment on exactly the same frozen 300 prior-work descriptions as the original dataset-validity run. Only the system prompt changes: `handbook-v3-openkb.txt` preserves handbook-v3 byte-for-byte and appends:

> OPEN PACKAGE AND SERVICE NAMES
> The package and service catalog lists examples. Unlisted packages and services may be named directly. Deployments may add package and service entries to the knowledge base.
> Return only the formal query.

The target NL and four demonstrations (a13, a02, a03, a19), their message order, all six model IDs and reasoning settings, 32768 output-token cap, one sample per model/description, and omission of temperature/top_p/seed remain unchanged. Original NL and Ansible source rows are private. Ansible output is absent from generation messages. No new filtering, source sampling or target-specific prompt tuning occurs in this experiment.

## Execution bounds

The paid controller started at **2026-11-12 22:09:28.745335 UTC**, with a persisted hard deadline of **22:44:28.745335 UTC**. It uses a separate zero-prior ledger and guards of **$12 total / $7 Anthropic**, including conservative in-flight and unknown-billing reservations. Each cell has at most three attempts (initial plus two transient retries). Billing errors stop new Opus admissions only. Successful cells are never repeated. Restarting the controller preserves the original deadline; it cannot extend the paid window.

Independent concurrent model pools launch in Opus/Sol, GLM, DeepSeek V4.1, Qwen, DeepSeek V4 order. This is concurrent launch order, not serial stage completion or guaranteed priority after each reservation settles. Conservative reservation guards dynamically constrain concurrency. At the deadline the supervisor terminates its own generation child, preserves unknown-billing receipts at their full reservations, and exports available responses. It does not run VMs, containers, generated tasks or a judge.

Unavailable rows distinguish provider/transport failures, explicit billing stops, final conservative budget gates, and the deadline. Where a cell was never admitted, its unavailable reason is classified from the final billing marker and conservative reservation gates before the deadline condition. Such rows are not parse failures. Costs are frozen-rate local accounting, not invoices; unavailable usage is never assumed free.

## Offline diagnostics

Generated text is passed unchanged through the existing grammar, semantic processing and native symbolic interpreter. `dual-kb/` uses the same outputs under:

- **Example**: the original closed example catalog.
- **Fallback**: the separately published evaluation-only package/service fallback KB; known-name behavior and all other errors remain unchanged.

The fallback changes neither the compiler nor the default Example KB. Its 21 supplied references and 2520 historical benchmark semantic/effect-match flags were checked independently before this run; native source hashes are verified against that audit. These are formal-query validity counts, not intent correctness or execution results.

## Artifacts and reproducibility

- `per-cell.csv`/`.json`: all 1800 planned cells with IDs/hashes, API status, output path, Example validity flags, token/cost history and settings.
- `outputs/<model>/<task-id>.txt`: canonical generated text only.
- `per-attempt.csv`/`.json`: every physical request, including retry failures, usage and conservative reserves.
- `sample-ids.json`: original path, row index and input/NL hashes for the identical 300-case sample.
- `generation-summary.csv`, `response-availability.csv`: available outputs and resource/API gaps separately.
- `dual-kb/`: both-KB per-cell/summary counts, remaining semantic rejection reasons and cross-model counts.
- `four-condition-summary.csv`/`.json`: original prompt + Example/fallback and open prompt + Example/fallback.
- `four-condition-rejection-reasons.csv`, `four-condition-cross-model.csv`, `native-failures.csv`: semantic and symbolic-interpreter diagnostics.
- `paired-available-summary.csv`: sensitivity restricted to each model's descriptions with responses from both prompt runs; availability and funding differ between experiments.
- `manifest.json`, `validation.json`, `report.md`: exact bounds, settings, provenance hashes, cost reconciliation, privacy checks and plain tables.
- `sources/`: the actual first-launch driver/transport, fixed project demonstrations and prompt snapshots; these contain no prior-work corpus rows or provider reasoning.

Run `python3 evaluation/code/openkb_prompt.py run` only within the original persisted window; expired windows make no further paid calls. Free finalization is `python3 evaluation/code/openkb_analyze.py --wait`. The native Example/fallback effects and query_interp binaries must already be built; no model API is used by finalization.

## Settled result

The supervisor stopped at 2026-11-12 22:44:28.762148 UTC. There are 1,698 completed outputs, no cap-limited outputs and no terminal API failures. Opus has 64 global-budget-pending cells (not billing failures); DeepSeek V4 Flash has 38 deadline-stopped cells: 13 interrupted requests and 25 never admitted. The sample has 300 rows and 253 distinct normalized descriptions.

Receipt reconciliation recovered one already-complete DeepSeek response missing from state/canonical output; the original ledger is preserved privately and `receipt-recovery.json` records the correction. Final accounting is $11.500138654513 = $6.792664830311 reported-token charges + $4.707473824202 unknown-billing reserves. Anthropic accounts for $4.241164; no billing stop occurred. All 1,791 original tracked exports match commit b9e9a06 byte-for-byte.

Generation charges in four-condition and paired CSVs repeat across the two KB conditions because each prompt was generated once and scored twice for free. Do not sum duplicate KB-row charges. Read response availability and paired-common-response counts alongside the full 300-row comparisons.

## Current post-fill publication

Open-KB handbook-v3-openkb now has 1,800 responses across the same 300 rows, with no previous answer replaced. Original initial funding limits remain historical; additional charges are allocated from the separately approved shared $6/$3 fill phase. See the parent fill-in-2026-11-12/cumulative-accounting.json and report.md for known/reserved costs and current four-condition counts. Source corpus, NL/Ansible and provider reasoning remain private.
