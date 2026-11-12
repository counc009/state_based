# Missing-cell fill, separately funded

This phase targets exactly 141 cells without a prior model response: 39 original-prompt DeepSeek V4 Flash cells, 38 open-KB-prompt DeepSeek V4 Flash cells, and 64 open-KB-prompt Opus cells. All 3,459 previously completed answers and their canonical provider-response files are protected by SHA256. Invalid-but-existing formal queries are preserved and are not rerun.

The model IDs, full request messages, four demonstrations, HIGH reasoning, 32768-token cap and omission of temperature/top_p/seed remain unchanged. The Opus stage runs first (four workers), followed by DeepSeek across both source runs (64 workers). There are at most six attempts per fresh cell: initial plus five transient retries.

Start: **2026-11-12 23:19:04.742142 UTC**. Immutable deadline: **23:59:04.742142 UTC**. The fresh ledger has its own **$6 total / $3 Anthropic** guards. These funds are additional to the frozen original dataset $20/$8 and open-prompt $12/$7 initial phases. The initial classifier is counted only once. Costs are usage-priced receipts plus conservative unknown-billing reservations at frozen rates, not provider invoices.

## Offline overlay and audit

`evaluation/code/fill_finalize.py` reconciles complete durable receipts before marking genuinely interrupted requests unknown. It appends every fill attempt to the corresponding source ledger with a new monotonic per-cell index and explicit funding-phase/source-attempt/hash provenance. Earlier attempt files and ledger entries remain intact; old failed canonical receipts are archived before replacement. Only previously unavailable cells receive new canonical outputs. Repeated finalization is idempotent.

`pre-fill/original/` and `pre-fill/openkb/` freeze all 3,518 previous public export files, including the old baseline-invariance and unchanged-export audits. The private old manifests/ledgers and pre-reconciliation fill ledger remain private. `completed-preservation.json` protects all 3,459 previous answer/canonical hashes. Original exports are intentionally refreshed after the fill; the pre-fill snapshots preserve their earlier values.

The refreshed original prompt is first scored through Example and the evaluation-only fallback KB. The open prompt is then scored through both KBs, and the four-condition, paired, cross-model and rejection-reason tables are regenerated. Grammar/semantic/native interpretation counts are validity diagnostics, not intent correctness. “All models valid” means all six responded and all six were semantically accepted; conditional all-responding counts remain separately labeled. No model judge, VM, container or managed-host execution is used.

## Files

- `fill-per-cell.csv`/`.json`: the 141 target outcomes and canonical output links.
- `per-attempt.csv`/`.json`: the fresh phase's requests, tokens, costs and errors.
- `import-map.json`: fresh-to-cumulative attempt-index mapping and receipt hashes.
- `receipt-recovery.json`: any durable-receipt/canonical-file recovery.
- `cumulative-accounting.json`: original initial, open-prompt initial and fresh-fill costs; the fill is counted once, not once per KB.
- `validation.json`, `manifest.json`: phase guards/deadlines, unchanged answers, repricing and provenance evidence.
- Updated source exports remain at `../` and `../openkb-prompt/`, with their respective Example/fallback and four-condition tables.

Corpus files, original NL/Ansible rows, full message manifests and provider reasoning remain private. Public snapshots contain only already-published artifacts; fresh public data is limited to IDs/hashes, model outputs and counts.

## Completed result

All 141 missing cells are filled, so both prompt datasets now have 1,800 responses. The fresh phase used $1.961241648367 ($1.361642539608 reported-token cost + $0.599599108759 conservative reserves), including $1.141040 Anthropic. Cumulative dataset cost is $33.447268795585, counting the classifier and each generation phase exactly once. All 3,459 old answers and canonical provider responses are byte-identical; all 3,518 old public exports remain frozen in pre-fill/. See report.md for the current four-condition and strict-six-model counts.
