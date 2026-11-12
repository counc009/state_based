# External dataset: NL-to-FQL validity counts

This experiment counts strict raw-output grammar parsing, semantic acceptance and native symbolic interpretation. It has no gold FQL, reference-effect comparison, execution tests, LLM output judge or correctness claim. Original NL descriptions and Ansible implementations stay private.

## Source and deadline subset

Source: `/tmp/AnsibleDataset/withheld_ftdata-new.json`, SHA-256 `4800b0c38ceca7d24458d5ed40709f5ca94cda6b583fe8618045b4aee8185e74`, 13,239 rows. The 1,646-row small file is not used. Free heuristics retain 10,788 rows (9,822 distinct normalized NL names); drops are 1,469 excluded task styles, 893 without candidate concrete objects, 89 unresolved Jinja inputs.

The full detail filter was started, then the user authorized an early random-subset cutoff for the paper deadline. Classification batches are ordered by SHA-256 of normalized NL, independent of repository order. The analysis cohort is the complete first 50 batches: the 1,000 smallest distinct NL digests, including all 1,093 matching source rows. This is deterministic bottom-hash sampling of NL clusters, not a fixed-size uniform sample of duplicate source rows. Every batch in this prefix had a valid completed label before sampling; API completion order does not select cohort members.

Within this subset: 1,093 rows classified, 311 classifier-kept, 300 source rows sampled without replacement with seed 20261112. The sample contains 253 distinct NL names. Duplicate source rows remain distinct and receive separate fresh generation calls. Before the cutoff the classifier also labeled 3,172 rows outside the cohort, 4,265 rows in total; those extra labels remain in the audit exports but never enter this sample. The 311-kept count applies to the 1,093-row cohort.

The filter judges NL self-containment only. The optional Ansible text is inspected solely for excluded top-level debug/assert/include/set_fact-style modules; no implementation/metadata is model context. Classifier batches contain only opaque IDs and NL. FQL expressibility is not a filter. A conservative lexical KB hint is recorded separately and is not a support oracle. Labels are the frozen LLM classifier's decisions, not manually validated truth. Some kept rows can still omit contextual detail; no labels are changed after looking at generation outputs.

## Frozen generation

Six models: `gpt-6.1-sol`, `claude-opus-5-5`, `deepseek-v4.1-flash`, `deepseek-v4-flash`, `glm-5.3`, `qwen3.8-flash`; one call per sampled row/model, 1,800 planned cells. System prompt: handbook-v3. Four fixed demonstrations: a13, a02, a03, a19, the first historical target's set; this is an explicit new-dataset policy, whereas the November 4 benchmark used per-target sets. Leading `name:` and surrounding whitespace are stripped. No Ansible implementation, classifier decision, gold query or repository metadata enters generation.

HIGH reasoning (Qwen XHIGH), 32,768 maximum output tokens, no temperature/top-p/seed. Provider request settings/hashes, returned IDs, tokens, timings, retry history and cost accounting are exported. Dedicated model pools start DeepSeek V4.1/Qwen first, initially with 32 workers each; DeepSeek V4/GLM 24 each; Sol/Opus 8 each, under one shared budget ledger. Temporary reservations can delay admissions; completed cells are preserved on resume.

Guards: $20 total including the classifier, and $8 Anthropic, separate from the held-out job. Transient/524 errors are retried up to 8 attempts with backoff. Unknown gateway/interrupted billing retains the full conservative reservation. Operator cutoff/resizing events are preserved in manifest.json; accounting is reported-token cost plus unknown-billing reserves, not an invoice. The manifest and per-attempt CSV reconcile every charged/reserved attempt.

## Diagnostic definitions

- `parsed`: the existing native lexer/parser accepts a nonempty query. Raw prose, Markdown fences and empty responses fail; no extraction/repair is applied.
- `semantic_accepted`: existing `Semant.analyze_top` returns `Ok`. A diagnostic flag records this before effect serialization, so a serializer error cannot masquerade as a semantic rejection. Grammar/semantics are unchanged.
- `interpreted`: semantic acceptance and native `query_interp` exits zero using the repository's module definitions. This is symbolic interpretation; it does not execute Ansible or management commands.

Some unsupported requests lead to prose explanations instead of FQL, while invented KB objects can parse but fail semantic processing. These counts measure pipeline-stage acceptance, not intent correctness. API failures, cap-limited responses and budget-pending cells are separate fields, retained in the denominator of 300 planned rows per model.

## Files and replay

- `model-summary.csv`: per-model counts out of 300; generation-only per-model cost.
- `per-cell.csv` / `.json`: every planned cell, stage flags, IDs/hashes, status, usage, cost, timing and output hash.
- `filter-decisions.csv`, `sample-ids.csv`: source path, zero-based row index, raw-input SHA-256, normalized-NL SHA-256, classifier labels and explicit `in_filter_subset`/sample membership; no bulk source NL/YAML.
- `per-attempt.csv`: all classifier/generation attempts, including transient/interrupted history.
- `classifier-outputs.json`: opaque-ID detail labels/reason codes; no task text.
- `native-diagnostics.json`, `outputs/<model>/<row-id>.txt`: model outputs and native evidence.
- `manifest.json`, `sources/`: model/settings/cost/funnel/provenance, exact generation-freeze runner/transport/prompt/demo snapshots and filter prompt/rubric.

With privately supplied source data and provider credentials, the current code reproduces the subset protocol using:

```sh
opam exec -- dune build evaluation/native/effects.exe bin/query_interp.exe
python3 evaluation/code/dataset_validity.py all \
  --source /private/withheld_ftdata-new.json \
  --hash-prefix-batches 50 \
  --run evaluation/results/my-dataset-validity \
  --credentials-file /private/provider-credentials.json
```

New stochastic classifier labels may differ; the exported IDs/labels/sample hashes define this frozen cohort. The historical run paid for extra labels before cutoff; a fresh prefix-only run will not reproduce that discarded operational work/cost. Never commit `private/` or force-add this whole directory recursively.


A runtime scheduling fix gives each model its own readmission loop after temporary reservations settle, avoiding an idle Claude queue behind the slow router cohort. Pending cells resumed with DeepSeek V4 Flash concurrency 64; all API prompts/settings and completed outputs were preserved. The 24 active interrupted requests retain their full $0.342304671862 reservation plus immutable attempt history. Initial settings, runtime invocations/source snapshots and all operator events are retained in the manifest.

`per-attempt.csv` includes the provider usage JSON (including cache billing fields) for independent cost reconstruction. Per-cell latency sums request durations across attempts; it excludes backoff, queue admission and native diagnostic time.

Toolchain versions and native source hashes are recorded in `toolchain.json`. Frozen-rate costs are locally reconstructed from provider usage/cache fields; router catalog prices use USD per million tokens as the documented accounting assumption.

## Deadline publication

Generation is stopped; no more gateway retries will run. Of 1,800 planned cells, 1,761 returned complete responses, 20 exhausted API retries, and 19 remain budget-pending. All unavailable outputs are separate from parsing results. DeepSeek V4 Flash accounts for all 39 unavailable cells. There were no in-flight requests at the final stop.

Total local accounting is $19.985888492705: $1.203712406450 classification and $18.782176086255 generation. This includes $10.526035672359 of conservative unknown-billing reservations for interrupted/transient requests that returned no usage; usage-priced receipts account for $9.459852820346. These are not provider invoices. Repeated gateway/stream failures, whole-cap reservations on attempts without usage, and extra classification before cutoff explain approaching the $20 guard. Anthropic accounts for $6.290804, below its $8 guard. See per-attempt.csv for the full audit.
