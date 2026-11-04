# Approved full NL-to-FQL matrix — 2026-11-04

21 tasks × 6 models × 2 prompts × 10 repetitions = 2,520 planned cells. All rows, including failures and any budget-pending cells, remain in the denominator. No charts are produced.

## Definitions

- Primary `correct`: `ref_match == true`, structural equality of normalized effect trees against the source-supplied reference FQL. This is **not** a proof of intent adequacy, behavioral equivalence or the paper's execution-based correctness.
- `parsed`: native lexer/parser accepted the raw string. `semantic_accepted`: the semantic analyzer and effect serializer accepted it. Output is never silently repaired or stripped of code fences.
- `interpreted`: native query lowering/symbolic interpretation succeeded. This runs no generated Ansible or shell commands.
- `nl_obligation`: the independent narrow `Create directory /PATH` requirement check; unsupported task wording abstains. It does not consult reference FQL. The raw diagnostics also flag extra actions for review.
- `reference_program_status`: symbolic verification against each supplied reference playbook; acceptance may carry assumptions/residual effects.
- a03 and a20 carry `reference_discrepancy=true`: their source-supplied playbooks respectively fail native program lowering and reject verification. Their reference FQL processes successfully. Originals are unchanged. Primary rates include them, with separate counts excluding them for sensitivity.
- `n`: all planned cells per group, not just successfully completed API responses. Wilson intervals are descriptive 95% binomial intervals; repeated samples and tasks are correlated, so these are not a claim of independent task generalization.
- `syntax_parse_fail` counts attempted outputs whose parser rejects; `semantic_fail` counts parsed outputs rejected by semantic processing; `interp_fail` includes unsuccessful query interpretation. Pending calls are separate.
- Per-call latency sums request durations across attempts, excluding retry backoff. Costs include all attempts. Token fields sum reported usage across attempts; `tokens_complete=false` flags unknown-billing usage. Missing reasoning-token fields stay null. Latency stays null if any attempt duration is unknown. Provider-reported reasoning tokens are a subset of output tokens and are not added again.
- `cost_usd` is an estimate from reported tokens and frozen standard rates; unavailable usage and interrupted requests retain their full conservative reservation. It is not an account invoice. Router catalog units are assumed USD per million tokens. Prior smoke costs have a separate conservative reserve, never charged to matrix rows.

## Files

- `per-call.csv`, `per-call.json`: one row for every planned model/variant/task/repeat, aggregating attempt costs/tokens and retaining error history.
- `per-attempt.csv`, `per-attempt.json`: one row per actual API attempt, preserving individual transient failures, interruptions and retries.
- `model-variant-summary.csv`: model × prompt totals, primary rates, Wilson intervals, failures, cost and mean latency.
- `task-model-variant.csv`: corresponding per-task breakdown.
- `paper-baseline.csv`: original Table 2 counts. These measure generated Ansible passing all VM execution tests on every applicable system; they are **not directly comparable** to NL-to-FQL reference-effect matching.
- `metadata.json`: costs, exact model IDs/rates/settings, source and binary/module hashes, and any remaining Claude funding requirement.
- `authorization.json`: approved limits and protocol.

Raw responses, full requests, native diagnostics, source references and the immutable manifest remain in ignored local run artifacts. Public tidy exports intentionally omit provider credentials, raw source playbooks and full prompt/task payloads. The checked-in prompts, runner, hashes and source references document how to reproduce the experiment with authorized inputs.

## Run and score

```sh
python3 evaluation/code/evaluate.py freeze --dataset evaluation/datasets/imported-private.json \
  --output evaluation/results/NEW-RUN/manifest.json
python3 evaluation/code/matrix_run.py --manifest evaluation/results/NEW-RUN/manifest.json \
  --output evaluation/results/NEW-RUN --workers 24 --total-budget-usd 110 --anthropic-budget-usd 22
python3 evaluation/code/export_matrix.py --run evaluation/results/NEW-RUN \
  --references evaluation/datasets/references-private.json
```

Supply model credentials as environment variables or an operator-owned private JSON via `--credentials-file`. Resume the same manifest/output; terminal responses are retained, transient failures receive at most four attempts total with exponential backoff. Each request is reserved durably before transmission. HTTP 408/409/425/429 and all 5xx, transport errors and interrupted unknown-billing attempts are transient. Unknown charges remain reserved. Non-transient errors and exhausted retries remain terminal. A skipped budget cell has no new attempt and can resume after funding and a provider-limit increase. Global limit cannot exceed $110.

Execution note: an early checkpoint added HTTP 524 to transient handling and corrected cache-write accounting. Interrupted in-flight attempts and the original gateway errors remain preserved, are charged conservatively when billing is unknown, and participate in retry limits. No successful output was regenerated. The initial and resumed runner source snapshots and hashes are retained for reproducibility.

## Completed cohort

See [the results report](report.md), [summary CSV](model-variant-summary.csv), [validation](validation.json), and [protocol](protocol.json). All 2,520 cells are terminal; there are no budget-pending cells and the remaining Claude top-up is $0.
