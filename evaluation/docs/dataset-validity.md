# NL-only dataset validity experiment

This workflow filters short task names for self-contained action detail, samples up to 300 source rows, generates handbook-v3 FQL once per row/model, and counts native diagnostic stages separately. There are no references, execution tests, output judges or correctness claims.

Source data stays outside Git. Input is a JSON array of strings or objects with an `input` task-name string. An optional `output` Ansible string is used only by the free screen to identify explicitly excluded top-level debug/assert/include/set_fact-style modules; it is never supplied to a model. Other source metadata is not model context. A leading `name:` is stripped. See [the frozen filter rubric](dataset-detail-rubric.md) and [classifier prompt](../prompts/detail-filter-v1.txt).

In a configured checkout, build only the diagnostic executables:

```sh
opam exec -- dune build evaluation/native/effects.exe bin/query_interp.exe
python3 -m unittest discover -s evaluation/tests -v
```

Run with a private source file and private provider-credentials JSON (or export the provider variables and omit `--credentials-file`):

```sh
python3 evaluation/code/dataset_validity.py all \
  --source /private/aaron-descriptions.json \
  --run evaluation/results/my-dataset-validity \
  --credentials-file /private/provider-credentials.json \
  --workers 24
```

The existing API model configuration is frozen on preparation, with current authenticated router catalog rates and limits. HIGH effort is used for generation, Qwen XHIGH; the inexpensive detail classifier uses DeepSeek V4 Flash LOW. Generation has a 32,768 output-token cap; no temperature, top-p or sampling seed is sent. The sample-selection seed is 20261112. The four generation demonstrations are frozen in `fixed-fql-demos-v1.json`: a13, a02, a03, a19, the first historical target's set. This is an explicit new dataset policy; the historical matrix had per-target sets.

The total guard is $20 including detail classification and generation; the Anthropic guard is $8. Reservations cover in-flight requests and unknown billing conservatively. Calls resume from durable receipts, retry transient/524 errors with bounded backoff, and preserve every attempt. Detail classification uses batches of 20, cached only for exact duplicate normalized NL; source-row multiplicity is retained. Pending budget cells and unresolved classifier/API errors are separate from negative detail labels and validity failures.

Commands `prepare`, `filter`, `sample`, `generate`, `score` and `export` can also run separately, always with the same `--run`. `all` resumes those stages. Do not change the frozen sample/manifest once generation starts. To score already generated outputs offline, use `score` followed by `export`; neither command calls a model.

Only the JSON `parsed` flag, together with nonempty-query status, determines grammar acceptance. Effects-driver status `ok` determines semantic/serialization acceptance. A zero exit from native `query_interp` determines symbolic interpretation acceptance; the interpreter is attempted only after semantic acceptance. None of these establishes intent correctness. The interpreter does not execute the generated management task.

Public exports: `filter-decisions.csv`, `sample-ids.csv`, `per-cell.csv`/`.json`, `per-attempt.csv`, `model-summary.csv`, `manifest.json`, `classifier-outputs.json`, `native-diagnostics.json` and `outputs/<model>/<row-id>.txt`. The `private/` subtree contains source data, normalized NL, complete prompts, provider responses/reasoning and replay state. Never commit it or use a recursive force-add of the result directory. Public exports contain source IDs/hashes and model outputs, without bulk copies of original NL/YAML.
