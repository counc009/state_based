# Appendix B playbook generation

This workflow generates NL-to-Ansible samples for Aaron's local evaluation VMs. It performs no runtime execution, Astrogator verification, or LLM judging.

The prompt in `prompts/appendix-b-v1.txt` is the verbatim Appendix B text provided by Darsh, instantiated once per task as a single user message with no added system text. All 21 descriptions use the original dataset's explicit legacy problem mapping, including p11a and p11b. Six models, ten samples each, HIGH reasoning (Qwen XHIGH), and 4,096 output tokens give 1,260 planned cells. No small/local models are added.

## Setup and commands

From the repository root, using the existing OCaml/opam setup. Free syntax checks also require Linux `bwrap` (the `bubblewrap` package); integrity and extraction replay without `--syntax` do not use it.

```sh
uv venv /tmp/astrogator-ansible-venv
uv pip install --python /tmp/astrogator-ansible-venv/bin/python -r evaluation/ansible/requirements-checks.txt
opam exec -- dune build evaluation/ansible/native/paper_process.exe
python3 -m unittest discover -s evaluation/tests -q
/tmp/astrogator-ansible-venv/bin/python -m unittest discover -s evaluation/ansible/tests -q

python3 evaluation/ansible/code/generate.py freeze \
  --references evaluation/datasets/references-private.json \
  --manifest evaluation/ansible/results/NEW-RUN/private/manifest.json
python3 evaluation/ansible/code/generate.py run \
  --manifest evaluation/ansible/results/NEW-RUN/private/manifest.json \
  --output evaluation/ansible/results/NEW-RUN/private \
  --credentials-file /path/to/operator-owned-private-model-vars.json \
  --workers 24 --total-budget-usd 25 --anthropic-budget-usd 15
/tmp/astrogator-ansible-venv/bin/python evaluation/ansible/code/check_and_package.py \
  --run evaluation/ansible/results/NEW-RUN --workers 6
```

Credentials are never part of prompts, git URLs or public artifacts. The durable attempt ledger reserves before requests and reconciles reported usage. Unknown billing remains reserved. HTTP 524 and other transient gateway/transport errors receive exponential backoff, up to four total attempts per cell; failed responses are never written into YAML files as model outputs. Successful terminal samples are reused on resume. Incomplete token-limited responses are retained as sampled outcomes, not automatically regenerated. Hard guards are $25 total and $15 Anthropic for this experiment; the previous FQL run has a separate ledger.

Router Chat Completions uses streaming plus usage reporting to avoid long silent connections during reasoning. OpenAI Responses and Anthropic Messages use their direct endpoints. Every exact request is retained in the ignored private ledger; public manifests include model IDs/settings, prompt hashes, usage, timings and costs. Costs are reproducible local accounting at frozen rates, not account invoices; router catalog units are assumed USD/MTok.

## Extraction and checks

`new_extract.py`'s exact fence-removal regex is followed by `astrogator-eval/processing.ml`'s task/handler/vars wrapping algorithm. The adapted native copy changes only the model list to argv and skips missing raw files. It preserves the original processor's host sets, task ordering, omitted fields and response0–response9 naming. Full raw completions are retained separately; extraction failures are reported rather than repaired.

Checks distinguish raw YAML parsing, processed-file presence/nonemptiness, processed YAML parsing, nonempty task lists, and `ansible-playbook --syntax-check`. The syntax checker is a restricted local process with a read-only filesystem view, no network, no credentials and an empty home; it does not run tasks. It uses Ansible-core 2.19.11/builtin collections only, so an unresolved external module/role is an environment-sensitive check failure. Module-use flags cover shell/command/raw/script, including FQCNs, action/local_action, blocks and handlers; invalid YAML gets an explicitly labeled heuristic scan. These are format/tool-acceptance counts, not correctness.

## Handoff

Each run contains `<model-id>/pNN/response0.yml` through `response9.yml` for successfully extracted samples, plus `manifest.json`, `offline-checks.csv`, `model-summary.csv` and raw completions. Missing/extraction-failed samples remain explicit manifest rows. The run README explains copying these directories into Aaron's executor working directory, selecting the six model IDs, and removing the upstream p19-only debug override. No executor, VM, container, verifier or judge is launched here.

Public artifacts can be audited without credentials or the private ledger:

```sh
python3 evaluation/ansible/code/validate_export.py evaluation/ansible/results/2026-11-05
/tmp/astrogator-ansible-venv/bin/python evaluation/ansible/code/recheck_public.py \
  evaluation/ansible/results/2026-11-05
# Add --syntax to also repeat all free Ansible syntax checks.
```

The public replay recreates the native paper extraction from raw completions in a temporary directory and checks it byte-for-byte against the handoff files. It never executes tasks.
