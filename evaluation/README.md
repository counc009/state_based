# NL-to-FQL evaluation

Translate natural-language requests into Astrogator's formal query language, with ten fresh calls per task/model/prompt variant. This evaluates the formalizer. Compiler acceptance does not establish that a specification satisfies a person's intent; user validation remains necessary.

## Setup and repository map

Python 3.10+; the runner uses only the standard library. API keys are read from environment variables and never logged. Obtain them through the secure Replicas variable form or your authorized secret-delivery path. No agent CLI, browsing or tool calls are included in model requests.

| Location | Contents |
|---|---|
| `code/` | Import, freeze, estimate, run, resume, compiler/reference/semantic audits |
| `prompts/` | Byte-preserved compact baseline, existing handbook, separately versioned improvement, provenance registry |
| `configs/` | Exact model IDs, provider, capability stratum, prices, output/reasoning budgets |
| `datasets/` | Input schema and private imports; never mix references/outcomes into generation inputs |
| `results/` | Public smoke summary; ignored run directories with immutable manifests, attempts and raw responses |
| `docs/` | Protocol, model sources, paper alignment and related work |
| `tests/` | Protocol/budget/resume tests and real native diagnostic controls |
| `../lib`, `../bin`, `../modules` | Existing compiler, verifier and module specifications |
| `../astrogator-eval` | Historical playbook evaluation entrypoints, retained at their original paths |

The current compiler layout and historical scripts remain compatible. This change creates one discoverable evaluation area rather than moving compiler modules or rewriting archived experiment paths. Historical VPS research and results are preserved separately; see the provenance document before treating them as a paper baseline.

## Commands (from repository root)

```sh
python3 -m unittest discover -s evaluation/tests -v

# Supply the authorized existing frozen-inputs.json from the research checkout.
python3 evaluation/code/import_frozen.py /path/to/frozen-inputs.json evaluation/datasets/imported-private.json

# Freeze 21 tasks × 2 variants × 10 repetitions for one accessible model.
python3 evaluation/code/evaluate.py freeze \
  --dataset evaluation/datasets/imported-private.json --models sol \
  --output /tmp/nl-fql-manifest.json
python3 evaluation/code/evaluate.py estimate --manifest /tmp/nl-fql-manifest.json

# For a smoke run, add --cases a01 to freeze. Run only after inspecting its estimate.
# Keys must already be in the environment; never put them on the command line.
python3 evaluation/code/evaluate.py run --manifest /tmp/nl-fql-manifest.json \
  --output evaluation/results/my-run --max-calls 10 --budget-usd 2
python3 evaluation/code/evaluate.py analyze --output evaluation/results/my-run

# Optional native check, after building the compiler and reviewing the command:
python3 evaluation/code/evaluate.py analyze --output evaluation/results/my-run \
  --checker 'python3 {repo}/evaluation/code/check_query.py {query}'
```

The last command is an argv template, not a shell. The wrapper supplies sorted absolute module paths. `query-interp` also symbolically interprets; a nonzero result is broader than a parsing error. The recorded smoke used the recovered narrow diagnostic driver instead; see its precise limits in `results/smoke-2026-11-04.md`.

A run can be resumed with the same manifest and directory. The dollar ceiling covers accumulated reserved attempts in that directory, not just the new invocation. An interrupted attempt is never silently resent. Use a new run for a protocol change. Calls reaching a configured cap leave the remaining ten-repeat cells explicitly missing; do not publish them as complete.

OpenAI `sol` and all four approved router routes are connectivity-tested. Claude Opus is optional/pending until its key arrives; default freeze excludes it. Before local inference, pin model/tokenizer/chat-template revisions and runtime/precision, supply `EVALUATION_LOCAL_URL` for an authorized existing OpenAI-compatible server, and verify which model it actually serves. No model download, GPU allocation or service launch is implicit. The current local transport has no entitlement or revision attestation; full local runs need that preflight. Anthropic effort is explicitly configured through `output_config.effort`; its thinking behavior differs from OpenAI and still needs a bounded entitlement/preflight check.

See [protocol](docs/protocol.md), [sources and paper alignment](docs/provenance.md), and [actual smoke results](results/smoke-2026-11-04.md).

Fresh native build and reference/semantic validation are documented in [native validation](docs/native-validation.md). [Verified model identities and budget options](docs/model-identities.md) supersede the original base-input-only full-run estimate.

Current selection, ten-repeat costs and the Qwen HIGH rejection are recorded in [model settings](docs/model-identities.md), [router checks](docs/router-connectivity.md) and [Darsh decisions](docs/decisions.md). Prior five-repeat smoke data remain historical.
