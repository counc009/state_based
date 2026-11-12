# Evaluation-only open package/service KB: offline sensitivity analysis

This analysis makes no model calls and costs $0. The original parent-folder Example-KB exports are unchanged. It reuses all 1,800 planned dataset cells: 1,761 responses and 39 API-failed/budget-pending cells. Counts are out of 300 per model, not counts of correct translations.

## Exact fallback

`evaluation/native/fallback_kb.ml` implements the existing `Fql.Knowledge.KB` signature by including Example and overriding only `pkgDef` and `serviceDef`. Example is always called first. Only an error beginning exactly `Unknown package: ` or `Unknown service: ` triggers the fallback. A nonempty list containing exclusively nonempty literal `Str` values becomes a name by joining those strings with one space, preserving their spelling/case. A package becomes a single `{name; pkg_manager=System}` entry; a service becomes `Modules.Ast.StringLit name`. The same generic name applies on every OS, using the existing default/system package-manager lowering. This is a general rule, not a sample-fitted generated catalog.

All known entries retain their exact existing semantics, including OS-specific expansions and errors when OS context is missing. The fallback neither supplies unknown placeholders such as `?package` nor extends files, directories, executables, repositories, actions or conditions. Generic package lookup supplies the default manager rather than inventing a pip/virtualenv mapping; the existing semantic analyzer still handles/rejects action arguments. Availability of an actual package or service on a deployment is assumed by this sensitivity analysis, not verified.

No compiler source, `Fql.Knowledge.Example`, or original executable source is modified. `effects_fallback.ml` is the existing evaluation probe with only the semantic functor's KB argument substituted. `query_interp_fallback.ml` is the upstream native interpreter entrypoint with only that argument substituted. Tests assert these exact relationships. Native interpretation therefore uses the same existing lowering/module definitions/symbolic interpreter with the alternate KB, without executing infrastructure tasks.

## Results and meaning

`model-summary.csv` has paired Example/fallback rows; `per-cell.csv` and JSON retain unavailable cells separately and record both KBs, exact semantic errors and native exit codes. Parsing is unchanged for every cell. Semantic acceptance is independent of effect serialization, as in the parent dataset run. Empty queries remain invalid. Parsing is strict raw text: commentary/fences are not repaired or stripped. `rejection-reasons.csv` reports every remaining parse/semantic reason, grouping compiler errors at their colon delimiter; exact errors remain in per-cell rows. `cross-model.csv` counts descriptions with at least one semantic success, all responding models successful (requiring at least one response), and all six models responding and successful. No reference, NL obligation, LLM judge or intent-correctness score is introduced.

At least one semantic success: Example 89/300, fallback 267/300. All responding models successful: Example 32/300, fallback 42/300. All-six-responding-and-successful gives the same counts for this frozen sample. Missing responses do not become parse failures.

The remaining `Unknown package`/`Unknown service` errors are nonliteral unknown placeholders: Sol has 12 package and two service errors; Opus has one package error. Those are deliberately retained instead of assigning a concrete name to an unknown.

## Benchmark invariance check

YES: all 21 benchmark reference queries retain identical semantic acceptance and effect trees. All 2,520 cells of the 2026-11-04 full matrix retain identical semantic-acceptance and reference-effect-match flags under Example and fallback; independently recomputed Example per-model/variant counts reproduce the published numbers exactly. This includes both prompt variants, completed/incomplete outputs and API failures. See `benchmark-validation.json`, `benchmark-references.csv`, `benchmark-per-cell.csv` and `benchmark-summary.csv`. No original reference is changed.

## Reproduction

```sh
opam exec -- dune build evaluation/native/effects.exe bin/query_interp.exe \
  evaluation/native/effects_fallback.exe evaluation/native/query_interp_fallback.exe
python3 evaluation/code/kb_rescore.py \
  --run evaluation/results/2026-11-12-dataset-validity \
  --out evaluation/results/2026-11-12-dataset-validity/extended-kb \
  --benchmark evaluation/results/2026-11-04-full-matrix
python3 -m unittest discover -s evaluation/tests -p test_fallback_kb.py -v
```

The public parent outputs suffice for the dataset rescore; the benchmark audit additionally needs the preserved private historical response/reference artifacts. Probe and interpreter caches remain private; results, source hashes, benchmark evidence and CSVs are public. Native subprocesses have a 30-second timeout and run in a bounded thread pool. `validation.json` records original Example cell-flag reproduction, unchanged parsing and source hashes. Five native boundary controls validate the fallback, preservation of known entries/context errors, unchanged non-package errors, and entrypoint provenance.
