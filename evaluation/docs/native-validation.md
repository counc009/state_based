# Native validation and semantic evidence

This validation uses a fresh local OCaml 5.5.0 build in the Replicas workspace, not the disk-full VPS. Installation/build logs are retained in the local validation run directory. The initial package installation exposed missing dependencies (`jingoo` was the first reported missing library). The declared package dependencies are corrected in `dune-project` and its generated opam file; compiler semantics are not patched for this refresh.

## Reproduction

From the repository root, with Opam installed and initialized:

```sh
opam switch create . 5.5.0 --no-install -y
opam install -y dune
opam exec -- dune build state_based.opam
opam install . --deps-only --working-dir -y
opam exec -- dune build @all
opam exec -- dune runtest
python3 -m unittest discover -s evaluation/tests -v

python3 evaluation/code/semantic_audit.py \
  --run evaluation/results/2026-11-04-sol-smoke \
  --references evaluation/datasets/references-private.json \
  --interpreter _build/default/bin/query_interp.exe \
  > /tmp/semantic-audit.json
python3 evaluation/code/reference_verifier_audit.py \
  --run evaluation/results/2026-11-04-sol-smoke \
  --references evaluation/datasets/references-private.json \
  > /tmp/reference-verifier-audit.json
```

Use the authorized original `benchmarks/original.json` as `references-private.json`; it contains source-supplied reference FQL and playbooks, is ignored by Git, and is never read by generation. The recovered smoke raw responses also remain local. These commands perform parsing, semantic analysis, symbolic interpretation and symbolic verification only; no Ansible program is executed against the host.

The effects diagnostic in `native/effects.ml` is recovered from the existing research `scripts/fql_json.ml` and builds against the unmodified current FQL AST/semantic analyzer. It exposes structured actions, paths, conditions and KB lowering choices. Its serializer is not a denotational equivalence algorithm; unsupported serializations fail closed. The reference comparison checks structural normalized-effect equality, not raw string equality. A mismatch is a review signal, not automatically an intent error.

## Evidence layers

1. Compiler acceptance checks whether a query is supported and can be processed.
2. Supplied-reference effect agreement checks whether its normalized semantic AST matches the existing reference. The reference is a control, not independently validated gold.
3. A separate, deliberately narrow NL obligation check extracts the target path from exactly `Create directory /PATH` and checks for that remote-directory action. It does not consult reference FQL; unsupported NL forms abstain. Extra actions are flagged for review rather than automatically declared wrong intent.
4. Symbolic verification checks each generated query against its supplied reference playbook and a wrong-path program witness for the completed a01 smoke. Acceptance can carry assumptions/residual effects. This is not real execution or complete adequacy evidence.
5. Independent human adequacy review and broader bounded behavioral tests remain separate. Existing research explicitly demonstrates that killing one mutant or accepting a reference is insufficient to establish adequacy; those prior findings are not newly reproduced here.

Diagnostic controls use neutral paths: quoted/unquoted equivalent creation, wrong target, wrong operation and omitted requested action. They were constructed after the smoke for checking the audit machinery and were not used to tune either prompt. Scientific evaluation must disclose this post-hoc status.

## Completed results (2026-11-04)

- Fresh native build: `dune build @all` exit 0, OCaml 5.5.0, Dune 3.24.2. `dune runtest` exits 0, but the inherited test source is empty; the added native controls below supply substantive checks.
- `opam install . --deps-only --working-dir -y` reports no missing dependencies after regenerating the manifest. An inherited placeholder license warning remains; no license was invented. Direct versions: yaml 3.2.0, jingoo 1.5.4, angstrom 0.16.1, re 1.14.0 and ocolor 1.3.1; full transitive metadata are in `configs/native-switch.export`.
- Twelve Python tests pass, including two real native tests covering compiler-valid semantic counterexamples, quoted/unquoted equivalence controls, and empty-query rejection. The five diagnostic controls are not five independent fault classes: wrong-target/omitted-target variants share a mechanism.
- All 21 supplied FQL references complete native semantic processing. All ten recorded smoke outputs match the supplied semantic effect tree, satisfy the narrow independent directory/path obligation and complete native symbolic interpretation. Each arm is 5/5 at those stages, with no measured advantage.
- All ten generated queries symbolically accept the supplied a01 reference program and reject a wrong-path program. Acceptance is explicitly with possible assumptions/residual effects; no real playbook execution occurred.
- Across the 21 supplied reference-program controls: 19 accepted, a03 fails program lowering (`string` versus `file_state` in a templated `with_items` state), and a20 rejects. A diagnostic a20 copy replacing only its eight-space sudoers separator with a YAML-escaped tab is accepted. The upstream source also documents spacing sensitivity at `lib/fql/codegen.ml` around the sudoers line. These discrepancies were retained; neither the references nor compiler semantics were changed. They prevent treating the supplied artifact as an unquestioned oracle.

All raw diagnostics, stdout/stderr, original reference hashes, native binary/module hashes, install/build logs, package versions and test logs are retained in ignored `results/native-validation-2026-11-04/`. Initial failed installation logs are preserved alongside the successful retry. No files were deleted on the VPS.

The recovered normalized references have explicit `id`, `paper_id` and `legacy_id` fields. These differ from checked-in `playbooks/bench/queryNN.txt` numbering (e.g. a20 maps to legacy p19). The new audit joins by task IDs from the supplied artifact; it never assumes filenames use paper numbering.
