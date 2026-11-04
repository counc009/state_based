# Astrogator

Formal queries and symbolic verification for Ansible. For the model/prompt refresh, start with [the NL-to-FQL evaluation guide](evaluation/README.md): setup, repository map, frozen five-repeat runs, budgets and actual smoke results. Historical playbook evaluation scripts remain in `astrogator-eval/`; compiler and module paths retain their existing layout.

# Building and Usage Instructions
This system is written in [OCaml](https://ocaml.org/) and should be built using the [Dune](https://dune.build) build system.
This system can be built as follows:

1. Install and initialize [Opam](https://opam.ocaml.org), the OCaml package manager as described [here](https://ocaml.org/install).
2. Create a local OCaml 5.5.0 switch without auto-installing the project: `opam switch create . 5.5.0 --no-install -y`.
3. Install Dune and generate the dependency manifest: `opam install -y dune` then `opam exec -- dune build state_based.opam`.
4. Install declared dependencies: `opam install . --deps-only --working-dir -y`.
5. Build and check: `opam exec -- dune build @all` and `opam exec -- dune runtest`.

OCaml 5.5+ is required by the existing String APIs. The checked native dependency export is
[`evaluation/configs/native-switch.export`](evaluation/configs/native-switch.export); import it into an empty switch with
`opam switch import evaluation/configs/native-switch.export` to reproduce the recorded package versions.
See [native validation](evaluation/docs/native-validation.md) for the actual compiler, semantic/reference checks and limitations.

The system contain 3 executables:

1. Ansible Interpreter: `ansible-interp` takes a playbook and list of module definitions and interprets the Ansible playbook
2. Query Interpreter: `query-interp` takes a formal language query and list of module definitions and interprets the query
3. Verifier: `ansible-verify` takes a formal language query and ansible playbook and a list of module definitions and checks whether the playbook matches the query

These executables can be executed through dune as `dune exec <executable name> -- <arguments>` or the built executables can be executed which can be found under `_build/install/default/bin`.

For example, to interpret an Ansible playbook we execute:
```
dune exec ansible-interp -- <playbook path> -- modules/*
```
or equivalently
```
./_build/install/default/bin/ansible-interp <playbook path> -- modules/*
```

# TODO Tasks
- (Later) Handle file modes
- (Later) Fix file-system descriptions, at minimum glob should try to identify
  the base directory, and then use its path list
- (Later) Improve handling of user home directory based paths
