# Building and Usage Instructions
This system is written in [OCaml](https://ocaml.org/) and should be built using the [Dune](https://dune.build) build system.
This system can be built as follows:

1. Install and initialize [Opam](https://opam.ocaml.org), the OCaml package manager as described [here](https://ocaml.org/install).
2. Install required OCaml packages, as follows:
   `opam install dune yaml jingoo angstrom`
3. Build using the command `dune build`

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
- Assert existance of users/groups used in various places (copy, file, etc.)
- Fix unification to avoid unifying conflicting elements (i.e.,
  fs("/etc/file.txt") and not fs("/etc/file.txt") in problem 13)

- Code-gen handlers

- (Later) Handle file modes
- (Later) Fix file-system descriptions, at minimum glob should try to identify
  the base directory, and then use its path list
- (Later) Improve handling of user home directory based paths
- (Later) Unify/check-validity of constraints
- (Later) Account for unification results when merging candidate diffs (in
  particular, map unknowns to known values when possible and potentially map
  back into unknowns from the reference)
