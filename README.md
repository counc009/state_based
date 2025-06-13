# Testing Instructions
```
let parsed = match Modules.Parser.parse_file "test_copy.type" with Ok res -> [res] | Error msg -> failwith msg;;
let (types, env) = Modules.Codegen.codegen parsed;;
let prg = Modules.Codegen.codegen_program (Modules.Parser.parse_stmts_string "env().is_root = false; let _ = ansible.builtin.copy {{ dest: '/path/to/dest', src: 'src_path' }};") types env;;
Modules.Target.TargetInterp.interpret prg (Primitive Unit);;
```

# TODO List
- (Later) Handle file modes
- (Later) Fix file-system descriptions, at minimum glob should try to identify
  the base directory, and then use its path list
- (Later) Improve handling of user home directory based paths
- (Later) Unify/check-validity of constraints
- (Later) Account for unification results when merging candidate diffs (in
  particular, map unknowns to known values when possible and potentially map
  back into unknowns from the reference)
