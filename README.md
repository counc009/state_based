# Testing Instructions
```
let parsed = match Modules.Parser.parse_file "test_copy.type" with Ok res -> [res] | Error msg -> failwith msg;;
let (types, env) = Modules.Codegen.codegen parsed;;
let prg = Modules.Codegen.codegen_program (Modules.Parser.parse_stmts_string "env().is_root = false; let _ = ansible.builtin.copy {{ dest: '/path/to/dest', src: 'src_path' }};") types env;;
Modules.Target.TargetInterp.interpret prg (Primitive Unit);;
```

# TODO List
1. Make sure we automatically create the env() element
