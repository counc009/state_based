# Testing Instructions
```
let parsed = match Modules.Parser.parse_file "test_copy.type" with Ok res -> [res] | Error msg -> failwith msg;;
let (types, env) = Modules.Codegen.codegen parsed;;
let prg = Modules.Codegen.codegen_program (Modules.Parser.parse_stmts_string "let _ = ansible.builtin.copy {{ dest: '/path/to/dest' }};") types env;;
Modules.Target.TargetInterp.interpret prg (Primitive Unit);;
```

Current bug: using prg with `, content: \"content for the file\"` produces
```
Failed to locate attribute in current state
```

probably need to look at the code being generated. My guess is the issue has something to do with trying to access file(dest, remote).content before we even add file(dest, remote).
