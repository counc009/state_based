open Parser

let interp_ansible sources ansible_src =
  Result.bind (Modules.Parser.parse_files sources) (fun parsed ->
    let (types, env) = Modules.Codegen.codegen parsed
    in Result.bind (process_ansible ansible_src types env) (fun prg ->
      let prg = Modules.Codegen.codegen_program prg types env
      in Ok (Modules.Target.TargetInterp.interpret prg (Primitive Unit))))
