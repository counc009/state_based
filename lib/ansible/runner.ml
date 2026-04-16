module Interp = Modules.Target.TargetInterp
module Calc = Modules.Target.Ast_Target
module Target = Modules.Target

let interp_ansible sources ansible_src =
  let _interp p : Interp.interp_res =
    Interp.interpret p Interp.init_interp_state Calc.VariableMap.empty
      (* continue -- should not continue, should always return *)
      (fun _ _ -> Err "Ansible program reached end without return")
      (* yield -- nothing to yield to *)
      (fun _ _ _ -> Err "Ansible program yielded at top-level")
      (* return -- great! *)
      (fun s _ _ -> Success s)
      (* raise -- exception raised *)
      (fun _ _ (v, _) ->
        match v with
        | Literal (Except (_, exc, v), _) ->
            Err (Printf.sprintf "Exception %s(%s)" exc
                  (Target.string_of_value v))
        | _ -> Err "Unknown Exception")
  in Result.bind (Modules.Parser.parse_files sources) (fun parsed ->
      Result.bind (Modules.Codegen.codegen parsed) (fun _ctx ->
        Result.bind (Parser.parse_ansible ansible_src) (fun _prg ->
          Error "TODO")))
