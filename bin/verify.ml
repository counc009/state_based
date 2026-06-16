let usage_msg = "runner <query> <ansible program> -- <module definitions>"
let query = ref ""
let program = ref ""
let module_defs = ref []

let cnt = ref 0
let anon_fun filename =
  (if !cnt = 0 then query := filename
  else if !cnt = 1 then program := filename
  else failwith "Only expected two anonymous arguments"); cnt := !cnt + 1

module Interp = Modules.Target.TargetInterp
module Calc = Modules.Target.Ast_Target
module Target = Modules.Target

module Semant = Fql.Semant.Semant(Fql.Knowledge.Example)

let arglist =
  [("--", Arg.Rest_all (fun fs -> module_defs := fs), "Ansible Module Definitions")]

let interp p =
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

let () = Printf.printf "\n";
  Arg.parse arglist anon_fun usage_msg;
  let parsed =
    match Modules.Parser.parse_files !module_defs with
    | Error msg ->
        Printf.printf "ERROR: While parsing module definitions, encountered\n%s\n" msg
        ; exit 1
    | Ok parsed -> parsed
  in let ctx =
    match Modules.Codegen.codegen parsed with
    | Error msg ->
        Printf.printf "ERROR: While lowering module definitions, encountered\n%s\n" msg
        ; exit 2
    | Ok ctx -> ctx

  in let query =
    let parsed =
      let ch = open_in !query
      in let s = really_input_string ch (in_channel_length ch)
      in let () = close_in ch
      in let lexbuf = Lexing.from_string s
      in Fql.Parser.query Fql.Lexer.token lexbuf
    in let stmt =
      Result.bind (Semant.analyze_top parsed) (fun query ->
        Result.bind (Fql.Codegen.codegen_query query) (fun query ->
          Modules.Codegen.codegen_program query ctx))
    in match stmt with
    | Error msg ->
        Printf.printf "ERROR: While lowering query, encountered\n%s\n" msg
        ; exit 3
    | Ok stmt -> stmt

  in let ansible =
    let stmt =
      Result.bind (Ansible.Parser.parse_ansible !program) (fun prg ->
        Result.bind (Ansible.Semant.process_playbook prg ctx) (fun typed ->
          Ansible.Codegen.codegen_playbook typed ctx))
    in match stmt with
    | Error msg ->
        Printf.printf "ERROR: While lowering Ansible, encountered\n%s\n" msg
        ; exit 4
    | Ok stmt -> stmt

  in let query_interp = interp query
  in let ansible_interp = interp ansible

  in let res = Fql.Verifier.unify_candidate query_interp ansible_interp
  in match res with
  | Some _ -> Printf.printf "VERIFIER\n"; exit 0
  | None   -> Printf.printf "FAILED TO VERIFY\n"; exit 5
