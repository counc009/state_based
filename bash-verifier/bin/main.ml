open Frontend

let parse_file filename =
  try
    let res = Runner.parse_file filename
    in Ok res
  with
  | Lexer.LexerError msg ->
      Error (Printf.sprintf "While processing file %s, encountered:\n  %s\n"
              filename msg)
  | Sys_error _->
      Error (Printf.sprintf "Failed to read file %s\n" filename)

let process_files files =
  let (decls, errors) =
    List.fold_left (fun (decls, errors) file ->
      match parse_file file with
      | Ok res -> (res @ decls, errors)
      | Error msg -> print_string msg; (decls, true)
    ) ([], false) files
  in if errors
  then false
  else
    match Semant.analyze_program decls with
    | Ok _env -> Printf.printf "SUCCESS!\n"; true
    | Err (_env, errs) -> Runner.print_semant_errors errs; false

let () =
  let () = Clap.description "State Calculus Front-End Compiler"
  in let files =
    Clap.list_string ~placeholder:"FILENAME"
      ~description:"Files to process (order does not matter)" ()
  in let () = Clap.close ()
  in if process_files files
  then ()
  else exit 1
