open Frontend

let errored = ref false

let process_file filename =
  try
    let res = Runner.parse_file filename
    in Printf.printf "File %s\n\n%s\n\n" filename (Format.string_of_ast res)
  with
  | Lexer.LexerError msg ->
    Printf.printf "While processing file %s encountered:\n  %s\n" filename msg;
    errored := true
  | Sys_error _ ->
    Printf.printf "Failed to read file %s\n" filename;
    errored := true

let () =
  let () = Clap.description "State Calculus Front-End Compiler"
  in let files =
    Clap.list_string ~placeholder:"FILENAME"
      ~description:"Files to process (order does not matter)" ()
  in let () = Clap.close ()
  in let () = List.iter process_file files
  in if !errored
  then exit 1
  else ()
