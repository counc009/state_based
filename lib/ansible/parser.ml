let process_ansible (file: string) : (Modules.Ast.stmt list, string) result =
  let process_play play =
    match play with
    | `O _map -> Error "TODO" (* Result at this point is a list of names and values *)
    | _ -> Error ("Expected play to be a mapping with fields")
  in let rec process_plays plays =
    match plays with
    | [] -> Ok []
    | hd :: tl -> 
        match process_play hd, process_plays tl with
        | Ok hd, Ok tl -> Ok (hd @ tl)
        | Ok _, Error msg -> Error msg
        | Error msg, Ok _ -> Error msg
        | Error mhd, Error mtl -> Error (mhd ^ "\n" ^ mtl)
  in let process_yaml code =
    match code with
    | `A seq -> process_plays seq
    | _ -> Error ("Expected top-level of an ansible playbook to be a sequence of plays")
  in let ch = open_in file
  in let s = really_input_string ch (in_channel_length ch)
  in let () = close_in ch
  in match Yaml.of_string s with
  | Error (`Msg msg) -> Error msg
  | Ok contents ->
      process_yaml contents
