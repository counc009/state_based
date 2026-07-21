let models = ["deepseek"; "gpt"; "granite"; "llama"; "qwen"; "starcoder";
              "gpt-5-mini"; "gpt-oss"; "ministral"; "qwen3"; "qwen-coder"]
(* NOTE: we run 11b only on one machine since we use fetch with flat. We
 * choose debian since it seems to be the most tempermental of the systems *)
let benchmarks = [("p01", "all"); ("p02", "all"); ("p03", "all");
                  ("p04", "all"); ("p05", "all"); ("p06", "all");
                  ("p07", "all"); ("p08", "all"); ("p09", "all");
                  ("p10", "all"); ("p11a", "all"); ("p11b", "debian");
                  ("p12", "all"); ("p13", "all"); ("p14", "debian");
                  ("p15", "all"); ("p16", "all"); ("p17", "redhat,ubuntu");
                  ("p18", "redhat"); ("p19", "all"); ("p20", "redhat,debian")]

let read_whole_file filename =
  let ch = open_in filename
  in let s = really_input_string ch (in_channel_length ch)
  in close_in ch; s

let write_to_file filename contents =
  let ch = open_out filename
  in let () = Printf.fprintf ch "%s\n" contents
  in close_out ch

let identify_tasks (code: Yaml.yaml)
  : (Yaml.yaml list * Yaml.yaml list option
    * (Yaml.yaml * Yaml.yaml) list option, unit) result =
  let items =
    match code with
    | `A { s_members = items } -> items
    (* Sometimes the models generate just something that looks like
     * tasks:
     * - name: ...
     * to handle this we treat the entire code as the single item *)
    | _ -> [code]
  in let res =
    List.fold_left (fun acc (item : Yaml.yaml) ->
      Result.bind acc (fun (tasks, handlers, vars) ->
        match item with
        | `O { m_members = members } ->
            Ok (List.fold_left (fun (tasks, handlers, vars)
              ((label, value) : Yaml.yaml * Yaml.yaml) ->
              match label, value with
              | `Scalar { value = "tasks" }, `A { s_members = ts } ->
                  let new_tasks =
                    match tasks with
                    | None -> Some ts
                    | Some tasks -> Some (ts @ tasks)
                  in (new_tasks, handlers, vars)
              | `Scalar { value = "handlers" }, `A { s_members = hs } ->
                  let new_handlers =
                    match handlers with
                    | None -> Some hs
                    | Some handlers -> Some (hs @ handlers)
                  in (tasks, new_handlers, vars)
              | `Scalar { value = "vars" }, `O { m_members = vs } ->
                  let new_vars =
                    match vars with
                    | None -> Some vs
                    | Some vars -> Some (vs @ vars)
                  in (tasks, handlers, new_vars)
              | _, _ -> (tasks, handlers, vars)
            ) (tasks, handlers, vars) members)
        | _ -> Error ()
      )
    ) (Ok (None, None, None)) items
  in Result.bind res (fun (tasks, handlers, vars) ->
    match tasks with
    | Some tasks -> Ok (tasks, handlers, vars)
    | None -> Ok (items, None, None)
  )

let () =
  let process_model model =
    let process_benchmark (problem, hosts) =
      for i = 1 to 10 do
        let n = i mod 10
        in let path = Printf.sprintf "%s/%s/raw%d.yml" model problem n
        in let content = read_whole_file path
        in match Yaml.yaml_of_string content with
        | Ok as_yaml ->
            begin match identify_tasks as_yaml with
            | Error _ -> Printf.printf
              "Model %s, Problem %s, Response %d - structure not handled\n"
              model problem i
            | Ok (tasks, handlers, vars) ->
                let handlers : (Yaml.yaml * Yaml.yaml) list =
                  match handlers with None -> []
                  | Some handlers ->
                    [(`Scalar { anchor = None; tag = None; value = "handlers";
                                plain_implicit = true; quoted_implicit = false;
                                style = `Plain },
                      `A { s_anchor = None; s_tag = None; s_implicit = true;
                           s_members = handlers })]
                in let tasks : (Yaml.yaml * Yaml.yaml) list =
                    (`Scalar
                      { anchor = None; tag = None; value = "tasks";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain },
                     `A { s_anchor = None; s_tag = None; s_implicit = true;
                          s_members = tasks})
                    :: handlers
                in let vars : (Yaml.yaml * Yaml.yaml) list =
                  match vars with None -> tasks
                  | Some vars ->
                    (`Scalar
                      { anchor = None; tag = None; value = "vars";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain },
                     `O { m_anchor = None; m_tag = None; m_implicit = true;
                          m_members = vars})
                    :: tasks
                in let play : Yaml.yaml = `O { 
                  m_anchor = None; m_tag = None; m_implicit = true;
                  m_members =
                    (`Scalar
                      { anchor = None; tag = None; value = "name";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain },
                     `Scalar
                      { anchor = None; tag = None;
                        value = Printf.sprintf
                                  "Model %s, Problem %s, Response %d"
                                  model problem i;
                        plain_implicit = false; quoted_implicit = true;
                        style = `Double_quoted })
                    :: (`Scalar
                      { anchor = None; tag = None; value = "hosts";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain },
                     `Scalar
                      { anchor = None; tag = None;
                        value = hosts; plain_implicit = true;
                        quoted_implicit = false; style = `Plain })
                    :: (`Scalar
                      { anchor = None; tag = None; value = "become";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain },
                     `Scalar
                      { anchor = None; tag = None; value = "true";
                        plain_implicit = true; quoted_implicit = false;
                        style = `Plain })
                    :: vars
                  }
                in let plays : Yaml.yaml = `A { 
                  s_anchor = None; s_tag = None; s_implicit = true;
                  s_members = [play] }
                in match Yaml.yaml_to_string plays with
                | Ok plays ->
                    let res = "---\n" ^ plays
                    in let output =
                      Printf.sprintf "%s/%s/response%d.yml" model problem n
                    in write_to_file output res
                | Error _ -> Printf.printf
                  "Model %s, Problem %s, Response %d - failed to export\n"
                  model problem i
            end
        | Error _ -> Printf.printf
            "Model %s, Problem %s, Response %d - failed to parse\n"
            model problem i
      done
    in List.iter process_benchmark benchmarks
  in List.iter process_model models
