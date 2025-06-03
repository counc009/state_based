type args = (ParseTree.vals, ParseTree.vals) Hashtbl.t option

let make_args args : args = Some (Hashtbl.of_seq (List.to_seq args))

let extract_arg (t: args) (k: string) : 'a option =
  match t with
  | None -> None
  | Some t ->
      match Hashtbl.find_opt t [Str k] with
      | None -> None
      | Some v -> Hashtbl.remove t [Str k]; Some v

let extract (t: ('a, 'b) Hashtbl.t option) (k: 'a) : 'b option =
  match t with
  | None -> None
  | Some t ->
      match Hashtbl.find_opt t k with
      | None -> None
      | Some v -> Hashtbl.remove t k; Some v

let args_empty (t: args) : bool =
  match t with
  | None -> true
  | Some t -> Hashtbl.length t = 0

let args_to_string (t: args) : string =
  match t with
  | None -> ""
  | Some t ->
      String.concat ", " (List.map 
        (fun (x, y) -> Printf.sprintf "%s = %s" (ParseTree.unparse_vals x)
                                                (ParseTree.unparse_vals y))
        (List.of_seq (Hashtbl.to_seq t)))

let rec list_last xs =
  match xs with
  | [] -> failwith "cannot compute last element of empty list"
  | [x] -> (x, [])
  | x :: xs ->
      let (l, rest) = list_last xs
      in (l, x :: rest)

let rec list_rem xs y =
  match xs with
  | [] -> []
  | x :: xs -> if x = y then xs else x :: list_rem xs y

type context = { os: Ast.ansible_os list option }

let init_context : context = { os = None }

let refine_context_os ctx os =
  let refine_os ctx os =
    match ctx with
    | None -> Some [os]
    | Some ctx -> if List.mem os ctx then Some [os] else Some []
  in { os = refine_os ctx.os os }

let refine_context_not_os ctx os =
  let refine_os ctx os =
    match ctx with
    | None -> None
    | Some ctx -> Some (list_rem ctx os)
  in { os = refine_os ctx.os os }
