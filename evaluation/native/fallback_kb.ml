(* Evaluation-only extension. Existing entries and all non-package/service
   definitions are delegated unchanged to the production Example KB. *)
include Fql.Knowledge.Example

let literal_name values =
  match values with
  | [] -> None
  | _ ->
      let names = List.filter_map (function Fql.ParseTree.Str s -> Some s | _ -> None) values in
      if List.length names = List.length values && List.for_all (fun s -> String.trim s <> "") names
      then Some (String.concat " " names) else None

let pkgDef ctx values args =
  match Fql.Knowledge.Example.pkgDef ctx values args with
  | Error e when String.starts_with ~prefix:"Unknown package: " e ->
      (match literal_name values with
       | Some name -> Ok [{ Fql.Ast.name = name; pkg_manager = Fql.Ast.System }]
       | None -> Error e)
  | result -> result

let serviceDef ctx values args =
  match Fql.Knowledge.Example.serviceDef ctx values args with
  | Error e when String.starts_with ~prefix:"Unknown service: " e ->
      (match literal_name values with
       | Some name -> Ok (Modules.Ast.StringLit name)
       | None -> Error e)
  | result -> result
