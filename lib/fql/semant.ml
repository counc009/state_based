(* We'll use a semantic analysis phase to ensure that appropriate arguments and
 * categories are selected and we'll produce a new query AST incorporating the
 * info for easy code generation.
 *
 * The goal of this analysis is to normalize the query into a form in which
 * a signle action will always be translated (mostly) the same way to the
 * module language perhaps with some pieces filled by the knowledge base.
 *)
module Target = Modules.Target.Ast_Target

open Knowledge

let init_context : Knowledge.context = { os = None }

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
    | Some ctx -> Some (Ast.list_rem ctx os)
  in { os = refine_os ctx.os os }

module Semant(Knowledge: Knowledge_Base) = struct
  let analyze_path (p: ParseTree.vals) : (Ast.path, string) result =
    match p with
    | [s] | [Str "remote"; s] -> Ok (Remote s)
    | [Str "controller"; s] -> Ok (Controller s)
    | _ -> Error (Printf.sprintf "unhandled path specifier '%s'"
                      (ParseTree.unparse_vals p))

  let rec analyze_conditional (ctx: context) (c: ParseTree.cond)
    (t: ParseTree.base) (e: ParseTree.base)
    : (Ast.query, string) result =
    match c with
    | And (x, y) -> analyze_conditional ctx x (If (y, t, e)) e
    | Or (x, y) -> analyze_conditional ctx x t (If (y, t, e))
    | Not c -> analyze_conditional ctx c e t
    | Eq (lhs, rhs) ->
        if lhs = [Str "os"]
        then let os : (Ast.ansible_os, string) result =
          match rhs with
          | [Str "Debian"] -> Ok Debian
          | [Str "Ubuntu"] -> Ok Ubuntu
          | [Str "RedHat"] -> Ok RedHat
          | _ -> Error (Printf.sprintf "Unknown OS: %s"
                                       (ParseTree.unparse_vals rhs))
        in Result.bind os (fun os ->
          Result.bind (analyze_base (refine_context_os ctx os) t) (fun t ->
            Result.bind (analyze_base (refine_context_not_os ctx os) e)
              (fun e -> Ok (Ast.Cond (Ast.CheckOs os, t, e)))))
        else Error (Printf.sprintf "Unhandled equality check between %s and %s"
                     (ParseTree.unparse_vals lhs) (ParseTree.unparse_vals rhs))
    | Exists desc ->
        begin match desc with
        | Str "file" :: path ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.FileExists p, t, e)))))
        | Str "directory" :: path ->
            Result.bind (analyze_path path) (fun p ->
              Result.bind (analyze_base ctx t) (fun t ->
                Result.bind (analyze_base ctx e) (fun e ->
                  Ok (Ast.Cond (Ast.DirExists p, t, e)))))
        | _ ->
            let (last, rest) = Ast.list_last desc
            in match last with
            | Str "file" ->
                Result.bind (Knowledge.fileDef ctx rest None) (fun p ->
                  Result.bind (analyze_base ctx t) (fun t ->
                    Result.bind (analyze_base ctx e) (fun e ->
                      Ok (Ast.Cond (Ast.FileExists p, t, e)))))
            | Str "directory" ->
                Result.bind (Knowledge.dirDef ctx rest None) (fun p ->
                  Result.bind (analyze_base ctx t) (fun t ->
                    Result.bind (analyze_base ctx e) (fun e ->
                      Ok (Ast.Cond (Ast.DirExists p, t, e)))))
            | _ -> Error (Printf.sprintf "cannot check existance of: %s"
                            (ParseTree.unparse_vals desc))
        end
    | Required desc ->
        Result.bind (Knowledge.requirementDef ctx desc) (fun c ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (c, t, e)))))
    | Installed desc ->
        Result.bind (Knowledge.pkgDef ctx desc None) (fun pkg ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (PkgInstalled pkg, t, e)))))
    | Running desc ->
        Result.bind (Knowledge.serviceDef ctx desc None) (fun nm ->
          Result.bind (analyze_base ctx t) (fun t ->
            Result.bind (analyze_base ctx e) (fun e ->
              Ok (Ast.Cond (ServiceRunning nm, t, e)))))

  and analyze_atom (_ctx: context) (a: ParseTree.atom)
    : (Ast.act, string) result =
    let (act, args) = a
    in let _args = Ast.make_args args
    in match act with
    | _ -> Error "TODO"

  and analyze_base (ctx: context) (b: ParseTree.base)
    : (Ast.query, string) result =
    match b with
    | Nil -> Ok End
    | Cons (a, b) ->
        Result.bind (analyze_atom ctx a) (fun a ->
          Result.bind (analyze_base ctx b) (fun b ->
            Ok (Ast.Seq (Atom a, b))))
    | If (c, t, e) -> analyze_conditional ctx c t e

  let rec analyze_top (q: ParseTree.top) : (Ast.query, string) result =
    match q with
    | [] -> Ok End
    | b :: q ->
        Result.bind (analyze_base init_context b) (fun b ->
          Result.bind (analyze_top q) (fun q ->
            Ok (Ast.Seq (b, q))))
end
