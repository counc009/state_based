let ( let^ ) r f = Result.bind r f

module Ast = Ast.Parsed

let cnt = ref 0
let new_tmp () =
  let n = !cnt
  in let () = cnt := n + 1
  in "!" ^ string_of_int n

module Target = Modules.Target.Ast_Target
module Context = Modules.Codegen

module StringMap = Modules.Target.StringMap
module UniqueMap = Modules.Codegen.UniqueMap

type 'a list2 = 'a Modules.Target.list2

let rec list2_map_list (f : 'a -> 'b) (xs : 'a list2) : 'b list =
  match xs with
  | LastTwo (x, y) -> [f x; f y]
  | Cons (x, tl) -> f x :: list2_map_list f tl

type var_type =
  | Unknown  of Target.typ (* A suggested type *)
  | Concrete of Target.typ

type play_env = (string, var_type) Hashtbl.t

let rec fold_map_res (f : 'a -> ('b, 'e) result) (g : 'b -> 'c -> 'c)
  (xs : 'a list) (i : 'c) : ('c, 'e) result =
  match xs with
  | [] -> Ok i
  | x :: xs ->
      let^ x = f x
      in let^ xs = fold_map_res f g xs i
      in Ok (g x xs)

let rec list_to_and (v : Ast.value) : Ast.value =
  match v with
  | List [] -> Bool true
  | List [v] -> v
  | List (v :: vs) -> Ast.Binary (v, And, list_to_and (List vs))
  | _ -> v

(* Utilities for constructing the target calculus *)
let element (ctx : Context.context) (nm : string) : Target.element =
  match UniqueMap.find nm ctx.globals with
  | Some (Element (nm, t)) -> (nm, Result.get_ok (Context.lower_type t))
  | _ -> failwith ("internal error, failed to find element " ^ nm)

let attribute (ctx : Context.context) (nm : string) : Target.attribute =
  match UniqueMap.find nm ctx.globals with
  | Some (Attribute (nm, t)) -> (nm, Result.get_ok (Context.lower_type t))
  | _ -> failwith ("internal error, failed to find attribute " ^ nm)

let rec seq (xs : Target.stmt list) : Target.stmt =
  match xs with
  | [] -> Pass
  | [s] -> s
  | hd :: tl -> Seq (hd, seq tl)

(* Generates a tryCatch exception that catches 'AnsibleFailure' exceptions *)
let tryCatch (ctx : Context.context)
  (body : Target.stmt) (catch : Target.stmt) (finally : Target.stmt)
  : Target.stmt =
  TryCatch (body, "!catch",
    Match (
      Function (UnpackExcept (ctx.excepts, "AnsibleFailure"), Variable "!catch"),
      "!except",
      (* None, some other error *)
      Raise (Variable "!catch"),
      (* Some, an AnsibleFailure exception *)
      catch),
    finally)

(* CHANGES WE NEED
 * 1. We need to support handlers and note that handlers that are notified can
 *    be derived dynamically. Also are called in the order they are defined not
 *    the order they are notified. Also, they are only invoked after the whole
 *    section (pre-tasks, tasks/role, post-tasks) is run. *)

let singleton_list (elemTy : Target.typ) (elem : Target.expr) : Target.expr =
  Function (Constructor (false, List elemTy),
    Pair (elem, Function (Constructor (true, List elemTy), Literal (Unit ()))))

(* coerce_value converts some primitive values into other types and generates
 * code for certain coercing *)
let rec coerce_value (goal : Target.typ option) (v : Target.expr) (ty : Target.typ)
  : (Target.expr * Target.typ, string) result =
  match goal, ty with
  | None, _ -> Ok (v, ty)

  | Some (Primitive Int), Primitive Int -> Ok (v, Primitive Int)
  | Some (Primitive Int), Primitive Float ->
      begin match v with
      | Literal (Float f) ->
          if Float.is_integer f
          then Ok (Literal (Int (Float.to_int f)), Primitive Int)
          else Error (Printf.sprintf "Expected integer found float literal %f" f)
      | _ -> Error "Incorrect type, expected integer found float"
      end
  | Some (Primitive Int), _ -> Error "Incorrect type, expected int"

  | Some (Primitive Float), Primitive Float -> Ok (v, Primitive Float)
  | Some (Primitive Float), Primitive Int ->
      begin match v with
      | Literal (Int i) ->
          Ok (Literal (Float (float_of_int i)), Primitive Float)
      | _ ->
          (* Allow coercions from int to float *)
          Ok (Function (FloatOfInt, v), Primitive Float)
      end
  | Some (Primitive Float), _ -> Error "Incorrect type, expected float"

  | Some (Primitive String), Primitive String -> Ok (v, Primitive String)
  | Some (Primitive String), Primitive Bool ->
      begin match v with
      | Literal (Bool b) ->
          Ok (Literal (String (string_of_bool b)), Primitive String)
      | _ -> Error "Incorrect type, expected string found bool"
      end
  | Some (Primitive String), Primitive Int ->
      begin match v with
      | Literal (Int i) ->
          Ok (Literal (String (string_of_int i)), Primitive String)
      | _ -> Error "Incorrect type, expected string found int"
      end
  | Some (Primitive String), Primitive Float ->
      begin match v with
      | Literal (Float f) ->
          Ok (Literal (String (string_of_float f)), Primitive String)
      | _ -> Error "Incorrect type, expected string found float"
      end
  | Some (Primitive String), Primitive Path ->
      begin match v with
      | Literal (Path p) ->
          Ok (Literal (String p), Primitive String)
      | _ ->
          (* Allow coercions from path to string *)
          Ok (Function (StringOfPath, v), Primitive String)
      end
  | Some (Primitive String), _ -> Error "Incorrect type, expected string"

  | Some (Primitive Path), Primitive Path -> Ok (v, Primitive Path)
  | Some (Primitive Path), Primitive Bool ->
      begin match v with
      | Literal (Bool b) ->
          Ok (Literal (Path (string_of_bool b)), Primitive Path)
      | _ -> Error "Incorrect type, expected path found bool"
      end
  | Some (Primitive Path), Primitive Int ->
      begin match v with
      | Literal (Int i) ->
          Ok (Literal (Path (string_of_int i)), Primitive Path)
      | _ -> Error "Incorrect type, expected path found int"
      end
  | Some (Primitive Path), Primitive Float ->
      begin match v with
      | Literal (Float f) ->
          Ok (Literal (Path (string_of_float f)), Primitive Path)
      | _ -> Error "Incorrect type, expected path found float"
      end
  | Some (Primitive Path), Primitive String ->
      begin match v with
      | Literal (String s) ->
          Ok (Literal (Path s), Primitive Path)
      | _ ->
          (* Allow coercions from string to path *)
          Ok (Function (PathOfString, v), Primitive Path)
      end

  | Some t, ty when t = ty -> Ok (v, ty)
  | Some (Named (List t)), ty ->
      let^ (e, et) = coerce_value (Some t) v ty
      in Ok (singleton_list et e, Target.Named (List et))

  | Some _, _ -> Error "Type mismatch"

let codegen_value (v : Ast.value) (ty : Target.typ option)
  (ctx : Context.context) (env : play_env)
  (k : Target.expr * Target.typ -> (Target.stmt, string) result)
  : (Target.stmt, string) result =

  let rec codegen (v : Ast.value) (ty : Target.typ option)
    (k : Target.expr * Target.typ -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match v with
    | Int i ->
        Result.bind (coerce_value ty (Literal (Int i)) (Primitive Int)) k
    | Float f ->
        Result.bind (coerce_value ty (Literal (Float f)) (Primitive Float)) k
    | Bool b ->
        Result.bind (coerce_value ty (Literal (Bool b)) (Primitive Bool)) k
    | List vs ->
        begin match ty with
        | None | Some (Named (List _)) ->
            let init_elem_type =
              match ty with
              | None -> None
              | Some (Named (List t)) -> Some t
              | _ -> failwith "matching error"
            in let rec handle_vals (vs : Ast.value list)
              (elemTy : Target.typ option)
              (* type here is the element type, not the list's type *)
              (k : Target.expr -> Target.typ -> (Target.stmt, string) result)
              : (Target.stmt, string) result =
              match vs with
              | v :: vs ->
                  codegen v elemTy (fun (hd, thd) ->
                    handle_vals vs (Some thd) (fun tl el ->
                      k (Target.Function (Constructor (true, List el),
                          Pair (hd, tl))) el))
              | [] ->
                  match elemTy with
                  | None -> Error "Could not determine the type of an empty list"
                  | Some el ->
                      k (Target.Function (Constructor (false, List el),
                          Literal (Unit ())))
                        el
            in handle_vals vs init_elem_type
                  (fun lst elemTy -> k (lst, Named (List elemTy)))
        | _ -> Error "Incorrect type, found list"
        end
    | String s ->
        (* Strings in YAML can actually represent many things in our type-system,
         * specifically they can be strings, paths, or enum values *)
        begin match ty with
        | None | Some (Primitive String) ->
            k (Literal (String s), Primitive String)
        | Some (Primitive Path) ->
            k (Literal (Path s), Primitive Path)
        | Some (Named (Cases (enum_name, constrs))) ->
            let rec construct_case (cases : (string * Target.typ) list2)
              : (Target.expr, string) result =
              match cases with
              | Cons ((nm, Primitive Unit), tl) ->
                  if s = nm
                  then Ok (Target.Function (
                            Constructor (true, Cases (enum_name, cases)),
                            Literal (Unit ())))
                  else
                    let^ res = construct_case tl
                    in Ok (Function (
                            Constructor (false, Cases (enum_name, cases)),
                            res) : Target.expr)
              | Cons ((nm, _), tl) ->
                  if s = nm
                  then Error ("Constructor " ^ s
                        ^ "cannot be used in Ansible as it has arguments")
                  else
                    let^ res = construct_case tl
                    in Ok (Function (
                            Constructor (false, Cases (enum_name, cases)),
                            res) : Target.expr)
              | LastTwo ((nm, Primitive Unit), _) when s = nm ->
                  Ok (Target.Function (
                      Constructor (true, Cases (enum_name, cases)),
                      Literal (Unit ())))
              | LastTwo ((nm, _), _) when s = nm ->
                  Error ("Constructor " ^ s
                    ^ " cannot be used in Ansible as it has arguments")
              | LastTwo (_, (nm, Primitive Unit)) when s = nm ->
                  Ok (Target.Function (
                      Constructor (false, Cases (enum_name, cases)),
                      Literal (Unit ())))
              | LastTwo (_, (nm, _)) when s = nm ->
                  Error ("Constructor " ^ s
                    ^ " cannot be used in Ansible as it has arguments")
              | LastTwo (_, _) ->
                  Error ("Invalid valid " ^ s ^ " expected one of: "
                    ^ String.concat ", " (list2_map_list fst constrs))
            in let^ res = construct_case constrs
            in k (res, Target.Named (Cases (enum_name, constrs)))
        | Some (Named (List t)) ->
            codegen v (Some t) (fun (e, t) ->
              k (singleton_list t e, Target.Named (List t)))
        | _ -> Error "Incorrect type, found string-like"
        end
    | Ident nm ->
        begin match Hashtbl.find_opt env nm with
        | Some (Concrete t) -> Result.bind (coerce_value ty (Variable nm) t) k
        | Some (Unknown t) ->
            begin match ty with
            | None ->
                let () = Hashtbl.add env nm (Concrete t)
                in k (Variable nm, t)
            | Some ty ->
                let () = Hashtbl.add env nm (Concrete ty)
                in k (Variable nm, ty)
            end
        | None ->
            (* See if this is a built-in variable *)
            match nm with
            | "ansible_os_family" ->
                let^ res =
                  Result.bind
                    (coerce_value ty (Variable "!os_family") (Primitive String))
                    k
                in Ok (Target.Seq (
                    Get ("!os_family",
                      OnElement (element ctx "env", Literal (Unit ()),
                        AttrAccess (attribute ctx "os_family"))),
                    res))
            | "ansible_distribution" ->
                let^ res =
                  Result.bind
                    (coerce_value ty (Variable "!distribution") (Primitive String))
                    k
                in Ok (Target.Seq (
                    Get ("!distribution",
                      OnElement (element ctx "env", Literal (Unit ()),
                        AttrAccess (attribute ctx "os_distribution"))),
                    res))
            | "ansible_user_id" ->
                let^ res =
                  Result.bind
                    (coerce_value ty (Variable "!user_id") (Primitive String))
                    k
                in Ok (Target.Seq (
                    Get ("!user_id",
                      OnElement (element ctx "env", Literal (Unit ()),
                        AttrAccess (attribute ctx "active_user"))),
                    res))
            (* FIXME: This should actually be the group ID not number (I think) *)
            | "ansible_user_gid" ->
                let^ res =
                  Result.bind
                    (coerce_value ty (Variable "!group_gid") (Primitive String))
                    k
                in Ok (Target.Seq (
                    Get ("!group_gid",
                      OnElement (element ctx "env", Literal (Unit ()),
                        AttrAccess (attribute ctx "active_group"))),
                    res))
            | _ -> Error ("Unknown variable " ^ nm)
        end
    | Fact nm ->
        begin match nm with
        | "os_family" ->
            let^ res =
              Result.bind
                (coerce_value ty (Variable "!os_family") (Primitive String))
                k
            in Ok (Target.Seq (
                Get ("!os_family",
                  OnElement (element ctx "env", Literal (Unit ()),
                    AttrAccess (attribute ctx "os_family"))),
                res))
        | "distribution" ->
            let^ res =
              Result.bind
                (coerce_value ty (Variable "!distribution") (Primitive String))
                k
            in Ok (Target.Seq (
                Get ("!distribution",
                  OnElement (element ctx "env", Literal (Unit ()),
                    AttrAccess (attribute ctx "os_distribution"))),
                res))
        | _ -> Error ("Unknown ansible_fact " ^ nm)
        end
    | Unary (v, op) ->
        begin match op with
        | Not ->
            codegen v (Some (Primitive Bool)) (fun (v, _) ->
              Result.bind
                (coerce_value ty (Function (BoolNeg, v)) (Primitive Bool))
                k)
        | Neg ->
            codegen v None (fun (v, t) ->
              match t with
              | Primitive Int ->
                  Result.bind 
                    (coerce_value ty
                      (Function (SubInt, Pair (Literal (Int 0), v)))
                      (Primitive Int))
                    k
              | Primitive Float ->
                  Result.bind
                    (coerce_value ty
                      (Function (SubFloat, Pair (Literal (Float 0.0), v)))
                      (Primitive Float))
                    k
              | _ -> Error "Incorrect type, cannot negate non-numeric type")
        | Lower ->
            codegen v (Some (Primitive String)) (fun (v, _) ->
              Result.bind
                (coerce_value ty (Function (ToLower, v)) (Primitive String))
                k)
        end
    | Binary (lhs, op, rhs) ->
        begin match op with
        (* For the numeric ops, since we allow int -> float promotion, we have
         * to be careful to not just take the type of the first but to instead
         * join the types of both arguments to determine the type of the
         * operation and then coerce each side as needed *)
        | Add | Sub | Mul | Pow | Div | Mod | Lt | Gt | Le | Ge ->
            let (lhs, rhs, op_name, int_op, float_op)
              : Ast.value * Ast.value * string
              * (Target.funct * Target.typ) option
              * (Target.funct * Target.typ) option =
              match op with
              | Add -> (lhs, rhs, "+",
                        Some (AddInt, Primitive Int),
                        Some (AddFloat, Primitive Float))
              | Sub -> (lhs, rhs, "-",
                        Some (SubInt, Primitive Int),
                        Some (SubFloat, Primitive Float))
              | Mul -> (lhs, rhs, "*",
                        Some (MulInt, Primitive Int),
                        Some (MulFloat, Primitive Float))
              | Pow -> (lhs, rhs, "^",
                        None,
                        Some (Power, Primitive Float))
              | Div -> (lhs, rhs, "/",
                        Some (DivInt, Primitive Int),
                        Some (DivFloat, Primitive Float))
              | Mod -> (lhs, rhs, "%",
                        Some (Modulo, Primitive Int),
                        None)
              | Lt  -> (lhs, rhs, "<",
                        Some (LtInt, Primitive Bool),
                        Some (LtFloat, Primitive Bool))
              | Gt  -> (rhs, lhs, ">",
                        Some (LtInt, Primitive Bool),
                        Some (LtFloat, Primitive Bool))
              | Le  -> (lhs, rhs, "<=",
                        Some (LeInt, Primitive Bool),
                        Some (LeFloat, Primitive Bool))
              | Ge  -> (rhs, lhs, ">=",
                        Some (LeInt, Primitive Bool),
                        Some (LeFloat, Primitive Bool))
              | _ -> failwith "matching error"
            in codegen lhs None (fun (lhs, lty) ->
                codegen rhs None (fun (rhs, rty) ->
                  match lty, rty, int_op, float_op with
                  | _, _, None, None -> failwith "operator with no definition"
                  | Primitive Int, Primitive Int, Some (f, res), _ ->
                      Result.bind
                        (coerce_value ty (Function (f, Pair (lhs, rhs))) res)
                        k
                  | Primitive Int, Primitive Int, None, Some (f, res) ->
                      Result.bind
                        (coerce_value ty
                          (Function (f, Pair (
                            Function (FloatOfInt, lhs),
                            Function (FloatOfInt, rhs)))) res)
                        k
                  | Primitive Int, Primitive Float, _, Some (f, res) ->
                      Result.bind
                        (coerce_value ty
                          (Function (f, 
                            Pair (Function (FloatOfInt, lhs), rhs))) res)
                        k
                  | Primitive Float, Primitive Int, _, Some (f, res) ->
                      Result.bind
                        (coerce_value ty
                          (Function (f,
                            Pair (lhs, Function (FloatOfInt, rhs)))) res)
                        k
                  | Primitive Float, Primitive Float, _, Some (f, res) ->
                      Result.bind
                        (coerce_value ty
                          (Function (f, Pair (lhs, rhs))) res)
                        k
                  | _, _, _, _ ->
                      Error (Printf.sprintf 
                        "Operator %s not defined for given types" op_name)))
        (* For equals and not equals we need equal types, but we'll try to
         * coerce either direction if needed *)
        | Eq | Neq ->
            let f ty lhs rhs : Target.expr =
              match op with
              | Eq -> Function (Equal ty, Pair (lhs, rhs))
              | Neq -> Function (BoolNeg, Function (Equal ty, Pair (lhs, rhs)))
              | _ -> failwith "matching ereror"
            in codegen_same lhs rhs (fun lhs rhs t ->
                Result.bind (coerce_value ty (f t lhs rhs) (Primitive Bool)) k)
        | And | Or ->
            let op : Target.funct =
              match op with
              | And -> BoolAnd
              | Or  -> BoolOr
              | _   -> failwith "matching error"
            in codegen lhs (Some (Primitive Bool)) (fun (lhs, _) ->
                codegen rhs (Some (Primitive Bool)) (fun (rhs, _) ->
                  Result.bind
                    (coerce_value ty (Function (op, Pair (lhs, rhs))) 
                      (Primitive Bool))
                    k))
        | Concat ->
            codegen lhs (Some (Primitive String)) (fun (lhs, _) ->
              codegen rhs (Some (Primitive String)) (fun (rhs, _) ->
                Result.bind
                  (coerce_value ty (Function (Concat, Pair (lhs, rhs)))
                    (Primitive String))
                  k))
        end
    | Dot (ex, field) ->
        (* TODO: Can we code-gen it under a context requiring field and its type? *)
        codegen ex None (fun (ex, t) ->
          match t with
          | Struct fields ->
              begin match StringMap.find_opt field fields with
              | None -> Error (Printf.sprintf "Value has no field %s" field)
              | Some t ->
                  Result.bind
                    (coerce_value ty (Function (ReadField (fields, field), ex))
                      t)
                    k
              end
          | _ -> Error (Printf.sprintf "Value has no field %s" field))
    | VarDefined v ->
        Result.bind
          (coerce_value ty (Literal (Bool (Hashtbl.mem env v)))
            (Primitive Bool))
          k
    | Ternary (cond, thn, els) ->
        codegen cond (Some (Primitive Bool)) (fun (cond, _) ->
          codegen thn ty (fun (thn, resTy) ->
            codegen els ty (fun (els, _) ->
              let var = new_tmp ()
              in Result.bind (k (Variable var, resTy)) (fun s ->
                Ok (Target.Seq (
                  Cond (cond, Assign (var, thn), Assign (var, els)),
                  s))))))
    | Record fields ->
        let^ field_tys =
          match ty with
          | None -> Ok StringMap.empty
          | Some (Struct ts) -> Ok ts
          | _ -> Error "Incorrect type, found record"

        in let rec process_fields (fields : (string * Ast.value) list)
          (tys : Target.typ StringMap.t)
          (k : Target.expr -> Target.typ StringMap.t 
              -> (Target.stmt, string) result) : (Target.stmt, string) result =
          match fields with
          | [] -> k (Function (EmptyStruct tys, Literal (Unit ()))) tys
          | (nm, v) :: tl ->
              if StringMap.mem nm tys
              then Error ("Duplicate key " ^ nm ^ " in sequence")
              else
                codegen v (StringMap.find_opt nm field_tys) (fun (v, t) ->
                  process_fields tl (StringMap.add nm t tys) (fun r tys ->
                    k (Function (AddField (tys, nm), Pair (r, v))) tys))

        in process_fields fields StringMap.empty (fun v ts -> k (v, Struct ts))

  (* Takes two values which can be of any type but we want to be of the
   * same type. *)
  and codegen_same (x : Ast.value) (y : Ast.value)
    (k : Target.expr -> Target.expr -> Target.typ -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match
      codegen x None (fun (x, t) -> codegen y (Some t) (fun (y, _) -> k x y t))
    with
    | Ok res -> Ok res
    | Error _ ->
        codegen y None (fun (y, t) -> codegen x (Some t) (fun (x, _) -> k x y t))

  in codegen v ty k

(* TODO: Needs to generate the check for failure and exception raise *)
let codegen_module_invocation (_m : Ast.mod_use) (_ctx : Context.context)
  (_env : play_env) (_register : string) : (Target.stmt * Target.typ, string) result =
  Error "TODO"

let rec codegen_task (t : Ast.task) (ctx : Context.context) (env : play_env)
  : (Target.stmt, string) result =
  let^ body =
    match t.loop with
    | None ->
        let^ body =
          match t.body with
          | Module m ->
              let^ (stmt, typ) = codegen_module_invocation m ctx env t.register
              in let () =
                if t.register <> "_"
                then Hashtbl.add env t.register (Concrete typ)
              in Ok stmt
          | Block { tasks; rescue; always } ->
              let^ tasks = codegen_tasks tasks ctx env
              in let^ rescue =
                match rescue with
                (* If there is no rescue block we re-raise any exception *)
                | None -> Ok (Target.Raise (Variable "!catch"))
                | Some rescue -> codegen_tasks rescue ctx env
              in let^ always =
                match always with
                | None -> Ok Target.Pass
                | Some always -> codegen_tasks always ctx env
              in Ok (tryCatch ctx tasks rescue always)
        in let error_handling =
          if t.ignore_errors
          then tryCatch ctx body Pass Pass
          else body
        in let^ notification =
          fold_map_res
            (fun v -> codegen_value v (Some (Primitive String)) ctx env
              (fun (nm, _) ->
                (* !notified = nm :: !notified *)
                Ok (Assign ("!notified",
                  Function (Constructor (false, List (Primitive String)),
                    Pair (nm, Variable "!notified"))))))
            (fun notify stmt -> Target.Seq (stmt, notify))
            t.notify
            error_handling
        in let^ conditioned =
          match t.condition with
          | None -> Ok notification
          | Some v ->
              codegen_value (list_to_and v) (Some (Primitive Bool)) ctx env
                (fun (cond, _) ->
                  Ok (Target.Cond (cond, notification, Pass)))
        in Ok conditioned
    | _ -> Error "TODO"
  in Ok body (* Handle become/become_user *)

  (*
  let () =
    match t.loop with
    | None -> ()
    | Some (FileGlob _) -> Hashtbl.add env "item" (Concrete (Primitive Path))
    | Some (ItemLoop v) ->
        (* Item loops may end up with the item type constrained by a usage
         * to give us more information, but we'll first try to type it in
         * case the item's usage is not in a constrained context *)
        match codegen_value v None ctx env with
        | Ok (_, Named (List t)) -> Hashtbl.add env "item" (Unknown ("item", t))
        | Ok (_, t) -> Hashtbl.add env "item" (Unknown ("item", t))
        | _ -> Hashtbl.add env "item" (Unknown ("item", Primitive String))
  in let^ body =
    match t.body with
    | Module m ->
        let^ (stmt, typ) = codegen_module_invocation m ctx env t.register
        in let () =
          if t.register <> "_" then Hashtbl.add env t.register (Concrete typ)
        in Ok stmt
    | Block { tasks; rescue; always} ->
        let^ tasks = codegen_tasks tasks ctx env
        in let^ rescue =
          match rescue with
          (* If there is no catch block, we re-raise any exception *)
          | None -> Ok (Target.Raise (Variable "!catch"))
          | Some rescue -> codegen_tasks rescue ctx env
        in let^ always =
          match always with
          | None -> Ok Target.Pass
          | Some always -> codegen_tasks always ctx env
        in Ok (tryCatch ctx tasks rescue always)
  in let error_handling =
    if t.ignore_errors
    then tryCatch ctx body Pass Pass
    else body
  in let^ conditioned =
    match t.condition with
    | None -> Ok error_handling
    | Some v -> 
        let^ (cond, _) =
          codegen_value (list_to_and v) (Some (Primitive Bool)) ctx env
        in Ok (Target.Cond (cond, error_handling, Pass))
  in let^ () =
    match t.loop, t.body with
    | Some _, Block _ -> Error "Cannot loop over a block"
    | _, _ -> Ok ()
  in let _looped =
    match t.loop with
    | None -> Ok conditioned
    | Some (ItemLoop lst) ->
        let item_typ =
          match Hashtbl.find env "item" with
          | Unknown (_, t) -> t
          | Concrete t -> t
        in let () = Hashtbl.remove env "item"
        in let^ (lst, _) =
          codegen_value lst (Some (Named (List item_typ))) ctx env
        in if t.register = "_"
        then Ok (Target.ForEach ("_", Primitive Unit, lst, "item", conditioned))
        else
          let result_typ =
            match Hashtbl.find env t.register with
            | Unknown (_, t) -> t
            | Concrete t -> t
          in let strct : Target.typ StringMap.t =
            StringMap.singleton "results" (Target.Named (List result_typ))
          in let () = Hashtbl.add env t.register (Concrete (Target.Struct strct))
          in Ok (seq [
            ForEach ("!results", result_typ, lst,
              "item", Seq (conditioned, Yield (Variable t.register)));
            Assign (t.register,
              Function (AddField (strct, "results"),
                Pair (Function (EmptyStruct strct, Literal (Unit ())),
                  Variable "!results")))
          ])
    | Some (FileGlob _glob) -> Error "TODO"
  in Error "TODO"
  *)

and codegen_tasks (ts : Ast.task list) (ctx : Context.context)
  (env : play_env) : (Target.stmt, string) result =
  match ts with
  | [] -> Ok Pass
  | t :: ts ->
      let^ t = codegen_task t ctx env
      in let^ ts = codegen_tasks ts ctx env
      in Ok (Target.Seq (t, ts))

let codegen_handler (h : Ast.handler) (ctx : Context.context) (env : play_env)
  : (Target.stmt, string) result =
  let listen = h.listen
  in let^ h =
    codegen_task {
      name = h.name; register = h.register; ignore_errors = h.ignore_errors;
      condition = h.condition; loop = h.loop; body = Module h.module_invoke;
      become = h.become; become_user = h.become_user; notify = [] } ctx env
  in
  Ok (Target.Cond (
    Function (SetContains, Pair (Literal (String listen), Variable "#input")),
    h, Pass))

(* Given a list of handlers, we produce a function (action) which invokes the
 * notified handlers (which are provided as a list of strings *)
let codegen_handlers (hs : Ast.handler list) (ctx : Context.context)
  (env : play_env)
  : (Target.action, string) result =
  let rec codegen (hs : Ast.handler list) : (Target.stmt, string) result =
    match hs with
    | [] -> Ok Pass
    | hd :: tl ->
        let^ hd = codegen_handler hd ctx env
        in let^ tl = codegen tl
        in Ok (Target.Seq (hd, tl))
  in let^ hs = codegen hs
  in Ok ("handlers",
         Target.Primitive StringSet, Target.Primitive Unit,
         ref (Some hs))

(* TODO: This does not account for hosts
 * - The most likely solution is to condition on some kind of expression like
 *   isHostIncluded(env().host, <hosts>) *)
let codegen_play (p : Ast.play) (ctx : Context.context)
  : (Target.stmt, string) result =
  let play_env = Hashtbl.create 10
  in let () = List.iter (fun (nm, _) ->
    Hashtbl.add play_env nm (Unknown (Primitive String))
  ) p.vars
  in let^ pre_tasks =
    match p.pre_tasks with
    | None -> Ok None
    | Some ts -> Result.map Option.some (codegen_tasks ts ctx play_env)
  in let^ tasks = codegen_tasks p.tasks ctx play_env
  in let^ post_tasks =
    match p.post_tasks with
    | None -> Ok None
    | Some ts -> Result.map Option.some (codegen_tasks ts ctx play_env)
  in let^ handlers = codegen_handlers p.handlers ctx play_env
  in let^ vars =
    fold_map_res (fun (nm, v) ->
        let var_typ =
          match Hashtbl.find play_env nm with
          | Unknown t -> t
          | Concrete t -> t
        in codegen_value v (Some var_typ) ctx play_env (fun (v, t) ->
          let () = Hashtbl.add play_env nm (Concrete t)
          in Ok (Target.Assign (nm, v))))
      (fun assign s -> Target.Seq (assign, s))
      p.vars Target.Pass
  in let user_setup : Target.stmt =
    seq [
      (* env().active_user = p.remote_user *)
      Add (Element (element ctx "env", Literal (Unit ()),
        Some (Attribute (attribute ctx "active_user",
          Literal (String p.remote_user)))));
      (* env().is_root = p.is_root *)
      begin match p.is_root with
      | None -> Pass
      | Some b ->
          Add (Element (element ctx "env", Literal (Unit ()),
            Some (Attribute (attribute ctx "is_root",
              Literal (Bool b)))))
      end;
      (* assert can_become(env().active_user, p.become_user) *)
      Cond (
        Function (CanBecome,
          Pair (Literal (String p.remote_user),
            Literal (String p.become_user))),
        seq [
          (* env().active_user = p.become_user *)
          Add (Element (element ctx "env", Literal (Unit ()),
            Some (Attribute (attribute ctx "active_user",
              Literal (String p.become_user)))));
          (* env().active_group = p.become_user *)
          Add (Element (element ctx "env", Literal (Unit ()),
            Some (Attribute (attribute ctx "active_group",
              Literal (String p.become_user)))));
          (* env().is_root = p.become_user == "root" *)
          Add (Element (element ctx "env", Literal (Unit ()),
            Some (Attribute (attribute ctx "is_root",
              Literal (Bool (p.become_user = "root"))))))
        ],
        Context.fatal "assertion failed" ctx.excepts)
    ]
  in Ok (seq [
    user_setup;
    vars;
    (* TODO: Support force_handlers option in a play, which would cause the
     * handlers invocation to be moved into a finally block *)
    begin match pre_tasks with
    | None -> Pass
    | Some pre_tasks ->
        seq [
          Assign ("!notified",
            Function (Constructor (true, List (Primitive String)),
              Literal (Unit ())));
          pre_tasks;
          Action ("_", handlers, Variable "!notified") ]
    end;
    seq [
      Assign ("!notified",
        Function (Constructor (true, List (Primitive String)),
          Literal (Unit ())));
      tasks;
      Action ("_", handlers, Variable "!notified") ];
    begin match post_tasks with
    | None -> Pass
    | Some post_tasks ->
        seq [
          Assign ("!notified",
            Function (Constructor (true, List (Primitive String)),
              Literal (Unit ())));
          post_tasks;
          Action ("_", handlers, Variable "!notified") ]
    end
  ])

let codegen_playbook (p : Ast.playbook) (ctx : Context.context)
  : (Target.stmt, string) result =
  (* The preamble to Ansible programs sets up the environment appropriately.
   * In particular:
   * - ensure env() exists
   * - ensure env().time_counter is 0
   * - ensure env().last_reboot is -1
   *)
  let^ preamble : Target.stmt =
    Modules.Codegen.codegen_stmts
      [ AssertExists (FuncExp (Id "env", []))
      ; Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"),
                           IntLit 0, Eq))
      ; Assert (BinaryExp (Field (FuncExp (Id "env", []), "last_reboot"),
                           IntLit (-1), Eq)) ]
      ctx.types ctx.globals ctx.excepts Modules.Codegen.empty_local_env
      (Primitive Unit) None None (Ok Pass)

  in Result.bind (
      List.fold_right (fun play res -> Result.bind res (fun res ->
        Result.bind (codegen_play play ctx) (fun hd ->
          Ok (Target.Seq (hd, res)))))
        p
        (Ok Target.Pass)) (fun s ->
      Ok (Target.Seq (preamble, s)))
