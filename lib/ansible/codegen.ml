let ( let^ ) r f = Result.bind r f
let ( let$ ) r f = r f

module Typed = Semant.Typed

module Target = Modules.Target.Ast_Target
module Context = Modules.Codegen

module StringMap = Modules.Target.StringMap
module StringSet = Modules.Target.StringSet

type 'a list2 = 'a Modules.Target.list2

type play_env = (string, Target.typ) Hashtbl.t

let cnt = ref 0
let new_tmp () =
  let n = !cnt
  in let () = cnt := n + 1
  in "!" ^ string_of_int n
let named_tmp (s : string) =
  let n = !cnt
  in let () = cnt := n + 1
  in "!" ^ s ^ string_of_int n

let rec typ_of_itype (t : Semant.itype) : Target.typ =
  match t with
  | Int -> Primitive Int
  | Float -> Primitive Float
  | Bool -> Primitive Bool
  | StringLike | String -> Primitive String
  | Path -> Primitive Path
  | Enum (nm, cs) -> Named (Cases (nm, cs))
  (* Somewhat arbitrary coercion but we have to do something *)
  | EmptyList -> Named (List (Primitive Unit))
  | List t -> Named (List (typ_of_itype t))
  | Struct ts -> Struct (StringMap.map typ_of_itype ts)

let env_attr (attr : string) (ty : Target.typ) : Target.attr =
  OnElement (("env", Primitive Unit), Literal (Unit ()),
    AttrAccess (attr, ty))

let env_qual (attr : string) (ty : Target.typ) (v : Target.expr) : Target.qual =
  Element (("env", Primitive Unit), Literal (Unit ()),
    Some (Attribute ((attr, ty), v)))

let rec seq (ts : Target.stmt list) : Target.stmt =
  match ts with
  | [] -> Target.Pass
  | [s] -> s
  | s :: tl -> Target.Seq (s, seq tl)

let rec codegen_enum (c : string) (enum_nm : string) 
  (cases : (string * Target.typ) list2) : (Target.expr, string) result =
  match cases with
  | LastTwo ((c1, t1), (c2, t2)) ->
      if c = c1
      then
        match t1 with
        | Primitive Unit ->
            Ok (Function (Constructor (true, Cases (enum_nm, cases)),
                          Literal (Unit ())))
        | _ -> Error "Enum value in Ansible cannot have arguments"
      else if c = c2
      then
        match t2 with
        | Primitive Unit ->
            Ok (Function (Constructor (false, Cases (enum_nm, cases)),
                          Literal (Unit ())))
        | _ -> Error "Enum value in Ansible cannot have arguments"
      else Error ("No such constructor: " ^ c)
  | Cons ((c1, t1), tl) ->
      if c = c1
      then
        match t1 with
        | Primitive Unit ->
            Ok (Function (Constructor (true, Cases (enum_nm, cases)),
                          Literal (Unit ())))
        | _ -> Error "Enum value in Ansible cannot have arguments"
      else
        let^ res = codegen_enum c enum_nm tl
        in Ok (Function (Constructor (false, Cases (enum_nm, cases)),
                         res) : Target.expr)

let rec codegen_list (elem_ty : Target.typ) (vals : Target.expr list)
  : Target.expr =
  match vals with
  | [] -> Function (Constructor (true, List elem_ty), Literal (Unit ()))
  | v :: vs ->
      Function (Constructor (false, List elem_ty),
        Pair (v, codegen_list elem_ty vs))

(* Given a type that some expression has and a type that we need to coerce it
 * to, generates the resulting type and None if no coersion is needed or
 * Some f where f e k produces the result of k run on the coercion of e. *)
let rec codegen_coerce (ty : Target.typ) (need : Semant.itype)
  : (Target.typ * (Target.expr -> (Target.expr -> (Target.stmt, string) result)
                    -> (Target.stmt, string) result) option,
     string) result =
  match ty, need with
  | Primitive Int, Int -> Ok (Primitive Int, None)
  | Primitive Int, Float ->
      Ok (Primitive Float, Some (fun e k -> k (Function (FloatOfInt, e))))
  | Primitive Int, (StringLike | String) ->
      Ok (Primitive String, Some (fun e k -> k (Function (StringOfInt, e))))
  | Primitive Int, Path ->
      Ok (Primitive Path, Some (fun e k ->
          k (Function (PathOfString, Function (StringOfInt, e)))))

  | Primitive Float, Float -> Ok (Primitive Float, None)
  | Primitive Float, (StringLike | String) ->
      Ok (Primitive String, Some (fun e k -> k (Function (StringOfFloat, e))))
  | Primitive Float, Path ->
      Ok (Primitive Path, Some (fun e k ->
          k (Function (PathOfString, Function (StringOfFloat, e)))))

  | Primitive Bool, Bool -> Ok (Primitive Bool, None)
  | Primitive Bool, (StringLike | String) ->
      Ok (Primitive String, Some (fun e k -> k (Function (StringOfBool, e))))
  | Primitive Bool, Path ->
      Ok (Primitive Path, Some (fun e k ->
          k (Function (PathOfString, Function (StringOfBool, e)))))

  | Primitive String, (StringLike | String) -> Ok (Primitive String, None)
  | Primitive String, Path ->
      Ok (Primitive Path, Some (fun e k -> k (Function (PathOfString, e))))

  | Primitive Path, Path -> Ok (Primitive Path, None)
  | Primitive Path, (StringLike | String) ->
      Ok (Primitive String, Some (fun e k -> k (Function (StringOfPath, e))))

  | Named (Cases (n, _)), Enum (m, _) when n = m -> Ok (ty, None)

  | Named (List _), EmptyList -> Ok (ty, None)
  | Named (List t), List n ->
      let^ (elem_ty, coerce_elem) = codegen_coerce t n
      in begin match coerce_elem with
      (* No coercion is needed of elements *)
      | None -> Ok (Target.Named (List elem_ty), None)
      (* Coerce elements using a for-each expression *)
      | Some coerce_elem ->
          Ok (Target.Named (List elem_ty),
            Some (fun e k ->
              let^ coerce_body =
                coerce_elem (Target.Variable "#item")
                  (fun c -> Ok (Target.Yield c))
              in let tmp = new_tmp ()
              in let^ rest = k (Target.Variable tmp)
              in Ok (Target.Seq (
                      Target.ForEach (tmp, elem_ty, e, "#item", coerce_body),
                      rest))))
      end

  | Struct ts, Struct ns ->
      if StringMap.cardinal ts <> StringMap.cardinal ns
      then Error "Internal Error: mismatched record fields in code-gen"
      else
        let^ (res_ts, coercions, any_coerced) =
          StringMap.fold (fun f n acc ->
            let^ (res, coercions, any_coerced) = acc
            in let t = StringMap.find f ts
            in let^ (res_t, coerce) = codegen_coerce t n
            in match coerce with
            | None -> Ok (StringMap.add f res_t res,
                          (f, fun e k -> k e) :: coercions,
                          any_coerced)
            | Some c -> Ok (StringMap.add f res_t res,
                            (f, c) :: coercions,
                            true)
          ) ns (Ok (StringMap.empty, [], false))
        in begin match any_coerced with
        | false -> Ok ((Struct res_ts : Target.typ), None)
        | true ->
            Ok ((Struct res_ts : Target.typ),
                Some (fun e k ->
                  List.fold_left (fun k (f, coerce) new_struct ->
                    coerce (Function (ReadField (res_ts, f), e) : Target.expr)
                      (fun e_field ->
                        k (Function (AddField (res_ts, f),
                            Pair (new_struct, e_field)) : Target.expr))
                  ) k coercions
                  (Target.Function (EmptyStruct res_ts, Literal (Unit ())))
            ))
        end

  (* Promote single values to a list *)
  | t, List n ->
      let^ (res_t, coerce) = codegen_coerce t n
      in begin match coerce with
      | None -> Ok (Target.Named (List res_t),
                    Some (fun e k -> k (codegen_list res_t [e])))
      | Some coerce ->
          Ok (Target.Named (List res_t),
              Some (fun e k -> coerce e (fun res_e ->
                      k (codegen_list res_t [res_e]))))
      end

  | _, _ -> Error "Type Error in Codegen"

let codegen_value (v : Typed.value) (env : play_env)
  (k : Target.expr * Target.typ -> (Target.stmt, string) result)
  : (Target.stmt, string) result =

  let rec codegen (v : Typed.value)
    (k : Target.expr * Target.typ -> (Target.stmt, string) result)
    : (Target.stmt, string) result =
    match v with
    | String (s, t) ->
        begin match t with
        | StringLike | String ->
            k (Target.Literal (String s), Primitive String)
        | Path ->
            k (Target.Literal (Path s), Primitive Path)
        | Enum (nm, cs) ->
            let^ e = codegen_enum s nm cs
            in k (e, Named (Cases (nm, cs)))
        | _ -> 
            Error (Printf.sprintf "Codegen Error: String cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Int (i, t) ->
        begin match t with
        | Int -> k (Target.Literal (Int i), Primitive Int)
        | _ -> 
            Error (Printf.sprintf "Codegen Error: Int cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Float (f, t) ->
        begin match t with
        | Int -> k (Target.Literal (Float f), Primitive Float)
        | _ -> 
            Error (Printf.sprintf "Codegen Error: Float cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Bool (b, t) ->
        begin match t with
        | Bool -> k (Target.Literal (Bool b), Primitive Bool)
        | _ ->
            Error (Printf.sprintf "Codegen Error: Bool cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | List (vs, t) ->
        let rec codegen_vals (vs : Typed.value list) (elem : Target.typ option)
          (k : Target.expr * Target.typ -> (Target.stmt, string) result) =
          match vs with
          | v :: vs ->
              let$ (e, ety) = codegen v
              in let$ (evs, elem) = codegen_vals vs (Some ety)
              in k (Target.Function (Constructor (false, List elem),
                      Pair (e, evs)), elem)
          | [] ->
              match elem with
              | None ->
                  k (Target.Function (
                        Constructor (true, List (Primitive Unit)),
                        Literal (Unit ())), Primitive Unit)
              | Some elem ->
                  k (Target.Function (
                        Constructor (true, List elem),
                        Literal (Unit ())), elem)
        in let^ elem =
          match t with
          | List t -> Ok (Some (typ_of_itype t))
          | EmptyList -> Ok None
          | _ -> 
              Error (Printf.sprintf "Codegen Error: List cannot have type %s"
                      (Semant.string_of_itype t))
        in let$ (e, elemTy) = codegen_vals vs elem
        in k (e, Named (List elemTy))
    | Ident (nm, t) ->
        let varty = Hashtbl.find env nm
        in let^ (t, coerce) = codegen_coerce varty !t
        in begin match coerce with
        | None -> k (Variable nm, t)
        | Some coerce -> coerce (Variable nm) (fun res_e -> k (res_e, t))
        end
    | Unary ((v, op), t) ->
        begin match op, t with
        | Not, Bool ->
            let$ (e, _) = codegen v
            in k (Target.Function (BoolNeg, e), Primitive Bool)
        | Not, _ ->
            Error (Printf.sprintf "Codegen Error: Not cannot have type %s"
                    (Semant.string_of_itype t))
        | Neg, Int ->
            let$ (e, _) = codegen v
            in k (Target.Function (SubInt, Pair (Literal (Int 0), e)),
                  Primitive Int)
        | Neg, Float ->
            let$ (e, _) = codegen v
            in k (Target.Function (SubFloat, Pair (Literal (Float 0.0), e)),
                  Primitive Float)
        | Neg, _ ->
            Error (Printf.sprintf "Codegen Error: Neg cannot have type %s"
                    (Semant.string_of_itype t))
        | Lower, String ->
            let$ (e, _) = codegen v
            in k (Target.Function (ToLower, e), Primitive String)
        | Lower, _ ->
            Error (Printf.sprintf "Codegen Error: Lower cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Binary ((lhs, op, rhs), t) ->
        begin match op, t with
        | Add, Int ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (AddInt, Pair (lhs, rhs)), Primitive Int)
        | Add, Float ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (AddFloat, Pair (lhs, rhs)), Primitive Float)
        | Add, _ ->
            Error (Printf.sprintf "Codegen Error: Add cannot have type %s"
                    (Semant.string_of_itype t))
        | Sub, Int ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (SubInt, Pair (lhs, rhs)), Primitive Int)
        | Sub, Float ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (SubFloat, Pair (lhs, rhs)), Primitive Float)
        | Sub, _ ->
            Error (Printf.sprintf "Codegen Error: Sub cannot have type %s"
                    (Semant.string_of_itype t))
        | Mul, Int ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (MulInt, Pair (lhs, rhs)), Primitive Int)
        | Mul, Float ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (MulFloat, Pair (lhs, rhs)), Primitive Float)
        | Mul, _ ->
            Error (Printf.sprintf "Codegen Error: Mul cannot have type %s"
                    (Semant.string_of_itype t))
        | Pow, Float ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (Power, Pair (lhs, rhs)), Primitive Float)
        | Pow, _ ->
            Error (Printf.sprintf "Codegen Error: Pow cannot have type %s"
                    (Semant.string_of_itype t))
        | Div, Int ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (DivInt, Pair (lhs, rhs)), Primitive Int)
        | Div, Float ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (DivFloat, Pair (lhs, rhs)), Primitive Float)
        | Div, _ ->
            Error (Printf.sprintf "Codegen Error: Div cannot have type %s"
                    (Semant.string_of_itype t))
        | Mod, Int ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (Modulo, Pair (lhs, rhs)), Primitive Int)
        | Mod, _ ->
            Error (Printf.sprintf "Codegen Error: Mod cannot have type %s"
                    (Semant.string_of_itype t))
        | And, Bool ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (BoolAnd, Pair (lhs, rhs)), Primitive Bool)
        | And, _ ->
            Error (Printf.sprintf "Codegen Error: And cannot have type %s"
                    (Semant.string_of_itype t))
        | Or, Bool ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (BoolOr, Pair (lhs, rhs)), Primitive Bool)
        | Or, _ ->
            Error (Printf.sprintf "Codegen Error: Or cannot have type %s"
                    (Semant.string_of_itype t))
        | Neq, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (BoolNeg,
                    Target.Function (Equal t, Pair (lhs, rhs))),
                    Primitive Bool)
        | Neq, _ ->
            Error (Printf.sprintf "Codegen Error: Neq cannot have type %s"
                    (Semant.string_of_itype t))
        | Eq, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (Equal t, Pair (lhs, rhs)), Primitive Bool)
        | Eq, _ ->
            Error (Printf.sprintf "Codegen Error: Eq cannot have type %s"
                    (Semant.string_of_itype t))
        | Lt, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in begin match t with
            | Primitive Int ->
                k (Target.Function (LtInt, Pair (lhs, rhs)), Primitive Bool)
            | Primitive Float ->
                k (Target.Function (LtFloat, Pair (lhs, rhs)), Primitive Bool)
            | _ -> Error "Codegen Error: Lt argument is not a number"
            end
        | Lt, _ ->
            Error (Printf.sprintf "Codegen Error: Lt cannot have type %s"
                    (Semant.string_of_itype t))
        | Gt, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in begin match t with
            | Primitive Int ->
                k (Target.Function (LtInt, Pair (rhs, lhs)), Primitive Bool)
            | Primitive Float ->
                k (Target.Function (LtFloat, Pair (rhs, lhs)), Primitive Bool)
            | _ -> Error "Codegen Error: Gt argument is not a number"
            end
        | Gt, _ ->
            Error (Printf.sprintf "Codegen Error: Gt cannot have type %s"
                    (Semant.string_of_itype t))
        | Le, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in begin match t with
            | Primitive Int ->
                k (Target.Function (LeInt, Pair (lhs, rhs)), Primitive Bool)
            | Primitive Float ->
                k (Target.Function (LeFloat, Pair (lhs, rhs)), Primitive Bool)
            | _ -> Error "Codegen Error: Le argument is not a number"
            end
        | Le, _ ->
            Error (Printf.sprintf "Codegen Error: Le cannot have type %s"
                    (Semant.string_of_itype t))
        | Ge, Bool ->
            let$ (lhs, t) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in begin match t with
            | Primitive Int ->
                k (Target.Function (LeInt, Pair (rhs, lhs)), Primitive Bool)
            | Primitive Float ->
                k (Target.Function (LeFloat, Pair (rhs, lhs)), Primitive Bool)
            | _ -> Error "Codegen Error: Ge argument is not a number"
            end
        | Ge, _ ->
            Error (Printf.sprintf "Codegen Error: Ge cannot have type %s"
                    (Semant.string_of_itype t))
        | Concat, String ->
            let$ (lhs, _) = codegen lhs
            in let$ (rhs, _) = codegen rhs
            in k (Target.Function (Concat, Pair (lhs, rhs)), Primitive String)
        | Concat, _ ->
            Error (Printf.sprintf "Codegen Error: Concat cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Dot ((v, f), _) ->
        let$ (e, t) = codegen v
        in begin match t with
        | Struct fs ->
            k (Target.Function (ReadField (fs, f), e), StringMap.find f fs)
        | _ -> Error "Codegen Error: Dot cannot operate on non-struct"
        end
    | VarDefined (nm, t) ->
        begin match t with
        | Bool ->
            k (Target.Literal (Bool (Hashtbl.mem env nm)), Primitive Bool)
        | _ ->
            Error (Printf.sprintf "Codegen Error: VarDefined cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Fact (f, t) ->
        begin match f, t with
        | OSFamily, String ->
            let tmp = new_tmp ()
            in let^ cont = k (Target.Variable tmp, Primitive String)
            in Ok (Target.Seq (
                    Get (tmp, env_attr "os_family" (Primitive String)),
                    cont))
        | OSFamily, _ ->
            Error (Printf.sprintf "Codegen Error: OSFamily Fact cannot have type %s"
                    (Semant.string_of_itype t))
        | Distribution, String ->
            let tmp = new_tmp ()
            in let^ cont = k (Target.Variable tmp, Primitive String)
            in Ok (Target.Seq (
                    Get (tmp, env_attr "os_distribution" (Primitive String)),
                    cont))
        | Distribution, _ ->
            Error (Printf.sprintf "Codegen Error: Distribution Fact cannot have type %s"
                    (Semant.string_of_itype t))
        | UserID, String ->
            let tmp = new_tmp ()
            in let^ cont = k (Target.Variable tmp, Primitive String)
            in Ok (Target.Seq (
                    Get (tmp, env_attr "active_user" (Primitive String)),
                    cont))
        | UserID, _ ->
            Error (Printf.sprintf "Codegen Error: UserID Fact cannot have type %s"
                    (Semant.string_of_itype t))
        | GroupID, String ->
            let tmp = new_tmp ()
            in let^ cont = k (Target.Variable tmp, Primitive String)
            in Ok (Target.Seq (
                    Get (tmp, env_attr "active_group" (Primitive String)),
                    cont))
        | GroupID, _ ->
            Error (Printf.sprintf "Codegen Error: GroupID Fact cannot have type %s"
                    (Semant.string_of_itype t))
        end
    | Ternary ((cond, thn, els), _) ->
        let tmp = new_tmp ()
        in let res_ty = ref (Target.Primitive Unit)
        in let^ thn =
          codegen thn (fun (thn, ty) ->
            let () = res_ty := ty
            in Ok (Target.Assign (tmp, thn)))
        in let^ els =
          codegen els (fun (els, _) -> Ok (Target.Assign (tmp, els)))
        in let$ (cond, _) = codegen cond
        in let^ cont = k (Target.Variable tmp, !res_ty)
        in Ok (Target.Seq (Target.Cond (cond, thn, els), cont))
    | Record (fields, _) ->
        let rec codegen_fields (fs : (string * Typed.value) list)
          (ts : Target.typ StringMap.t) k =
          match fs with
          | [] ->
              k ((Function (EmptyStruct ts, Literal (Unit ())) : Target.expr),
                  ts)
          | (f, v) :: fs ->
              let$ (e, ety) = codegen v
              in let$ (efs, ts) = codegen_fields fs (StringMap.add f ety ts)
              in k ((Function (AddField (ts, f), Pair (e, efs)) : Target.expr),
                    ts)
        in codegen_fields fields StringMap.empty
            (fun (e, ts) -> k (e, Struct ts))
    | ReAnnt (v, c) ->
        let$ (e, t) = codegen v
        in let^ (res_ty, gen) = codegen_coerce t c
        in begin match gen with
        | None -> k (e, res_ty)
        | Some gen -> gen e (fun e -> k (e, res_ty))
        end

  in codegen v k

(* Note: ignore_errors appears to apply outside of the loop hence the catch
 * goes outside: https://stackoverflow.com/questions/49755884 *)
(* k is an optional statement to immediately follow the module invocation,
 * inside of any loop and condition, will execute only if the task succeeds *)
let codegen_mod_use (m : Typed.mod_use) (cond : Typed.value option)
  (loop : Typed.loop_kind option) (register : string) (ignore_errors : bool)
  (failed_when : Typed.value option) (env : play_env) (ctx : Context.context)
  (k : Target.stmt option) : (Target.stmt, string) result =
  (* If errors are ignored we wrap with a try-catch *)
  let { Typed.mod_info = (nm, in_tys, out_ty, body); args } = m
  in let$ () = fun k ->
    if not ignore_errors
    then k ()
    else
      let^ res = k ()
      in Ok (Target.TryCatch (res, "@except",
            Target.Match (
              Function (
                UnpackExcept (ctx.excepts, "AnsibleError"),
                Variable "@except"),
              "@", (* Don't care about the result *)
              (* None, some other error *)
              Raise (Variable "@except"),
              Target.Pass),
            (* No finally *)
            Target.Pass))
  in let$ () = fun k ->
    match loop with
    | None -> k ()
    | Some (ItemLoop v) ->
        let$ (e, t) = codegen_value v env
        in let^ () =
          match t with
          | Named (List ety) -> Ok (Hashtbl.add env "item" ety)
          | _ -> Error "Code Gen Error: expected list for loop"
        in let^ res = k ()
        in if register = "_"
        then Ok (Target.ForEach ("_", Primitive Unit, e, "item", res))
        else
          (* The results of loops are collected into a record with a results
           * field which is the list of results. We also have to update the
           * environment so that subsequent tasks have the right type for the
           * result of the loop. *)
          let res_fields = StringMap.singleton "results" (Target.Named (List out_ty))
          in let () = Hashtbl.replace env register (Struct res_fields)
          in let tmp = new_tmp ()
          in Ok (Target.Seq (
            ForEach (tmp, out_ty, e, "item",
              Seq (res, Yield (Variable register))),
            Assign (register,
              Function (AddField (res_fields, "results"), Pair (
                Function (EmptyStruct res_fields, Literal (Unit ())),
                Variable tmp)))))
    | Some (FileGlob v) ->
        let$ (e, _) = codegen_value v env
        in let () = Hashtbl.add env "item" (Primitive Path)
        in let^ res = k ()
        (* with_fileglob returns files on the local machine *)
        (* NOTE: There's a lot of stuff below that is very fragile; I would
         * much rather pull the information from the context, instead of
         * building stuff by hand, but it is quite annoying do to so. *)
        in let find_file_type_cs : (string * Target.typ) list2 =
          Cons (("any", Primitive Unit),
          Cons (("directory", Primitive Unit),
          LastTwo (("file", Primitive Unit),
                  ("link", Primitive Unit))))
        in let file_system_cs : (string * Target.typ) list2 =
          LastTwo (("remote", Primitive Unit), ("local", Primitive Unit))
        in let file_type_cs : (string * Target.typ) list2 =
          Cons (("file", Primitive String),
          Cons (("directory", Named (List (Primitive Path))),
          LastTwo (("hard", Primitive Path),
                  ("link", Primitive Path))))
        in let lst : Target.expr =
          Function (
            Uninterpreted ("file_glob",
              Product (Named (List (Primitive String)),
                Product (Named (Cases ("find_file_type", find_file_type_cs)),
                  Named (Cases ("file_system", file_system_cs)))),
              Named (List (Primitive Path))),
            Pair (e,
              Pair (Result.get_ok (codegen_enum "file" "find_file_type" find_file_type_cs),
                Result.get_ok (codegen_enum "local" "file_system" file_system_cs))))
        in let with_assertions : Target.stmt =
          (* Also add assertions about the items (they exist and are files) *)
          (* NOTE: Again, this is very fragile. file is thankfully the first
           * constructor of file_type *)
            Seq (
              Get ("tmp",
                OnElement (
                  ("fs",
                  Product (Primitive Path, 
                    Named (Cases ("file_system", file_system_cs)))),
                  Pair (Variable "item",
                    Result.get_ok (codegen_enum "local" "file_system" file_system_cs)),
                  AttrAccess ("fs_type", Named (Cases ("file_type", file_type_cs))))),
              Match (Variable "tmp", "_",
                res,
                Context.fatal "assertion failed" ctx.excepts))
        in if register = "_"
        then
          Ok (Target.ForEach ("_", Primitive Unit, lst, "item", with_assertions))
        else
          let res_fields = StringMap.singleton "results" (Target.Named (List out_ty))
          in let () = Hashtbl.replace env register (Struct res_fields)
          in let tmp = new_tmp ()
          in Ok (Target.Seq (
            ForEach (tmp, out_ty, lst, "item",
              Seq (with_assertions, Yield (Variable register))),
            Assign (register,
              Function (AddField (res_fields, "results"), Pair (
                Function (EmptyStruct res_fields, Literal (Unit ())),
                Variable tmp)))))
  in let$ () = fun k ->
    match cond with
    | None -> k ()
    | Some v ->
        let$ (e, _) = codegen_value v env
        in let^ body = k ()
        in Ok (Target.Cond (e, body, Pass))
  in let args = StringMap.of_list args
  in let$ arg =
    let rec codegen_struct (fs : (string * Target.typ) list) k =
      match fs with
      | [] ->
          k (Function (EmptyStruct in_tys, Literal (Unit ())) : Target.expr)
      | (f, t) :: tl ->
          match t with
          | Named (Option t) ->
            begin match StringMap.find_opt f args with
            | Some v ->
                let$ (e, _) = codegen_value v env
                in let$ res = codegen_struct tl
                in k (Target.Function (AddField (in_tys, f),
                      Pair (Function (Constructor (false, Option t), e), res)))
            | None ->
                let$ res = codegen_struct tl
                in k (Target.Function (AddField (in_tys, f),
                      Pair (Function (Constructor (true, Option t), 
                              Literal (Unit ())), res)))
            end
          | _ -> Error "Codegen Error: Arguments to module must be options"
    in codegen_struct (StringMap.to_list in_tys)
  in let^ out_fields =
    match out_ty with
    | Struct fs -> Ok fs
    | _ -> Error (Printf.sprintf "Error: Module %s does not return struct" nm)
  (* Update the environment with the result of the module *)
  in let () =
    if register <> "_"
    then Hashtbl.add env register out_ty
  in let^ act =
    match failed_when with
    | None ->
        Ok (Target.Seq (
          Action (register, (nm, Struct in_tys, out_ty, body), arg),
          Cond (
              Function (ReadField (out_fields, "failed"), Variable register),
              Context.raise "AnsibleError" (Literal (Unit ())) ctx.excepts,
              Pass)))
    | Some cond ->
        let$ (c, _) = codegen_value cond env
        in Ok (Target.Seq (
            Action (register, (nm, Struct in_tys, out_ty, body), arg),
            Cond (c,
              Context.raise "AnsibleError" (Literal (Unit ())) ctx.excepts,
              Pass)))
  in match k with
  | None -> Ok act
  | Some k -> Ok (Target.Seq (act, k))

let codegen_become (become : bool) (become_user : string) (body : Target.stmt)
  (ctx : Context.context) : Target.stmt =
  if not become then body
  (* Become means we should attempt to escalate to be become_user (we also
   * set is_root based on this) and then after the body we undo the
   * escalation. NOTE: It would actually be great to have local state to use
   * here; because we don't have that and have to perform resets we use a
   * try-catch-finally so that we can put the reset in the finally *)
  else
    (* Archive env().active_user/active_group/is_root (to tmps)
     * Assert can_escalate(env().active_user)
     * Set env().active_user/active_group/is_root based on become_user
     * body
     * Reset env().active_user/active_group/is_root (from tmps) *)
    let old_user = named_tmp "user"
    in let old_group = named_tmp "group"
    in let old_root = named_tmp "root"
    in seq [
      (* Stash current user/group *)
      Get (old_user, env_attr "active_user" (Primitive String));
      Get (old_group, env_attr "active_group" (Primitive String));
      Get (old_root, env_attr "is_root" (Primitive Bool));

      (* Assert that we can escalate *)
      Cond (Function (CanBecome,
              Pair (Variable old_user, Literal (String become_user))),
        Pass,
        Context.fatal "failed to become user" ctx.excepts);

      (* Update user/group *)
      Add (env_qual "active_user" (Primitive String)
            (Literal (String become_user)));
      Add (env_qual "active_group" (Primitive String)
            (Literal (String become_user)));
      Add (env_qual "is_root" (Primitive Bool)
            (Literal (Bool (become_user = "root"))));

      (* Body *)
      TryCatch (body, "@except", Raise (Variable "@except"),
        (* Reset user/group *)
        seq [
          Add (env_qual "active_user" (Primitive String) (Variable old_user));
          Add (env_qual "active_group" (Primitive String) (Variable old_group));
          Add (env_qual "is_root" (Primitive Bool) (Variable old_root))
        ])
    ]

let rec codegen_task (t : Typed.task) (extra_notify : Target.expr list)
  (env : play_env) (ctx : Context.context) : (Target.stmt, string) result =
  let^ body =
    match t.body with
    | Module m ->
      (* Notifying of handlers only occurs if the result task produced a change
       * and the task succeeded. *)
      let^ do_notify =
        let { Typed.mod_info = (nm, _, out_ty, _); _ } = m
        (* We have to add the result to the environment so we can properly
         * resolve variables for notify and changed_when *)
        in let () =
          if t.register <> "_"
          then Hashtbl.add env t.register out_ty
        in let$ names =
          let rec codegen_notifies (vs : Typed.value list)
            (k : Target.expr list -> (Target.stmt, string) result) =
            match vs with
            | [] -> k extra_notify
            | v :: vs ->
                let$ (e, _) = codegen_value v env
                in let$ names = codegen_notifies vs
                in k (e :: names)
          in codegen_notifies t.notify
        in let$ changed_cond = fun k ->
          match t.changed_when with
          | None ->
              let^ out_fields =
                match out_ty with
                | Struct fs -> Ok fs
                | _ ->
                    Error (Printf.sprintf
                              "Error: Module %s does not return struct" nm)
              in k (Function (ReadField (out_fields, "changed"),
                      Variable t.register) : Target.expr)
          | Some cond -> codegen_value cond env (fun (e, _) -> k e)
        in let notify : Target.stmt =
          let add_notify (n : Target.expr) : Target.stmt =
            Assign ("@notified",
              Function (SetAdd, Pair (n, Variable "@notified")))
          in seq (List.map add_notify names)
        (* And remove the result from the environment since codegen_mod_use
         * will update it appropriately. *)
        in let () =
          if t.register <> "_"
          then Hashtbl.remove env t.register
        in Ok (Target.Cond (
          changed_cond,
          notify,
          Pass (* No change hence don't notify *)
        ))
      in codegen_mod_use m t.condition t.loop t.register t.ignore_errors
          t.failed_when env ctx (Some do_notify)
    | Block b ->
      (* notify is (as of the last few years it seems) allowed on blocks, and
       * it seems to behave as if that notify was added to each task in the
       * block (or rescue/always) *)
      let$ new_notify =
        let rec codegen_notifies (vs : Typed.value list)
          (k : Target.expr list -> (Target.stmt, string) result) =
          match vs with
          | [] -> k extra_notify
          | v :: vs ->
              let$ (e, _) = codegen_value v env
              in let$ names = codegen_notifies vs
              in k (e :: names)
        in codegen_notifies t.notify
      (* Blocks have some restrictions, they don't support loops, register,
       * or failed_when. We check those here. *)
      in let^ () =
        match t.loop with
        | None -> Ok ()
        | Some _ -> Error "Blocks do not support loops"
      in let^ () =
        if t.register = "_"
        then Ok ()
        else Error "Blocks do not support register key"
      in let^ () =
        match t.failed_when with
        | None -> Ok ()
        | Some _ -> Error "Blocks do not support failed_when key"
      in let^ tasks =
        codegen_tasks b.tasks new_notify env ctx
      in let^ rescue =
        match b.rescue with
        | None -> Ok None
        | Some ts ->
            Result.map Option.some (codegen_tasks ts new_notify env ctx)
      in let^ always =
        match b.always with
        | None -> Ok None
        | Some ts ->
            Result.map Option.some (codegen_tasks ts new_notify env ctx)
      in let body : Target.stmt =
        TryCatch (tasks, "@except",
          (* If there's a rescue block we ignore the error, otherwise re-raise *)
          begin match rescue with
          | None -> Raise (Variable "@except")
          | Some catch ->
              Match (
                Function (UnpackExcept (ctx.excepts, "AnsibleError"),
                          Variable "@except"),
                "@",
                Raise (Variable "@except"), (* None case, some other error *)
                catch)
          end,
          begin match always with None -> Pass | Some finally -> finally end)
      in let handle_ignore_errors : Target.stmt =
        if t.ignore_errors
        then
          TryCatch (body, "@except",
            Match (
              Function (UnpackExcept (ctx.excepts, "AnsibleError"),
                        Variable "@except"),
              "@",
              Raise (Variable "@except"), (* None case, some other error *)
              Pass),
            Pass)
        else body
      in begin match t.condition with
      | None -> Ok handle_ignore_errors
      | Some cond ->
          codegen_value cond env (fun (cond, _) ->
            Ok (Target.Cond (cond, handle_ignore_errors, Pass)))
      end
  in Ok (codegen_become t.become t.become_user body ctx)
and codegen_tasks (ts : Typed.task list) (extra_notify : Target.expr list)
  (env : play_env) (ctx : Context.context) : (Target.stmt, string) result =
  match ts with
  | [] -> Ok Target.Pass
  | t :: ts ->
      let^ t = codegen_task t extra_notify env ctx
      in let^ ts = codegen_tasks ts extra_notify env ctx
      in Ok (Target.Seq (t, ts))

(* Generates if <h.listen> in @notified then do body else do nothing *)
let codegen_handler (h : Typed.handler) (env : play_env) (ctx : Context.context)
  : (Target.stmt, string) result =
  let^ body =
    codegen_mod_use h.module_invoke h.condition h.loop h.register
      h.ignore_errors h.failed_when env ctx None
  in let with_become = codegen_become h.become h.become_user body ctx
  in Ok (Target.Cond (
          Function (SetContains, 
            Pair (Literal (String h.listen), Variable "@notified")),
          with_become, Pass))

let codegen_play (p : Typed.play) (ctx : Context.context)
  : (Target.stmt, string) result =
  let play_env = Hashtbl.create 10
  in let^ var_setup =
    let rec codegen_vars (vs : (string * Typed.value) list) =
      match vs with
      | [] -> Ok Target.Pass
      | (nm, v) :: tl ->
          let$ (e, t) = codegen_value v play_env
          in let () = Hashtbl.add play_env nm t
          in let^ rest = codegen_vars tl
          in Ok (Target.Seq (Assign (nm, e), rest))
    in codegen_vars p.vars
  (* Note: This scould probably be done with a fold_left and just reversing the
   * order of the Seq but that feels like premature optimization. *)
  in let^ handlers_run =
    List.fold_right (fun h hs ->
      let^ hs = hs
      in let^ h = codegen_handler h play_env ctx in Ok (Target.Seq (h, hs)))
      p.handlers
      (Ok Target.Pass)
  in let^ pre_tasks =
    match p.pre_tasks with
    | None -> Ok Target.Pass
    | Some ts ->
        let^ res_ts = codegen_tasks ts [] play_env ctx
        in Ok (seq [
                Assign ("@notified", Literal (StringSet StringSet.empty));
                res_ts;
                handlers_run ])
  in let^ tasks =
    let^ res_ts = codegen_tasks p.tasks [] play_env ctx
    in Ok (seq [
            Assign ("@notified", Literal (StringSet StringSet.empty));
            res_ts;
            handlers_run ])
  in let^ post_tasks =
    match p.post_tasks with
    | None -> Ok Target.Pass
    | Some ts ->
        let^ res_ts = codegen_tasks ts [] play_env ctx
        in Ok (seq [
                Assign ("@notified", Literal (StringSet StringSet.empty));
                res_ts;
                handlers_run ])
  in let body = seq [
    (* Finally, we handle details of what user the play runs as
     * (i.e., remote_user, is_root, become, become_user) *)
    Target.Add (env_qual "active_user" (Primitive String)
                  (Literal (String p.remote_user)));
    begin match p.is_root with
    | None -> Target.Pass
    | Some is_root -> Target.Add (env_qual "is_root" (Primitive Bool)
                                    (Literal (Bool is_root)))
    end;
    codegen_become p.become p.become_user
      (seq [ var_setup; pre_tasks; tasks; post_tasks ]) ctx ]
  (* Lastly, we will wrap the play body with a condition that checks if the
   * host is actually run by the current play *)
  in Ok (seq [
    Target.Get ("@hostname", env_attr "hostname" (Primitive String));
    Cond (
      Function (HostIncluded,
        Pair (Variable "@hostname", Literal (String p.hosts))),
      body,
      Pass) ])

let codegen_playbook (p : Typed.playbook) (ctx : Context.context)
  : (Target.stmt, string) result =
  (* The preamble to Ansible programs sets up the environment appropriately, in
   * particular:
   * - ensure env() exists
   * - ensure env().time_counter is 0
   * - ensure env().last_reboot  is -1
   *)
  let^ preamble : Target.stmt =
    Modules.Codegen.codegen_stmts [
      AssertExists (FuncExp (Id "env", []));
      Assert (BinaryExp (Field (FuncExp (Id "env", []), "time_counter"),
                         IntLit 0, Eq));
      Assert (BinaryExp (Field (FuncExp (Id "env", []), "last_reboot"),
                         IntLit (-1), Eq))
    ]
    ctx.types ctx.globals ctx.excepts Modules.Codegen.empty_local_env
    (Primitive Unit) None None (Ok Pass)

  in let^ s =
    List.fold_right (fun play rest ->
      let^ rest = rest
      in let^ hd = codegen_play play ctx
      in Ok (Target.Seq (hd, rest)))
      p (Ok Target.Pass)
  in Ok (Target.Seq (preamble, s))
