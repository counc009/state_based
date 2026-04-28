let ( let^ ) r f = Result.bind r f

module Context = Modules.Codegen

type 'a list2 = 'a Modules.Target.list2

module StringMap = Modules.Target.StringMap
module Target = Modules.Target.Ast_Target

(* An expected type *)
type etype =
  | Int
  | Float
  | Bool
  | String
  | Path
  | Enum of string * (string * Target.typ) list2
  | List of etype
  | SingleOrList of etype
  | Struct of etype StringMap.t

(* An inferred type for a value *)
type itype =
  | Int
  | Float
  | Bool
  | StringLike
  | String
  | Path
  | Enum of string * (string * Target.typ) list2
  | EmptyList (* Type of an empty-list, essentially 'a list *)
  | List of itype
  | Struct of itype StringMap.t

class type_stack =
object
  val mutable lst = ([] : itype ref list)
  method push x =
    lst <- x :: lst
  method elems = lst
end

(* For each variable we track the type that we infer for it, which is the
 * broadest type it can have based on the value assigned to it. We'll also
 * track all the uses of the variable which may allow us to refine the type
 * to be the broadest type of all its uses; this is important to allowing us
 * to determine when a variable is meant to be some enum value. *)
type var_type = { inferred : itype; uses : type_stack }
type play_env = var_type StringMap.t

module Parsed = Ast.Parsed

module Typed = struct
  type facts = OSFamily | Distribution | UserID | GroupID

  include Ast.Ast(struct
    type 'a anntd = 'a * itype
    type 'a vanntd = 'a * (itype ref)
    type fact_kind = facts
  end)

  let typeof (v : value) : itype =
    match v with
    | String (_, t)     | Int (_, t)   | Float (_, t)   | Bool (_, t)
    | List (_, t)       | Unary (_, t) | Binary (_, t)  | Dot (_, t)
    | VarDefined (_, t) | Fact (_, t)  | Ternary (_, t) | Record (_, t)
    | ReAnnt (_, t)
        -> t
    | Ident (_, t) -> !t
end

let rec map_res (f : 'a -> ('b, 'e) result) (xs : 'a list)
  : ('b list, 'e) result =
  match xs with
  | [] -> Ok []
  | x :: xs ->
      let^ y = f x
      in let^ ys = map_res f xs
      in Ok (y :: ys)

let smap_res (f : 'a -> ('b, 'e) result) (xs : 'a StringMap.t)
  : ('b StringMap.t, 'e) result =
  StringMap.fold (fun k x acc ->
    let^ res = acc
    in let^ y = f x
    in Ok (StringMap.add k y res))
    xs (Ok StringMap.empty)

(* Merge two string maps that we expect to have the same set of keys and our
 * merge function produces a result. Returns None if the sets of keys are
 * mismatched *)
let merge_same_res (f : 'a -> 'b -> ('c, 'e) result) (xs : 'a StringMap.t)
  (ys : 'b StringMap.t) : ('c StringMap.t, 'e) result option =
  let res =
    StringMap.fold (fun k x acc ->
      match acc with
      | None -> None
      | Some (Error msg) -> Some (Error msg)
      | Some (Ok (res, ys)) ->
          match StringMap.find_opt k ys with
          | None -> None
          | Some y ->
              match f x y with
              | Error msg -> Some (Error msg)
              | Ok z ->
                  Some (Ok (StringMap.add k z res, StringMap.remove k ys)))
      xs (Some (Ok (StringMap.empty, ys)))
  in match res with
  | None -> None
  | Some (Error msg) -> Some (Error msg)
  | Some (Ok (res, ys)) ->
      if StringMap.is_empty ys
      then Some (Ok res)
      else None

let rec string_of_etype (t : etype) : string =
  match t with
  | Int -> "int"
  | Float -> "float"
  | Bool -> "bool"
  | String -> "string"
  | Path -> "path"
  | Enum (nm, _) -> nm
  | List t -> "list of " ^ string_of_etype t
  | SingleOrList t -> "single value or list of " ^ string_of_etype t
  | Struct ts ->
      "{" 
      ^ String.concat ", " 
          (List.map (fun (f, t) -> f ^ ": " ^ string_of_etype t)
            (StringMap.to_list ts))
      ^ "}"

let rec string_of_itype (t : itype) : string =
  match t with
  | Int -> "int"
  | Float -> "float"
  | Bool -> "bool"
  | StringLike -> "string-like"
  | String -> "string"
  | Path -> "path"
  | Enum (nm, _) -> nm
  | EmptyList -> "list"
  | List t -> "list of " ^ string_of_itype t
  | Struct ts ->
      "{"
      ^ String.concat ", "
          (List.map (fun (f, t) -> f ^ ": " ^ string_of_itype t) 
            (StringMap.to_list ts))
      ^ "}"

let rec etype_of_itype (t : itype) : (etype, string) result =
  match t with
  | Int -> Ok Int
  | Float -> Ok Float
  | Bool -> Ok Bool
  | StringLike -> Error "Cannot convert string-like to an etype"
  | String -> Ok String
  | Path -> Ok Path
  | Enum (nm, cs) -> Ok (Enum (nm, cs))
  | EmptyList -> Error "Cannot convert empty list to an etype"
  | List t -> let^ res_t = etype_of_itype t in Ok (List res_t : etype)
  | Struct fs ->
      let^ res =
        StringMap.fold (fun f t res ->
          let^ res = res
          in let^ res_t = etype_of_itype t
          in Ok (StringMap.add f res_t res))
        fs (Ok StringMap.empty)
      in Ok (Struct res : etype)

let rec itype_of_etype (t : etype) : itype =
  match t with
  | Int -> Int
  | Float -> Float
  | Bool -> Bool
  | String -> String
  | Path -> Path
  | Enum (nm, cs) -> Enum (nm, cs)
  | List t -> List (itype_of_etype t)
  | SingleOrList t -> List (itype_of_etype t)
  | Struct ts -> Struct (StringMap.map itype_of_etype ts)

let type_error (t : itype) (e : etype) : ('a, string) result =
  Error (Printf.sprintf
          "Type error, found %s but expected %s"
          (string_of_itype t) (string_of_etype e))

let typecheck (v : Parsed.value) (t : etype option) (env : play_env)
  : (Typed.value, string) result =

  (* Determine whether t can be coerced to e *)
  let rec can_coerce (t : itype) (e : etype) : itype option =
    match t, e with
    | Int, Int -> Some Int
    | (Int | Float), Float -> Some Float
    | Bool, Bool -> Some Bool
    | (Int | Float | Bool | StringLike | String | Path), String -> Some String
    | (Int | Float | Bool | StringLike | String | Path), Path -> Some Path
    | StringLike, Enum (nm, cs) -> Some (Enum (nm, cs))
    | Enum (n, cs), Enum (m, _) when n = m -> Some (Enum (n, cs))
    | EmptyList, (List e | SingleOrList e) -> Some (List (itype_of_etype e))
    | List t, (List e | SingleOrList e) ->
        Option.map (fun t -> List t) (can_coerce t e)
    | Struct ts, Struct es ->
        let res =
          StringMap.fold (fun f t res ->
            match res with
            | None -> None
            | Some (es, res) ->
                match StringMap.find_opt f es with
                | None -> None
                | Some e ->
                    match can_coerce t e with
                    | None -> None
                    | Some t -> 
                        Some (StringMap.remove f es, StringMap.add f t res))
            ts (Some (es, StringMap.empty))
        in begin match res with
        | None -> None
        | Some (es_remain, res) ->
            if StringMap.is_empty es_remain
            then Some (Struct res)
            else None
        end
    | _, SingleOrList e ->
        Option.map (fun t -> List t) (can_coerce t e)
    | _, _ -> None

  in let rec coerce (v : Typed.value) (t : etype) : (Typed.value, string) result =
    match v with
    | String (s, c) ->
        let rec handle_type (t : itype) (c : etype)
          : (Typed.value, string) result =
          match t, c with
          | (StringLike | String | Path), String -> Ok (String (s, String))
          | (StringLike | String | Path), Path -> Ok (String (s, Path))
          | StringLike, Enum (nm, cs) -> Ok (String (s, Enum (nm, cs)))

          | Enum (n, _), Enum (m, _) when n = m -> Ok (String (s, t))

          | _, SingleOrList c ->
              let^ res = handle_type t c
              in Ok (Typed.List ([res], List (Typed.typeof res)))

          | _, _ -> type_error t c
        in handle_type c t
    | Int (i, c) ->
        let rec handle_type (t : itype) (c : etype)
          : (Typed.value, string) result =
          match t, c with
          | Int, Int -> Ok (Int (i, Int))
          | Int, Float -> Ok (Float (float_of_int i, Float))
          | Int, String -> Ok (String (string_of_int i, String))
          | Int, Path -> Ok (String (string_of_int i, Path))

          | _, SingleOrList c ->
              let^ res = handle_type t c
              in Ok (Typed.List ([res], List (Typed.typeof res)))

          | _, _ -> type_error t c
        in handle_type c t
    | Float (f, c) ->
        let rec handle_type (t : itype) (c : etype)
          : (Typed.value, string) result =
          match t, c with
          | Float, Float -> Ok (Float (f, Float))
          | Float, String -> Ok (String (string_of_float f, String))
          | Float, Path -> Ok (String (string_of_float f, Path))

          | _, SingleOrList c ->
              let^ res = handle_type t c
              in Ok (Typed.List ([res], List (Typed.typeof res)))

          | _, _ -> type_error t c
        in handle_type c t
    | Bool (b, c) ->
        let rec handle_type (t : itype) (c : etype)
          : (Typed.value, string) result =
          match t, c with
          | Bool, Bool -> Ok (Bool (b, Bool))
          | Bool, String -> Ok (String (string_of_bool b, String))
          | Bool, Path -> Ok (String (string_of_bool b, Path))

          | _, SingleOrList c ->
              let^ res = handle_type t c
              in Ok (Typed.List ([res], List (Typed.typeof res)))

          | _, _ -> type_error t c
        in handle_type c t
    | List (vs, c) ->
        begin match c, t with
        | EmptyList, List t | EmptyList, SingleOrList t ->
            Ok (List ([], List (itype_of_etype t)))
        | List c, (List t | SingleOrList t) ->
            begin match can_coerce c t with
            | None -> 
                type_error c t
            | Some res ->
                let^ res_vs = map_res (fun v -> coerce v t) vs
                in Ok (Typed.List (res_vs, List res))
            end
        | _, _ -> type_error c t
        end
    | Ident (nm, c) ->
        begin match can_coerce !c t with
        | None -> type_error !c t
        | Some t ->
            let () = c := t
            in Ok (Ident (nm, c))
        end
    | Unary ((v, op), c) ->
        begin match op with
        | Not -> (* Always produces a bool can add a coercion *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | Bool -> Ok (Unary ((v, Not), Bool))
              | String -> Ok (ReAnnt (Unary ((v, Not), Bool), String))
              | Path -> Ok (ReAnnt (Unary ((v, Not), Bool), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error Bool t
            in handle_type t
        | Neg -> (* Either produces an int or a float *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match c, t with
              | Int, Int -> Ok (Unary ((v, Neg), Int))
              | Int, Float ->
                  let^ coerce_v = coerce v Float
                  in Ok (Typed.Unary ((coerce_v, Neg), Float))
              | Float, Float -> Ok (Unary ((v, Neg), Float))
              | _, String -> Ok (ReAnnt (Unary ((v, op), c), String))
              | _, Path -> Ok (ReAnnt (Unary ((v, op), c), Path))
              | _, SingleOrList t ->
                  let^ res = handle_type t
                  in Ok (Typed.List ([res], List (Typed.typeof res)))
              | _, _ -> type_error c t
            in handle_type t
        | Lower -> (* Always produces a string can add a coercion *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | String -> Ok (Unary ((v, Lower), String))
              | Path -> Ok (ReAnnt (Unary ((v, Lower), String), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error String t
            in handle_type t
        end
    | Binary ((lhs, op, rhs), c) ->
        begin match op with
        (* Always produce a bool can add a coercion *)
        | And | Or | Neq | Eq | Lt | Gt | Le | Ge ->
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | Bool -> Ok (Binary ((lhs, op, rhs), Bool))
              | String -> Ok (ReAnnt (Binary ((lhs, op, rhs), Bool), String))
              | Path -> Ok (ReAnnt (Binary ((lhs, op, rhs), Bool), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error Bool t
            in handle_type t
        | Concat -> (* Always produces a string can add a coercion *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | String -> Ok (Binary ((lhs, op, rhs), String))
              | Path -> Ok (ReAnnt (Binary ((lhs, op, rhs), String), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error String t
            in handle_type t
        | Mod -> (* Always produces an int can add a coercion *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | Int -> Ok (Binary ((lhs, op, rhs), Int))
              | Float -> Ok (ReAnnt (Binary ((lhs, op, rhs), Int), Float))
              | String -> Ok (ReAnnt (Binary ((lhs, op, rhs), Int), String))
              | Path -> Ok (ReAnnt (Binary ((lhs, op, rhs), Int), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error Int t
            in handle_type t
        | Pow -> (* Always produces a float can add a coercion *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match t with
              | Float -> Ok (Binary ((lhs, op, rhs), Float))
              | String -> Ok (ReAnnt (Binary ((lhs, op, rhs), Float), String))
              | Path -> Ok (ReAnnt (Binary ((lhs, op, rhs), Float), Path))
              | SingleOrList t ->
                  let^ res_v = handle_type t
                  in Ok (Typed.List ([res_v], List (Typed.typeof res_v)))
              | _ -> type_error Float t
            in handle_type t
        | Add | Sub | Mul | Div -> (* Overloaded for float & int *)
            let rec handle_type (t : etype) : (Typed.value, string) result =
              match c, t with
              | Int, Int -> Ok (Binary ((lhs, op, rhs), Int))
              | Int, Float ->
                  let^ coerce_lhs = coerce lhs Float
                  in let^ coerce_rhs = coerce rhs Float
                  in Ok (Typed.Binary ((coerce_lhs, op, coerce_rhs), Float))
              | Float, Float -> Ok (Binary ((lhs, op, rhs), Float))
              | _, String -> Ok (ReAnnt (Binary ((lhs, op, rhs), c), String))
              | _, Path -> Ok (ReAnnt (Binary ((lhs, op, rhs), c), Path))
              | _, SingleOrList t ->
                  let^ res = handle_type t
                  in Ok (Typed.List ([res], List (Typed.typeof res)))
              | _, _ -> type_error c t
            in handle_type t
        end
    | Dot ((v, f), c) ->
        let^ fs =
          match Typed.typeof v with
          | Struct fs -> smap_res etype_of_itype fs
          | _ -> failwith "Internal Error: Dot cannot be applied to non-struct value"
        in let rec handle_type (t : etype) : (Typed.value, string) result =
          match c, t with
          | List c, SingleOrList t ->
              let^ () =
                match can_coerce c t with
                | Some _ -> Ok ()
                | None -> type_error c t
              in let new_fs = StringMap.add f (List t : etype) fs
              in let^ res_v = coerce v (Struct new_fs)
              in begin match Typed.typeof res_v with
              | Struct res_fs ->
                  begin match StringMap.find_opt f res_fs with
                  | None -> failwith "Internal Error: Missing field"
                  | Some t -> Ok (Typed.Dot ((res_v, f), t))
                  end
              | _ -> failwith "Interal Error: Must be a struct type"
              end
          | _, SingleOrList t ->
              let^ res = handle_type t
              in Ok (Typed.List ([res], List (Typed.typeof res)))
          | _, _ ->
              let^ () =
                match can_coerce c t with
                | Some _ -> Ok ()
                | None -> type_error c t
              in let new_fs = StringMap.add f t fs
              in let^ res_v = coerce v (Struct new_fs)
              in begin match Typed.typeof res_v with
              | Struct res_fs ->
                  begin match StringMap.find_opt f res_fs with
                  | None -> failwith "Internal Error: Missing field"
                  | Some t -> Ok (Typed.Dot ((res_v, f), t))
                  end
              | _ -> failwith "Interal Error: Must be a struct type"
              end
        in handle_type t
    | VarDefined (_, _) ->
        failwith "Internal Error: Var Defined are removed before coercion"
    | Fact (f, _) ->
        (* Currently all of the facts are string values which makes this
         * easier *)
        let rec handle_type (t : etype) : (Typed.value, string) result =
          match t with
          | String -> Ok (Fact (f, String))
          | Path -> Ok (ReAnnt (Fact (f, String), Path))
          | SingleOrList t ->
              let^ res = handle_type t
              in Ok (Typed.List ([res], List (Typed.typeof res)))
          | _ -> type_error String t
        in handle_type t
    | Ternary ((cond, thn, els), _) ->
        let^ thn_coerce = coerce thn t
        in let^ els_coerce = coerce els t
        in Ok (Typed.Ternary ((cond, thn_coerce, els_coerce),
                              Typed.typeof thn_coerce))
    | Record (vs, c) ->
        begin match t with
        | Struct ts ->
            let^ (vs_coerced, fs) =
              let rec helper (vs : (string * Typed.value) list)
                (ts : etype StringMap.t) =
                match vs with
                | [] ->
                    if StringMap.is_empty ts
                    then Ok ([], StringMap.empty)
                    else type_error c t
                | (f, v) :: vs ->
                    let^ ty_f =
                      match StringMap.find_opt f ts with
                      | None -> type_error c t
                      | Some t -> Ok t
                    in let^ res_v = coerce v ty_f
                    in let^ (res_vs, fs) = helper vs (StringMap.remove f ts)
                    in Ok ((f, res_v) :: res_vs,
                           StringMap.add f (Typed.typeof res_v) fs)
              in helper vs ts
            in Ok (Typed.Record (vs_coerced, Struct fs))
        | _ -> type_error c t
        end
    | ReAnnt (v, c) ->
        begin match can_coerce c t with
        | None -> type_error c t
        | Some res -> Ok (ReAnnt (v, res))
        end

  (* Given two itypes attempts to return a type they can both be coerced to *)
  in let rec unify_types (t : itype) (s : itype) : (itype, string) result =
    match t, s with
    | Int, Int -> Ok Int
    | Int, Float | Float, Int | Float, Float -> Ok Float
    | Bool, Bool -> Ok Bool
    | (Int | Float), Bool | Bool, (Int | Float) -> Ok String
    | (Int | Float | Bool), (StringLike | String) -> Ok String
    | (Int | Float | Bool), Path -> Ok Path

    | StringLike, (Int | Float | Bool) -> Ok String
    | StringLike, StringLike -> Ok StringLike
    | StringLike, String -> Ok String
    | StringLike, Path -> Ok Path
    | StringLike, Enum (nm, cs) -> Ok (Enum (nm, cs))

    | String, (Int | Float | Bool | StringLike | String | Path) -> Ok String
    | Path, (Int | Float | Bool | StringLike | String | Path) -> Ok Path

    | EmptyList, EmptyList -> Ok EmptyList
    | EmptyList, List s -> Ok (List s)
    | List t, EmptyList -> Ok (List t)
    | List t, List s -> let^ res_t = unify_types t s in Ok (List res_t)

    | Enum (nm, cs), StringLike -> Ok (Enum (nm, cs))
    | Enum (n, _), Enum (m, _) when n = m -> Ok t

    | Struct ts, Struct ss ->
        let^ (ss_remainder, res) =
          StringMap.fold (fun f t res ->
            let^ (ss, res) = res
            in match StringMap.find_opt f ss with
            | None -> Error ("Incompatible types, missing field " ^ f)
            | Some s ->
                let^ ty = unify_types t s
                in Ok (StringMap.remove f ss, StringMap.add f ty res))
          ts (Ok (ss, StringMap.empty))
        in if StringMap.is_empty ss_remainder
        then Ok (Struct res)
        else Error ("Incompatible types, missing field "
                      ^ fst (StringMap.min_binding ss_remainder))

    | _, _ ->
        Error (Printf.sprintf
                "Incompatible types %s and %s"
                (string_of_itype t) (string_of_itype s))

  in let rec infer (v : Parsed.value) : (Typed.value, string) result =
    match v with
    | String s -> Ok (String (s, StringLike))
    | Int i -> Ok (Int (i, Int))
    | Float f -> Ok (Float (f, Float))
    | Bool b -> Ok (Bool (b, Bool))
    | List vs ->
        begin match vs with
        | [] -> Ok (List ([], EmptyList))
        | v :: vs ->
            let^ res_v = infer v
            in let init_ty = Typed.typeof res_v
            in let^ (res_vs, elem_ty) =
              List.fold_right (fun v res ->
                let^ (res_vs, elem_ty) = res
                in let^ res_v = infer v
                in let^ res_ty = unify_types elem_ty (Typed.typeof res_v)
                in Ok (res_v :: res_vs, res_ty))
                vs (Ok ([], init_ty))
            in match etype_of_itype elem_ty with
            | Ok elem ->
                let^ res_vs =
                  map_res (fun v -> coerce v elem) (res_v :: res_vs)
                in Ok (Typed.List (res_vs, List elem_ty))
            (* An error in this conversion means we have a type like EmptyList
             * or StringLike, which we would only have because all elements
             * have those exact types, so we don't need to do any coercion. *)
            | Error _ ->
                Ok (Typed.List (res_v :: res_vs, List elem_ty))
        end
    | Ident nm ->
        begin match StringMap.find_opt nm env with
        | Some { inferred; uses } ->
            let typ = ref inferred
            in let () = uses#push typ
            in Ok (Ident (nm, typ))
        (* Check if this is a built-in variable (which becomes a fact) *)
        | None ->
            match nm with
            | "ansible_os_family" -> infer (Fact "os_family")
            | "ansible_distribution" -> infer (Fact "distribution")
            | "ansible_user_id" -> infer (Fact "user_id")
            | "ansible_user_gid" -> infer (Fact "user_gid")
            | _ -> Error ("Undefined variable " ^ nm)
        end
    | Unary (v, op) ->
        let^ res_v = infer v
        in begin match op with
        | Not ->
            let^ v_typed = coerce res_v Bool
            in Ok (Typed.Unary ((v_typed, Not), Bool))
        | Neg ->
            begin match Typed.typeof res_v with
            | Int -> Ok (Typed.Unary ((res_v, Neg), Int))
            | Float -> Ok (Typed.Unary ((res_v, Neg), Float))
            | t ->
                Error (Printf.sprintf
                  "Type error, found %s but expected number"
                  (string_of_itype t))
            end
        | Lower ->
            let^ v_typed = coerce res_v String
            in Ok (Typed.Unary ((v_typed, Lower), String))
        end
    | Binary (lhs, op, rhs) ->
        let^ res_lhs = infer lhs
        in let^ res_rhs = infer rhs
        in begin match op with
        | Add | Sub | Mul | Div ->
            begin match Typed.typeof res_lhs, Typed.typeof res_rhs with
            | Int, Int ->
                Ok (Typed.Binary ((res_lhs, op, res_rhs), Int))
            | Int, Float ->
                let^ lhs_f = coerce res_lhs Float
                in Ok (Typed.Binary ((lhs_f, op, res_rhs), Float))
            | Float, Int ->
                let^ rhs_f = coerce res_rhs Float
                in Ok (Typed.Binary ((res_lhs, op, rhs_f), Float))
            | Float, Float ->
                Ok (Typed.Binary ((res_lhs, op, res_rhs), Float))
            | (Int | Float), t | t, _ ->
                Error (Printf.sprintf
                  "Type error, found %s but expected number"
                  (string_of_itype t))
            end
        | Pow ->
            let^ typ_lhs = coerce res_lhs Float
            in let^ typ_rhs = coerce res_rhs Float
            in Ok (Typed.Binary ((typ_lhs, Pow, typ_rhs), Float))
        | Mod ->
            let^ typ_lhs = coerce res_lhs Int
            in let^ typ_rhs = coerce res_rhs Int
            in Ok (Typed.Binary ((typ_lhs, Mod, typ_rhs), Int))
        | And | Or ->
            let^ typ_lhs = coerce res_lhs Bool
            in let^ typ_rhs = coerce res_rhs Bool
            in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
        | Lt | Gt | Le | Ge ->
            begin match Typed.typeof res_lhs, Typed.typeof res_rhs with
            | Int, Int ->
                Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
            | Int, Float ->
                let^ lhs_f = coerce res_lhs Float
                in Ok (Typed.Binary ((lhs_f, op, res_rhs), Bool))
            | Float, Int ->
                let^ rhs_f = coerce res_rhs Float
                in Ok (Typed.Binary ((res_lhs, op, rhs_f), Bool))
            | Float, Float ->
                Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
            | (Int | Float), t | t, _ ->
                Error (Printf.sprintf
                  "Type error, found %s but expected number"
                  (string_of_itype t))
            end
        | Concat ->
            let^ typ_lhs = coerce res_lhs String
            in let^ typ_rhs = coerce res_rhs String
            in Ok (Typed.Binary ((typ_lhs, Concat, typ_rhs), String))
        | Eq | Neq ->
            (* Boolean value to return for incompatible comparisons (i.e., definitely not equal) *)
            let neq_bool =
              match op with
              | Eq -> false
              | Neq -> true
              | _ -> failwith "Match error"
            in begin match Typed.typeof res_lhs, Typed.typeof res_rhs with
            | Int, Int -> Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
            | Bool, Bool -> Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
            | Path, Path -> Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
            | Int, Float | Float, Int | Float, Float ->
                let^ typ_lhs = coerce res_lhs Float
                in let^ typ_rhs = coerce res_rhs Float
                in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
            (* FIXME: Coercing StringLike, StringLike to String could be wrong
             * if they're both the same enum type that would be fine, but also
             * this may be enough of an edge case. *)
            | (StringLike | String | Path), (StringLike | String)
            | (StringLike | String), Path ->
                let^ typ_lhs = coerce res_lhs String
                in let^ typ_rhs = coerce res_rhs String
                in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
            | EmptyList, EmptyList ->
                Ok (Typed.Bool (neq_bool, Bool))
            | EmptyList, List t | List t, EmptyList ->
                let^ t = etype_of_itype t
                in let^ typ_lhs = coerce res_lhs (List t)
                in let^ typ_rhs = coerce res_rhs (List t)
                in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
            | List t, List s ->
                let^ goal = unify_types t s
                in let^ elem = etype_of_itype goal
                in let^ typ_lhs = coerce res_lhs (List elem)
                in let^ typ_rhs = coerce res_rhs (List elem)
                in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
            | Enum (n, _), Enum (m, _) ->
                if n = m
                then Ok (Typed.Binary ((res_lhs, op, res_rhs), Bool))
                (* FIXME: This may not be correct technically, since enums
                 * don't really exist in Ansible/Jinja and so we would just
                 * perform a string comparison. That said not even sure this
                 * is possible to reach so it may not matter. *)
                else Ok (Typed.Bool (neq_bool, Bool))
            | Enum (nm, cs), StringLike | StringLike, Enum (nm, cs) ->
                let^ typ_lhs = coerce res_lhs (Enum (nm, cs))
                in let^ typ_rhs = coerce res_rhs (Enum (nm, cs))
                in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
            | Struct ts, Struct fs ->
                let unify_convert t s =
                  let^ res = unify_types t s
                  in etype_of_itype res
                (* Structs are equal if each of their fields are equal *)
                in begin match merge_same_res unify_convert ts fs with
                (* Fields are different *)
                | None -> Ok (Typed.Bool (neq_bool, Bool))
                | Some (Error msg) -> Error msg
                | Some (Ok fields) ->
                    let^ typ_lhs = coerce res_lhs (Struct fields)
                    in let^ typ_rhs = coerce res_rhs (Struct fields)
                    in Ok (Typed.Binary ((typ_lhs, op, typ_rhs), Bool))
                end
            (* Handles non type-equivalent equalities by just returning false *)
            | _, _ -> Ok (Typed.Bool (neq_bool, Bool))
            end
        end
    | Dot (v, f) ->
        let^ res_v = infer v
        in begin match Typed.typeof res_v with
        | Struct fs ->
            let^ t =
              match StringMap.find_opt f fs with
              | None -> Error (Printf.sprintf "Value does not have field %s" f)
              | Some t -> Ok t
            in Ok (Typed.Dot ((res_v, f), t))
        | _ -> Error (Printf.sprintf "Value does not have field %s" f)
        end
    | VarDefined nm ->
        begin match StringMap.find_opt nm env with
        | Some _ -> Ok (Typed.Bool (true, Bool))
        | None -> Ok (Typed.Bool (false, Bool))
        end
    | Fact nm ->
        begin match nm with
        | "os_family" -> Ok (Fact (OSFamily, String))
        | "distribution" -> Ok (Fact (Distribution, String))
        | "user_id" -> Ok (Fact (UserID, String))
        | "user_gid" -> Ok (Fact (GroupID, String))
        | _ -> Error (Printf.sprintf "Unknown Ansible fact %s" nm)
        end
    | Ternary (cond, thn, els) ->
        let^ res_cond = infer cond
        in let^ res_thn = infer thn
        in let^ res_els = infer els
        in let^ typ_cond = coerce res_cond Bool
        in let^ res_typ =
          let rec handle_types (t : itype) (s : itype) : (etype, string) result =
            match t, s with
            | Int, Int -> Ok Int
            | Int, Float | Float, Int | Float, Float -> Ok Float
            | Bool, Bool -> Ok Bool

            | (Int | Float), (Bool | StringLike | String)
            | Bool, (Int | Float | StringLike | String) -> Ok String

            | (StringLike | String), 
                  (Int | Float | Bool | StringLike | String | Path) ->
                Ok String
            | Path, (StringLike | String) -> Ok String
            | StringLike, Enum (nm, cs) | Enum (nm, cs), StringLike ->
                Ok (Enum (nm, cs))

            | Path, Path -> Ok Path
            | Path, (Int | Float | Bool) -> Ok Path
            | (Int | Float | Bool), Path -> Ok Path

            | Enum (n, cs), Enum (m, _) when n = m -> Ok (Enum (n, cs))

            | Int, EmptyList | EmptyList, Int -> Ok (List Int)
            | Float, EmptyList | EmptyList, Float -> Ok (List Float)
            | Bool, EmptyList | EmptyList, Bool -> Ok (List Bool)
            | (StringLike | String), EmptyList
            | EmptyList, (StringLike | String) ->
                Ok (List String)
            | Path, EmptyList | EmptyList, Path -> Ok (List Path)
            | Enum (nm, cs), EmptyList | EmptyList, Enum (nm, cs) -> 
                Ok (List (Enum (nm, cs)))
            | Struct ts, EmptyList | EmptyList, Struct ts ->
                let^ ts = smap_res etype_of_itype ts
                in Ok (List (Struct ts) : etype)
            | EmptyList, EmptyList ->
                Error "Type error, cannot infer type of empty lists"

            | (Int | Float | Bool | StringLike | String | Path | Enum (_, _) 
                   | Struct _), List s ->
                let^ res = handle_types t s in Ok (List res : etype)
            | List t, (Int | Float | Bool | StringLike | String | Path
                           | Enum (_, _) | Struct _)
              -> let^ res = handle_types t s in Ok (List res : etype)
            | EmptyList, List t | List t, EmptyList ->
                etype_of_itype (List t)
            | List t, List s ->
                let^ res = handle_types t s in Ok (List res : etype)

            | Struct ts, Struct ss ->
                let^ res_ts =
                  match merge_same_res handle_types ts ss with
                  | None -> Error "Incompatible record types"
                  | Some r -> r
                in Ok (Struct res_ts : etype)

            | _, _ ->
                Error (Printf.sprintf "Type mismatch, found %s and %s"
                        (string_of_itype t) (string_of_itype s))
          in handle_types (Typed.typeof res_thn) (Typed.typeof res_els)
        in let^ typ_thn = coerce res_thn res_typ
        in let^ typ_els = coerce res_els res_typ
        in Ok (Typed.Ternary ((typ_cond, typ_thn, typ_els),
                              Typed.typeof typ_thn))
    | Record vs ->
        let^ (res_vs, typ_fs) =
          let rec helper (vs : (string * Parsed.value) list) =
            match vs with
            | [] -> Ok ([], StringMap.empty)
            | (f, v) :: vs ->
                let^ res_v = infer v
                in let^ (res_vs, fs) = helper vs
                in Ok ((f, res_v) :: res_vs, 
                        StringMap.add f (Typed.typeof res_v) fs)
          in helper vs
        in Ok (Typed.Record (res_vs, Struct typ_fs))
    | ReAnnt v -> infer v

  in let^ v = infer v
  in match t with
  | None -> Ok v
  | Some t -> coerce v t
