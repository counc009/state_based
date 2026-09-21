open Stdint
open Ast.Parsed
open Ast

module type FORMAT = sig
  type t
  val init : t
  val print : t -> ('a, unit, string) format -> 'a
  val print_seq : t -> ('a -> string) -> 'a list -> string
  val print_block : t -> (t -> string) -> ('a, unit, string) format -> 'a
end

module FmtIndent : FORMAT = struct
  type t = string
  let init = ""

  let print (indent : string) = Printf.ksprintf (fun s -> indent ^ s)
  let print_seq (indent : string) (k : 'a -> string) (xs : 'a list) =
    String.concat "\n" (List.map k xs)
  let print_block (indent : string) (k : t -> string) =
    Printf.ksprintf (fun s -> 
      Printf.sprintf "%s%s {\n%s\n%s}" indent s (k ("  " ^ indent)) indent)
end

module FmtFlat : FORMAT = struct
  type t = unit
  let init = ()

  let print () = Printf.sprintf
  let print_seq () (k : 'a -> string) (xs : 'a list) =
    String.concat " " (List.map k xs)
  let print_block () (k : unit -> string) =
    Printf.ksprintf (fun s -> Printf.sprintf "%s { %s }" s (k ()))
end

let string_of_ast (prg : decl list) : string =
  let string_of_type_args (ts : name list) : string =
    if List.is_empty ts
    then ""
    else Printf.sprintf "<%s>"
            (String.concat ", " (List.map (fun t -> t.ast) ts))
  in let rec string_of_typ (t : typ) : string =
    match t.ast with
    | Void      -> "void"
    | Bool      -> "bool"
    | SInt8     -> "i8"
    | SInt16    -> "i16"
    | SInt32    -> "i32"
    | SInt64    -> "i64"
    | UInt8     -> "u8"
    | UInt16    -> "u16"
    | UInt32    -> "u32"
    | UInt64    -> "u64"
    | Float32   -> "f32"
    | Float64   -> "f64"
    | StateRef  -> "state"
    | String    -> "string"
    | Char      -> "char"
    | Function (ret, args) ->
        Printf.sprintf "(%s) -> %s"
          (String.concat ", " (List.map string_of_typ args))
          (string_of_typ ret)
    | Product ts ->
        Printf.sprintf "(%s)"
          (String.concat ", " (List.map string_of_typ ts))
    | List t ->
        Printf.sprintf "list::<%s>" (string_of_typ t)
    | Named (nm, ts) ->
        Printf.sprintf "%s%s"
          nm
          (string_of_type_params ts)
  and string_of_type_params (ts : typ list) : string =
    if List.is_empty ts
    then ""
    else
      Printf.sprintf "::<%s>" (String.concat ", " (List.map string_of_typ ts))
  in let rec fmt_block (module F : FORMAT) (b : stmt list) : string =
    let string_of_expr (e : expr) : string =
      (* Precedence 11 is reserved for as, 13 for exists, 14 for dot & funcs *)
      let prec_unary (u : unary) : int =
        match u with
        | Neg | LNot | BNot -> 12
      in let string_of_unary (u : unary) : string =
        match u with
        | Neg -> "-"
        | LNot -> "!"
        | BNot -> "~"
      in let prec_binary (b : binary) : int =
        match b with
        | LOr -> 1
        | LAnd -> 2
        | BOr -> 3
        | BXor -> 4
        | BAnd -> 5
        | Eq | Ne -> 6
        | Lt | Le | Gt | Ge -> 7
        | LShft | RShft -> 8
        | Add | Sub -> 9
        | Mul | Div | Mod -> 10
      in let string_of_binary (b : binary) : string =
        match b with
        | LOr   -> "||"
        | LAnd  -> "&&"
        | BOr   -> "|"
        | BXor  -> "^"
        | BAnd  -> "&"
        | Eq    -> "=="
        | Ne    -> "!="
        | Lt    -> "<"
        | Le    -> "<="
        | Gt    -> ">"
        | Ge    -> ">="
        | LShft -> "<<"
        | RShft -> ">>"
        | Add   -> "+"
        | Sub   -> "-"
        | Mul   -> "*"
        | Div   -> "/"
        | Mod   -> "%"
      in let rec to_string (prec : int) (e : expr) : string =
        match e.ast with
        | Id nm -> nm
        | BoolLit true  -> "true"
        | BoolLit false -> "false"
        | Int8Lit i   -> Printf.sprintf "%si8" (Int8.to_string i)
        | Int16Lit i  -> Printf.sprintf "%si16" (Int16.to_string i)
        | Int32Lit i  -> Printf.sprintf "%si32" (Int32.to_string i)
        | Int64Lit i  -> Printf.sprintf "%si64" (Int64.to_string i)
        | UInt8Lit i  -> Printf.sprintf "%su8" (Uint8.to_string i)
        | UInt16Lit i -> Printf.sprintf "%su16" (Uint16.to_string i)
        | UInt32Lit i -> Printf.sprintf "%su32" (Uint32.to_string i)
        | UInt64Lit i -> Printf.sprintf "%su64" (Uint64.to_string i)
        | F32Lit f -> Printf.sprintf "%sf32" (F32.to_string f)
        | F64Lit f -> Printf.sprintf "%ff64" f
        | StringLit s -> Printf.sprintf "\"%s\"" s
        | CharLit c -> Printf.sprintf "'%c'" c
        | UnitLit -> Printf.sprintf "()"
        | UnaryExp (op, e) ->
            if prec_unary op >= prec
            then
              Printf.sprintf "%s %s"
                (string_of_unary op)
                (to_string (prec_unary op) e)
            else
              Printf.sprintf "(%s %s)"
                (string_of_unary op)
                (to_string (prec_unary op) e)
        | BinaryExp (lhs, op, rhs) ->
            if prec_binary op >= prec
            then
              Printf.sprintf "%s %s %s"
                (to_string (prec_binary op) lhs)
                (string_of_binary op)
                (to_string (prec_binary op) rhs)
            else
              Printf.sprintf "(%s %s %s)"
                (to_string (prec_binary op) lhs)
                (string_of_binary op)
                (to_string (prec_binary op) rhs)
        | FieldExp (e, field) ->
            Printf.sprintf "%s.%s"
              (to_string 14 e)
              field.ast
        | ProdField (e, n) ->
            Printf.sprintf "%s.%d"
              (to_string 14 e)
              n.ast
        | CastExp (e, t) ->
            if prec <= 11
            then
              Printf.sprintf "%s as %s"
                (to_string 11 e)
                (string_of_typ t)
            else
              Printf.sprintf "(%s as %s)"
                (to_string 11 e)
                (string_of_typ t)
        | TupleExp es ->
            Printf.sprintf "(%s)"
              (String.concat ", " (List.map (to_string 0) es))
        | StructExp (nm, tys, fields) ->
            Printf.sprintf "%s%s{ %s }"
              nm.ast
              (string_of_type_params tys)
              (String.concat ", " (List.map (fun (f, e) ->
                  f.ast ^ " = " ^ to_string 0 e
                ) fields))
        | EnumExp (nm, tys, constr, es) ->
            Printf.sprintf "%s%s::%s(%s)"
              nm.ast
              (string_of_type_params tys)
              constr.ast
              (String.concat ", " (List.map (to_string 0) es))
        | FuncExp (f, ts, es) ->
            Printf.sprintf "%s%s(%s)"
              (to_string 14 f)
              (string_of_type_params ts)
              (String.concat ", " (List.map (to_string 0) es))
        | CondExp (c, th, el) ->
            if prec <= 0
            then
              Printf.sprintf "if %s then %s else %s"
                (to_string 0 c)
                (to_string 0 th)
                (to_string 0 el)
            else
              Printf.sprintf "(if %s then %s else %s)"
                (to_string 0 c)
                (to_string 0 th)
                (to_string 0 el)
        | Exists e ->
            if prec <= 13
            then Printf.sprintf "exists %s" (to_string 13 e)
            else Printf.sprintf "(exists %s)" (to_string 13 e)
        | ForEach (v, e, b) ->
            Printf.sprintf "for %s in %s%s" v.ast (to_string 0 e)
              (fmt_block (module FmtFlat : FORMAT) b)
        | ForAll (on, elem, vs, b) ->
            Printf.sprintf "forall %s(%s)%s%s"
              elem.ast
              (String.concat ", " (List.map (fun v -> v.ast) vs))
              (Option.value ~default:""
                (Option.map (fun e -> " in " ^ to_string 0 e) on))
              (fmt_block (module FmtFlat : FORMAT) b)
        | Element _ | Attribute _ -> .
      in to_string 0 e
    in let rec fmt_stmts (f : F.t) (b : stmt list) : string =
      let fmt_stmt (s : stmt) : string =
        match s.ast with
        | LetStmt (nm, None, e) ->
            F.print f "let %s = %s;"
              nm.ast
              (string_of_expr e)
        | LetStmt (nm, Some t, e) ->
            F.print f "let %s : %s = %s;"
              nm.ast
              (string_of_typ t)
              (string_of_expr e)
        | Assign (lhs, rhs) ->
            F.print f "%s = %s;"
              (string_of_expr lhs)
              (string_of_expr rhs)
        | Clear e ->
            F.print f "clear %s;" (string_of_expr e)
        | Touch e ->
            F.print f "touch %s;" (string_of_expr e)
        | Assert e ->
            F.print f "assert %s;" (string_of_expr e)
        | Return e ->
            F.print f "return %s;" (string_of_expr e)
        | Yield e ->
            F.print f "yield %s;" (string_of_expr e)
        | Raise (nm, args) ->
            F.print f "raise %s(%s);"
              nm.ast
              (String.concat ", " (List.map string_of_expr args))
        | Localize b ->
            F.print_block f (fun f -> fmt_stmts f b) "localize"
        | IfThenElse (c, th, el) ->
            let if_str = F.print_block f (fun f -> fmt_stmts f th)
              "if %s" (string_of_expr c)
            in let else_str = F.print_block f (fun f -> fmt_stmts f el)
              "else"
            in if_str ^ " " ^ else_str
        | ForLoop (v, l, b) ->
            F.print_block f (fun f -> fmt_stmts f b)
              "for %s in %s" v.ast (string_of_expr l)
        | ForElem (on, elem, vs, b) ->
            F.print_block f (fun f -> fmt_stmts f b)
              "forall %s(%s)%s"
                elem.ast
                (String.concat ", " (List.map (fun v -> v.ast) vs))
                (Option.value ~default:""
                  (Option.map (fun e -> " in " ^ string_of_expr e) on))
        | WhileLoop (c, b) ->
            F.print_block f (fun f -> fmt_stmts f b)
              "while %s" (string_of_expr c)
        | TryCatch (b, None, fnly) ->
            let try_str =
              F.print_block f (fun f -> fmt_stmts f b) "try"
            in let finally_str =
              F.print_block f (fun f -> fmt_stmts f fnly) "finally"
            in try_str ^ " " ^ finally_str
        | TryCatch (b, Some (ex, vs, ctch), fnly) ->
            let try_str =
              F.print_block f (fun f -> fmt_stmts f b) "try"
            in let catch_str =
              F.print_block f (fun f -> fmt_stmts f ctch)
                "catch %s(%s)" ex.ast
                  (String.concat ", " (List.map (fun v -> v.ast) vs))
            in let finally_str =
              F.print_block f (fun f -> fmt_stmts f fnly) "finally"
            in try_str ^ " " ^ catch_str ^ " " ^ finally_str
        | Match (e, (cases, d)) ->
            let fmt_case (f : F.t) ({ ast = { enum; constr; vars}; _ }, b) =
              F.print_block f (fun f -> fmt_stmts f b)
                "%s::%s(%s) =>" enum.ast constr.ast
                  (String.concat ", " (List.map (fun v -> v.ast) vars))
            in let fmt_cases (f : F.t) =
              let case_strs = List.map (fmt_case f) cases
              in let default_str =
                F.print_block f (fun f -> fmt_stmts f d) "_"
              in F.print_seq f (fun s -> s) (case_strs @ [default_str])
            in F.print_block f fmt_cases "match %s" (string_of_expr e)
      in F.print_seq f fmt_stmt b
    in F.print_block F.init (fun f -> fmt_stmts f b) ""
  in let string_of_decl (d : decl) : string =
    match d.ast with
    | Enum { name; ty_args; constrs } ->
        let string_of_constr (nm, tys) =
          Printf.sprintf "%s(%s)"
            nm.ast (String.concat ", " (List.map string_of_typ tys))
        in Printf.sprintf "enum %s%s { %s }"
            name.ast
            (string_of_type_args ty_args)
            (String.concat ", " (List.map string_of_constr constrs))
    |  Struct { name; ty_args; fields } ->
        let string_of_field (nm, ty) =
          Printf.sprintf "%s : %s" nm.ast (string_of_typ ty)
        in Printf.sprintf "struct %s%s { %s }"
            name.ast
            (string_of_type_args ty_args)
            (String.concat ", " (List.map string_of_field fields))
    | Type { name; def } ->
        Printf.sprintf "type %s = %s" name.ast (string_of_typ def)
    | Uninterp { name; ty_args; args; ret } ->
        Printf.sprintf "uninterpreted %s%s(%s) -> %s"
          name.ast
          (string_of_type_args ty_args)
          (String.concat ", " (List.map string_of_typ args))
          (string_of_typ ret)
    | Attribute { local; name; ty } ->
        Printf.sprintf "%sattribute %s : %s"
          (if local then "local " else "")
          name.ast
          (string_of_typ ty)
    | Element { local; name; ty } ->
        Printf.sprintf "%selement %s(%s)"
          (if local then "local " else "")
          name.ast
          (String.concat ", " (List.map string_of_typ ty))
    | Exception { name; ty } ->
        Printf.sprintf "exception %s(%s)"
          name.ast
          (String.concat ", " (List.map string_of_typ ty))
    | Function { name; ty_args; args; ret; body } ->
        Printf.sprintf "fn %s%s(%s) -> %s%s"
          name.ast
          (string_of_type_args ty_args)
          (String.concat ", " 
            (List.map (fun (nm, t) -> nm.ast ^ " : " ^ string_of_typ t) args))
          (string_of_typ ret)
          (fmt_block (module FmtIndent) body)
  in String.concat "\n\n" (List.map string_of_decl prg)
