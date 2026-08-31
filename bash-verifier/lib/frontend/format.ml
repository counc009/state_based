open Stdint

let string_of_ast (prg : Ast.decl list) : string =
  let indent_step = "  "
  in let string_of_type_args (ts : string list) : string =
    if List.is_empty ts
    then ""
    else Printf.sprintf "<%s>" (String.concat ", " ts)
  in let rec string_of_typ (t : Ast.typ) : string =
    match t with
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
  and string_of_type_params (ts : Ast.typ list) : string =
    if List.is_empty ts
    then ""
    else
      Printf.sprintf "::<%s>" (String.concat ", " (List.map string_of_typ ts))
  in let string_of_expr (e : Ast.expr) : string =
    (* Precedence 11 is reserved for as, 13 for exists, 14 for dot & funcs *)
    let prec_unary (u : Ast.unary) : int =
      match u with
      | Neg | LNot | BNot -> 12
    in let string_of_unary (u : Ast.unary) : string =
      match u with
      | Neg -> "-"
      | LNot -> "!"
      | BNot -> "~"
    in let prec_binary (b : Ast.binary) : int =
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
    in let string_of_binary (b : Ast.binary) : string =
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
    in let rec to_string (prec : int) (e : Ast.expr) : string =
      match e with
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
            field
      | ProdField (e, n) ->
          Printf.sprintf "%s.%d"
            (to_string 14 e)
            n
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
            nm
            (string_of_type_params tys)
            (String.concat ", " (List.map (fun (f, e) ->
                f ^ " = " ^ to_string 0 e
              ) fields))
      | EnumExp (nm, tys, constr, es) ->
          Printf.sprintf "%s%s::%s(%s)"
            nm
            (string_of_type_params tys)
            constr
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
      | ForEach (_v, _e, _b) -> failwith "TODO: for-each expressions"
    in to_string 0 e
  in let rec string_of_stmts (indent : string) (b : Ast.stmt list) : string =
    let rec string_of_stmt (s : Ast.stmt) : string =
      match s with
      | LetStmt (nm, None, e) ->
          Printf.sprintf "%slet %s = %s;"
            indent
            nm
            (string_of_expr e)
      | LetStmt (nm, Some t, e) ->
          Printf.sprintf "%slet %s : %s = %s;"
            indent
            nm
            (string_of_typ t)
            (string_of_expr e)
      | Assign (lhs, rhs) ->
          Printf.sprintf "%s%s = %s;"
            indent
            (string_of_expr lhs)
            (string_of_expr rhs)
      | Clear e ->
          Printf.sprintf "%sclear %s;" indent (string_of_expr e)
      | Touch e ->
          Printf.sprintf "%stouch %s;" indent (string_of_expr e)
      | Assert e ->
          Printf.sprintf "%sassert %s;" indent (string_of_expr e)
      | Return e ->
          Printf.sprintf "%sreturn %s;" indent (string_of_expr e)
      | Yield e ->
          Printf.sprintf "%syield %s;" indent (string_of_expr e)
      | Raise (nm, args) ->
          Printf.sprintf "%sraise %s(%s);"
            indent
            nm
            (String.concat ", " (List.map string_of_expr args))
      | Localize b ->
          Printf.sprintf "%slocalize {\n%s\n%s}"
            indent
            (string_of_stmts (indent_step ^ indent) b)
            indent
      | IfThenElse (c, th, el) ->
          Printf.sprintf "%sif %s {\n%s\n%s} else {\n%s\n%s}"
            indent
            (string_of_expr c)
            (string_of_stmts (indent_step ^ indent) th)
            indent
            (string_of_stmts (indent_step ^ indent) el)
            indent
      | ForLoop (v, l, b) ->
          Printf.sprintf "%sfor %s in %s {\n%s\n%s}"
            indent
            v
            (string_of_expr l)
            (string_of_stmts (indent_step ^ indent) b)
            indent
      | TryCatch (b, None, f) ->
          Printf.sprintf "%stry {\n%s\n%s} finally {\n%s\n%s}"
            indent
            (string_of_stmts (indent_step ^ indent) b)
            indent
            (string_of_stmts (indent_step ^ indent) f)
            indent
      | TryCatch (b, Some (ex, vs, c), f) ->
          Printf.sprintf "%stry {\n%s\n%s} catch %s(%s) {\n%s\n%s} finally {\n%s\n%s}"
            indent
            (string_of_stmts (indent_step ^ indent) b)
            indent
            ex
            (String.concat ", " vs)
            (string_of_stmts (indent_step ^ indent) c)
            indent
            (string_of_stmts (indent_step ^ indent) f)
            indent
      | Match (e, cases, d) ->
          let c_indent = indent_step ^ indent
          in Printf.sprintf "%smatch %s {\n%s%s\n%s}"
              indent
              (string_of_expr e)
              (String.concat "" (List.map (fun ({ Ast.enum; constr; vars }, b) ->
                  Printf.sprintf "%s%s::%s(%s) => {\n%s\n%s}\n"
                    c_indent
                    enum
                    constr
                    (String.concat ", " vars)
                    (string_of_stmts (indent_step ^ c_indent) b)
                    c_indent)
                cases))
              (Printf.sprintf "%s_ => {\n%s\n%s}"
                c_indent
                (string_of_stmts (indent_step ^ c_indent) d)
                c_indent)
              indent
    in String.concat "\n" (List.map string_of_stmt b)
  in let string_of_decl (d : Ast.decl) : string =
    match d with
    | Enum { name; ty_args; constrs } ->
        let string_of_constr (nm, tys) =
          Printf.sprintf "%s(%s)"
            nm (String.concat ", " (List.map string_of_typ tys))
        in Printf.sprintf "enum %s%s { %s }"
            name 
            (string_of_type_args ty_args)
            (String.concat ", " (List.map string_of_constr constrs))
    |  Struct { name; ty_args; fields } ->
        let string_of_field (nm, ty) =
          Printf.sprintf "%s : %s" nm (string_of_typ ty)
        in Printf.sprintf "struct %s%s { %s }"
            name
            (string_of_type_args ty_args)
            (String.concat ", " (List.map string_of_field fields))
    | Type { name; def } ->
        Printf.sprintf "type %s = %s" name (string_of_typ def)
    | Uninterp { name; ty_args; args; ret } ->
        Printf.sprintf "uninterpreted %s%s(%s) -> %s"
          name
          (string_of_type_args ty_args)
          (String.concat ", " (List.map string_of_typ args))
          (string_of_typ ret)
    | Attribute { local; name; ty } ->
        Printf.sprintf "%sattribute %s : %s"
          (if local then "local " else "")
          name
          (string_of_typ ty)
    | Element { local; name; ty } ->
        Printf.sprintf "%selement %s(%s)"
          (if local then "local " else "")
          name
          (String.concat ", " (List.map string_of_typ ty))
    | Exception { name; ty } ->
        Printf.sprintf "exception %s(%s)"
          name
          (String.concat ", " (List.map string_of_typ ty))
    | Function { name; ty_args; args; ret; body } ->
        Printf.sprintf "fn %s%s(%s) -> %s {\n%s\n}"
          name
          (string_of_type_args ty_args)
          (String.concat ", " 
            (List.map (fun (nm, t) -> nm ^ " : " ^ string_of_typ t) args))
          (string_of_typ ret)
          (string_of_stmts indent_step body)
  in String.concat "\n\n" (List.map string_of_decl prg)
