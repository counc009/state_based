(* This file defines the built-in functions of the module language and provides
 * information necessary for their compilation. *)

module TargetAst = Target.Ast_Target

let lookup_builtin (nm : string) 
  : ((TargetAst.typ * TargetAst.typ * TargetAst.funct),
      string) result =
  match nm with
  | "cons_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ConsPath
      in Ok (arg_ty, res_ty, Target.ConsPath)
  | "path_of_string" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef PathOfString
      in Ok (arg_ty, res_ty, Target.PathOfString)
  | "string_of_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef StringOfPath
      in Ok (arg_ty, res_ty, Target.StringOfPath)
  | "ends_with_dir" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef EndsWithDir
      in Ok (arg_ty, res_ty, Target.EndsWithDir)
  | "base_name" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef BaseName
      in Ok (arg_ty, res_ty, Target.BaseName)
  | "path_from" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef PathFrom
      in Ok (arg_ty, res_ty, Target.PathFrom)
  | "add_ext" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef AddExt
      in Ok (arg_ty, res_ty, Target.AddExt)
  | "norm_path" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef NormalizePath
      in Ok (arg_ty, res_ty, Target.NormalizePath)
  | "can_become" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef CanBecome
      in Ok (arg_ty, res_ty, Target.CanBecome)
  | "to_lower" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef ToLower
      in Ok (arg_ty, res_ty, Target.ToLower)
  | "substring" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef Substring
      in Ok (arg_ty, res_ty, Target.Substring)
  | "string_of_int" ->
      let (arg_ty, res_ty, _) = TargetAst.funcDef StringOfInt
      in Ok (arg_ty, res_ty, Target.StringOfInt)
  | _ -> Error ("Undefined name " ^ nm)
